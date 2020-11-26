#include "pool.h"

#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <unordered_map>
#include <vector>

namespace {

template <std::size_t Size>
struct Dummy
{
    unsigned char data[Size];

    Dummy()
    {
        for (std::size_t i = 0; i < Size; ++i) {
            data[i] = 0x5a;
        }
    }

    ~Dummy()
    {
        for (std::size_t i = 0; i < Size; ++i) {
            data[i] = 0xa5;
        }
    }

    bool check() const
    {
        for (std::size_t i = 0; i < Size; ++i) {
            if (data[i] != 0x5a) {
                return false;
            }
        }
        return true;
    }
};

struct Complex
{
    int a;
    char & b;
    const double c;

    Complex(const int a_, char & b_, const double c_)
        : a(a_), b(b_), c(c_)
    {}

    ~Complex()
    {
        a = -1;
    }
};

template <std::size_t Size, std::size_t Count>
struct Params
{
    static constexpr std::size_t size = Size;
    static constexpr std::size_t count = Count;
};

template <class T>
class Pointer
{
    std::optional<PoolAllocator::pointer> m_ptr;
public:
    Pointer() = default;

    Pointer(const PoolAllocator::pointer ptr)
        : m_ptr(ptr)
    {}

    Pointer & operator = (const std::nullptr_t)
    {
        m_ptr.reset();
        return *this;
    }

    explicit operator bool () const
    { return m_ptr.has_value(); }

    PoolAllocator::pointer get() const
    { return m_ptr.value(); }

    T * operator -> () const
    { return static_cast<T *>(**m_ptr); }

    T & operator * () const
    { return *static_cast<T *>(**m_ptr); }
};

template <class P>
struct AllocatorTest : ::testing::Test
{
    static constexpr std::size_t pool_size = P::size * P::count;

    PoolAllocator alloc;

    template <class T, class... Args>
    Pointer<T> create(Args &&... args)
    {
        auto aptr = alloc.allocate(sizeof(T));
        new (*aptr) T(std::forward<Args>(args)...);
        return aptr;
    }

    template <class T>
    void destroy(const Pointer<T> ptr)
    {
        if (ptr) {
            ptr->~T();
            alloc.deallocate(ptr.get());
        }
    }

    AllocatorTest()
        : alloc(pool_size)
    {}

    using D = Dummy<P::size>;
    using DPtr = Pointer<D>;

    DPtr create_dummy()
    {
        return create<D>();
    }

    void destroy_dummy(const DPtr ptr)
    {
        destroy(ptr);
    }

    using CPtr = Pointer<Complex>;

    CPtr create_complex(const int a, char & b, const double c)
    {
        return create<Complex>(a, b, c);
    }

    void destroy_complex(const CPtr ptr)
    {
        destroy(ptr);
    }
};

using TestedTypes = ::testing::Types<Params<1, 1>, Params<1, 24>, Params<3, 1>, Params<7, 4>, Params<7, 15>, Params<10, 10>, Params<256, 1>, Params<256, 256>>;
TYPED_TEST_SUITE(AllocatorTest, TestedTypes);

} // anonymous namespace

TYPED_TEST(AllocatorTest, single_dummy)
{
    auto ptr = this->create_dummy();
    ptr->data[0] = 112;
    this->destroy_dummy(ptr);
}

TYPED_TEST(AllocatorTest, single_complex)
{
    char x = '@';
    if (this->pool_size >= sizeof(Complex)) {
        auto ptr = this->create_complex(-511, x, 0.05);
        EXPECT_EQ(-511, ptr->a);
        EXPECT_EQ('@', ptr->b);
        EXPECT_EQ(0.05, ptr->c);
        this->destroy_complex(ptr);
    }
    else {
        EXPECT_THROW(this->create_complex(0, x, 0.01), std::bad_alloc);
    }
}

TYPED_TEST(AllocatorTest, full_dummy)
{
    using Ptr = decltype(this->create_dummy());
    std::vector<Ptr> ptrs;
    for (std::size_t i = 0; i < TypeParam::count; ++i) {
        auto ptr = this->create_dummy();
        ptr->data[0] = 199;
        ptrs.push_back(ptr);
    }
    EXPECT_THROW(this->create_dummy(), std::bad_alloc);
    EXPECT_THROW(this->create_dummy(), std::bad_alloc);
    for (auto ptr : ptrs) {
        EXPECT_EQ(199, ptr->data[0]);
        this->destroy_dummy(ptr);
    }
    EXPECT_NO_THROW(this->destroy_dummy(this->create_dummy()));
}

TYPED_TEST(AllocatorTest, full_complex)
{
    using Ptr = decltype(this->create_complex(1, std::declval<char &>(), 0.1));
    const std::size_t complex_count = this->pool_size / sizeof(Complex);
    std::vector<Ptr> ptrs;
    char x = 'X';
    int n = -11;
    const double d = 1.11e-3;
    for (std::size_t i = 0; i < complex_count; ++i, --n) {
        auto ptr = this->create_complex(n, x, d);
        EXPECT_EQ(n, ptr->a);
        EXPECT_EQ(x, ptr->b);
        EXPECT_EQ(d, ptr->c);
        ptrs.push_back(ptr);
    }
    if (this->pool_size >= sizeof(Complex)) {
        EXPECT_THROW(this->create_complex(0, x, 0.01), std::bad_alloc);
    }
    n = -11;
    for (auto ptr : ptrs) {
        EXPECT_EQ(n, ptr->a);
        EXPECT_EQ(x, ptr->b);
        EXPECT_EQ(d, ptr->c);
        --n;
        this->destroy_complex(ptr);
    }
    if (this->pool_size >= sizeof(Complex)) {
        EXPECT_NO_THROW(this->destroy_complex(this->create_complex(0, x, 0.01)));
    }
}

TYPED_TEST(AllocatorTest, full_mixed)
{
    using DPtr = decltype(this->create_dummy());
    using CPtr = decltype(this->create_complex(1, std::declval<char &>(), 0.1));
    std::vector<DPtr> d_ptrs;
    std::vector<CPtr> c_ptrs;
    char x = '7';
    const double d = 100.99;
    const int n = -113;
    const unsigned char u = 0x1F;
    std::size_t available = this->pool_size;
    while (available >= TypeParam::size || available >= sizeof(Complex)) {
        if (available >= sizeof(Complex)) {
            c_ptrs.push_back(this->create_complex(n, x, d));
            available -= sizeof(Complex);
        }
        if (available >= TypeParam::size) {
            d_ptrs.push_back(this->create_dummy());
            d_ptrs.back()->data[0] = u;
            available -= TypeParam::size;
        }
    }
    EXPECT_TRUE(available < TypeParam::size && available < sizeof(Complex));
    EXPECT_THROW(this->create_dummy(), std::bad_alloc);
    if (this->pool_size >= sizeof(Complex)) {
        EXPECT_THROW(this->create_complex(0, x, 0.01), std::bad_alloc);
    }
    for (auto ptr : c_ptrs) {
        EXPECT_EQ(n, ptr->a);
        EXPECT_EQ(x, ptr->b);
        EXPECT_EQ(d, ptr->c);
        this->destroy_complex(ptr);
    }
    for (auto ptr : d_ptrs) {
        EXPECT_EQ(u, ptr->data[0]);
        this->destroy_dummy(ptr);
    }
}

TYPED_TEST(AllocatorTest, dummy_fragmentation)
{
    using DPtr = decltype(this->create_dummy());
    using CPtr = decltype(this->create_complex(1, std::declval<char &>(), 0.1));
    std::vector<DPtr> d_ptrs;
    for (std::size_t i = 0; i < TypeParam::count; ++i) {
        d_ptrs.push_back(this->create_dummy());
    }

    std::size_t available = 0;
    for (std::size_t i = 0; i < TypeParam::count; i += 2) {
        this->destroy_dummy(d_ptrs[i]);
        d_ptrs[i] = nullptr;
        available += TypeParam::size;
    }

    char x = ' ';
    const double d = 0xF.Fp10;
    int n = 0;
    std::vector<CPtr> c_ptrs;
    while (available >= 2 * sizeof(Complex)) {
        EXPECT_NO_THROW(c_ptrs.push_back(this->create_complex(n, x, d)));
        ++n;
        available -= sizeof(Complex);
    }

    for (auto ptr : d_ptrs) {
        if (ptr) {
            EXPECT_TRUE(ptr->check());
        }
        this->destroy_dummy(ptr);
    }
    n = 0;
    for (auto ptr : c_ptrs) {
        EXPECT_EQ(n, ptr->a);
        EXPECT_EQ(x, ptr->b);
        EXPECT_EQ(d, ptr->c);
        this->destroy_complex(ptr);
        ++n;
    }
}

TYPED_TEST(AllocatorTest, complex_fragmentation)
{
    using DPtr = decltype(this->create_dummy());
    using CPtr = decltype(this->create_complex(1, std::declval<char &>(), 0.1));
    const std::size_t complex_num = this->pool_size / sizeof(Complex);
    char x = ' ';
    const double d = 0xF.Fp10;
    int n = 0;
    std::vector<CPtr> c_ptrs;
    for (std::size_t i = 0; i < complex_num; ++i) {
        c_ptrs.push_back(this->create_complex(n, x, d));
        ++n;
    }

    std::size_t available = 0;
    for (std::size_t i = 0; i < complex_num; i += 2) {
        this->destroy_complex(c_ptrs[i]);
        c_ptrs[i] = nullptr;
        available += sizeof(Complex);
    }

    std::vector<DPtr> d_ptrs;
    while (available >= 2 * TypeParam::size) {
        EXPECT_NO_THROW(d_ptrs.push_back(this->create_dummy()));
        available -= TypeParam::size;
    }

    n = 0;
    for (auto ptr : c_ptrs) {
        if (ptr) {
            EXPECT_EQ(n, ptr->a);
            EXPECT_EQ(x, ptr->b);
            EXPECT_EQ(d, ptr->c);
        }
        this->destroy_complex(ptr);
        ++n;
    }
    for (auto ptr : d_ptrs) {
        EXPECT_TRUE(ptr->check());
        this->destroy_dummy(ptr);
    }
}
