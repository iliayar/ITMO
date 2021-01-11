#include "allocator.h"
#include "cache.h"

#include <gtest/gtest.h>

#include <iomanip>
#include <string>
#include <utility>

namespace {

struct WithIntKey
{
    const int key;

    WithIntKey(const int key_)
        : key(key_)
    { }

    virtual ~WithIntKey() = default;

    bool operator == (const int other_key) const
    { return key == other_key; }
};

template <std::size_t Size>
struct StringT : WithIntKey
{
    char dummy_[Size];
    std::string data;

    StringT(const int key_)
        : WithIntKey(key_)
        , data(std::to_string(key_))
    { }

    friend std::ostream & operator << (std::ostream & strm, const StringT & s)
    { return strm << s.key << "[" << s.data << "]"; }
};

struct Point : WithIntKey
{
    unsigned long long data = 0;
    bool marked = false;

    static unsigned long long convert_data(const int key)
    { return key; }

    Point(const int key_)
        : WithIntKey(key_)
        , data(key_)
    {}

    friend std::ostream & operator << (std::ostream & strm, const Point & p)
    { return strm << p.key << "[" << std::hex << std::setw(16) << p.data << "]" << (p.marked ? "{*}" : ""); }
};

template <std::size_t size>
using Size = std::integral_constant<std::size_t, size>;

template <class S>
struct SecondChanceTest : ::testing::Test
{
    static constexpr std::size_t cache_size = 13;

    Cache<int, WithIntKey, AllocatorWithPool> cache;

    using String = StringT<S::value>;

    String & get_string(const int n)
    { return cache.get<String>(n); }

    Point & get_point(const int n)
    { return cache.get<Point>(n); }

    SecondChanceTest()
        : cache(cache_size, (cache_size + 1) * std::max(sizeof(Point), sizeof(String)))
    {}
};

using TestedTypes = ::testing::Types<Size<1>, Size<9>, Size<500>>;
TYPED_TEST_SUITE(SecondChanceTest, TestedTypes);

} // anonymous namespace

TYPED_TEST(SecondChanceTest, empty)
{
    EXPECT_TRUE(this->cache.empty());
    EXPECT_EQ(0, this->cache.size());
}

TYPED_TEST(SecondChanceTest, add_two_items)
{
    const auto & s1 = this->get_string(1);
    EXPECT_EQ("1", s1.data) << "Wrong item 1: " << s1;
    const auto & s2 = this->get_string(2);
    EXPECT_EQ("2", s2.data) << "Wrong item 2: " << s2;
    EXPECT_FALSE(this->cache.empty());
    EXPECT_EQ(2, this->cache.size());
}

TYPED_TEST(SecondChanceTest, add_different_items)
{
    auto & s1 = this->get_string(111);
    EXPECT_EQ("111", s1.data) << "Wrong item 1: " << s1;
    s1.data += '@';
    auto & s2 = this->get_point(-111);
    EXPECT_EQ(static_cast<unsigned long long>(-111), s2.data) << "Wrong item 2: " << s2;
    s2.marked = true;

    EXPECT_EQ("111@", this->get_string(111).data);
    EXPECT_TRUE(this->get_point(-111).marked);
}

TYPED_TEST(SecondChanceTest, add_full)
{
    int n = -5;
    for (std::size_t i = 0; i < this->cache_size; ++i, ++n) {
        auto & s = this->get_string(n);
        const auto expected = std::to_string(n);
        EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
        s.data += '@';
    }
    EXPECT_FALSE(this->cache.empty());
    EXPECT_EQ(this->cache_size, this->cache.size());

    n = -5;
    for (std::size_t i = 0; i < this->cache_size; ++i, ++n) {
        const auto & s = this->get_string(n);
        const auto expected = std::to_string(n) + '@';
        EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
    }
    EXPECT_EQ(this->cache_size, this->cache.size());
}

TYPED_TEST(SecondChanceTest, add_full__add_new_one__not_found_first)
{
    int n = 111;
    for (std::size_t i = 0; i < this->cache_size; ++i, --n) {
        if (i % 2) {
            this->get_string(n).data += '#';
        }
        else {
            this->get_point(n).marked = true;
        }
    }
    {
        auto & s = this->get_string(1001);
        const auto expected = std::to_string(1001);
        EXPECT_EQ(expected, s.data) << "Wrong item 1001: " << s;
        s.data += '@';
    }
    for (int k = 0; k < 4; ++k) {
        EXPECT_EQ("1001@", this->get_string(1001).data) << "Wrong item 1001";
        n = 110;
        for (std::size_t i = 1; i < this->cache_size; ++i, --n) {
            if (i % 2) {
                const auto & s = this->get_string(n);
                const auto expected = std::to_string(n) + '#';
                EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
            }
            else {
                const auto & p = this->get_point(n);
                EXPECT_TRUE(p.marked) << "Wrong item " << n << ": " << p;
            }
        }
    }
    EXPECT_FALSE(this->get_point(111).marked);
}

TYPED_TEST(SecondChanceTest, add_full__revisit_first__add_new_one)
{
    int n = 117;
    for (std::size_t i = 0; i < this->cache_size; ++i, --n) {
        if (i % 2) {
            this->get_string(n).data += '&';
        }
        else {
            this->get_point(n).marked = true;
        }
    }
    EXPECT_TRUE(this->get_point(117).marked) << "Wrong item 117";
    {
        auto & s = this->get_string(1001);
        const auto expected = std::to_string(1001);
        EXPECT_EQ(expected, s.data) << "Wrong item 1001: " << s;
        s.data += '@';
    }
    for (int k = 0; k < 4; ++k) {
        EXPECT_TRUE(this->get_point(117).marked) << "Wrong item 117";
        EXPECT_EQ("1001@", this->get_string(1001).data) << "Wrong item 1001";
        n = 115;
        for (std::size_t i = 2; i < this->cache_size; ++i, --n) {
            if (i % 2) {
                const auto & s = this->get_string(n);
                const auto expected = std::to_string(n) + '&';
                EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
            }
            else {
                const auto & p = this->get_point(n);
                EXPECT_TRUE(p.marked) << "Wrong item " << n << ": " << p;
            }
        }
    }
}

TYPED_TEST(SecondChanceTest, add_full__revisit_full__add_two_new_ones)
{
    int n = 997;
    for (std::size_t i = 0; i < this->cache_size; ++i, --n) {
        if (i % 2) {
            this->get_point(n).marked = true;
        }
        else {
            this->get_string(n).data += '!';
        }
    }
    ++n;
    const std::size_t fix = (this->cache_size % 2 ? 0 : 1);
    for (std::size_t i = 0; i < this->cache_size; ++i, ++n) {
        if ((i + fix) % 2) {
            const auto & p = this->get_point(n);
            EXPECT_TRUE(p.marked) << "Wrong item " << n << ": " << p;
        }
        else {
            const auto & s = this->get_string(n);
            const auto expected = std::to_string(n) + '!';
            EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
        }
    }

    {
        auto & p = this->get_point(1113);
        EXPECT_FALSE(p.marked) << "Wrong item 1113: " << p;
        p.marked = true;
    }
    {
        auto & s = this->get_string(-97);
        const auto expected = std::to_string(-97);
        EXPECT_EQ(expected, s.data) << "Wrong item -97: " << s;
        s.data += '_';
    }

    n = 995;
    for (std::size_t i = 2; i < this->cache_size; ++i, --n) {
        if (i % 2) {
            const auto & p = this->get_point(n);
            EXPECT_TRUE(p.marked) << "Wrong item " << n << ": " << p;
        }
        else {
            const auto & s = this->get_string(n);
            const auto expected = std::to_string(n) + '!';
            EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
        }
    }
    {
        const auto & p = this->get_point(1113);
        EXPECT_TRUE(p.marked) << "Wrong item 1113: " << p;
    }
    {
        const auto & s = this->get_string(-97);
        const auto expected = std::to_string(-97) + '_';
        EXPECT_EQ(expected, s.data) << "Wrong item -97: " << s;
    }

    {
        const auto & s = this->get_string(997);
        const auto expected = std::to_string(997);
        EXPECT_EQ(expected, s.data) << "Wrong item 997: " << s;
    }
    {
        const auto & p = this->get_point(996);
        EXPECT_FALSE(p.marked) << "Wrong item 996: " << p;
    }
}

TYPED_TEST(SecondChanceTest, add_full__then_revisit_half__then_add_half)
{
    int n = 10000;
    for (std::size_t i = 0; i < this->cache_size; ++i, --n) {
        auto & s = this->get_string(n);
        const auto expected = std::to_string(n);
        EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
        s.data += '@';
    }
    EXPECT_FALSE(this->cache.empty());
    EXPECT_EQ(this->cache_size, this->cache.size());

    n = 10000;
    for (std::size_t i = 0; i < this->cache_size / 2; ++i, n -= 2) {
        auto & s = this->get_string(n);
        const auto expected = std::to_string(n) + '@';
        EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
        s.data += '!';
    }
    EXPECT_EQ(this->cache_size, this->cache.size());

    n = -5;
    for (std::size_t i = 0; i < this->cache_size / 2; ++i, ++n) {
        auto & p = this->get_point(n);
        const auto expected = Point::convert_data(n);
        EXPECT_EQ(expected, p.data) << "Wrong item " << n << ": " << p;
        EXPECT_FALSE(p.marked) << "Wrong item " << n << ": " << p;
        p.marked = true;
    }
    EXPECT_EQ(this->cache_size, this->cache.size());

    n = 10000;
    for (std::size_t i = 0; i < this->cache_size / 2; ++i, n -= 2) {
        const auto & s = this->get_string(n);
        const auto expected = std::to_string(n) + "@!";
        EXPECT_EQ(expected, s.data) << "Wrong item " << n << ": " << s;
    }
    n = -5;
    for (std::size_t i = 0; i < this->cache_size / 2; ++i, ++n) {
        auto & p = this->get_point(n);
        const auto expected = Point::convert_data(n);
        EXPECT_EQ(expected, p.data) << "Wrong item " << n << ": " << p;
        EXPECT_TRUE(p.marked) << "Wrong item " << n << ": " << p;
        p.marked = true;
    }
    EXPECT_EQ(this->cache_size, this->cache.size());
}
