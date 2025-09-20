#include "hash_set.h"
#include "utils.h"

#include <gtest/gtest.h>

#include <set>
#include <string>
#include <type_traits>

using namespace test_utils;

namespace {

struct CountingHashSetTest : ::testing::Test
{
    HashSet<ConstructionAware, LinearProbing, CustomHash, CustomEqual> set;
};

template <class Policy>
struct BadHashingHashSetTest : ::testing::Test
{
    HashSet<std::string, Policy, BadHash> set;
};

struct ComplexConstructionHashSetTest : ::testing::Test
{
    HashSet<std::string> set;
};

template <class T>
struct HashSetTest
    : ::testing::Test
    , Converter<T>
{
    using Set = HashSet<T>;
    Set set;
};

template <class T>
using HashSetTest_CopyableElems = HashSetTest<T>;

using TestedTypes = ::testing::Types<int, std::string, NonCopyable>;
using CopyableTestedTypes = ::testing::Types<int, std::string>;
using BadHashPolicies = ::testing::Types<LinearProbing, QuadraticProbing>;
TYPED_TEST_SUITE(HashSetTest, TestedTypes);
TYPED_TEST_SUITE(HashSetTest_CopyableElems, CopyableTestedTypes);
TYPED_TEST_SUITE(BadHashingHashSetTest, BadHashPolicies);

} // anonymous namespace

TYPED_TEST(HashSetTest, check_types)
{
    using Set = typename std::remove_pointer_t<decltype(this)>::Set;
    using Value = std::remove_reference_t<decltype(*std::declval<Set>().begin())>;
    static_assert(std::is_same_v<TypeParam, typename Set::key_type>,
            "key_type should be equal to element type parameter");
    static_assert(std::is_same_v<TypeParam, typename Set::value_type>,
            "value_type should be equal to element type parameter");
    static_assert(std::is_same_v<TypeParam *, typename Set::pointer>,
            "pointer should be equal to pointer to element type parameter");
    static_assert(std::is_same_v<TypeParam &, typename Set::reference>,
            "reference should be equal to reference to element type parameter");
    static_assert(std::is_constructible_v<typename Set::const_iterator, typename Set::iterator>,
            "const_iterator should be constructible from iterator");
    static_assert(std::is_same_v<const TypeParam, Value>,
            "iteration should be non-mutable");
}

TYPED_TEST(HashSetTest, empty)
{
    EXPECT_TRUE(this->set.empty());
    EXPECT_EQ(0, this->set.size());
    {
        std::size_t count = 0;
        for ([[maybe_unused]] const auto & x : this->set) {
            ++count;
        }
        EXPECT_EQ(0, count);
    }
    EXPECT_FALSE(this->set.contains(this->create(0)));
    EXPECT_FALSE(this->set.contains(this->create(1)));
    EXPECT_FALSE(this->set.contains(this->create(101)));
    EXPECT_EQ(this->set.end(), this->set.find(this->create(3)));
    {
        const auto [begin, end] = this->set.equal_range(this->create(5));
        EXPECT_EQ(end, begin);
        EXPECT_EQ(this->set.end(), begin);
    }
}

TYPED_TEST(HashSetTest, max_size)
{
    EXPECT_LE(this->set.max_size(), this->set.max_bucket_count());
}

TYPED_TEST(HashSetTest, reserve_does_not_change_size)
{
    this->set.reserve(1001);
    EXPECT_TRUE(this->set.empty());
    EXPECT_EQ(0, this->set.size());
}

TYPED_TEST(HashSetTest, singleton)
{
    const auto element = this->create(0);
    this->set.emplace(this->copy(element));
    EXPECT_FALSE(this->set.empty());
    EXPECT_EQ(1, this->set.size());
    {
        std::size_t count = 0;
        for (const auto & x : this->set) {
            EXPECT_EQ(x, element);
            ++count;
        }
        EXPECT_EQ(1, count);
    }
    EXPECT_TRUE(this->set.contains(element));
    EXPECT_NE(this->set.end(), this->set.find(element));
    EXPECT_EQ(this->set.begin(), this->set.find(element));
    {
        auto [begin, end] = this->set.equal_range(element);
        EXPECT_EQ(this->set.begin(), begin);
        EXPECT_NE(begin, end);
        ++begin;
        EXPECT_EQ(begin, end);
    }
}

TYPED_TEST(HashSetTest, many)
{
    const std::initializer_list<TypeParam> present_elements = {this->create(0), this->create(1), this->create(2), this->create(3), this->create(4)};
    const std::initializer_list<TypeParam> missing_elements = {this->create(5), this->create(6), this->create(7), this->create(8), this->create(9)};
    for (const auto & x : present_elements) {
        const auto [it, success] = this->set.emplace(this->copy(x));
        EXPECT_TRUE(success);
        EXPECT_EQ(x, *it);
    }
    EXPECT_EQ(present_elements.size(), this->set.size());
    for (const auto & x : present_elements) {
        EXPECT_TRUE(this->set.contains(x));
        const auto [it, success] = this->set.emplace(this->copy(x));
        EXPECT_FALSE(success);
        EXPECT_EQ(x, *it);
    }
    EXPECT_EQ(present_elements.size(), this->set.size());
    for (const auto & y : missing_elements) {
        EXPECT_FALSE(this->set.contains(y));
        EXPECT_EQ(this->set.end(), this->set.find(y));
        {
            const auto [begin, end] = this->set.equal_range(y);
            EXPECT_EQ(begin, end);
            EXPECT_EQ(this->set.end(), begin);
        }
    }
}

TYPED_TEST(HashSetTest, iter_through)
{
    const auto max = 1009;
    for (int i = 0; i < max; ++i) {
        EXPECT_TRUE(this->set.emplace(this->create(i)).second);
    }
    const auto end = this->set.end();
    for (int i = 0; i < max; ++i) {
        EXPECT_NE(end, this->set.find(this->create(i)));
    }
    std::set<int> values;
    std::size_t count = 0;
    for (const auto & x : this->set) {
        const int v = this->value(x);
        EXPECT_LE(0, v);
        EXPECT_GT(max, v);
        values.insert(v);
        ++count;
    }
    EXPECT_EQ(max, values.size());
    EXPECT_EQ(max, count);
    EXPECT_EQ(max, this->set.size());
}

TYPED_TEST(HashSetTest, buckets)
{
    const auto max = 919;
    for (int i = 0; i < max; ++i) {
        EXPECT_TRUE(this->set.emplace(this->create(i)).second);
    }
    const auto bucket_num = this->set.bucket_count();
    EXPECT_LE(max, bucket_num);
    for (int i = 0; i < max; ++i) {
        const auto bucket_i = this->set.bucket(this->create(i));
        EXPECT_LE(0, bucket_i);
        EXPECT_GT(bucket_num, bucket_i);
        EXPECT_EQ(1, this->set.bucket_size(bucket_i));
    }
    for (std::size_t k = 0; k < this->set.bucket_count(); ++k) {
        EXPECT_GE(1, this->set.bucket_size(k));
    }
}

TYPED_TEST(HashSetTest, load_factor_and_rehash)
{
    EXPECT_GE(1.0, this->set.load_factor());

    this->set.emplace(this->create(1));
    this->set.emplace(this->create(2));
    this->set.emplace(this->create(3));

    float lf = this->set.size();
    lf /= this->set.bucket_count();
    EXPECT_FLOAT_EQ(lf, this->set.load_factor());
    EXPECT_GE(1.0, this->set.load_factor());

    std::size_t buckets = static_cast<std::size_t>(this->set.size() / this->set.max_load_factor());
    this->set.rehash(0);
    EXPECT_LE(buckets, this->set.bucket_count());

    const std::size_t new_size = 997;
    buckets = static_cast<std::size_t>(new_size / this->set.max_load_factor());
    this->set.reserve(new_size);
    EXPECT_LE(buckets, this->set.bucket_count());
    EXPECT_GE(1.0, this->set.load_factor());
}

TYPED_TEST(HashSetTest, add_and_remove)
{
    const std::initializer_list<TypeParam> elements = {this->create(0), this->create(1), this->create(2), this->create(3), this->create(4), this->create(5), this->create(6), this->create(7)};
    for (const auto & x : elements) {
        this->set.emplace(this->copy(x));
    }
    {
        int i = 0;
        for (const auto & x : elements) {
            if (i % 2) {
                EXPECT_EQ(1, this->set.erase(x));
            }
            ++i;
        }
    }
    EXPECT_EQ(elements.size() / 2, this->set.size());
    {
        int i = 0;
        for (const auto & x : elements) {
            if (i % 2) {
                EXPECT_FALSE(this->set.contains(x));
            }
            else {
                EXPECT_TRUE(this->set.contains(x));
            }
            ++i;
        }
    }
    {
        auto first = this->set.begin();
        const auto end = this->set.end();
        ++first;
        auto last = first;
        for (auto next = last; next != end; ++next) {
            last = next;
        }
        const auto first_el = this->copy(*this->set.begin());
        const auto last_el = this->copy(*last);
        EXPECT_EQ(2, std::distance(first, last));
        this->set.erase(first, last);
        EXPECT_EQ(2, this->set.size());
        EXPECT_TRUE(this->set.contains(first_el));
        EXPECT_TRUE(this->set.contains(last_el));
    }
}

TYPED_TEST(HashSetTest, erase)
{
    for (int i = 0; i < 50; ++i) {
        EXPECT_TRUE(this->set.emplace(this->create(i)).second);
    }
    EXPECT_EQ(50, this->set.size());
    for (int i = 0; i < 50; i += 2) {
        const auto it = this->set.find(this->create(i));
        EXPECT_NE(this->set.end(), it);
        this->set.erase(it);
    }
    EXPECT_EQ(25, this->set.size());
    for (int i = 0; i < 50; i += 2) {
        const auto it = this->set.find(this->create(i));
        EXPECT_EQ(this->set.end(), it);
    }
    for (int i = 1; i < 50; i += 2) {
        const auto it = this->set.find(this->create(i));
        EXPECT_NE(this->set.end(), it);
    }
}

TYPED_TEST(HashSetTest, emplace_hint)
{
    auto hint = this->set.cend();
    for (int i = 0; i < 1000; ++i) {
        hint = this->set.emplace_hint(hint, this->create(i));
        hint = this->set.emplace_hint(hint, this->create(i));
        hint = this->set.emplace_hint(hint, this->create(i));
    }
    for (int i = 0; i < 1000; ++i) {
        EXPECT_TRUE(this->set.contains(this->create(i)));
    }
}

TYPED_TEST(HashSetTest, no_iterator_invalidation)
{
    this->set.reserve(2000);
    const int max = 1109;
    std::vector<decltype(this->set.cbegin())> first_ten;
    first_ten.reserve(10);
    for (int i = 0; i < 10; ++i) {
        const auto [it, success] = this->set.emplace(this->create(i));
        EXPECT_TRUE(success);
        first_ten.push_back(it);
    }
    {
        int i = 0;
        for (const auto it : first_ten) {
            EXPECT_EQ(i, this->value(*it));
            ++i;
        }
    }
    for (int i = 0; i < max; ++i) {
        const bool success = this->set.emplace(this->create(i)).second;
        if (i < 10) {
            EXPECT_FALSE(success);
        }
        else {
            EXPECT_TRUE(success);
        }
    }
    {
        int i = 0;
        for (const auto it : first_ten) {
            EXPECT_EQ(i, this->value(*it));
            ++i;
        }
    }
}

TYPED_TEST(HashSetTest_CopyableElems, insert_range)
{
    std::vector<TypeParam> elements;
    for (int i = 0; i < 9999; ++i) {
        elements.push_back(this->create(i));
    }
    this->set.insert(elements.begin(), elements.end());
    EXPECT_EQ(elements.size(), this->set.size());
}

TEST_F(CountingHashSetTest, insert)
{
    ConstructionAware::reset_counters();
    const int max = 631;
    set.reserve(max);
    for (int i = 0; i < max; ++i) {
        set.insert(i);
    }
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_EQ(max, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
}

TEST_F(CountingHashSetTest, emplace)
{
    ConstructionAware::reset_counters();
    const int max = 1999;
    set.reserve(max);
    for (int i = 0; i < max; ++i) {
        set.emplace(i);
    }
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_GE(max, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
    ConstructionAware::reset_counters();
    for (int i = 0; i < max; ++i) {
        set.emplace(i);
    }
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
}

TEST_F(CountingHashSetTest, emplace_hint)
{
    ConstructionAware::reset_counters();
    set.emplace_hint(set.end(), 1);
    EXPECT_EQ(1, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_GE(1, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
}

TEST_F(CountingHashSetTest, resize_during_insert)
{
    ConstructionAware::reset_counters();
    const int max = 491;
    for (int i = 0; i < max; ++i) {
        set.emplace(i);
    }
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    // there can be many move constructions
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
}

TEST_F(CountingHashSetTest, copy)
{
    ConstructionAware::reset_counters();
    const int max = 11;
    set.reserve(max);
    for (int i = 0; i < max; ++i) {
        set.emplace(i);
    }
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_GE(max, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
    decltype(set) another = set;
    EXPECT_EQ(set, another);
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(max, ConstructionAware::copy_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
}

TEST_F(CountingHashSetTest, move)
{
    ConstructionAware::reset_counters();
    const int max = 11;
    set.reserve(max);
    for (int i = 0; i < max; ++i) {
        set.emplace(i);
    }
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_GE(max, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
    decltype(set) another = std::move(set);
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
}

TEST_F(CountingHashSetTest, swap)
{
    ConstructionAware::reset_counters();
    const int max = 11;
    set.reserve(max);
    for (int i = 0; i < max; ++i) {
        set.emplace(i);
    }
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_GE(max, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
    decltype(set) another;
    another.swap(std::move(set));
    EXPECT_EQ(max, ConstructionAware::constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_constructor_calls_count());
    EXPECT_EQ(0, ConstructionAware::copy_assignment_calls_count());
    EXPECT_EQ(0, ConstructionAware::move_assignment_calls_count());
}

TYPED_TEST(BadHashingHashSetTest, insert_with_collisions)
{
    const auto create = [] (const std::size_t x) {
        const std::size_t n = x / 100 + 1;
        std::string s(n, ' ');
        const unsigned char ch = 32 + x % 100;
        for (std::size_t i = 0; i < n; ++i) {
            s[i] = ch;
        }
        return s;
    };
    const std::size_t max = 1087;
    this->set.reserve(max / 3);
    for (std::size_t i = 0; i < max; ++i) {
        const auto s = create(i);
        const bool success = this->set.insert(s).second;
        EXPECT_TRUE(success) << s << " wasn't inserted";
        EXPECT_GE(1.0, this->set.load_factor());
    }
    EXPECT_EQ(max, this->set.size());
    EXPECT_TRUE(this->set.contains(create(333)));
    EXPECT_FALSE(this->set.contains(create(max)));
    EXPECT_FALSE(this->set.contains(create(max + 1)));
    EXPECT_FALSE(this->set.contains(create(max + 7)));
    EXPECT_FALSE(this->set.contains(create(max + 100)));
    EXPECT_FALSE(this->set.contains(create(max + 200)));
    EXPECT_GE(1.0, this->set.load_factor());
    for (std::size_t i = 0; i < this->set.bucket_count(); ++i) {
        EXPECT_GE(1, this->set.bucket_size(i));
    }
}

TEST_F(ComplexConstructionHashSetTest, emplace)
{
    const std::vector<std::string_view> elements = {
        "The",
        "quick",
        "brown fox",
        "jumps",
        "over",
        "the",
        "lazy dog"
    };
    for (const auto s : elements) {
        set.emplace(s.data(), s.size());
    }
    const std::string s_copy("copy");
    std::string s_move("move");
    set.emplace(s_copy);
    set.emplace(std::move(s_move));
    EXPECT_TRUE(set.contains("quick"));
    EXPECT_TRUE(set.contains("copy"));
    EXPECT_TRUE(set.contains("move"));
}
