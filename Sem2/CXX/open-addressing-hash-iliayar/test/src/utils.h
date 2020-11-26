#pragma once

#include <functional>
#include <string>

namespace test_utils {

class ConstructionAware
{
    static std::size_t constructor_calls;
    static std::size_t copy_constructor_calls;
    static std::size_t move_constructor_calls;
    static std::size_t copy_assignment_calls;
    static std::size_t move_assignment_calls;

    int m_data = 0;
public:
    static void reset_counters()
    {
        constructor_calls = 0;
        copy_constructor_calls = 0;
        move_constructor_calls = 0;
        copy_assignment_calls = 0;
        move_assignment_calls = 0;
    }
    static std::size_t constructor_calls_count()
    { return constructor_calls; }
    static std::size_t copy_constructor_calls_count()
    { return copy_constructor_calls; }
    static std::size_t move_constructor_calls_count()
    { return move_constructor_calls; }
    static std::size_t copy_assignment_calls_count()
    { return copy_assignment_calls; }
    static std::size_t move_assignment_calls_count()
    { return move_assignment_calls; }

    ConstructionAware(const int data = 0)
        : m_data(data)
    { ++constructor_calls; }
    ConstructionAware(const ConstructionAware & other)
        : m_data(other.m_data)
    { ++copy_constructor_calls; }
    ConstructionAware(ConstructionAware && other)
        : m_data(other.m_data)
    { ++move_constructor_calls; }
    ConstructionAware & operator = (const ConstructionAware & other)
    {
        m_data = other.m_data;
        ++copy_assignment_calls;
        return *this;
    }
    ConstructionAware & operator = (ConstructionAware && other)
    {
        m_data = other.m_data;
        ++move_assignment_calls;
        return *this;
    }

    int value() const
    { return m_data; }

    friend bool operator == (const ConstructionAware & lhs, const ConstructionAware & rhs)
    { return lhs.value() == rhs.value(); }
};

struct CustomHash : std::hash<int>
{
    std::size_t operator() (const ConstructionAware & x) const
    { return std::hash<int>::operator() (x.value()); }
    std::size_t operator() (const int x) const
    { return std::hash<int>::operator() (x); }
};

struct CustomEqual
{
    bool operator () (const ConstructionAware & lhs, const ConstructionAware & rhs) const
    { return lhs.value() == rhs.value(); }
    bool operator() (const ConstructionAware & lhs, const int rhs) const
    { return lhs.value() == rhs; }
    bool operator () (const int lhs, const ConstructionAware & rhs) const
    { return lhs == rhs.value(); }
};

struct BadHash
{
    std::size_t operator() (const std::string & x) const
    { return x.size(); }
};

class NonCopyable
{
    int m_data = 0;
public:
    NonCopyable() = default;
    NonCopyable(const int data) : m_data(data) {}
    NonCopyable(const NonCopyable &) = delete;
    NonCopyable(NonCopyable &&) = default;
    NonCopyable & operator = (NonCopyable &&) = default;

    operator int () const { return m_data; }
    NonCopyable & operator = (const int value)
    {
        m_data = value;
        return *this;
    }

    NonCopyable & operator *= (const NonCopyable & other)
    {
        m_data *= other.m_data;
        return *this;
    }

    int value() const { return m_data; }

    friend bool operator == (const int lhs, const NonCopyable & rhs)
    { return lhs == rhs.m_data; }
};

template <class T>
struct FromInt;

template <>
struct FromInt<int>
{
    static int create(const int x)
    { return x; }
};

template <>
struct FromInt<std::string>
{
    static std::string create(const int x)
    { return std::to_string(x); }
};

template <>
struct FromInt<NonCopyable>
{
    static NonCopyable create(const int x)
    { return x; }
};

template <class T>
struct ToInt;

template <>
struct ToInt<int>
{
    static int value(const int x)
    { return x; }
};

template <>
struct ToInt<std::string>
{
    static int value(const std::string & x)
    { return std::stoi(x); }
};

template <>
struct ToInt<NonCopyable>
{
    static int value(const NonCopyable & x)
    { return x.value(); }
};

template <class T>
struct Copy
{
    static T copy(const T & x)
    { return x; }
};

template <>
struct Copy<NonCopyable>
{
    static NonCopyable copy(const NonCopyable & x)
    { return x.value(); }
};

template <class T>
struct Converter
    : FromInt<T>
    , ToInt<T>
    , Copy<T>
{};

} // test_utils namespace

namespace std {

template <>
struct hash<test_utils::NonCopyable> : std::hash<int>
{
    std::size_t operator () (const test_utils::NonCopyable & x) const
    {
        return std::hash<int>::operator () (x.value());
    }
};

} // std namespace
