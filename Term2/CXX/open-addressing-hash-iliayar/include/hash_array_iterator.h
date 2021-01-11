#pragma once

#include "states.h"
#include <cassert>
#include <iterator>

template<class Value, class Container>
class hash_array_iterator
{
  public:
    using iterator_category = std::forward_iterator_tag;
    using difference_type = std::ptrdiff_t;
    using distance_type = std::size_t;
    using value_type = Value;
    using pointer = value_type*;
    using reference = value_type&;

    hash_array_iterator(){};
    hash_array_iterator(const Container* container, std::size_t index)
      : m_container(container)
      , m_index(index)
    {
        if (index < m_container->m_capacity &&
            (m_container->m_states[index] != State::SET))
            ++(*this);
    }

    hash_array_iterator& operator++()
    {
        next();
        return *this;
    }

    hash_array_iterator operator++(int)
    {
        size_t res = m_index;
        next();
        return hash_array_iterator(m_container, res);
    }

    reference operator*() const
    {
        assert(m_index < m_container->m_data.size());
        return *(m_container->m_data[m_index]);
    }

    pointer operator->() const
    {
        assert(m_index < m_container->m_data.size());
        return m_container->m_data[m_index].get();
    }

    friend bool operator==(const hash_array_iterator& lhs,
                           const hash_array_iterator& rhs)
    {
        return lhs.m_index == rhs.m_index;
    }
    friend bool operator!=(const hash_array_iterator& lhs,
                           const hash_array_iterator& rhs)
    {
        return !(lhs.m_index == rhs.m_index);
    }

  private:
    void next()
    {
        do {
            m_index++;
        } while (m_index < m_container->m_capacity &&
                 (m_container->m_states[m_index] != State::SET));
    }

  public:
    const Container* m_container;
    std::size_t m_index;
};

template<class Value, class Container>
class const_hash_array_iterator
{
  public:
    using iterator_category = std::forward_iterator_tag;
    using difference_type = std::ptrdiff_t;
    using distance_type = std::size_t;
    using value_type = const Value;
    using pointer = value_type*;
    using reference = value_type&;

    const_hash_array_iterator(){};
    const_hash_array_iterator(hash_array_iterator<Value, Container> it)
      : m_container(it.m_container)
      , m_index(it.m_index)
    {}
    const_hash_array_iterator(const Container* container, std::size_t index)
      : m_container(container)
      , m_index(index)
    {
        if (index < m_container->m_capacity &&
            (m_container->m_states[index] != State::SET))
            ++(*this);
    }

    const_hash_array_iterator& operator++()
    {
        next();
        return *this;
    }

    const_hash_array_iterator operator++(int)
    {
        size_t res = m_index;
        next();
        return const_hash_array_iterator(m_container, res);
    }

    reference operator*() const
    {
        assert(m_index < m_container->m_data.size());
        return *(m_container->m_data[m_index]);
    }

    pointer operator->() const
    {
        assert(m_index < m_container->m_data.size());
        return m_container->m_data[m_index].get();
    }

    friend bool operator==(const const_hash_array_iterator& lhs,
                           const const_hash_array_iterator& rhs)
    {
        return lhs.m_index == rhs.m_index;
    }
    friend bool operator!=(const const_hash_array_iterator& lhs,
                           const const_hash_array_iterator& rhs)
    {
        return !(lhs.m_index == rhs.m_index);
    }

  private:
    void next()
    {
        do {
            m_index++;
        } while (m_index < m_container->m_capacity &&
                 (m_container->m_states[m_index] != State::SET));
    }

  public:
    const Container* m_container;
    std::size_t m_index;
};
