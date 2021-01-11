#pragma once

#include "states.h"
#include <iterator>
#include <memory>
#include <vector>

template<class ValueType,
         class KeyType,
         class SizeType,
         class CollisionPolicy,
         class Hash,
         class Equal,
         class Iterator>
class HashArray
{

  protected:
    HashArray(const Hash& hash = Hash(), const Equal& equal = Equal())
      : m_hash(hash)
      , m_equal(equal)
    {}

  public:
    void rehash(const SizeType count)
    {
        if (count <= m_capacity)
            return;
        SizeType old_size = m_capacity;
        m_capacity = std::max(count, m_capacity);
        std::vector<std::unique_ptr<ValueType>> old_data = std::move(m_data);
        std::vector<State> old_states = std::move(m_states);
	
        init_arrays();
        m_size = 0;

        for (SizeType i = 0; i < old_size; ++i) {
            if (old_states[i] == State::SET) {
                insert_imp(std::move(old_data[i]));
            }
        }
    }

  private:
    virtual const KeyType& get_key(const ValueType& value) const = 0;
    virtual Iterator get_iterator(const SizeType index) const = 0;

  protected:
    std::pair<Iterator, bool> insert_imp(std::unique_ptr<ValueType>&& value,
                                         SizeType hint)
    {
        SizeType index = find_free_or_equal(get_key(*value), hint);
        if (m_states[index] == State::SET) {
            return { get_iterator(index), false };
        }
        m_data[index] = std::move(value);
        m_states[index] = State::SET;
        m_size++;
        return { get_iterator(index), true };
    }
    std::pair<Iterator, bool> insert_imp(std::unique_ptr<ValueType>&& value)
    {
        return insert_imp(std::move(value), m_hash(get_key(*value)));
    }

    void init_arrays()
    {
        m_data.resize(m_capacity);
        m_states.resize(m_capacity, State::EMPTY);
    }

    SizeType find_free_or_equal(const KeyType& key)
    {
        return find_free_or_equal(key, m_hash(key));
    }
    SizeType find_free_or_equal(const KeyType& key) const
    {
        return find_free_or_equal(key, m_hash(key));
    }
    SizeType find_free_or_equal(const KeyType& key, SizeType hint)
    {
        if (m_capacity == 0) {
            rehash(2);
            return find_free_or_equal(key, hint);
        }
        SizeType res = find_free_or_equal_no_rehash(key, hint);
        if (res == m_capacity) {
            rehash(m_capacity * 2);
            return find_free_or_equal(key, hint);
        } else {
            return res;
        }
    }
    SizeType find_free_or_equal(const KeyType& key, SizeType hint) const
    {
        if (m_capacity == 0)
            return 0;

        return find_free_or_equal_no_rehash(key, hint);
    }
    SizeType find_free_or_equal_no_rehash(const KeyType& key,
                                          SizeType hint) const
    {
        hint %= m_capacity;

        if (m_states[hint] == State::EMPTY)
            return hint;

        CollisionPolicy cp(hint, m_capacity);

        SizeType deleted = m_capacity;
        for (SizeType i = 0; i < m_capacity; ++i, cp.next()) {
            if (m_states[cp.index] == State::SET &&
                m_equal(get_key(*m_data[cp.index]), key)) {
                return cp.index;
            }

            if (m_states[cp.index] == State::EMPTY) {
                return cp.index;
            }

            if (deleted == m_capacity && m_states[cp.index] == State::DELETE) {
                deleted = cp.index;
            }
        }

        return deleted;
    }

    std::vector<std::unique_ptr<ValueType>> m_data;
    std::vector<State> m_states;
    const Hash m_hash;
    const Equal m_equal;
    SizeType m_capacity = 0;
    SizeType m_size = 0;
};
