#pragma once

#include "hash_array.h"
#include "hash_array_iterator.h"
#include "policy.h"
#include "states.h"
#include <iterator>
#include <memory>
#include <stdexcept>
#include <tuple>

template<class Key,
         class T,
         class CollisionPolicy = LinearProbing,
         class Hash = std::hash<Key>,
         class Equal = std::equal_to<Key>>
class HashMap
  : public HashArray<
      std::pair<const Key, T>,
      Key,
      std::size_t,
      CollisionPolicy,
      Hash,
      Equal,
      hash_array_iterator<std::pair<const Key, T>,
                          HashMap<Key, T, CollisionPolicy, Hash, Equal>>>
{
  public:
    // types
    using key_type = Key;
    using mapped_type = T;
    using value_type = std::pair<const Key, T>;
    using size_type = std::size_t;
    using difference_type = std::ptrdiff_t;
    using hasher = Hash;
    using key_equal = Equal;
    using reference = value_type&;
    using const_reference = const value_type&;
    using pointer = value_type*;
    using const_pointer = const value_type*;

    using iterator = hash_array_iterator<value_type, HashMap>;
    using const_iterator = const_hash_array_iterator<value_type, HashMap>;

    friend class hash_array_iterator<value_type, HashMap>;
    friend class const_hash_array_iterator<value_type, HashMap>;

    explicit HashMap(size_type expected_max_size = 0,
                     const hasher& hash = hasher(),
                     const key_equal& equal = key_equal())
      : HashArray<value_type,
                  Key,
                  std::size_t,
                  CollisionPolicy,
                  Hash,
                  Equal,
                  iterator>(hash, equal)
    {
        this->m_capacity = expected_max_size;
        this->init_arrays();
    }

    template<class InputIt>
    HashMap(InputIt first,
            InputIt last,
            size_type expected_max_size = 0,
            const hasher& hash = hasher(),
            const key_equal& equal = key_equal())
      : HashMap(expected_max_size, hash, equal)
    {
        insert(first, last);
    }

    HashMap(const HashMap& other)
      : HashMap()
    {
        reserve(other.size());
        for (const_iterator it = other.begin(); it != other.end(); it++) {
            emplace(it->first, it->second);
        }
    }
    HashMap(HashMap&& other)
      : HashMap()
    {
        *this = std::move(other);
    }

    HashMap(std::initializer_list<value_type> init,
            size_type expected_max_size = 0,
            const hasher& hash = hasher(),
            const key_equal& equal = key_equal())
      : HashMap(expected_max_size, hash, equal)
    {
        insert(init.cbegin(), init.cend());
    }

    HashMap& operator=(const HashMap& other)
    {
        clear();
        reserve(other.size());
        for (const_iterator it = other.begin(); it != other.end(); it++) {
            emplace(it->first, it->second);
        }
        return *this;
    }

    HashMap& operator=(HashMap&& other) noexcept
    {
        this->swap(std::move(other));
        return *this;
    }
    HashMap& operator=(std::initializer_list<value_type> init)
    {
        clear();
        insert(init.begin(), init.end());
    }

    iterator begin() noexcept { return iterator(this, 0); }
    const_iterator begin() const noexcept { return const_iterator(this, 0); }
    const_iterator cbegin() const noexcept { return begin(); }

    iterator end() noexcept { return iterator(this, this->m_capacity); }
    const_iterator end() const noexcept
    {
        return const_iterator(this, this->m_capacity);
    }
    const_iterator cend() const noexcept { return end(); }

    bool empty() const { return this->m_size == 0; }
    size_type size() const { return this->m_size; }
    size_type max_size() const { return this->m_capacity; }

    void clear()
    {
        this->init_arrays();
        this->m_size = 0;
    }
    std::pair<iterator, bool> insert(const value_type& value)
    {
        return this->insert_imp(new value_type(value));
    }
    std::pair<iterator, bool> insert(value_type&& value)
    {
        return this->insert_imp(std::make_unique<value_type>(std::move(value)));
    }
    template<class P>
    std::pair<iterator, bool> insert(P&& value)
    {
        return emplace(std::forward<P>(value));
    }
    iterator insert(const_iterator hint, const value_type& value)
    {
        return insert(value, hint._index).first;
    }
    iterator insert(const_iterator hint, value_type&& value)
    {
        return insert(value, hint._index).first;
    }
    template<class P>
    iterator insert(const_iterator hint, P&& value)
    {
        return insert(value, hint._index).first;
    }
    template<class InputIt>
    void insert(InputIt first, InputIt last)
    {
        for (; first != last; ++first) {
            insert(*first);
        }
    }
    void insert(std::initializer_list<value_type> init)
    {
        insert(init.begin(), init.end());
    }

    template<class M>
    std::pair<iterator, bool> insert_or_assign(const key_type& key, M&& value)
    {
        return insert_or_assign_imp(key, std::forward<M>(value));
    }
    template<class M>
    std::pair<iterator, bool> insert_or_assign(key_type&& key, M&& value)
    {
        return insert_or_assign_imp(std::move(key), std::forward<M>(value));
    }
    template<class M>
    iterator insert_or_assign(const_iterator hint,
                              const key_type& key,
                              M&& value)
    {
        return insert_or_assign_imp(key, std::forward<M>(value), hint.m_index)
          .first;
    }
    template<class M>
    iterator insert_or_assign(const_iterator hint, key_type&& key, M&& value)
    {
        return insert_or_assign_imp(
                 std::move(key), std::forward<M>(value), hint.m_index)
          .first;
    }

    // construct element in-place, no copy or move operations are performed;
    // element's constructor is called with exact same arguments as `emplace`
    // method (using `std::forward<Args>(args)...`)
    template<class... Args>
    std::pair<iterator, bool> emplace(Args&&... args)
    {
        return this->insert_imp(
          std::make_unique<value_type>(std::forward<Args>(args)...));
    }
    template<class... Args>
    iterator emplace_hint(const_iterator, Args&&... args)
    {
        return this
          ->insert_imp(
            std::make_unique<value_type>(std::forward<Args>(args)...))
          .first;
    }

    template<class... Args>
    std::pair<iterator, bool> try_emplace(const key_type& key, Args&&... args)
    {
        size_type index = this->find_free_or_equal(key);
        if (this->m_states[index] == State::SET)
            return { iterator(this, index), false };
        this->m_data[index] = std::make_unique<value_type>(
          std::piecewise_construct,
          std::forward_as_tuple(key),
          std::forward_as_tuple(std::forward<Args>(args)...));
        this->m_states[index] = State::SET;
        this->m_size++;
        return { iterator(this, index), true };
    }
    template<class... Args>
    std::pair<iterator, bool> try_emplace(key_type&& key, Args&&... args)
    {
        size_type index = this->find_free_or_equal(key);
        if (this->m_states[index] == State::SET)
            return { iterator(this, index), false };
        this->m_data[index] = std::make_unique<value_type>(
          std::piecewise_construct,
          std::forward_as_tuple(std::move(key)),
          std::forward_as_tuple(std::forward<Args>(args)...));
        this->m_states[index] = State::SET;
        this->m_size++;
        return { iterator(this, index), true };
    }
    template<class... Args>
    iterator try_emplace(const_iterator, const key_type& key, Args&&... args)
    {
        return try_emplace(key, std::forward<Args>(args)...).first;
    }
    template<class... Args>
    iterator try_emplace(const_iterator, key_type&& key, Args&&... args)
    {
        return try_emplace(std::move(key), std::forward<Args>(args)...).first;
    }

    iterator erase(const_iterator pos)
    {
        size_type index = pos.m_index;
        if (this->m_states[index] != State::SET) {
            return iterator(this, pos.m_index);
        }

        this->m_states[index] = State::DELETE;
        this->m_size--;
        return ++iterator(this, pos.m_index);
    }
    iterator erase(const_iterator first, const_iterator last)
    {
        iterator res;
        for (; first != last; first++) {
            res = erase(first);
        }
        return res;
    }
    size_type erase(const key_type& key)
    {
        size_type index = this->find_free_or_equal(key);
        if (this->m_states[index] != State::SET) {
            return 0;
        }

        this->m_states[index] = State::DELETE;
        this->m_size--;
        return 1;
    }

    // exchanges the contents of the container with those of other;
    // does not invoke any move, copy, or swap operations on individual elements
    void swap(HashMap&& other) noexcept
    {
        std::swap(this->m_data, other.m_data);
        std::swap(this->m_states, other.m_states);
        std::swap(this->m_capacity, other.m_capacity);
        std::swap(this->m_size, other.m_size);
    }

    size_type count(const key_type& key) const
    {
        return find(key) == end() ? 0 : 1;
    }
    iterator find(const key_type& key)
    {
        size_type index = this->find_free_or_equal(key);

        if (this->m_states[index] != State::SET) {
            return end();
        }

        return iterator(this, index);
    }
    const_iterator find(const key_type& key) const
    {
        size_type index = this->find_free_or_equal(key);

        if (index >= this->m_capacity || this->m_states[index] != State::SET) {
            return cend();
        }

        return const_iterator(this, index);
    }
    bool contains(const key_type& key) const
    {
        return static_cast<bool>(count(key));
    }
    std::pair<iterator, iterator> equal_range(const key_type& key)
    {
        iterator res = find(key);
        if (res == end()) {
            return { res, res };
        } else {
            return { res++, res };
        }
    }
    std::pair<const_iterator, const_iterator> equal_range(
      const key_type& key) const
    {
        return equal_range(key);
    }

    mapped_type& at(const key_type& key)
    {
        size_type index = this->find_free_or_equal(key);
        if (this->m_states[index] != State::SET) {
            throw std::out_of_range("Key not in map");
        }
        return this->m_data[index]->second;
    }
    const mapped_type& at(const key_type& key) const
    {
        size_type index = this->find_free_or_equal(key);
        if (index >= this->m_capacity || this->m_states[index] != State::SET) {
            throw std::out_of_range("Key not in map");
        }
        return this->m_data[index]->second;
    }
    mapped_type& operator[](const key_type& key)
    {
        iterator it = find(key);
        if (it == end()) {
            return this->insert_imp(new value_type(key, mapped_type()))
              .first->second;
        }
        return it->second;
    }
    mapped_type& operator[](key_type&& key)
    {
        size_type index = this->find_free_or_equal(key);
        if (this->m_states[index] == State::SET) {
            return this->m_data[index]->second;
        }
        this->m_data[index] =
          std::make_unique<value_type>(std::piecewise_construct,
                                       std::forward_as_tuple(std::move(key)),
                                       std::forward_as_tuple());
        this->m_states[index] = State::SET;
        this->m_size++;
        return this->m_data[index]->second;
    }

    size_type bucket_count() const { return this->m_capacity; }
    size_type max_bucket_count() const { return this->m_capacity; }
    size_type bucket_size(const size_type) const { return 1; }
    size_type bucket(const key_type& key) const { return find(key).m_index; }

    float load_factor() const
    {
        if (this->m_capacity == 0)
            return 1.0;
        return static_cast<float>(this->m_size) / this->m_capacity;
    }
    float max_load_factor() const { return 1.0; }
    void reserve(size_type count) { this->rehash(count); }

    // compare two containers contents
    friend bool operator==(const HashMap& lhs, const HashMap& rhs)
    {
        if (lhs.m_size != rhs.m_size) {
            return false;
        }
        for (const value_type& element : lhs) {
            const_iterator it = rhs.find(element.first);
            if (it == rhs.end()) {
                return false;
            }
            if (!(it->second == element.second)) {
                return false;
            }
        }

        return true;
    }
    friend bool operator!=(const HashMap& lhs, const HashMap& rhs)
    {
        return !(lhs == rhs);
    }

  protected:
    const key_type& get_key(const value_type& value) const
    {
        return value.first;
    }
    iterator get_iterator(const size_type index) const
    {
        return iterator(this, index);
    }

  private:
    template<class K, class M>
    std::pair<iterator, bool> insert_or_assign_imp(K key, M&& value)
    {
        return insert_or_assign_imp(
          std::move(key), std::forward<M>(value), this->m_hash(key));
    }
    template<class K, class M>
    std::pair<iterator, bool> insert_or_assign_imp(K key,
                                                   M&& value,
                                                   size_type hint)
    {
        size_type index = this->find_free_or_equal(key, hint);
        if (this->m_states[index] != State::SET) {
            return this->insert_imp(std::make_unique<value_type>(
              std::move(key), std::forward<M>(value)));
        }
        this->m_data[index]->second = std::move(value);
        return { iterator(this, index), false };
    }
};
