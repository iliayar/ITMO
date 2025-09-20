#pragma once

#include "hash_array.h"
#include "hash_array_iterator.h"
#include "policy.h"
#include <cstddef>
#include <iterator>
#include <memory>

template<class Key,
         class CollisionPolicy = LinearProbing,
         class Hash = std::hash<Key>,
         class Equal = std::equal_to<Key>>
class HashSet
  : public HashArray<
      Key,
      Key,
      std::size_t,
      CollisionPolicy,
      Hash,
      Equal,
      const_hash_array_iterator<Key,
                                HashSet<Key, CollisionPolicy, Hash, Equal>>>
{
  private:
    using MyType = HashSet<Key, CollisionPolicy, Hash, Equal>;

  public:
    // types
    using key_type = Key;
    using value_type = Key;
    using size_type = std::size_t;
    using difference_type = std::ptrdiff_t;
    using hasher = Hash;
    using key_equal = Equal;
    using reference = value_type&;
    using const_reference = const value_type&;
    using pointer = value_type*;
    using const_pointer = const value_type*;

    using const_iterator = const_hash_array_iterator<value_type, HashSet>;
    using iterator = const_iterator;

    friend const_hash_array_iterator<value_type, HashSet>;

    explicit HashSet(size_type expected_max_size = 0,
                     const hasher& hash = hasher(),
                     const key_equal& equal = key_equal())

      : HashArray<Key,
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
    HashSet(InputIt first,
            InputIt last,
            size_type expected_max_size = 0,
            const hasher& hash = hasher(),
            const key_equal& equal = key_equal())
      : HashSet(expected_max_size, hash, equal)
    {
        insert(first, last);
    }

    HashSet(const HashSet& other)
      : HashSet()
    {
        reserve(other.size());
        insert(other.begin(), other.end());
    }
    HashSet(HashSet&& other)
      : HashSet()
    {
        *this = std::move(other);
    }

    HashSet(std::initializer_list<value_type> init,
            size_type expected_max_size = 0,
            const hasher& hash = hasher(),
            const key_equal& equal = key_equal())
      : HashSet(expected_max_size, hash, equal)
    {
        insert(init.begin(), init.end());
    }

    HashSet& operator=(const HashSet& other)
    {
        clear();
        reserve(other.size());
        insert(other.begin(), other.end());
        return *this;
    }
    HashSet& operator=(HashSet&& other) noexcept
    {
        this->swap(std::move(other));
        return *this;
    }
    HashSet& operator=(std::initializer_list<value_type> init)
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

    std::pair<iterator, bool> insert(const value_type& key)
    {
        return this->insert_imp(std::make_unique<value_type>(key));
    }

    std::pair<iterator, bool> insert(value_type&& key)
    {
        return this->insert_imp(std::make_unique<value_type>(std::move(key)));
    }
    iterator insert(const_iterator hint, const value_type& key)
    {
        return this->insert_imp(std::make_unique<value_type>(key), hint._index)
          .first;
    }
    iterator insert(const_iterator hint, value_type&& key)
    {
        return this
          ->insert_imp(std::make_unique<value_type>(std::move(key)),
                       hint._index)
          .first;
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

    iterator erase(const_iterator pos)
    {
        size_type index = pos.m_index;
        if (this->m_states[index] != State::SET) {
            return pos;
        }

        this->m_states[index] = State::DELETE;
        this->m_size--;
        return ++pos;
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
    void swap(HashSet&& other) noexcept
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
            return end();
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
    friend bool operator==(const HashSet& lhs, const HashSet& rhs)
    {
        if (lhs.m_size != rhs.m_size) {
            return false;
        }
        for (const key_type& element : lhs) {
            if (rhs.find(element) == rhs.end()) {
                return false;
            }
        }

        return true;
    }
    friend bool operator!=(const HashSet& lhs, const HashSet& rhs)
    {
        return !(lhs == rhs);
    }

  protected:
    const key_type& get_key(const value_type& value) const { return value; }

    iterator get_iterator(const size_type index) const
    {
        return iterator(this, index);
    }
};
