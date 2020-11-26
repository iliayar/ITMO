#pragma once

#include <cstddef>
#include <deque>
#include <new>
#include <ostream>

template<class Key, class KeyProvider, class Allocator>
class Cache
{
    using pointer = typename Allocator::pointer;

  public:
    struct Entry
    {
        pointer ptr;
        bool usability;

        Entry(pointer ptr, bool usability = false)
          : ptr(ptr)
          , usability(usability)
        {}
    };

    template<class... AllocArgs>
    Cache(const std::size_t cache_size, AllocArgs&&... alloc_args)
      : m_max_size(cache_size)
      , m_alloc(std::forward<AllocArgs>(alloc_args)...)
    {}

    std::size_t size() const { return m_entries.size(); }

    bool empty() const { return m_entries.empty(); }

    template<class T>
    T& get(const Key& key);

    std::ostream& print(std::ostream& strm) const;

    friend std::ostream& operator<<(std::ostream& strm, const Cache& cache)
    {
        return cache.print(strm);
    }

  private:
    const std::size_t m_max_size;
    Allocator m_alloc;
    std::deque<Entry> m_entries;
};

template<class Key, class KeyProvider, class Allocator>
template<class T>
inline T&
Cache<Key, KeyProvider, Allocator>::get(const Key& key)
{
    for (Entry& e : m_entries) {
        if (*static_cast<KeyProvider*>(*e.ptr) == key) {
            e.usability = true;
            return *static_cast<T*>(*e.ptr);
        }
    }
    while (m_entries.size() >= m_max_size) {
        Entry e = m_entries.front();
        m_entries.pop_front();
        if (e.usability) {
            e.usability = false;
            m_entries.push_back(e);
        } else {
            m_alloc.template destroy<KeyProvider>(e.ptr); // FIXME
        }
    }
    m_entries.push_back(Entry(m_alloc.template create<T>(key)));
    return *static_cast<T*>(*m_entries.back().ptr);
}

template<class Key, class KeyProvider, class Allocator>
inline std::ostream&
Cache<Key, KeyProvider, Allocator>::print(std::ostream& strm) const
{
    for (Entry e : m_entries) {
        strm << "{" << *static_cast<KeyProvider*>(*e.ptr) << ", "
             << (e.usability ? "true" : "false") << "} ";
    }
    return strm;
}
