#include "pool.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <new>
#include <vector>

using pointer = PoolAllocator::pointer;

pointer
PoolAllocator::allocate(const std::size_t size_unaligned)
{
    std::size_t size = ((size_unaligned + 7) / 8) * 8;
    std::size_t i;
    for (i = 0; i < m_size; ++i) {
        if (!m_used[i]) {
            std::size_t k = size;
            std::size_t j = i;
            for (; k > 0 && j < m_size; ++j, --k) {
                if (m_used[j]) {
                    break;
                }
            }
            if (k != 0) {
                i = j - 1;
            } else {
                break;
            }
        }
    }
    if (m_used_unaligned > m_size_unaligned - size_unaligned ||
        m_size_unaligned < size_unaligned) {
        throw std::bad_alloc{};
    }
    if (i == m_size &&
        (m_used_unaligned >= m_size_unaligned - 2 * size_unaligned ||
         m_size_unaligned < 2 * size_unaligned)) {
        throw std::bad_alloc{};
    }
    if (i == m_size) {
        defragment();
        i = m_used_size;
    }
    for (std::size_t j = 0; j < size; ++j) {
        m_used[j + i] = true;
    }
    m_used_unaligned += size_unaligned;
    m_used_size += size;
    m_chunks[m_chunk_max] = Chunk(i, size, size_unaligned);
    return pointer(*this, m_chunk_max++);
}

void
PoolAllocator::deallocate(const pointer ptr)
{
    std::size_t chunk = ptr.m_ptr_value;
    auto chunk_it = m_chunks.find(chunk);
    if (chunk_it == m_chunks.end()) {
        throw std::bad_alloc{};
    }
    std::size_t chunk_size = chunk_it->second.size;
    for (std::size_t i = 0; i < chunk_size; ++i) {
        m_used[chunk_it->second.pos + i] = false;
    }
    m_used_unaligned -= chunk_it->second.size_unaligned;
    m_used_size -= chunk_it->second.size;
    m_chunks.erase(chunk_it);
}

void
PoolAllocator::defragment()
{
    for (auto chunk : m_chunks) {
        std::size_t size = chunk.second.size;
        std::size_t& k = chunk.second.pos;
        std::size_t offset = 0;
        while (k > 0 && !m_used[k - 1]) {
            k--;
            offset++;
        }
        k--;
        for (std::size_t q = 0; q < size; ++q) {
            swap(m_data[k + q], m_data[k + q + offset]);
            swap(m_used[k + q], m_used[k + q + offset]);
        }
    }
}
