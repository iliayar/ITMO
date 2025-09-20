#pragma once

#include <cstdlib>

struct LinearProbing
{
    std::size_t index;
    std::size_t size;

    LinearProbing(std::size_t index, std::size_t size)
      : index(index % size)
      , size(size)
    {}

    std::size_t next()
    {
        index = (index + 1) % size;
        return index;
    }
};
struct QuadraticProbing
{
    std::size_t index;
    std::size_t size;
    std::size_t i;

    QuadraticProbing(std::size_t index, std::size_t size)
      : index(index % size)
      , size(size)
      , i(1)
    {}

    std::size_t next()
    {
        index = (index + i * i) % size;
        i++;
        return index;
    }
};
