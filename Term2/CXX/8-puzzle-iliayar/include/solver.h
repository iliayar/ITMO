#pragma once

#include "board.h"

class Solver
{
  public:
    explicit Solver(const Board& board);

    Solver(const Solver& other) = default;

    Solver& operator=(const Solver& other) = default;

    std::size_t moves() const;

    auto begin() const { return m_moves.begin(); }

    auto end() const { return m_moves.end(); }

  private:
    std::vector<Board> m_moves;
    unsigned m_moves_cnt = 0;
};
