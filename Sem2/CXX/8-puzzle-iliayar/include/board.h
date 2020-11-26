#pragma once

#include <string>
#include <vector>

#include <iostream>

class Board
{
  public:
    static Board create_goal(unsigned size);

    Board() = default;

    Board(const Board& other) = default;

    Board& operator=(const Board& other) = default;

    explicit Board(unsigned size);

    explicit Board(const std::vector<std::vector<unsigned>>& data);

    std::size_t size() const;

    bool is_goal() const;

    unsigned hamming() const;

    unsigned manhattan() const;

    std::string to_string() const;

    bool is_solvable() const;

    friend bool operator==(const Board& lhs, const Board& rhs)
    {
        return lhs.m_board == rhs.m_board;
    }

    friend bool operator!=(const Board& lhs, const Board& rhs)
    {
        return lhs.m_board != rhs.m_board;
    }

    const std::vector<std::vector<unsigned>>& array() const;
    const std::pair<unsigned, unsigned> empty_cell() const;

    const std::vector<unsigned>& operator[](std::size_t i) const;

    static unsigned manhattan_imp(const std::vector<std::vector<unsigned>>&);
    static unsigned hamming_imp(const std::vector<std::vector<unsigned>>&);
    static bool is_goal_imp(const std::vector<std::vector<unsigned>>&);
    static const std::pair<unsigned, unsigned> empty_cell_imp(const std::vector<std::vector<unsigned>>&);


    friend std::ostream& operator<<(std::ostream& out, const Board& board)
    {
        return out << board.to_string();
    }

  private:
    std::vector<std::vector<unsigned>> m_board;
};
