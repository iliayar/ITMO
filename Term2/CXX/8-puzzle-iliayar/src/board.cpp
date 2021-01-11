#include "board.h"
#include "solver.h"

unsigned
Board::manhattan_imp(const std::vector<std::vector<unsigned>>& board)
{
    unsigned res = 0;
    unsigned size = board.size();
    for (unsigned i = 0; i < size * size; ++i) {
        unsigned n = board[i / size][i % size];
        if (n == 0)
            continue;
        res +=
          abs(static_cast<int>(i % size) - static_cast<int>((n - 1) % size)) +
          abs(static_cast<int>(i / size) - static_cast<int>((n - 1) / size));
    }
    return res;
}

unsigned
Board::hamming_imp(const std::vector<std::vector<unsigned>>& board)
{
    unsigned res = 0;
    unsigned size = board.size();
    for (unsigned i = 0; i < size * size; ++i) {
        if (board[i / size][i % size] != ((i + 1) % (size * size))) {
            res++;
        }
    }
    return res;
}

bool
Board::is_goal_imp(const std::vector<std::vector<unsigned>>& board)
{
    return hamming_imp(board) == 0;
}

const std::pair<unsigned, unsigned>
Board::empty_cell_imp(const std::vector<std::vector<unsigned>>& board)
{
    unsigned size = board.size();
    for (unsigned i = 0; i < size; ++i) {
        for (unsigned j = 0; j < size; ++j) {
            if (board[i][j] == 0) {
                return { i, j };
            }
        }
    }
    return { -1, -1 };
}

Board
Board::create_goal(const unsigned size)
{
    return Board(size);
}

Board::Board(const unsigned size)
  : m_board(size, std::vector<unsigned>(size))
{
    for (unsigned i = 0; i < size * size; ++i) {
        m_board[i / size][i % size] = i + 1;
    }
    if (size >= 1)
        m_board[size - 1][size - 1] = 0;
}

Board::Board(const std::vector<std::vector<unsigned>>& data)
  : m_board(data)
{}

std::size_t
Board::size() const
{
    return m_board.size();
}

bool
Board::is_goal() const
{
    return is_goal_imp(m_board);
}

unsigned
Board::hamming() const
{
    return hamming_imp(m_board);
}

unsigned
Board::manhattan() const
{
    return manhattan_imp(m_board);
}

const std::pair<unsigned, unsigned>
Board::empty_cell() const
{
    return empty_cell_imp(m_board);
}

const std::vector<std::vector<unsigned>>&
Board::array() const
{
    return m_board;
}

std::string
Board::to_string() const
{
    std::string res = "";
    for (std::vector<unsigned> row : m_board) {
        for (unsigned n : row) {
            if (n == 0)
                res += "░ ";
            else
                res += std::to_string(n) + " ";
        }
        res += "\n";
    }
    return res;
}

bool
Board::is_solvable() const
{
    unsigned size = m_board.size();
    unsigned inverse = 0;
    bool res;
    for (unsigned i = 0; i < size * size; ++i) {
        if (m_board[i / size][i % size] == 0)
            continue;
        for (unsigned j = i + 1; j < size * size; ++j) {
            if (m_board[j / size][j % size] == 0)
                continue;
            if (m_board[j / size][j % size] < m_board[i / size][i % size])
                inverse++;
        }
    }
    if (size % 2 == 1) {
        if (inverse % 2 == 0) {
            res = true;
        } else {
            res = false;
        }
        return res;
    }
    auto empty = empty_cell();
    if (empty.first % 2 != inverse % 2) {
        res = true;
    } else {
        res = false;
    }
    return res;
}

const std::vector<unsigned>&
Board::operator[](const std::size_t i) const
{
    return m_board[i];
}
