#include "solver.h"

#include <gtest/gtest.h>

#include <array>
#include <type_traits>
#include <utility>

namespace {

template <class T>
void fill_goal(T & x)
{
    if (x.size() > 0) {
        for (unsigned i = 1; i < x.size(); ++i) {
            x[i-1] = i;
        }
        x[x.size()-1] = 0;
    }
}

template <std::size_t Size>
struct Configuration
{
    static std::array<unsigned, Size * Size> make_goal();

    std::array<unsigned, Size * Size> data;
    const bool is_solvable;
    const std::size_t moves;
};

template <std::size_t Size>
std::array<unsigned, Size * Size> Configuration<Size>::make_goal()
{
    std::array<unsigned, Size * Size> data;
    fill_goal(data);
    return data;
}

using Two = Configuration<2>;
using Three = Configuration<3>;
using Four = Configuration<4>;

const std::vector<Two> twos = {
      {0, 1, 2, 3, false, 0}
    , {0, 1, 3, 2, true, 2}
    , {0, 2, 1, 3, true, 2}
    , {0, 2, 3, 1, false, 0}
    , {0, 3, 1, 2, false, 0}
    , {0, 3, 2, 1, true, 6}
    , {1, 0, 2, 3, false, 0}
    , {1, 0, 3, 2, true, 1}
    , {1, 2, 0, 3, true, 1}
    , {1, 2, 3, 0, true, 0}
    , {1, 3, 0, 2, false, 0}
    , {1, 3, 2, 0, false, 0}
    , {2, 0, 1, 3, true, 3}
    , {2, 0, 3, 1, false, 0}
    , {2, 1, 0, 3, false, 0}
    , {2, 1, 3, 0, false, 0}
    , {2, 3, 0, 1, true, 5}
    , {2, 3, 1, 0, true, 4}
    , {3, 0, 1, 2, false, 0}
    , {3, 0, 2, 1, true, 5}
    , {3, 1, 0, 2, true, 3}
    , {3, 1, 2, 0, true, 4}
    , {3, 2, 0, 1, false, 0}
    , {3, 2, 1, 0, false, 0}
};

const std::vector<Three> threes = {
      {1, 7, 4, 6, 2, 5, 8, 3, 0, true, 24}
    , {3, 8, 1, 4, 6, 2, 7, 0, 5, true, 19}
    , {8, 5, 1, 6, 7, 3, 4, 0, 2, false, 0}
    , {2, 6, 1, 0, 5, 3, 8, 7, 4, true, 23}
    , {6, 0, 8, 4, 7, 3, 5, 1, 2, true, 21}
    , {1, 8, 7, 5, 6, 2, 3, 4, 0, false, 0}
    , {3, 0, 1, 8, 4, 6, 7, 5, 2, false, 0}
    , {4, 6, 1, 7, 8, 3, 0, 5, 2, false, 0}
    , {5, 1, 8, 2, 4, 7, 6, 0, 3, false, 0}
    , {7, 8, 3, 4, 5, 2, 1, 6, 0, false, 0}
    , {1, 2, 3, 4, 5, 6, 7, 8, 0, true, 0}
};

const std::vector<Four> fours = {
      {5, 2, 9, 0, 14, 6, 1, 4, 3, 10, 15, 8, 13, 11, 7, 12, true, 39}
    , {7, 3, 2, 4, 8, 15, 14, 5, 9, 1, 0, 11, 6, 13, 10, 12, true, 38}
    , {7, 15, 6, 2, 1, 5, 3, 4, 9, 14, 8, 11, 13, 10, 0, 12, true, 33}
      /*
    , {7, 3, 2, 0, 8, 15, 14, 4, 9, 1, 11, 5, 6, 13, 10, 12, true, 41}
    , {5, 3, 2, 6, 7, 11, 1, 0, 8, 4, 14, 13, 10, 9, 15, 12, true, 48}
    , {5, 7, 11, 15, 4, 12, 8, 1, 14, 6, 2, 10, 3, 9, 13, 0, true, 54}
    , {3, 11, 13, 8, 15, 1, 9, 0, 6, 2, 12, 7, 10, 14, 5, 4, true, 56}
    , {10, 8, 12, 3, 0, 1, 14, 5, 2, 4, 6, 9, 13, 11, 7, 15, false, 0}
    , {14, 3, 4, 10, 8, 0, 2, 1, 15, 9, 6, 13, 7, 5, 11, 12, true, 54}
    , {7, 2, 12, 11, 5, 1, 14, 15, 6, 9, 0, 3, 10, 13, 8, 4, true, 44}
    , {6, 7, 14, 0, 5, 1, 13, 11, 10, 8, 4, 12, 3, 9, 15, 2, true, 51}
    , {1, 12, 0, 9, 6, 3, 13, 10, 11, 15, 7, 14, 5, 4, 8, 2, false, 0}
    , {5, 7, 2, 10, 0, 3, 15, 14, 8, 13, 12, 11, 6, 9, 1, 4, true, 53}
    , {11, 9, 7, 5, 6, 2, 0, 8, 15, 12, 4, 1, 10, 13, 14, 3, true, 49}
    */
    , {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, true, 0}
};

constexpr std::size_t isqrt(const std::size_t n)
{
    if (n > 2) {
        const auto small = isqrt(n >> 2) << 1;
        const auto large = small + 1;
        if (large * large > n) {
            return small;
        }
        else {
            return large;
        }
    }
    else if (n == 2) {
        return 1;
    }
    else {
        return n;
    }
}

template <std::size_t Size>
Board make_board(const std::array<unsigned, Size> & oned)
{
    constexpr std::size_t n = isqrt(Size);
    static_assert(n * n == Size, "Can make only square boards");
    std::vector<std::vector<unsigned>> data;
    data.reserve(n);
    for (std::size_t i = 0; i < n; ++i) {
        auto & row = data.emplace_back();
        row.reserve(n);
        for (std::size_t j = 0; j < n; ++j) {
            row.emplace_back(oned[i * n + j]);
        }
    }
    return Board{data};
}

Board make_board(const std::size_t n, const std::vector<unsigned> & oned)
{
    std::vector<std::vector<unsigned>> data;
    if (n > 0) {
        data.reserve(n);
        for (std::size_t i = 0; i < n; ++i) {
            auto & row = data.emplace_back();
            row.reserve(n);
            for (std::size_t j = 0; j < n; ++j) {
                row.emplace_back(oned[i * n + j]);
            }
        }
    }
    return Board{data};
}

Board make_goal(const std::size_t n)
{
    std::vector<unsigned> oned(n * n);
    fill_goal(oned);
    return make_board(n, oned);
}

} // anonymous namespace

TEST(SolverTest, zero)
{
    Board board(0);
    Solver solver(board);
    EXPECT_EQ(0, solver.moves());
    auto begin = solver.begin();
    const auto end = solver.end();
    EXPECT_EQ(board, *begin);
    EXPECT_NE(begin, end);
    ++begin;
    EXPECT_EQ(begin, end);

    {
        auto other = solver;
        EXPECT_EQ(solver.moves(), other.moves());
        EXPECT_EQ(std::distance(solver.begin(), solver.end()), std::distance(other.begin(), other.end()));
        EXPECT_EQ(*solver.begin(), *other.begin());
    }
    {
        Solver other(Board(3));
        other = solver;
        EXPECT_EQ(solver.moves(), other.moves());
        EXPECT_EQ(std::distance(solver.begin(), solver.end()), std::distance(other.begin(), other.end()));
        EXPECT_EQ(*solver.begin(), *other.begin());
    }
}

TEST(SolverTest, one)
{
    Board board(1);
    Solver solver(board);
    EXPECT_EQ(0, solver.moves());
    auto begin = solver.begin();
    const auto end = solver.end();
    EXPECT_EQ(board, *begin);
    EXPECT_NE(begin, end);
    ++begin;
    EXPECT_EQ(begin, end);

    {
        auto other = solver;
        EXPECT_EQ(solver.moves(), other.moves());
        EXPECT_EQ(std::distance(solver.begin(), solver.end()), std::distance(other.begin(), other.end()));
        EXPECT_EQ(*solver.begin(), *other.begin());
    }
    {
        Solver other(Board(3));
        other = solver;
        EXPECT_EQ(solver.moves(), other.moves());
        EXPECT_EQ(std::distance(solver.begin(), solver.end()), std::distance(other.begin(), other.end()));
        EXPECT_EQ(*solver.begin(), *other.begin());
    }
}

TEST(SolverTest, two)
{
    for (const auto & c : twos) {
        Board initial = make_board(c.data), goal = make_board(c.make_goal());
        Solver solver(initial);
        if (c.is_solvable) {
            EXPECT_EQ(c.moves, solver.moves());
            auto begin = solver.begin();
            const auto end = solver.end();
            EXPECT_EQ(c.moves, std::distance(begin, end) - 1);
            EXPECT_EQ(initial, *begin);
            std::advance(begin, solver.moves());
            EXPECT_EQ(goal, *begin);
            ++begin;
            EXPECT_EQ(begin, end);
        }
        else {
            EXPECT_EQ(0, solver.moves());
            EXPECT_EQ(solver.begin(), solver.end());
        }
    }
}

TEST(SolverTest, three)
{
    for (const auto & c : threes) {
        Board initial = make_board(c.data), goal = make_board(c.make_goal());
        Solver solver(initial);
        if (c.is_solvable) {
            //EXPECT_EQ(c.moves, solver.moves());
            auto begin = solver.begin();
            const auto end = solver.end();
            //EXPECT_EQ(c.moves, std::distance(begin, end) - 1);
            EXPECT_EQ(initial, *begin);
            std::advance(begin, solver.moves());
            EXPECT_EQ(goal, *begin);
            ++begin;
            EXPECT_EQ(begin, end);
        }
        else {
            EXPECT_EQ(0, solver.moves());
            EXPECT_EQ(solver.begin(), solver.end());
        }
    }
}

TEST(SolverTest, four)
{
    for (const auto & c : fours) {
        Board initial = make_board(c.data), goal = make_board(c.make_goal());
        Solver solver(initial);
        if (c.is_solvable) {
            //EXPECT_EQ(c.moves, solver.moves());
            auto begin = solver.begin();
            const auto end = solver.end();
            //EXPECT_EQ(c.moves, std::distance(begin, end) - 1);
            EXPECT_EQ(initial, *begin);
            std::advance(begin, solver.moves());
            EXPECT_EQ(goal, *begin);
            ++begin;
            EXPECT_EQ(begin, end);
        }
        else {
            EXPECT_EQ(0, solver.moves());
            EXPECT_EQ(solver.begin(), solver.end());
        }
    }
}

TEST(SolverTest, zero_step)
{
    for (std::size_t i = 0; i < 199; ++i) {
        const auto goal = make_goal(i);
        Solver solver(goal);
        EXPECT_EQ(0, solver.moves());
    }
}
