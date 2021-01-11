#include "solver.h"

#include <iostream>

int
main()
{
    Board board({ { 3, 2, 1 }, { 0, 5, 4 }, { 7, 8, 6 } });
    // Board board({{3, 2, 1, 15}, {0, 5, 4, 12}, {7, 8, 13, 6}, {9, 10, 14,
    // 11}});
    Solver solver(board);
    std::cout << solver.moves() << std::endl;
    std::cout << board << std::endl;
    std::cout << board.is_solvable() << std::endl;
    for (const auto move : solver) {
        std::cout << move << std::endl;
    }
}
