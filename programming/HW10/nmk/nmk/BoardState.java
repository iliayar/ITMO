package nmk;

import ticTacToe.*;

public class BoardState implements Position {

    Cell[][] board;

    public BoardState(Cell[][] board) {
        this.board = board;
    }

    @Override
    public boolean isValid(Move move) {
        int y = move.getRow();
        int x = move.getColumn();

        if(x >= board[0].length ||
            y >= board.length ||
            x < 0 ||
            y < 0) {
            return false;
        }
        if(board[y][x] != Cell.E) {
            return false;
        }

        return true;
    }

    @Override
    final public Cell getCell(int r, int c) {
        return board[r][c];
    }


}