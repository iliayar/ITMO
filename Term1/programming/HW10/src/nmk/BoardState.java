package nmk;

import ticTacToe.*;

public class BoardState implements Position {

    Cell[][] board;
    int k;


    public BoardState(Cell[][] board, int k) {
        this.board = board;
        this.k = k;
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

    @Override
    public int getN() {
        return board.length;
    }

    @Override
    public int getM() {
        return board[0].length;
    }

    @Override
    public int getK() {
        return k;
    }


}