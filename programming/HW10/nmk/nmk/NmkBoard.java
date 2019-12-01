package nmk;

import ticTacToe.*;

import java.util.Arrays;
import java.util.Map;

public class NmkBoard implements Board, Position {
    private static final Map<Cell, Character> SYMBOLS = Map.of(
            Cell.X, 'X',
            Cell.O, 'O',
            Cell.E, '.'
    );

    private int blanks;
//    private final Counter[][] counts;
    private final Cell[][] board;
    private final int k;

    private Cell turn;

    public NmkBoard(int n, int m, int k) {
        this.k = k;
        this.board = new Cell[n][m];
        for (Cell[] row : board) {
            Arrays.fill(row, Cell.E);
        }
//        this.counts = new Counter[n][m];
//        for (Counter[] row : counts) {
//            Arrays.fill(row, new Counter());
//        }
        this.turn = Cell.X;
        blanks = n*m;
    }

    @Override
    final public Position getPosition() {
        return this;
    }

    @Override
    final public Cell getCell() {
        return turn;
    }

    @Override
    final public Result makeMove(Move move) {
        if(!isValid(move)) {
            return Result.LOSE;
        }

        int x = move.getColumn();
        int y = move.getRow();

        blanks--;

        board[y][x] = move.getValue();

        System.out.println(this);


        if(count(x,y,move.getValue()) >= k) {
            return Result.WIN;
        }

        if(blanks == 0) {
            return Result.DRAW;
        }

        turn = turn == Cell.X ? Cell.O : Cell.X;
        return Result.UNKNOWN;
    }

    @Override
    final public boolean isValid(Move move) {
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
    final public String toString() {
        StringBuilder sb = new StringBuilder();

        for(int i = 0; i < board.length; ++i) {
            for(int j = 0; j < board[i].length; ++j) {
                sb.append(SYMBOLS.get(board[i][j]));
                sb.append(" ");
            }
            sb.append("\n");
        }

        return sb.toString();
    }


    private int count(int x, int y, Cell c) {
        int diag1 = 0;
        int diag2 = 0;
        int row = 0;
        int col = 0;

        for(int i = y; i < board.length; ++i) {
            if(board[i][x] != c) {
                break;
            }
            col++;
        }
        for(int i = y - 1; i >= 0; --i) {
            if(board[i][x] != c) {
                break;
            }
            col++;
        }

        for(int i = x; i < board[0].length; ++i) {
            if(board[y][i] != c) {
                break;
            }
            row++;
        }
        for(int i = x - 1; i >= 0; --i) {
            if(board[y][i] != c) {
                break;
            }
            row++;
        }

        for(int i = y, j = x; i < board.length && j < board[0].length; ++i, ++j) {
            if(board[i][j] != c) {
                break;
            }
            diag1++;
        }
        for(int i = y - 1, j = x - 1; i >= 0 && j >= 0; --i, --j) {
            if(board[i][j] != c) {
                break;
            }
            diag1++;
        }

        for(int i = y, j = x - 1; i < board.length && j >= 0; ++i, --j) {
            if(board[i][j] != c) {
                break;
            }
            diag2++;
        }
        for(int i = y - 1, j = x; i >= 0 && j < board[0].length; --i, ++j) {
            if(board[i][j] != c) {
                break;
            }
            diag2++;
        }

        int max = 0;
        if(col > max) {
            max = col;
        }
        if(row > max) {
            max = row;
        }
        if(diag1 > max) {
            max = diag1;
        }
        if(diag2 > max) {
            max = diag2;
        }

        return max;

    }

}
