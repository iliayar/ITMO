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
    private final Cell[][] board;
    private final int k;

    private Cell turn;

    public NmkBoard(int n, int m, int k) {
        this.k = k;
        this.board = new Cell[n][m];
        for (Cell[] row : board) {
            Arrays.fill(row, Cell.E);
        }
        this.turn = Cell.X;
        blanks = n*m;
    }

    public Board newBoard() {
        return new NmkBoard(board.length, board[0].length , k);
    }

    @Override
    final public Position getPosition() {
        return new BoardState(board, k);
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


        col += subCount(x, y, 0, 1, c);
        row += subCount(x, y, 1, 0, c);
        diag1 += subCount(x, y, 1, 1, c);
        diag2 += subCount(x - 1, y, -1, 1, c);
        
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

    private int subCount(int x, int y, int dx, int dy, Cell c) {
        int cnt = 0;
    
        
        for(int i = y, j = x; i >= 0 && j < board[0].length && j >= 0 && i < board.length; i+=dy, j+=dx) {
            if(board[i][j] != c) {
                break;
            }
            cnt++;
        }
        for(int i = y - dy, j = x - dx; i >= 0 && j < board[0].length && j >= 0 && i < board.length; i-=dy, j-=dx) {
            if(board[i][j] != c) {
                break;
            }
            cnt++;
        }
        return cnt;
    }

}
