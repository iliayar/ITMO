package ticTacToe;

import java.io.PrintStream;
import java.util.Scanner;

import nmk.NmkBoard;

/**
 * @author Georgiy Korneev (kgeorgiy@kgeorgiy.info)
 */
public class HumanPlayer implements Player {
    private final PrintStream out;
    private final Scanner in;

    public HumanPlayer(final PrintStream out, final Scanner in) {
        this.out = out;
        this.in = in;
    }

    public HumanPlayer() {
        this(System.out, new Scanner(System.in));
    }

    @Override
    public Move move(final Position position, final Cell cell) {
        while (true) {
            // out.println("Position");
//            out.println(position);
            out.println("Human " + cell + "'s move");
            // out.println("Enter row and column");
            final Move move = new Move(readInt("Enter row: ", in), readInt("Enter column: ", in), cell);
            if (position.isValid(move)) {
                return move;
            }
            final int row = move.getRow();
            final int column = move.getColumn();
            out.println("Move " + move + " is invalid");
        }
    }

    
    static public int readInt(String msg, Scanner in) {
        System.out.print(msg);
        String s = in.next();
        while(!isInteger(s)) {
            System.out.print("Try harder! ");
            System.out.print(msg);
            s = in.next();
        }
        return Integer.parseInt(s);
    }

    static private boolean isInteger(String s) {
        try {
            int n = Integer.parseInt(s);
            if(n < 0) {
                return false;
            }
            return true;
        } catch (NumberFormatException e) {
            return false;
        }
    }
}
