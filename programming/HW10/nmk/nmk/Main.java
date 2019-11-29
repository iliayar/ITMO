package nmk;

import ticTacToe.*;

import java.util.Scanner;

public class Main {

    private void run(String[] argv) {
        int result;
//        do {

        int m, n, k;
        Scanner s = new Scanner(System.in);
        System.out.print("Enter m: "); m = s.nextInt();
        System.out.print("Enter n: "); n = s.nextInt();
        System.out.print("Enter k: "); k = s.nextInt();
        final Game game = new Game(false, new RandomPlayer(n,m), new HumanPlayer());

        result = game.play(new NmkBoard(n,m,k));
        System.out.println("Game result: " + result);
//        } while (result != 0);    }
    }

    public static void main(String[] argv) {
        new Main().run(argv);
    }

}
