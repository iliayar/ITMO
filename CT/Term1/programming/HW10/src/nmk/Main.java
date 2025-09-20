package nmk;

import ticTacToe.*;

import java.util.Scanner;

public class Main {

    Scanner in;

    private void run(String[] argv) {
        int result;
//        do {

        int m, n, k;
        in = new Scanner(System.in);
        m = HumanPlayer.readInt("Enter m: ", in);
        n = HumanPlayer.readInt("Enter n: ", in);
        k = HumanPlayer.readInt("Enter k: ", in);
        int wins = HumanPlayer.readInt("Enter max wins: ", in);
        Match match = new Match(new HumanPlayer(), new HumanPlayer(), new NmkBoard(n,m,k));

        match.run(wins);
//        final Game game = new Game(false, new RandomPlayer(n,m), new HumanPlayer());
//
//        result = game.play(new NmkBoard(n,m,k));
//
//        String msg = "";
//
//        switch(result) {
//            case 0:
//                msg = "Draw"; break;
//            case 1:
//                msg = "Player 1 won"; break;
//            case 2:
//                msg = "Player 2 won"; break;
//        }
//        System.out.println(msg);
////        } while (result != 0);    }
    }

    public static void main(String[] argv) {
        new Main().run(argv);
    }

}
