 package nmk;

 import ticTacToe.*;

 public class Match {
    
     Player player1;
     Player player2;

     Board board;


     public Match(Player player1, Player player2, Board board) {
         this.player1 = player1;
         this.player2 = player2;
         this.board = board;
     }

     public void run(int wins) {
         int player1Wins = 0;
         int player2Wins = 0;

         int mod = 0;

         while(player1Wins < wins && player2Wins < wins) {
             Game game = new Game(false, player1, player2);
             int result = game.play(board);
             if(result == 1) {
                 player1Wins++;
             } else if(result == 2) {
                 player2Wins++;
             }
             int tmp = player1Wins;

             player1Wins = player2Wins;
             player2Wins = tmp;
             Player tmpPlayer = player1;
             player1 = player2;
             player2 = tmpPlayer;
             mod ^= 1;
             board = board.newBoard();
         }
         if(mod == 1) {
             int tmp = player1Wins;
             player1Wins = player2Wins;
             player2Wins = tmp;
             Player tmpPlayer = player1;
             player1 = player2;
             player2 = tmpPlayer;
         }

         int winPlayer = -1;

         if(player1Wins > player2Wins) {
             winPlayer = 1;
         } else {
             winPlayer = 2;
         }


         System.out.println("Player" + Integer.toString(winPlayer) + " win with score:");
         System.out.println(Integer.toString(player1Wins) + ":" + Integer.toString(player2Wins));
     }
 }