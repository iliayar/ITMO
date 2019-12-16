 package nmk;

 import ticTacToe.*;

 public class Match {
    
     Player player1;
     Player player2;

     Board board;

     private int order = 0;
     private int player1Wins = 0;
     private int player2Wins = 0;


     public Match(Player player1, Player player2, Board board) {
         this.player1 = player1;
         this.player2 = player2;
         this.board = board;
     }

     public void run(int wins) {

         player1Wins = 0;
         player2Wins = 0;
         order = 0;

         while(player1Wins < wins && player2Wins < wins) {
             Game game = new Game(false, player1, player2);
             int result = game.play(board);
             System.out.print("Player ");
             if(result == 1) {
                 player1Wins++;
             } else if(result == 2) {
                 player2Wins++;
             }
             printScores();
             int tmp = player1Wins;

             player1Wins = player2Wins;
             player2Wins = tmp;
             order ^= 1;
             board = board.newBoard();
             System.out.println(board.toString());
         }
         if(order == 1) {
             int tmp = player1Wins;
             player1Wins = player2Wins;
             player2Wins = tmp;
             swapPlayers();
         }

         int winPlayer = -1;

         if(player1Wins > player2Wins) {
             winPlayer = 1;
         } else {
             winPlayer = 2;
         }


         System.out.println("Player" + Integer.toString(winPlayer) + " win");
     }

     private void printScores() {
         int score1 = player1Wins;
         int score2 = player2Wins;
         if (order == 1) {
             int tmp = score1;
             score1 = score2;
             score2 = tmp;
         }
         System.out.println("Score: " + score1 + ":" + score2);
     }

     private void swapPlayers() {
         Player tmpPlayer = player1;
         player1 = player2;
         player2 = tmpPlayer;

     }
 }