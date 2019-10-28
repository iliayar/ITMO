import java.io.*;

public class Test {
    public static void main(String[] args) {
        Scanner in = new Scanner(System.in);

    //    for(int i = 0; i < 30; ++i) {
    //        if(in.hasNextInteger()) {
    //            System.out.println("Integer " + in.nextInteger());
    //        } else if(in.hasNextString()) {
    //            System.out.println("String " + in.nextString());
    //        } else if(in.hasNextLine()) {
    //            System.out.println("Line " + in.nextLine());
    //        }
    //    }

        try {
            while(in.hasNextLine()) {
                String l = in.nextLine();
                System.out.print("Line: ");
                // System.out.println(l);
                Scanner in2 = new Scanner(l);
                while(in2.hasNextString()) {
                    System.out.print(", String: " + in2.nextString());
                }
                System.out.println();
            }
        } catch(IOException e) {}   
        try {
            in.close();
        } catch(IOException e){

        }
    }
}
