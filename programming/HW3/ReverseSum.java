import java.util.Arrays;
import java.io.IOException;

public class ReverseSum {
    public static void main(String[] args) {

        Scanner inp = new Scanner(System.in);

        int colSum[] = new int[8];
        int res[][] = new int[8][0];
        int lineCnt = 0;
        try {
            // System.out.println(inp.hasNextLine());
            while(inp.hasNextLine()) {
                lineCnt++;
                if(lineCnt >= res.length) {
                    res = Arrays.copyOf(res, res.length + 1);
                }
                String numsStr = inp.nextLine();
                if(numsStr == null) {
                    continue;
                }
                int nums[] = new int[8];
                int numsCnt = 0;

                Scanner lineScanner = new Scanner(numsStr);
                while(lineScanner.hasNextInt()) {
                    if(numsCnt >= nums.length)  {
                        nums = Arrays.copyOf(nums, nums.length + 1);
                    }
                    nums[numsCnt++] = lineScanner.nextInt();
                }
    
                if(numsCnt > colSum.length) {
                    colSum = Arrays.copyOf(colSum, nums.length);
                }


                res[lineCnt-1] = new int[numsCnt];
    
                int sum = 0;
                for(int i = 0; i < numsCnt; ++i) {
                    sum += nums[i]; 
                    colSum[i] += nums[i];
                }
    
                for(int i = 0; i < numsCnt; ++i) {
                    res[lineCnt-1][i] = sum - nums[i];
                }            
            }
        } catch(IOException e) {
            // System.err.println(e.getClass());
        }

        for(int i = 0; i < lineCnt; ++i) {
            for(int j = 0; j < res[i].length; ++j) {
                System.out.print((res[i][j] + colSum[j])+ " ");
            }
            if(i != lineCnt - 1) {
                System.out.println();
            }
        }
        
        try {
            inp.close();
        } catch(Exception e) {}
        
    }

}
