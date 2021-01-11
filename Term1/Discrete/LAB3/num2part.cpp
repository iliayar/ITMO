#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long
#define vint vector<int>

#define FILENAME "local"
 
#ifndef LOCAL
#define FILENAME "num2part"
#endif
 
using namespace std;

const int SIZE = 1000;

int dp[SIZE][SIZE];

void prepare() {

    for(int i = 0; i < SIZE; ++i) dp[i][SIZE - 1] = 0;
    dp[SIZE - 1][SIZE - 1] = 1;
    // for(int i = 0; i < SIZE; ++i) dp[i][i] = 1;
    
    for(int i = 0 ; i < SIZE; ++i) {
        for(int j = SIZE - 2; j >= 0; --j) {
            if(j > i) dp[i][j] = 0;
            else if(j == i) dp[i][j] = 1;
            else dp[i][j] = dp[i][j+1] + dp[i - j][j];
        }
    }

}

vint res(0);

void solve(int n, int k) {
    
    int q = n;

    int i = 1;
    int d = 0;
    int j = 0;
    while(q - i >= i) {
        // cout << "k = " << k << endl;
        // cout << "q = " << q << endl;
        // cout << "i = " << i << endl;
        // cout << "j = " << j << endl;
        // cout << "dp[q-i][i] = " << dp[q-i][i] << endl << endl;
        if(k <= dp[q - i][i] + j) {
            // if(res.size() > 0) {
            //     j -= (i - res[res.size() - 1]);
            // }
            res.push_back(i);
            if(k == dp[q - i][i] + j) {
                if(q - i != 0 ) res.push_back(q - i);
                q = 0;
                break;
            }
            // k -= j;
            // j = 0;
            // j -= dp[q - i - 1][n];
            q -= i;
            // d++;
            // k++;
            continue;
        }
        j += dp[q - i][i];
        i++;
        // d++;
    }
    if(q != 0) res.push_back(q);

    cout << res[0];
    for(int i = 1; i < res.size(); ++i) {
        cout << "+" <<  res[i];
    }
    cout << endl;
}
signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
     
    //freopen(FILENAME".in", "r", stdin);
    //freopen(FILENAME".out", "w", stdout);
 
    prepare();

    int n, k; cin >> n >> k; 
    k++;
    // k = dp[n][SIZE - 1] - k - 1;
    
    
    solve(n,k);

    // cout << "TEST: " << dp[7][1] << endl;

    // for(int i = 0; i < dp[n][1]; ++i) {
    //     solve(n,i + 1);
    //     res.clear();
    // }
    
    return 0;
}
