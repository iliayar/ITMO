#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>


using namespace std;


#define int long long
#define vint vector<int>
#define INF 1 << 16;
#define ALL(a) a.begin(), a.end()


signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);

#ifdef LOCAL    
    freopen("local.in", "r", stdin);
    freopen("local.out", "w", stdout);
//#else
//    freopen("input.txt", "r", stdin);
//    freopen("output.txt", "w", stdout);
#endif

    int n; cin >> n;

    const int m = 1e+9;

    vint dp[3][4];
    for(int i = 0; i < 3; ++i)
        for(int j = 0; j < 4; ++j) {
            dp[i][j].resize(n + 1);
            if(!(j == 3 || (j == 2 && i == 1)))
                dp[i][j][1] = 1;
        }

    for(int i = 2; i < n+1; ++i) {
        for(int j = 0; j < 3; ++j)
            for(int k = 0; k < 4; ++k) {
                int s = 0;
                if((j == 0 && k == 3) || (j == 2 && k == 3)) continue;
                if(j - 1 >= 0 && k - 2 >= 0) s=(s + dp[j - 1][k - 2][i - 1]) % m;
                if(j + 1 < 3 && k - 2 >= 0) s=(s + dp[j + 1][k - 2][i - 1]) % m;
                if(j - 1 >= 0 && k + 2 < 4) s=(s + dp[j - 1][k + 2][i - 1]) % m;
                if(j + 1 < 3 && k + 2 < 4) s=(s + dp[j + 1][k + 2][i - 1]) % m;
                if(j - 2 >= 0 && k - 1 >= 0) s=(s + dp[j - 2][k - 1][i - 1]) % m;
                if(j + 2 < 3 && k - 1 >= 0) s=(s + dp[j + 2][k - 1][i - 1]) % m;
                if(j - 2 >= 0 && k + 1 < 4) s=(s + dp[j - 2][k + 1][i - 1]) % m;
                if(j + 2 < 3 && k + 1 < 4) s=(s + dp[j + 2][k + 1][i - 1]) % m;
                dp[j][k][i] = s % m;
            }
    }

    int res = 0;
    for(int i = 0; i < 3; ++i)
        for(int j = 0; j < 4; ++j)
            res =(res + dp[i][j][n]) % m;
    
    cout << res;

    return 0;
} 
