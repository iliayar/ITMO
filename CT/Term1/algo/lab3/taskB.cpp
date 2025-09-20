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
#else
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
#endif

    int n, m; cin >> n >> m;
   
    vector<vint> a(n, vint(m));
    vector<vint> dp(n, vint(m, 0));

    for(int i = 0; i < n; ++i) {
        for(int j = 0; j < m; ++j){ 
            cin >> a[i][j];
            if(j == 0) {
                if(i > 0) dp[i][j] = dp[i-1][j] + a[i][j];
                else dp[i][j] = a[i][j];
            }
            if(i == 0) {
                if(j > 0) dp[i][j] = dp[i][j-1] + a[i][j];
            }
        }
    }    

    for(int i = 1; i < n; ++i) {
        for(int j = 1; j < m; ++j) {
            dp[i][j] = max(dp[i][j - 1], dp[i - 1][j]) + a[i][j];
        }
    }

    string res = "";
    
    int x = m - 1, y = n - 1;
    while(x != 0 || y !=0) {
        if(x > 0 && dp[y][x] == dp[y][x - 1] + a[y][x]) {
            res += 'R';
            x = x - 1;
        } else {
            res += 'D';
            y = y - 1;
        }
    }

    cout << dp[n - 1][m - 1] << endl; 
    reverse(ALL(res)); 
    cout << res << endl;
    return 0;
} 
