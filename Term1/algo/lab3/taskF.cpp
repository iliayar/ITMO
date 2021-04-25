#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>


using namespace std;


// #define int long long
#define vint vector<int>
#define INF 30001
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

    if(n == 0) {
        cout << 0 << endl << 0 << " " << 0 << endl;
        return 0;
    }

    vint a(n + 1, 0);
    for(int i = 1; i < n + 1; ++i) cin >> a[i];
    
    vector<vint> dp(n + 1, vint(n + 1, INF));

    dp[0][0] = 0;
    // for(int i = 0; i < n + 1; ++i) dp[0][i] = 0;

    for(int i = 0; i < n; ++i) {
        for(int j = 0; j < n + 1; ++j) {
            if(j < n && a[i+1] > 100) dp[i + 1][j + 1] = min(dp[i+1][j+1], dp[i][j] + a[i + 1]);
            if(a[i+1] <= 100) dp[i + 1][j] = min(dp[i + 1][j], dp[i][j] + a[i + 1]);
            if(j > 0) dp[i + 1][j - 1] = min(dp[i + 1][j - 1], dp[i][j]);
        }
    }

    // for(int i = 0; i < n + 1; ++i) {
    //     // printf("Day: %d", i);
    //     for(int j = 0; j < n + 1; ++j) {
    //         printf("%5d ",dp[i][j]);
    //     }
    //     printf("\n");
    // }

    int mi = -1;
    int m = INF;
    for(int i = 0; i < n + 1; ++i) {
        if(dp[n][i] <= m) {
            m = dp[n][i];
            mi = i;
        }
    }

    vint res(n); int l = 0;
    int j = mi; int i = n;
    while(true) {
        if(i == 0) break;

        
        if(dp[i - 1][j] == (dp[i][j] - a[i])) {
            i = i - 1;
            j = j;
            continue;
        }

        if(j > 0 && dp[i - 1][j - 1] == (dp[i][j] - a[i])) {
            i = i - 1;
            j = j - 1;
            continue;
        }

        if(j < n && dp[i - 1][j + 1] == dp[i][j]) {
            res[l++] = i;
            i = i - 1;
            j = j + 1;
            continue;
        }
    }

    cout << dp[n][mi] << endl;
    cout << mi << " " << l << endl;
    for(int q = l - 1; q >= 0; --q) {
        cout << res[q] << endl;
    }

    return 0;
} 
