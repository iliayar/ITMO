#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>


using namespace std;


#define int long long
#define vint vector<int>
#define INF 1 << 16;

vint a;
vint from;
vint dp;

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

    int n, k; cin >> n >> k;
    
    a.resize(n, 0);
    from.resize(n, -1);
    dp.resize(n, 0);

    for(int i = 1; i < n; ++i) {
        cin >> a[i];
    }


    for(int i = 0 ; i < n; ++i) {
        int m = -INF;
        int mi = -1;
        for(int j = i - 1; j >= max((int)0,i - k); --j) {
            if(dp[j] > m) {
                m = dp[j];
                mi = j;
            }
        }
        if(mi == -1) continue;
        dp[i] = dp[mi] + a[i];
        from[i] = mi;
    }
    vint path(1);
    int i = n - 1;
    path[0] = i + 1; 
    while(from[i] >= 0) {
        path.push_back(from[i] + 1);
        i = from[i];
    }

    cout << dp[n - 1] << endl;
    cout << path.size() - 1 << endl;
    for(int j = path.size() - 1; j >= 0; --j) {
        cout << path[j] << " ";
    }
    cout << endl;
    return 0;
}
