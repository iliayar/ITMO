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
    
    vint a(n);
    for(int i = 0; i < n; ++i) cin >> a[i];

    vint from(n, -1);
    vint dp(n);
    
    int mx = 0;
    int mix = -1;

    for(int i = 0 ; i < n; ++i) {
        int m = 0;
        int mi = i;
        for(int j = i - 1; j >= 0; --j) {
            if(a[j] < a[i] && dp[j] > m) {
                m = dp[j];
                mi = j;
            }
        }   
        from[i] = mi;
        dp[i] = m + 1;
        if(dp[i] >= mx) {
            mx = dp[i];
            mix = i;
        }
    }

    int j = mix;
    vint res(0);
    while(true) {
        res.push_back(a[j]);
        if(from[j] == j) break;
        j = from[j];
    }

    cout << res.size() << endl;
    for(int i = res.size() - 1; i >= 0; --i)
        cout << res[i] << " ";
    cout << endl;
    return 0;
} 
