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



int min(int a, int b, int c) {
    return min(min(a,b),c);
}


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

    string s1, s2; cin >> s1 >> s2;
    s1 += '$'; s2 += '$';    
    s1 = '#' + s1; s2 = '#' + s2;

    vector<vint> dp(s1.length(), vint(s2.length(), 0));

    for(int i = 0; i < s1.length(); ++i) dp[i][0] = i;
    for(int i = 0; i < s2.length(); ++i) dp[0][i] = i;

    for(int i = 1; i < s1.length(); ++i) {
        for(int j = 1; j < s2.length(); ++j) {
            dp[i][j] = min(dp[i-1][j] + 1, dp[i][j-1] + 1, dp[i-1][j-1] + (s1[i] != s2[j] ? 1 : 0));
        }
    }
    
    cout << dp[s1.length() - 1][s2.length() - 1] << endl;

    return 0;
} 
