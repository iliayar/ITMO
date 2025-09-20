#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>


using namespace std;


#define int long long
#define vint vector<int>
#define INF 1 << 6
#define ALL(a) a.begin(), a.end()


int f(char c) {
    switch (c)
    {
        case ')':
        case '(':
            return 0;
        case '[':
        case ']':
            return 1;
        case '{':
        case '}':
            return 2;
    }
}

int g(char c) {
    switch(c) {
        case '(':
        case '[':
        case '{':
            return 1;
        case ')':
        case ']':
        case '}':
            return -1;
    }
}

vector<vector<int>> dp;
vector<vector<int>> d;
string s;

void foo(int l, int r){
    if(dp[l][r] == r - l + 1) {
        return;
    }
    if(dp[l][r] == 0) {
        cout << s.substr(l , r - l + 1);
        return;
    }

    if(d[l][r] == -1) {
        cout << s[l];
        foo(l + 1, r - 1);
        cout << s[r];
        return;
    }
    // cout << d[l][r] << endl;
    foo(l, d[l][r]);
    foo(d[l][r] + 1, r);
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

    cin >> s;
    int n = s.length();

    dp.resize(n + 1, vint(n + 1, INF));
    d.resize(n + 1, vint(n + 1, -1));


    for(int i = 0; i < n; ++i)
        for(int j = 0; j < n; ++j)
            if(i == j) dp[i][i] = 1;
            else if(i < j) dp[j][i] = 0;

    for(int i = 0; i <= n; ++i) {
        for(int j = 0; j <= n - i; ++j) {
            int l = j, r = i + j - 1;
            if((f(s[l]) == f(s[r])) && (g(s[l]) == 1) && (g(s[r]) == -1)) {
                dp[l][r] = min(dp[l][r], dp[l + 1][r - 1]);
            }

            for(int k = l; k < r; ++k) {
                if(dp[l][r] > dp[l][k] + dp[k + 1][r]) {
                    dp[l][r] = dp[l][k] + dp[k + 1][r];
                    d[l][r] = k;
                }
            }
            // if(d[l][r] == -1) d[l][r] == l;
        }
    }

    // for(int i = 0; i < n; ++i) {
    //     for(int j = 0; j < n; ++j) {
    //         printf("%3Ld", dp[i][j]);
    //     }
    //     printf("\n");
    // }
    // printf("_____________________________________\n");

    // for(int i = 0; i < n + 1; ++i) {
    //     for(int j = 0; j < n + 1; ++j) {
    //         printf("%3Ld", d[i][j]);
    //     }
    //     printf("\n");
    // }

    // cout << n << endl;
    // cout << "ANS: " << dp[0][n-1] << endl;
    // for(int i = 0; i < n - dp[0][n-1]; ++i) cout << "?"; cout << endl;


    foo(0,n-1); cout << endl;
    return 0;
} 
