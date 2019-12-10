#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>


using namespace std;


#define int long long
#define vint vector<int>
#define INF 1 << 4
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

    string s; cin >> s;
    int n = s.length();
    vector<vector<int>> dp[3];
    
    dp[0].resize(n + 1, vint(n + 1 , INF));
    dp[1].resize(n + 1, vint(n + 1 , INF));
    dp[2].resize(n + 1, vint(n + 1 , INF));
    
    // for(int i = 0; i < n + 1; ++i) dp[0][0][i] = dp[1][0][i] = dp[2][0][i] = 0;
    
    dp[0][0][0] = dp[1][0][0] = dp[2][0][0] = 0;

    for(int i = 0; i < n; ++i) {
        for(int j = 0; j < n + 1; ++j) {
            dp[f(s[i])][i + 1][j] = min(dp[f(s[i])][i + 1][j], dp[f(s[i])][i][j]) + 1;


            for(int k = 0; k < 3; ++k) {
                if(k == f(s[i]) && j + g(s[i]) >= 0 && j + g(s[i]) < n + 1) 
                    dp[k][i + 1][j + g(s[i])] = min(dp[k][i + 1][j + g(s[i])] , dp[k][i][j]);
                else if(k != f(s[i]))
                    dp[k][i + 1][j] = min(dp[k][i + 1][j] , dp[k][i][j]);
            }
            
            // for(int k = 0; k < 3; ++k)

        }
    }
    
    for(int i = 0; i < n + 1; ++i) {
        for(int j = 0; j < n + 1; ++j) {
            printf("(%2Ld, %2Ld, %2Ld) ", dp[0][i][j],dp[1][i][j],dp[2][i][j]);
        }
        printf("\n");
    }



    return 0;
} 
