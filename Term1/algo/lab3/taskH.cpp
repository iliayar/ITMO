#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>
 
 
using namespace std;
 
 
#define int long long
#define vint vector<int>
#define ALL(a) a.begin(), a.end()
 

const int INF = 1 << 30;

vector<vint> dp;
vector<vint> a;
vector<vint> d;
 
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
    
    const int N = pow(2,n);
 
    a.resize(n, vint(n));
    dp.resize(N, vint(n, INF));
    for(int i = 0; i < n; ++i)
        for(int j = 0; j < n; ++j)
            cin >> a[i][j];
 
    // for(int i = 0; i < n; ++i) dp[0][i] = 0;
    for(int i = 0; i < n; ++i) dp[1 << i][i] = 0;
    // for(int i = 0; i < n; ++i) 
    //     for(int j = 0; j < n; ++j){
    //         dp[(1 << j) | (1 << i)][i] = a[i][j];
    //         d[(1 << j) | (1 << i)][i] = j;
    //     }
    for(int mask = 0; mask < N; ++mask) {
        for(int i = 0; i < n; ++i) {
            if(!((mask >> i) & 1)) continue;
            for(int j = 0; j < n; ++j) {
                if(!((mask >> j) & 1)) continue;
                dp[mask][i] = min(dp[mask][i], dp[mask ^ (1 << i)][j] + a[i][j]);
            }
        }
    }
    
 
 
    // for(int i = 0; i < N; ++i) {
    //     for(int j = 0; j < n; ++j) {
    //         if(dp[i][j] == INF) {
    //             printf("%5s", "-");
    //             continue;
    //         }
    //         printf("%5Ld", dp[i][j]);
    //     }
    //     printf("\n");
    // }
    // printf("_____________________________________\n");
 
    // for(int i = 0; i < N; ++i) {
    //     for(int j = 0; j < n; ++j) {
    //         if(d[i][j] == INF) {
    //             printf("%5s", "-");
    //             continue;
    //         }
    //         printf("%5Ld", d[i][j]);
    //     }
    //     printf("\n");
    // }
 
    int id = -1;
    int m = INF;


    for(int i = 0; i < n; ++i) {
        if(dp[N-1][i] < m) {
            m = dp[N - 1][i];
            id = i;
        }
    }
    cout << m << endl;
    int mask = N - 1;
    // cout << id << endl;
    for(int i = 0; i < n; ++i) {
        cout << id + 1<< " ";
        for(int j = 0; j < n; ++j) {
            if(dp[mask][id] == dp[mask ^ (1 << id)][j] + a[id][j]) {
                mask = mask ^ (1 << id);
                id = j;
                break;
            }
        }
    }
    cout << endl;

    return 0;
} 
