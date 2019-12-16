#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long
#define vint vector<int>

#define FILENAME "local"

#ifndef LOCAL
#define FILENAME "choose2num"
#endif

using namespace std;

int n, k, m;

int fact(int n){
    int res = 1; 
    for(int i = 1 ; i <= n; ++i) {
        res  *= i;
    }
    return res;
}

int C(int n, int k) {
    int res = 1;
    int t = 1;
    for(int i = k + 1; i <= n; ++i) {
        res *= i;
        if(res % t == 0) res /= t++;
    }

    return res;
}


void sol() {
    vint res(k);
    
    int q = 0;
    int last = 0;
    for(int i = 1; i <= k; ++i) {
        for(int j = last + 1; j <= n; ++j) {
                if(q + C(n - j, k - i)> m) {
                //   q += C(n - j, k - i);
                    last = j;
                    res[i - 1] = j;
                    break;
                }
                q += C(n - j, k - i);
            //   cout << q + C(n - j + 1, k - i) << " ";
        }
        // cout << endl;
    }


    for(int i = 0; i < k; ++i) cout << res[i] << " ";
    cout << endl;
}

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);

    cin >> n >> k;
    vint a(k); 
    for(int i = 0; i < k; ++i) cin >> a[i];
    // vint was(n);
    int last = 1;
    int res = 0;
    for(int i = 0; i < k; ++i) {
        int t = a[i];
        // int l = 0;
        for(int j = last; j < t; ++j)
            res += C(n - j, k - i - 1);
        last = t + 1;
        // cout << res << endl;
        // was[t - 1] = 1;
    }

    cout << res << endl;
    // cin >> n >> k >> m; sol(); return 0;
    // for(int i = 0; i < C(n,k); ++i) {
    //     m = i; sol();
    // }
    return 0;
}
