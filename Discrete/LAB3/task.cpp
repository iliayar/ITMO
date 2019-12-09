#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long
#define vint vector<int>

#define FILENAME "local"

#ifndef LOCAL
#define FILENAME "num2perm"
#endif

using namespace std;

int n, k;

int fact(int n){
    int res = 1; 
    for(int i = 1 ; i <= n; ++i) {
        res  *= i;
    }
    return res;
}


signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);

    cin >> n >> k;

    vint res(n);
    vint was(n, false);

    int q = 0;
    for(int i = n - 1; i >= 0; --i) {
        for(int j = 0, o = 0; j < n; ++j, ++o) {
            if(was[j]) {
                o--;
                continue;
            }
            if(q + (o + 1) * fact(i) > k) {
                q += fact(i)*o ;
                was[j] = true;
                res[n - i - 1] = j + 1;
                break;
            }
        }
    }


    for(int i = 0; i < n; ++i) cout << res[i] << " ";
    cout << endl;
    return 0;
}
