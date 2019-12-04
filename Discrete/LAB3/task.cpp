#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long

#define FILENAME "local"

#ifndef LOCAL
#define FILENAME "brackets"
#endif

using namespace std;

int n;

string s;

void foo(int k, int len) {
    if(len == n*2) {
        cout << s << endl;
        return;
    }
    if(n*2 - len > k) {
        s[len] = '('; foo(k + 1, len + 1);
    }
    if(k > 0) {
        s[len] = ')'; foo(k - 1, len + 1);
    }

}

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);

    cin >> n;
    for(int i = 0; i < 2*n; ++i) s += ' ';

    foo(0, 0);

    return 0;
}