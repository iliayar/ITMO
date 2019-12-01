#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long

#define FILENAME "local"

#ifndef LOCAL
#define FILENAME "telemetry"
#endif

using namespace std;

bool* was;

// vector<int> a;

int n, k;

void foo(int i, int j) {
    if(j == n) {
        return;
    }
    foo(i/k, j + 1);
    cout << ( (i/k) % 2 == 0 ? (i % k) : k - 1 - (i % k));
}


signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);

    cin >> n >> k;

    // a.resize(n);

    for(int i = 0; i < pow(k,n); ++i) {
        foo(i, 0);
        cout << endl;
    }

    return 0;
}