#include <iostream>
//#include <bits/stdc++.h>
#include <vector>
#include <algorithm>

#define int long long
#define double long double

using namespace std;


signed main() {
    int n, x, y; cin >> n >> x >> y; n--;
    int t = 1.0*y*n/(x+y) + 0.5;
    int T1 = x*t;
    int T2 = y*(n-t);
    int T = max(T1,T2) + min(x,y);
    cout << T << endl;
    return 0;
}
