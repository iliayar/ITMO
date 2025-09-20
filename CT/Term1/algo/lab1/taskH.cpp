#include <iostream>
//#include <bits/stdc++.h>
#include <vector>

#define int long long

using namespace std;

bool check(int w,int h, int n, int a) {
    if((a/w) * (a/h) < n)
        return false;
    else
        return true;
}

signed main() {
    int w ,h ,n; cin >> w >> h >> n;
    int l = 0, r = max(w,h)*n;

    while(r - l > 1) {
        int m = (l+r)/2;
        if(check(w,h,n,m)) {
            r = m;
        } else {
            l = m;
        }
    }

    cout << r << endl;
    return 0;
}
