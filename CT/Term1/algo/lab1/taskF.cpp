#include <iostream>
//#include <bits/stdc++.h>
#include <vector>
#include <algorithm>

#define int long long

using namespace std;

vector<int> a;

void printArray() {
    for(int i = 0; i < a.size(); ++i) cout << a[i] << " ";
    cout << endl;
}

int bSearch(int x) {
    int l = 0, r = a.size();
    int m = (l + r)/2;
    while(r - l > 1) {
        if(x < a[m]) {
            r = m;
        } else {
            l = m;
        }
        m = (l+r)/2;
    }
    if(abs(x-a[l]) < abs(x-a[r]))
        return a[l];
    else if(abs(x-a[l]) > abs(x-a[r]))
        return a[r];
    else if(abs(x-a[l]) == abs(x-a[r]))
        return a[l];
}

signed main() {
    int n, k; cin >> n >> k;
    a.resize(n);
    for(int i = 0; i < n; ++i) {
        cin >> a[i];
    }
    sort(a.begin(), a.end());
    for(int i = 0; i < k; ++i) {
        int t; cin >> t;
        cout << bSearch(t) << endl;
    }



    return 0;
}
