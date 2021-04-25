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

int bSearchR(int x) {
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
    if(x >= a[l]) l = r;
    return l;
}
int bSearchL(int x) {
    int l = 0, r = a.size();
    int m = (l + r)/2;
    while(r - l > 1) {
        if(x <= a[m]) {
            r = m;
        } else {
            l = m;
        }
        m = (l+r)/2;
    }
    if(x > a[l]) l = r;
    return l;
}

signed main() {
    int n; cin >> n;
    a.resize(n);
    for(int i = 0; i < n; ++i) {
        cin >> a[i];
    }
    sort(a.begin(), a.end());
    int k; cin >> k;
    for(int i = 0; i < k; ++i) {
        int l, r; cin >> l >> r;
        int ll, lr;
        ll = bSearchL(l);
        lr = bSearchR(r);
        cout << lr -  ll <<  " ";
    }
    cout << endl;
    return 0;
}
