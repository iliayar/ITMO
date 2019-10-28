#include <iostream>
//#include <bits/stdc++.h>
#include <vector>
 
#define int long long
 
using namespace std;
 
vector<int> a;
 
int n = 0;
 
void insert(int x) {
    a[n++] = x;
 
    for(int i  = n -1; i > 0 && a[(i-1)/2] > a[i]; i = (i-1)/2) {
        swap(a[i],a[(i-1)/2]);
    }
}
 
int extract() {
    swap(a[0],a[--n]);
    int i = 0;
    while(true) {
        if(2*i + 1 < n && a[2*i + 1] < a[i]) {
            if(2*i + 2 < n && a[2*i + 2] < a[2*i + 1]) {
                swap(a[i],a[2*i + 2]);
                i = 2*i + 2;
            } else {
                swap(a[i],a[2*i + 1]);
                i = 2*i + 1;
            }
        }
        else {
            if(2*i + 2 < n && a[2*i + 2] < a[i]) {
                swap(a[i],a[2*i + 2]);
                i = 2*i + 2;
            } else
                break;
        }
    }
    return a[n];
}
 
signed main() {
 
    int m; cin >> m;
 
    a.resize(2*m);
 
    for(int i = 0; i < m; ++i) {
        int t; cin >> t;
        insert(t);
    }
    for(int i = 0; i < m; ++i) {
        cout << extract() << " ";
    }
    cout << endl;
 
    return 0;
}
