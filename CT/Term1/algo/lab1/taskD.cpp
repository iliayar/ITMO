#include <iostream>
//#include <bits/stdc++.h>
#include <vector>

#define int long long

using namespace std;

vector<int> a;

int n = 0;

int log2(int n) {
    int i = 0;
    while((n/=2) > 0) i++;
    return i;
}

void printTree() {
    cout << "----------TREEBEGIN-------" << endl;
    int c = log2(n) + 1;
    for(int i = 1, j = 0; j < n; i *= 3) {
        for(int q = 0; q < c; ++q) cout << " ";
        for(; j < min(i,n); ++j) {
            cout << a[j];
            for(int q = 0; q < c; ++q) cout << " "; 
        }
        cout << endl;
        c -= 1;
    }
    cout << "----------TREEEND----------" << endl;
}

void insert(int x) {
    a[n++] = x;

    for(int i  = n -1; i > 0 && a[(i-1)/2] < a[i]; i = (i-1)/2) {
        swap(a[i],a[(i-1)/2]);
    }
}

int extract() {
    swap(a[0],a[--n]);
    int i = 0;
    while(true) {
        if(2*i + 1 < n && a[2*i + 1] > a[i]) {
            if(2*i + 2 < n && a[2*i + 2] > a[2*i + 1]) {
                swap(a[i],a[2*i + 2]);
                i = 2*i + 2;
            } else {
                swap(a[i],a[2*i + 1]);
                i = 2*i + 1;
            }
        }
        else {
            if(2*i + 2 < n && a[2*i + 2] > a[i]) {
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
        if(t == 0) {
            cin >> t;
            insert(t);
        } else {
            cout << extract() << endl;
        }
    }

    return 0;
}
