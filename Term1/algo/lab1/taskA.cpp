#include <iostream>
#include <bits/stdc++.h>

using namespace std;


vector<int> a;
vector<int> b;

void mergeSort(int l, int r) {
    if(r-l==1) return;

    int m = (l+r)/2;

    mergeSort(l,m);
    mergeSort(m,r);
    
    int i = l, j = m, k = 0;

    while(i < m || j < r) {
        if(i < m && (a[i] < a[j] || j >= r)) {
            b[k] = a[i];
            i++;
        } else {
            b[k] = a[j];
            j++;
        }
        k++;
    }
    
    for(i = l; i < r; ++i) {
        a[i] = b[i-l];
    }
}


int main() {

    int n; cin >> n;

    a.resize(n);
    b.resize(n,0);

    for(int i = 0; i < n; ++i) {
        cin >> a[i];
    }

    mergeSort(0,n);

    for(int i = 0; i < n; ++i) {
        cout << a[i] << " ";
    }
    cout << endl;
    return 0;
}
