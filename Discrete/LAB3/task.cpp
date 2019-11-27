#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long

#define FILENAME "local"

#ifndef LOCAL
#define FILENAME "chaincode"
#endif

using namespace std;

bool* was;

void print_bits(int n, int k) {
    for(int i = k - 1; i >= 0; --i) {
        cout << ((n >> i) & 1);
    }
    cout << endl;
}

int cut(int n,int k) {
    return (n & ((1 << k) - 1));
}

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);


    int n; cin >> n;
    
    was = new bool[(1 << n)];


    for(int i = 0; i < (1 << n); ++i) was[i] = false;


    int k = 0;


    for(int i = 0; i < (1 << n); ++i) {
        was[k] = true;
        print_bits(k,n);
        if(!was[cut(k<<1, n) + 1]) {
            k = cut(k<<1, n) + 1;
        } else {
            k = cut(k<<1 , n);
        }
    }

    return 0;
}