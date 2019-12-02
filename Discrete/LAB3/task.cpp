#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <cmath>

#define int long long

#define FILENAME "local"

#ifndef LOCAL
#define FILENAME "choose"
#endif

using namespace std;


int* order;
int* out;
bool* was;
int n;
int k;


void foo(int id, int st) {
    if(id == k) {
        int j = 0;
        for(int i = 0; i < n; ++i) {
            if(was[i]) out[j++] = i + 1;
        }
        if(j < k) return;
        for(int i = 0; i < k; ++i) {
            cout << out[i] <<  " "; 
        }
        cout << endl;
        return;
    }

    for(int i = st; i < n; ++i) {
        if(!was[i]) {
            was[i] = true;
            foo(id + 1, i);
            was[i] = false;
        }
    }
}

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);


    cin >> n; cin >> k;

    order = new int[n]; for(int i = 0; i < n; ++i) order[i] = -1;
    out = new int[n]; for(int i = 0; i < n; ++i) out[i] = -1;
    was = new bool[n]; for(int i = 0; i < n; ++i) was[i] = false;
    
    foo(0, 0);

    return 0;
}