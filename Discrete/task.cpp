#include <iostream>
#include <algorithm>
#include <cmath>
#include <vector>
#include <string>

using namespace std;

vector<vector<int>> a;
vector<bool> vals;
vector<bool> used;

int n, k;


bool getVal(int n, int v) {
    if(n == 0) {
        return !v;
    } else if(n == 1) {
        return v;
    } else {
        return 0;
    }
}

int getSingle(int j) {
    int res = -1;
    for(int i = 0; i < n; ++i) {
        if(used[i]){
            if(getVal(a[j][i],vals[i])) {
                return -1;
            }
            continue;
        }
        if(a[j][i] != -1) {
            if(res != -1)
                return -1;
            else
                res = i;
        }
    }
    return res;
}

bool check() {
    for(int i = 0; i < k; ++i) {
        bool r = false;
        for(int j = 0; j < n; ++j) {
            r = r || getVal(a[i][j], vals[j]);
        }
        if(!r) {
            return true;
        }
    }
    return false;
}

signed main() {
    cin >> n >> k;
    a.resize(k, vector<int>(n));
    vals.resize(n, 0);
    used.resize(n, 0);

    for(int i = 0; i < k; ++i){
        for(int j = 0; j < n; ++j) {
            cin >> a[i][j];
        }
    }
    
    while(true) {
        bool flag = false;
        for(int i = 0; i < k; ++i) {
            int r = getSingle(i);
            if(r != -1) {
                flag = true;
                used[r] = true;
                if(a[i][r] == 1)
                    vals[r] = 1;
            }
        }
        if(!flag) break;
    }

    if(check()) {
        cout << "YES" << endl;
    } else {
        cout << "NO" << endl;
    }

    return 0;
}
