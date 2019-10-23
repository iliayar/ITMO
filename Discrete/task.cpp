#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <algorithm>
#include <cmath>

#define int long long

using namespace std;

bool calc(int table, int val) {
    return(( table >> val ) & 1);
}

bool checkT0(int n, int table) {
    if (calc(table,0) == 0) {
        return true;
    }
    return false;
}

bool checkS(int n, int table) {
    for(int i = 0; i < n; ++i) {
        if(calc(table,i) == calc(table,~i)) {
            return false;
        }
    }
    return true;
}

bool checkT1(int n, int table) {
    if(calc(table,pow(2,n) - 1) == 1) {
        return true;
    }
    return false;
}


bool checkM(int n, int table) {
    bool res = true;
    for(int i = 0; i < n; ++i) {
        if(calc(n,i) == 0) {
            if(calc(table, n | (1<<i)) < calc(table,n)) {
                return false;
            }
            res = res & checkM(n | (1<<i),table);
        }
    }
    return res;

}


// bool checkL(..)
// TODO linear check function
// and resulting check

signed main() {
    int n; cin >> n;

    for(int i = 0; i < n; ++i) {
        int k; cin >> k;
        int table = 0;
        for(int j = 0; j < pow(2,k); ++j) {
            char t; cin >> t;
            table = table*2 + (t-'0');
        }
    }

    return 0;
}
