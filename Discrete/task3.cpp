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
    for(int i = 0; i < pow(2,n); ++i) {
        if(calc(table,i) == calc(table,~i & ((int)pow(2,n)-1))) {
            return false;
        }
    }
    return true;
}

bool checkT1(int n, int table) {
    if(calc(table,pow(2,n)-1) == 1) {
        return true;
    }
    return false;
}


bool checkM(int n, int table, int val) {
    bool res = true;
    for(int i = 0; i < n; ++i) {
        if(calc(val,i) == 0) {
            if(calc(table, val | (1<<i)) < calc(table,val)) {
                return false;
            }
            res = res & checkM(n,table,val | (1<<i));
        }
    }
    return res;

}


bool checkL(int n, int table) {
    bool a0 = table & 1;
    vector<int> a(n);
    for(int i = 0; i < n; ++i) {
        a[i] = calc(table,pow(2,i))^a0;
    }
    for(int i = 0; i < pow(2,n); ++i) {
        bool v = a0;
        for(int j = 0; j < n; ++j) {
            v ^= calc(i,j)*a[j];
        }
        if(v != calc(table,i))
            return false;
    }
    return true;

}

signed main() {
    int n; cin >> n;
    bool isL = true, isM = true, isS = true, isT0 = true, isT1 = true;
    for(int i = 0; i < n; ++i) {
        int k; cin >> k;
        int table = 0;
        for(int j = 0; j < pow(2,k); ++j) {
            char t; cin >> t;
            table += (t-'0') << j;
        }

        bool tisL  = checkL (k,table);
        bool tisM  = checkM (k,table,0);
        bool tisS  = checkS (k,table);
        bool tisT1 = checkT1(k,table);
        bool tisT0 = checkT0(k,table);
        isL &= tisL; isM &= tisM; isS &= tisS; isT0 &= tisT0; isT1 &= tisT1;
        // cout << "DBG: " << tisT0 << " " << tisT1 << " " << tisL << " " << tisS << " " << tisM << endl;
    }
    if(isL || isM || isS || isT0 || isT1) {
        cout << "NO" << endl;
    } else {
        cout << "YES" << endl;
    }

    return 0;
}
