
// Generated at 2020-02-17 00:08:13.685904 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>


using namespace std;

#define ON 1
#define OFF 0
#ifdef LOCAL
#define FILE_IO ON
#define FILENAME "local"
#else
#define FILE_IO  OFF
#define FILENAME "smth"
#endif

#define int long long
#define vint vector<int>
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl;
#else
#define DBG(x)
#endif

//##################CODE BEGIN#############
vint tree;
 
int update(int i, int v, int x, int lx, int rx) {
    if(lx > i || rx <= i) {
        return tree[x];
    }
    if(rx - lx == 1) {
        tree[x] = v;
        return v;
    }
    int m = (lx + rx)/2;
    tree[x] = update(i, v, x*2 + 1, lx, m) + update(i, v, x*2 + 2, m, rx);
    return tree[x];
}
 
int sum(int l, int r, int x, int lx, int rx) {
    DBG("sum " << l << " " << r << " " << x << " " << lx << " " << rx);
    if(r <= l) {
        return 0;
    }
    if(l == lx && r == rx) {
        return tree[x];
    }
    int m = (lx+rx)/2;
    return sum(l,min(m,r),x*2 + 1, lx, m) + sum(max(l,m),r,x*2+2,m,rx);
 
}
 
//entry
void sol() {
    int n; cin >> n;
    // vint a(n);
    tree.resize(4*n,0);
    for(int i = 0; i < n; ++i) {
        // cin >> a[i];
        DBG("Updating " << i);
        int v; cin >> v;
        update(i, v, 0, 0, n);
    }
 
    string oper;
    while(cin >> oper) {
        if(oper == "set") {
            int i, v; cin >> i >> v; i--;
            DBG("Setting " << i << " to " << v);
            update(i, v, 0, 0, n);
        } else if(oper == "sum") {
            int l, r; cin >> l >> r; l--;
            DBG("Summing from " << l << " to " << r);
            cout << sum(l,r,0,0,n) << endl;
        }
    }
 
}
//##################CODE END###############
signed main() {
    #if FILE_IO == ON
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);
    #endif
    #ifdef LOCAL
    auto start = std::chrono::high_resolution_clock::now();
    #endif

    sol();

    #ifdef LOCAL
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << duration.count() << " microseconds" << endl;
    #endif
}
