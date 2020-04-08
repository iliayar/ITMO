
// Generated at 2020-02-27 03:02:49.629146 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#define vint vector<int>
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl;
#else
#define DBG(x)
#endif

//##################CODE BEGIN#############
#define FILE_IO ON
#define FILENAME "parking"


const int INF = 100001;

vint tree;


void update(int i, int x, int v, int lx, int rx) {
    if(rx - lx == 1) {
        if(x == 0) {
            tree[v] = INF;
        } else {
            tree[v] = lx;
        }
        return;
    }

    int m = (lx + rx)/2;
    if(i < m) {
        update(i, x, v*2 + 1, lx, m);
    } else {
        update(i, x, v*2 + 2, m, rx);
    }

    tree[v] = min(tree[v*2 + 1], tree[v*2 + 2]);
}

int tree_free(int l, int r, int v, int lx, int rx) {
    if(r <= l) {
        return INF;
    }
    if(lx == l && rx == r) {
        return tree[v];
    }
    int m = (lx + rx)/2;
    return min(tree_free(l, min(m,r), v*2 + 1, lx, m),
               tree_free(max(m,l), r, v*2 + 2, m, rx));
}


//entry
void sol() {
    int n, m; cin >> n >> m;

    tree.resize(n*4, INF);
    for(int i = 0; i < n; ++i) {
        update(i, 1, 0, 0, n);
    }

    for(int i = 0; i < m; ++i) {
        string s; cin >> s;
        int x; cin >> x;
        if(s == "exit") {
            update(x-1, 1, 0, 0, n);
        } else {
            int f;
            int r = tree_free(x - 1, n, 0, 0, n);
            int l = tree_free(0, x-1, 0, 0, n);
            if(r != INF) {
                f = r;
            } else {
                f = l;
            }
            update(f, 0, 0, 0, n);
            cout << f + 1 << endl;
        }
    }
}
//##################CODE END###############
#ifdef LOCAL
#undef FILE_IO
#undef FILENAME
#define FILE_IO ON
#define FILENAME "local"
#endif

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0);
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
