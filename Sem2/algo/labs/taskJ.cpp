
// Generated at 2020-02-28 20:41:04.064992 
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

const int INF = 1e+7 + 1;

struct Node {
    int min;
    int imin;
    bool set;
};

Node I = {INF, -1, false};

vector<Node> tree;

Node eval(Node a, Node b) {
    Node t;
    if(a.min < b.min) {
        t.min = a.min;
        t.imin = a.imin;
    } else {
        t.min = b.min;
        t.imin = b.imin;
    }
    // t.set = false;
    return t;
}

void sift(int v) {
    if(v*2 + 2 >= tree.size()) return;
    if(!tree[v].set) return;

    for(int i = 1; i < 3; ++i) {
        tree[v*2 + i].min = max(tree[v*2 + i].min, tree[v].min);
        tree[v*2 + i].set = true;
    }
    tree[v].set = false;
}

void t_set(int l, int r, int x, int v, int lx, int rx){
    if(r <= l) {
        return;
    }
    sift(v);
    if((l == lx) && (r == rx)) {
        tree[v].set = true;
        tree[v].min = max(tree[v].min, x);
        return;
    }
    int m = (lx + rx)/2;
    t_set(l, min(m,r), x, v*2 + 1, lx, m);
    t_set(max(l,m), r, x, v*2 + 2, m, rx);
    tree[v] = eval(tree[v*2 + 1], tree[v*2 + 2]);
}

Node t_min(int l, int r, int v, int lx, int rx) {
    if(r <= l) {
        return I;
    }
    // DBG("t_min: " << ((lx == l) &&  (rx == r)));
    if(((lx == l) &&  (rx == r))) {
        // DBG("WTF");
        return tree[v];
    }
    sift(v);
    int m = (lx + rx)/2;
    return eval(t_min(l, min(r,m), v*2 + 1, lx, m),
                t_min(max(l,m), r, v*2 + 2, m, rx));
}

void build(int v, int lx, int rx) {
    if(rx - lx == 1) {
        tree[v].min = 0;
        tree[v].imin = lx;
        tree[v].set = false;
        return;
    }
    int m = (lx + rx)/2;
    build(v*2 + 1, lx, m);
    build(v*2 + 2, m, rx);
    tree[v] = eval(tree[v*2 + 1], tree[v*2 + 2]);
}

//entry
void sol() {

    int n, m; cin >> n >> m;
    tree.resize(n*4, {0,0,0});
    build(0, 0, n);
    for(int i = 0; i < m; ++i) {
        string op; cin >> op;
        if(op == "attack") {
            int l, r; cin >> l >> r; l--;
            Node t = t_min(l, r, 0, 0, n);
            cout << t.min << " " << t.imin + 1 << endl;
        } else {
            int l, r, x; cin >> l >> r >> x; l--;
            t_set(l, r, x, 0 , 0, n);
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
