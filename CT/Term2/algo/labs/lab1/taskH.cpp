
// Generated at 2020-02-29 01:36:45.489643 
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
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

//##################CODE BEGIN#############

#define DEBUG OFF

#if DEBUG == OFF
#undef DBG
#undef DBG_CODE
#define DBG(x)
#define DBG_CODE(x)
#endif

#define FILE_IO ON
#define FILENAME "rmq"

const int INF = -((int)1) << 31;

struct Node {
    int min;
    bool set;
    bool any;
};
struct Request {
    int l;
    int r;
    int m;
};


Node I = {INF, false, true};

vector<Node> tree;
vector<Request> requests;

int n;

Node eval(Node a, Node b) {
    Node t = {0,0,0};
    t.min = min(a.min, b.min);
    if(a.any) {
        t.min = b.min;
    } else if(b.any) {
        t.min = a.min;
    }
    if(a.any && b.any) {
        t.min = -(INF + 1);
    }
    return t;
}
void sift(int v) {
    if(v*2 + 2 >= tree.size()) return;
    if(!tree[v].set) return;

    for(int i = 1; i < 3; ++i) {
        if(tree[v*2 + i].set) {
            tree[v*2 + i].min = max(tree[v*2 + i].min, tree[v].min);
        } else {
            tree[v*2 + i].min = tree[v].min;
        }
        tree[v*2 + i].set = true;
        tree[v*2 + i].any = false;
    }
    tree[v].set = false;
}

void t_set(int l, int r, int x, int v, int lx, int rx){
    if(r <= l) {
        return;
    }
    if((l == lx) && (r == rx)) {
        if(tree[v].set) {
            tree[v].min = max(tree[v].min, x);
        } else {
            tree[v].min = x;
        }
        tree[v].set = true;
        tree[v].any = false;
        DBG("t_set[" << lx << ", " << rx << ") " << tree[v].min << " " << tree[v].set);
        return;
    }
    sift(v);
    int m = (lx + rx)/2;
    t_set(l, min(m,r), x, v*2 + 1, lx, m);
    t_set(max(l,m), r, x, v*2 + 2, m, rx);
    tree[v] = eval(tree[v*2 + 1], tree[v*2 + 2]);
    DBG("t_set[" << lx << ", " << rx << ") " << tree[v].min << " " << tree[v].set);
}

void t_fill(int v, int lx, int rx) {
    if(rx - lx == 1) {
        if(tree[v].any) {
            tree[v] = {-(INF + 1), false, false};
        }
        DBG("t_fill[" << lx << ", " << rx << ") " << tree[v].min << " " << tree[v].set);
        return;
    }
    sift(v);
    int m = (lx + rx)/2;
    t_fill(v*2 + 1,lx,m);
    t_fill(v*2 + 2,m,rx);
    tree[v] = eval(tree[v*2 + 1], tree[v*2 + 2]);
    DBG("t_fill[" << lx << ", " << rx << ") " << tree[v].min << " " << tree[v].set);
}


Node t_min(int l, int r, int v, int lx, int rx) {
    if(r <= l) {
        return I;
    }
    // DBG("t_min: " << ((lx == l) &&  (rx == r)));
    if(((lx == l) &&  (rx == r))) {
        // DBG("WTF");
        DBG("t_min[" << lx << ", " << rx << ") " << tree[v].min << " " << tree[v].set);
        return tree[v];
    }
    sift(v);
    int m = (lx + rx)/2;
    Node t =  eval(t_min(l, min(r,m), v*2 + 1, lx, m),
                t_min(max(l,m), r, v*2 + 2, m, rx));
    DBG("t_min[" << lx << ", " << rx << ") " << t.min << " " << t.set);
    return t;
}

void print_array(int v, int lx, int rx) {
    DBG("print_array[" << lx << ", " << rx << ") " << tree[v].min << " " << tree[v].set);
    if(rx - lx == 1) {
        cout << tree[v].min << " ";
        DBG("[" << lx << "]");
        return;
    }
    sift(v);
    int m = (lx + rx)/2;
    print_array(v*2 + 1, lx, m);
    print_array(v*2 + 2, m, rx);
}

void inconsistent() {
    cout << "inconsistent" << endl;
    exit(0);
}

void build() {
    for(Request r : requests) {
        DBG(r.l << " " << r.r << " " << r.m);
        t_set(r.l, r.r, r.m, 0, 0, n);
    }
}

void check() {
    for(Request r : requests) {
        if(t_min(r.l, r.r, 0, 0, n).min != r.m) {
            DBG(r.l << " " << r.r << " " << r.m);
            inconsistent();
        }
    }
    cout << "consistent" << endl;
    print_array(0, 0, n);
    cout << endl;
}

//entry
void sol() {
    int m; cin >> n >> m;
    tree.resize(n*4, I);
    requests.resize(m);
    for(int i = 0; i < m; ++i) {
        Request t;
        cin >> t.l >> t.r >> t.m; t.l--;
        requests[i] = t;
    }
    build();
    t_fill(0,0,n);
    DBG_CODE(print_array(0, 0, n));
    check();
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
