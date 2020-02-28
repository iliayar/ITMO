
// Generated at 2020-02-21 03:37:26.404878 
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
#define W 1
#define B 0
#define NONE 2

struct Node {
    int b = 0;

    int l = NONE;
    int r = NONE;


    int set = NONE;
    int s = 0;
};


vector<Node> tree;



Node eval(Node v1, Node v2, int l) {
    Node res = v2;

    if(v1.set != NONE) {
        res = {(v1.set == B ? 1 : 0),
               v1.set,
               v1.set,
               v1.set,
               (v1.set == B ? l : 0)};
    }

    return res;
}

void sift(int v, int ll, int lr) {
    if(v*2 + 2 >= tree.size()) {
        return;
    }
    tree[v*2 + 1] = eval(tree[v], tree[v*2 + 1], ll);
    tree[v*2 + 2] = eval(tree[v], tree[v*2 + 2], lr);
}

void set_tree(int l, int r, int x, int v, int lx, int rx) {
    if(r <= l) {
        return;
    }
    int m  = (lx + rx)/2;
    sift(v, m - lx, rx - m);
    if(l == lx && r == rx) {
        tree[v] = eval({0, NONE, NONE, x}, tree[v], rx-lx);
        return;
    }
    set_tree(l, min(m,r), x, v*2 + 1, lx, m);
    set_tree(max(l, m), r,  x , v*2 + 2, m, rx);
    if(tree[v*2 + 1].r == tree[v*2 + 2].l && tree[v*2 + 1].r != NONE) {
        if(tree[v*2 + 1].r == W) {
            tree[v] = {tree[v*2 + 1].b + tree[v*2 + 2].b,
                       tree[v*2 + 1].l,
                       tree[v*2 + 2].r,
                       NONE,
                       tree[v*2 + 1].s + tree[v*2 + 2].s};
        } else {
            tree[v] = {tree[v*2 + 1].b + tree[v*2 + 2].b - 1,
                       tree[v*2 + 1].l,
                       tree[v*2 + 2].r,
                       NONE,
                       tree[v*2 + 1].s + tree[v*2 + 2].s};
        }
    } else {
        tree[v] = {tree[v*2 + 1].b + tree[v*2 + 2].b,
                   tree[v*2 + 1].l,
                   tree[v*2 + 2].r,
                   NONE,
                   tree[v*2 + 1].s + tree[v*2 + 2].s};
    }
}

struct Req{
    char c;
    int l;
    int r;
};

//entry
void sol() {



    int n; cin >> n;
    vector<Req> a(n);
    int shift = 500000;

    int m = 0;

    for(int i = 0; i < n; ++i) {
        cin >> a[i].c >> a[i].l >> a[i].r;
        a[i].c = (a[i].c == 'W' ? W : B);
        a[i].r += a[i].l;
        m = max(m,a[i].r);
        shift = min(shift, a[i].l);
    }
    if(shift > 0) shift = 0;
    else shift = -shift;
    m*=2;


    tree.resize((m + shift)*4, {0,NONE,NONE,NONE, 0});

    set_tree(0, m + shift, W, 0, 0, m + shift);

    for(int i = 0; i < n; ++i) {
        // print_tree();
        DBG("Setting " << (int)a[i].c << " in " << a[i].l << " " << a[i].r);
        set_tree(a[i].l + shift ,a[i].r + shift, a[i].c, 0, 0, m + shift);
        cout << tree[0].b << " " << tree[0].s << endl;
    }
   // print_tree();

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
