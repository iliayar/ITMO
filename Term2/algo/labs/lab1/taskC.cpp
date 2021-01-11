
// Generated at 2020-02-18 01:16:09.062927 
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

struct Node {

    bool isset;
    int add;

    int min;
};


vector<Node> tree;


const int INF = 1e+18;


int log2(int x) {
    int c = 0;
    while(x != 0) {
        c++;
        x >>= 1;
    }
    return c;
}


void print_tree() {
    for(int i = 0, j = 0; i < log2(tree.size()); ++i) {
        for(int q = 0; q < (1 << i); ++q, ++j) {
            for(int k = 0; k < (1 << (log2(tree.size()) -i))/2; ++k) cout << " ";
            if(tree[j].min >= INF) {
                cout << "INF";
            } else {
                cout << tree[j].min;
            }
            cout << "," << tree[j].isset << "," << tree[j].add;
            for(int k = 0; k < (1 << (log2(tree.size()) -i))/2; ++k) cout << " ";
        }
        cout << endl;
    }
}

/*
v1
 \
  +->v2 = res
*/
Node eval(Node v1, Node v2) {
    Node res = {false, 0, INF};

    if(v1.isset) {
        res = {true, 0, v1.min};
    } else if(v2.isset) {
        res = {true, 0, v2.min + v1.add};
    } else {
        res = {false, v1.add + v2.add, v2.min + v1.add};
    }
    return res;
}

void sift(int v) {
    if(v*2 + 2 >= tree.size()) {
        return;
    }
    tree[v*2 + 1] = eval(tree[v], tree[v*2 + 1]);
    tree[v*2 + 2] = eval(tree[v], tree[v*2 + 2]);
    tree[v] = {false, 0, tree[v].min};
}
void set_tree(int l, int r, int x, int v, int lx, int rx) {
    if(r <= l) {
        return;
    }
    sift(v);
    if(l == lx && r == rx) {
        tree[v] = eval({true, 0, x}, tree[v]);
        return;
    }
    int m  = (lx + rx)/2;
    set_tree(l, min(m,r), x, v*2 + 1, lx, m);
    set_tree(max(l, m), r,  x , v*2 + 2, m, rx);
    tree[v].min = min(tree[v*2 + 1].min, tree[v*2 + 2].min);
}

void add(int l, int r, int x, int v, int lx, int rx) {
    if(r <= l) {
        return;
    }
    sift(v);
    if(l == lx && r == rx) {
        tree[v] = eval({false, x, 0}, tree[v]);
        return;
    }
    int m  = (lx + rx)/2;
    add(l, min(m,r), x, v*2 + 1, lx, m);
    add(max(l, m), r,  x , v*2 + 2, m, rx);
    tree[v].min = min(tree[v*2 + 1].min, tree[v*2 + 2].min);
}
int tree_min(int l, int r, int v, int lx, int rx) {
    if(r <= l) {
        return INF;
    }
    if(l == lx && r == rx) {
        return tree[v].min;
    }
    sift(v);
    int m  = (lx + rx)/2;
    return min(tree_min(l, min(m,r), v*2 + 1, lx, m),
               tree_min(max(l, m), r , v*2 + 2, m, rx));
}


//entry
void sol() {

    int n; cin >> n;
    tree.resize(4*n, {false, 0,  INF});

    for(int i = 0; i < n; ++i) {
        int x; cin >> x;
        set_tree(i,i+1,x, 0, 0, n);
    }

    string oper;
    // print_tree();
    while(cin >> oper) {
        if(oper == "set") {
            int l, r, x; cin >> l >> r >> x; l--;
            set_tree(l, r, x, 0, 0, n);
        } else if(oper == "add") {
            int l, r, x; cin >> l >> r >> x; l--;
            add(l, r, x, 0, 0, n);
        } else if(oper == "min") {
            int l, r; cin >> l >> r; l--;
            cout << tree_min(l, r, 0, 0, n) << endl;
        }
        // print_tree();
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
