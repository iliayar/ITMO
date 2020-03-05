
// Generated at 2020-03-03 03:01:19.402011 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>


using namespace std;

#define ON 1
#define OFF 0

// #define int long long
#define vint vector<int>
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

//##################CODE BEGIN#############
const int INF = 1e+9 + 1;

struct Node {
    int sum = 0;
    int max = 0;

    int set = 0;
    bool isset = false;

    Node* left = nullptr;
    Node* right = nullptr;
};



// int tree_size;

Node* tree = new Node();

void create_childs(Node* v) {
    // DBG("create_childs: " << v->left << " " << v->right);
  if (v->left == nullptr)
    v->left = new Node();
  if (v->right == nullptr)
    v->right = new Node();
}


void eval(Node*v) {
    // DBG("Eval");
    v->sum = v->left->sum + v->right->sum;
    v->max = max(v->left->max, v->right->max + v->left->sum);
    v->left = v->left;
    v->right = v->right;
    v->isset = false;
}

void propagate(int s, Node* v, int lx, int rx) {
    // DBG("Propagate");
    if(!v->isset) return;

    int m = (lx + rx)/2;
    if(v->left != nullptr) { 
        v->left->isset = true;
        v->left->set = v->set;
        v->left->sum = v->set*(m - lx);
        v->left->max = max(v->left->sum, (int)0);
        if(m - lx == 1)
            v->left->max = v->left->sum;
    }

    if(v->left != nullptr) {
        v->right->isset = true;
        v->right->set = v->set;
        v->right->sum = v->set * (rx - m);
        v->right->max = max(v->right->sum, (int)0);
        if (rx - m == 1)
            v->right->max = v->right->sum;
    }
    // eval(v);
    v->isset = false;
}

void t_set(int l, int r, int x, int s, Node* v, int lx, int rx) {
    // DBG("t_set");
    if(r <= l) {
        return;
    }
    create_childs(v);
    propagate(s, v, lx, rx);
    if((r == rx) && (l == lx)) {
        v->isset = true;
        v->set = x;
        v->sum = (rx-lx)*x;
        v->max = max(v->sum, (int)0);
        if(rx - lx == 1)
          v->max = v->sum;
        return;
    }
    int m = (lx + rx)/2;
    t_set(l, min(m,r), x, s, v->left, lx, m);
    t_set(max(l,m), r, x, s + v->left->sum, v->right, m, rx);
    eval(v);
}

int t_find(int h, int s, Node* v, int lx, int rx) {
    // DBG("t_find");
    if (rx - lx == 1) {
        if (v->max + s > h) {
            return lx;
        }
        return rx;
    }
    create_childs(v);
    propagate(s, v, lx, rx);
    int m = (lx + rx)/2;
    int lmax = v->left->max + s;
    int rmax = v->right->max + v->left->sum + s;
    if(lmax > h) {
        return t_find(h, s, v->left, lx, m);
    } else {
        return t_find(h, s + v->left->sum, v->right, m, rx);
    }

}

void t_print(int s, Node* v, int lx, int rx) {
    // DBG("t_print[" << lx << ", " << rx << "] " << tree[v].sum << " " << tree[v].max);
    if (rx - lx == 1) {
        DBG(v->max + s);
        return;
    }
    create_childs(v);
    propagate(s, v, lx, rx);
    int m = (lx + rx) / 2;
    t_print(s, v->left, lx, m);
    t_print(s + v->left->sum, v->right, m, rx);
    return;
}

//entry
void sol() {
    int n; cin >> n;

    char op;

    for(;;) {
        cin >> op;
        if(op == 'Q') {
            // DBG("Running cart...");
            int h; cin >> h;
            cout << t_find(h, 0, tree, 0, n) << endl;
            // cout << tree[0].imax << endl;
        } else if(op == 'I') {
            // DBG("Lifting rails");
            int l, r, x; cin >> l >> r >> x; l--;
            t_set(l, r, x, 0, tree, 0, n);
            // t_print(0, tree, 0, n);
        } else {
            break;
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
