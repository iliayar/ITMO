
// Generated at 2020-03-02 19:05:06.259474 
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
const int INF = 1e+9;

struct Node {
    int sum;
    int max;

    int set;
    bool isset;
};

vector<Node> tree;

Node E = {0, -INF, 0, false};

Node eval(Node left, Node right) {
    // DBG("Eval");
    Node res = E;
    res.sum = left.sum + right.sum;
    res.max = max(left.max, right.max);
    return res;
}

void propagate(int v, int lx, int rx) {
    // DBG("Propagate");
    if(v*2 + 2 >= tree.size()) return;
    if(!tree[v].isset) return;

    int m = (lx + rx)/2;

    tree[v * 2 + 1].isset = true;
    tree[v * 2 + 1].set = tree[v].set;
    tree[v * 2 + 1].sum = tree[v].set*(m - lx);
    if(tree[v].set > 0 || (m - lx) <= 1)
        tree[v * 2 + 1].max = tree[v * 2 + 1].sum;
    else
        tree[v * 2 + 1].max = 0;

    tree[v * 2 + 2].isset = true;
    tree[v * 2 + 2].set = tree[v].set;
    tree[v * 2 + 2].sum = tree[v].set * (rx - m);
    if(tree[v].set > 0 || (rx - m) <= 1)
        tree[v * 2 + 2].max = tree[v * 2 + 2].sum;
    else
        tree[v * 2 + 2].max = 0;


    tree[v] = eval(tree[v*2 + 1], tree[v*2 + 2]);
}

void t_set(int l, int r, int x, int s, int v, int lx, int rx) {
    DBG("t_set[" << l << ", " << r << "]");
    if(r <= l) {
        return;
    }
    propagate(v, lx, rx);
    if((r == rx) && (l == lx)) {
        tree[v].isset = true;
        tree[v].set = x;
        tree[v].sum = (rx-lx)*x;
        if(x > 0 || (rx - lx) == 1)
            tree[v].max = tree[v].sum;
        else
            tree[v].max = 0;
        return;
    }
    int m = (lx + rx)/2;
    t_set(l, min(m,r), x, s, v * 2 + 1, lx, m);
    t_set(max(l,m), r, x, s + tree[v*2 + 1].sum, v * 2 + 2, m, rx);
    tree[v] = eval(tree[v*2 + 1], tree[v*2 + 2]);
}

int t_find(int h, int s, int v, int lx, int rx) {
    // DBG("t_find");
    if(rx - lx == 1) {
        if(tree[v].max + s > h) {
            return lx;
        }
        return rx;
    }
    propagate(v, lx, rx);
    int m = (lx + rx)/2;
    int lmax = tree[v*2 + 1].max + s;
    int rmax = tree[v*2 + 2].max + tree[v*2 + 1].sum + s;
    if(lmax > h) {
        return t_find(h, s, v*2 + 1, lx, m);
    } else {
        return t_find(h, s + tree[v*2 + 1].sum, v*2 + 2, m, rx);
    }

}

void t_print(int s, int v, int lx, int rx) {
    DBG("t_print[" << lx << ", " << rx << "] " << tree[v].sum << " " << tree[v].max + s);
  if (rx - lx == 1) {
      DBG(tree[v].max + s);
      return;
  }
  propagate(v, lx, rx);
  int m = (lx + rx) / 2;
  t_print(s, v * 2 + 1, lx, m);
  t_print(s + tree[v * 2 + 1].sum, v * 2 + 2, m, rx);
  return;
}

//entry
void sol() {
    int n; cin >> n;
    tree.resize(n*4, E);

    char op;
    while(cin >> op) {
        if(op == 'Q') {
            int h; cin >> h;
            // DBG("Running cart...");
            cout << t_find(h, 0, 0, 0, n) << endl;
        } else if(op == 'I') {
            int l, r, x; cin >> l >> r >> x; l--;
            // DBG("Lifting rails");
            t_set(l, r, x, 0, 0, 0, n);
            t_print(0, 0, 0, n);
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
