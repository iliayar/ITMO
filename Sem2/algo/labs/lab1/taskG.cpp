
// Generated at 2020-03-06 00:49:22.350305 
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
struct Line {
  int add;
  int x;
  int l;
  int r;
};

struct Node {
    int add;
    int max;
    int imax;
};

int n;

vector<Node> tree;

Node eval(Node a, Node b) {
    Node t;
    if(a.max > b.max) {
        t.max = a.max;
        t.add = 0;
        t.imax = a.imax;
    } else {
        t.max = b.max;
        t.add = 0;
        t.imax = b.imax;
    }
    return t;
}

void propagate(int v, int l, int r) {
  if (v * 2 + 1 >= tree.size()) {
    return;
  }
  if(tree[v].add == 0) return;

  int m = (l + r)/2;

  if(tree[v * 2 + 1].max == 0) {
      tree[v * 2 + 1].imax = l;
  }
  if(tree[v * 2 + 2].max == 0) {
      tree[v * 2 + 2].imax = m + 1;
  }

  tree[v * 2 + 1].max += tree[v].add;
  tree[v * 2 + 1].add += tree[v].add;
  tree[v * 2 + 2].max += tree[v].add;
  tree[v * 2 + 2].add += tree[v].add;

  tree[v].add = 0;
}

void tree_add(int l, int r, int x, int v, int lx, int rx) {
    if (r < l) {
        return;
    }
    propagate(v, lx, rx);
    if (l == lx && r == rx) {
        if(tree[v].max == 0) {
            tree[v].imax = lx;
        }
        tree[v].max += x;
        tree[v].add += x;
        return;
    }
    int m = (lx + rx) / 2;
    tree_add(l, min(m, r), x, v * 2 + 1, lx, m);
    tree_add(max(l, m + 1), r, x, v * 2 + 2, m + 1, rx);
    tree[v] = eval(tree[v * 2 + 1], tree[v * 2 + 2]);
}

void tree_print(int v, int lx, int rx) {
    if(lx == rx) {
        cout << "(" << tree[v].max << ", " << tree[v].imax << ") ";
        return;
    }
    propagate(v, lx, rx);
    int m = (lx + rx)/2;
    tree_print(v*2+1, lx ,m);
    tree_print(v*2+2, m +1, rx);
}

vector<Line> a;


void a_print() {
    for(int i = 0; i < a.size(); ++i) {
        cout << "(" << a[i].x << ", " << a[i].add << ", (" << a[i].l << ", " << a[i].r << "))" << endl;
    }
}

int log2(int n) {
    int c = 0;
    while(n > 0) {
        c++;
        n >>= 1;
    }
    return c;
}

// entry
void sol() {
  int m;
  cin >> m;

  int ma = 0, mi = 0;

  for (int i = 0; i < m; ++i) {
    int rx, ry, lx, ly;
    cin >> lx >> ly >> rx >> ry;
    a.push_back({1, lx, ly, ry});
    a.push_back({-1, rx + 1, ly, ry});
    ma = max(ma, max(ly, ry));
    mi = min(mi, min(ly, ry));
  }

  n = ma - mi;

  tree.resize((1 << log2(n))*2, {0, 0, -1});

  sort(a.begin(), a.end(), [](Line a, Line b) { if(a.x == b.x) return a.add < b.add; else return a.x < b.x;; });
  // DBG_CODE(a_print());
  ma = 0;
  int my, mx;

  for(int i = 0; i < a.size(); ++i) {
      tree_add(a[i].l - mi, a[i].r - mi, a[i].add, 0, 0, n);
      if(tree[0].max > ma) {
          ma = tree[0].max;
          mx = a[i].x;
          my = tree[0].imax + mi;
      }
      DBG_CODE(tree_print(0, 0, n); cout << endl;);
  }

  cout << ma << endl << mx << " " << my << endl;
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
