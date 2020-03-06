
// Generated at 2020-03-06 03:59:11.083274 
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
struct Node {
    Node() {
        for(int i = 0; i < 8; ++i) {
            to[i] = nullptr;
        }
    }

    int x = 0;
    Node* to[8];
};


void create_childs(Node *v)
{
    for(int i = 0; i < 8; ++i) {
        if(v->to[i] == nullptr) {
            v->to[i] = new Node();
        }
    }
}

void eval(Node* v, int lx, int rx, int ly, int ry, int lz, int rz) {
    v->x = 0;
    int mx = (lx + rx)/2;
    int my = (ly + ry)/2;
    int mz = (lz + rz)/2;
    if((lx <= mx) && (ly <= my) && (lz <= mz)) {
        v->x += v->to[0]->x;
    }
    if ((mx + 1 <= rx) && (ly <= my) && (lz <= mz)) {
        v->x += v->to[1]->x;
    }
    if ((lx <= mx) && (my + 1 <= ry) && (lz <= mz)) {
        v->x += v->to[2]->x;
    }
    if ((mx + 1 <= rx) && (my + 1 <= ry) && (lz <= mz)) {
        v->x += v->to[3]->x;
    }
    if ((lx <= mx) && (ly <= my) && (mz + 1 <= rz)) {
        v->x += v->to[4]->x;
    }
    if ((mx + 1 <= rx) && (ly <= my) && (mz + 1 <= rz)) {
        v->x += v->to[5]->x;
    }
    if ((lx <= mx) && (my + 1 <= ry) && (mz + 1 <= rz)) {
        v->x += v->to[6]->x;
    }
    if ((mx + 1 <= rx) && (my + 1 <= ry) && (mz + 1 <= rz)) {
        v->x += v->to[7]->x;
    }
}

Node *tree = new Node();
void tree_print(Node *v, int lx, int rx, int ly, int ry, int lz, int rz) {
  if ((rx < lx) || (ry < ly) || (rz < lz))
    return;
  DBG("tree_print " << lx << ", " << rx << "; " << ly << ", " << ry << "; "
                    << lz << ", " << rz);
  if (((rx - lx) == 0) && ((ry - ly) == 0) && ((rz - lz) == 0)) {
    cout << v->x << " ";
    return;
  }
  // DBG("tree_add");
  create_childs(v);
  int mx = (lx + rx) / 2;
  int my = (ly + ry) / 2;
  int mz = (lz + rz) / 2;

  tree_print(v->to[0], lx, mx, ly, my, lz, mz);
  tree_print(v->to[1], mx + 1, rx, ly, my, lz, mz);
  tree_print(v->to[2], lx, mx, my + 1, ry, lz, mz);
  tree_print(v->to[3], mx + 1, rx, my + 1, ry, lz, mz);
  tree_print(v->to[4], lx, mx, ly, my, mz + 1, rz);
  tree_print(v->to[5], mx + 1, rx, ly, my, mz + 1, rz);
  tree_print(v->to[6], lx, mx, my + 1, ry, mz + 1, rz);
  tree_print(v->to[7], mx + 1, rx, my + 1, ry, mz + 1, rz);
}
void tree_add(int x, int y, int z, int k, Node *v, int lx, int rx, int ly,
              int ry, int lz, int rz)
{
  if ((rx < lx) || (ry < ly) || (rz < lz))
    return;
  // DBG("tree_add enter " << lx << ", " << rx << "; " << ly << ", " << ry << "; "
  //                     << lz << ", " << rz << "; " << v->x);
  if (((rx - lx) == 0) && ((ry - ly) == 0) && ((rz - lz) == 0)) {
      v->x += k;
      return;
  }
    // DBG("tree_add");
    create_childs(v);
    int mx = (lx + rx)/2;
    int my = (ly + ry)/2;
    int mz = (lz + rz)/2;

    if(lx <= x && x <= mx) {
        if(ly <= y && y <= my) {
            if(lz <= z && z <= mz) {
                tree_add(x, y, z, k, v->to[0], lx, mx, ly, my, lz, mz);
            } else {
                tree_add(x , y, z, k, v->to[4], lx, mx, ly, my, mz + 1, rz);
            }
        } else {
            if (lz <= z && z <= mz) {
                tree_add(x, y, z, k, v->to[2], lx, mx, my + 1, ry, lz, mz);
            } else {
                tree_add(x, y, z, k, v->to[6], lx, mx, my + 1, ry, mz + 1, rz);
            }
        }
    } else {
        if (ly <= y && y <= my) {
            if (lz <= z && z <= mz) {
                tree_add(x, y, z, k, v->to[1], mx + 1, rx, ly, my, lz, mz);
            } else {
                tree_add(x, y, z, k, v->to[5], mx + 1, rx, ly, my, mz + 1, rz);
            }
        } else {
            if (lz <= z && z <= mz) {
                tree_add(x, y, z, k, v->to[3], mx + 1, rx, my + 1, ry, lz, mz);
            } else {
                tree_add(x, y, z, k, v->to[7], mx + 1, rx, my + 1, ry, mz + 1, rz);
            }
        }
    }
    eval(v, lx, rx, ly, ry, lz, rz);
    // DBG("tree_add quit " << lx << ", " << rx << "; " << ly << ", " << ry << "; "
    //                 << lz << ", " << rz << "; " << v->x);
}

int tree_sum(int flx, int frx, int fly, int fry, int flz, int frz,
             Node* v, int lx, int rx, int ly, int ry, int lz, int rz)
{
  if ((frx < flx) || (fry < fly) || (frz < flz))
    return 0;
  // DBG("tree_sum enter" << lx << ", " << rx << "; " << ly << ", " << ry << "; " << lz
  //     << ", " << rz << "; " << v->x);
  if ((flx == lx) && (frx == rx) && (fly == ly) && (fry == ry) && (flz == lz) &&
      (frz == rz)) {
      // DBG("tree_sum fin " << tree->x);
    return v->x;
    }
    // DBG("tree_sum");
    create_childs(v);
    int mx = (lx + rx)/2;
    int my = (ly + ry)/2;
    int mz = (lz + rz)/2;
    
    int res = 
        tree_sum(flx, min(frx, mx), fly, min(fry, my), flz, min(frz, mz), v->to[0], lx, mx, ly, my, lz, mz) +
        tree_sum(max(flx, mx + 1), frx, fly, min(fry, my), flz, min(frz, mz), v->to[1], mx + 1, rx, ly, my, lz, mz) +
        tree_sum(flx, min(frx, mx), max(fly, my + 1), fry, flz, min(frz, mz), v->to[2], lx, mx, my + 1, ry, lz, mz) +
        tree_sum(max(flx, mx + 1), frx, max(fly, my + 1), fry, flz, min(frz, mz), v->to[3], mx + 1, rx, my + 1, ry, lz, mz) +
        tree_sum(flx, min(frx, mx), fly, min(fry, my), max(flz, mz + 1), frz, v->to[4], lx, mx, ly, my, mz + 1, rz) +
        tree_sum(max(flx, mx + 1), frx, fly, min(fry, my), max(flz, mz + 1), frz, v->to[5], mx + 1, rx, ly, my, mz + 1, rz) +
        tree_sum(flx, min(frx, mx), max(fly, my + 1), fry, max(flz, mz + 1), frz, v->to[6], lx, mx, my + 1, ry, mz + 1, rz) +
        tree_sum(max(flx, mx + 1), frx, max(fly, my + 1), fry, max(flz, mz + 1), frz, v->to[7], mx + 1, rx, my + 1, ry, mz + 1, rz);

    // DBG("tree_sum quit " << res);
    return res;
}

//entry
void sol() {
    int n; cin >> n;
    char op;
    // for(int x = 0; x < n; ++x) {
    //     for(int y = 0; y < n; ++y) {
    //         for(int z = 0; z < n; ++z) {
    //           tree_add(x, y, z, 0, tree, 0, n, 0, n, 0, n);
    //         }
    //     }
    // }
    while(true) {
        cin >> op;
        if(op == '1') {
            int x, y, z, k;
            cin >> x >> y >> z >> k;
            tree_add(x, y, z, k, tree, 0, n-1, 0, n-1, 0, n-1);
        } else if(op == '2') {
            int lx, ly, lz, rx, ry, rz;
            cin >> lx >> ly >> lz >> rx >> ry >> rz;
            cout << tree_sum(lx, rx, ly, ry, lz, rz, tree, 0, n-1, 0, n-1, 0, n-1) << endl;
        } else {
            break;
        }
    }
    // tree_print(tree,  0, n, 0, n, 0, n);
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
