
// Generated at 2020-03-06 17:03:12.266530 
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

int a[128][128][128];

int n;


int f(int x) { return x & (x + 1); }
int g(int x) { return x | (x + 1); }

int sum(int x, int y, int z) {
    int s = 0;
    for (int i = x; i >= 0; i = f(i) - 1) {
        for (int j = y; j >= 0; j = f(j) - 1) {
            for (int k = z; k >= 0; k = f(k) - 1) {
                s += a[i][j][k];
            }
        }
    }
    DBG("sum " << s);
    return s;
}

void add(int x, int y, int z, int v) {
    DBG("add");
    for (int i = x; i < n; i = g(i)) {
        for (int j = y; j < n; j = g(j)) {
            for (int k = z; k < n; k = g(k)) {
                a[i][j][k] += v;
            }
        }
    }
}

//entry
void sol() {
    cin >> n;

    char op;
    while(true) {
        cin >> op;
        if(op == '1') {
            int x, y, z, v;
            cin >> x >> y >> z >> v;
            add(x, y, z, v);
        } else if(op == '2') {
            int lx, ly, lz, rx, ry, rz;
            cin >> lx >> ly >> lz >> rx >> ry >> rz;
            int s = sum(rx, ry, rz) -
                sum(lx - 1, ry, rz) -
                sum(rx, ly - 1, rz) -
                sum(rx, ry, lz - 1) +
                sum(lx - 1, ly - 1, rz) +
                sum(lx - 1, ry, lz - 1) +
                sum(rx, ly - 1, lz - 1) -
                sum(lx - 1, ly - 1, lz - 1);
            cout << s << endl;
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
