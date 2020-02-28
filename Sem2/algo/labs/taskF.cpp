
// Generated at 2020-02-27 01:44:59.154913 
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
vector<vint> t;
vint a;
const int INF = 16714589;

std::ostream& operator <<(ostream& o, vint a) {
    for(int c : a) {
        o << c << " ";
    }
    // o << endl;
    return o;
}


void t_print() {
    for(int i = 0; i < t.size(); ++i) {
        DBG(t[i]);
    }
}


int log2(int n) {
    int c = 0;
    while(n > 0) {c++; n >>= 1;}
    return c;
}

void t_build() {
    for(int i = 0; i < t.size(); ++i) {
        for(int j = 0; j < t[i].size(); j += (1 << (t.size() - i))) {
            t[i][j + (1 << (t.size() - i - 1))] = a[j + (1 << (t.size() - i - 1))];
            t[i][j + (1 << (t.size() - i - 1)) - 1] = a[j + (1 << (t.size() - i - 1)) - 1];
            for(int k = j + (1 << (t.size() - i - 1)) + 1; k < j + (1 << (t.size() - i)); ++k) {
                t[i][k] = min(a[k], t[i][k - 1]);
            }
            for(int k = j + (1 << (t.size() - i - 1)) - 2; k >= j; --k) {
                // DBG(i << " " << k);
                t[i][k] = min(a[k], t[i][k + 1]);
            }
        }
    }

}


int t_min(int l, int r) {
    int j = 0;
    for(int i = 0; i < t.size(); ++i) {
        if(r < j*(1 << (t.size() - i)) + (1 << (t.size() - 1 - i)) - 1) {
            j = j*2;
        } else if(l > j*(1 << (t.size() - i)) + (1 << (t.size() - 1 - i))) {
            j = j*2 + 1;
        } else {
            return min(t[i][l],t[i][r]);
        }
    }
    return INF;
}


//entry
void sol() {
    int n, m, a1; cin >> n >> m >> a1;
    int v, u; cin >> u >> v; u--; v--;

    t.resize(log2(n), vint(1 << log2(n), INF));
    a.resize(1 << log2(n), INF); a[0] = a1;
    for(int i = 1; i < n; ++i) a[i] = (23*a[i-1] + 21563) % 16714589;
    t_build();
    // DBG(a);
    t_print();
    int r = t_min(min(u,v), max(u,v));
    DBG(u<< " " << v << " " << r);
    for(int i = 0; i < m - 1; ++i) {
        u = (17*u + 17 + 751 + r + 2*(i+1)) % n;
        v = (13*v + 13 + 593 + r + 5*(i+1)) % n;
        r = t_min(min(u,v), max(u,v));
        DBG(u << " " << v << " " << r);
    }

    cout << u + 1 << " " << v + 1 << " " << r <<  endl;

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
