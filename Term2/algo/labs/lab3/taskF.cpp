
// Generated at 2020-05-20 19:23:35.307402 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>
#include <unordered_set>
#include <ctime>
#include <cstdlib>
#include <queue>


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

//##################CODE BEGIN#############

#define FILE_IO OFF

using vint = vector<int>;
using vint2 = vector<vint>;


const int INF = 1e+6 + 1;

int log2(int n) {
    int res = 0;
    while(n) {n >>= 1; res++;}
    return res;
}

inline int pow2(int n) {
    return (1 << n);
}

int lca(int u, int v, vint2 &jmp, vint &d)
{
    int res = 0;
    if (d[v] > d[u])
        swap(v, u);
    int logn = log2(jmp.size()) - 1;
    for(int i = logn; i >= 0; --i) {
        if(d[jmp[u][i]] >= d[v]) {
            u = jmp[u][i];
            res += pow2(i);
        }
    }
    if (v == u)
        return u;
    for(int i = logn; i >= 0; --i) {
        if(jmp[v][i] != jmp[u][i]) {
            v = jmp[v][i];
            u = jmp[u][i];
            res += pow2(i)*2;
        }
    }
    return jmp[v][0];
}
void build_d(int u, int from, int h, int& t, vint& d, vint2& to, vint& tin)
{
    tin[u] = t++;
    DBG("build_jmp_0 " << u << " from " << from);
    d[u] = h;
    for(int v : to[u]) {
        if(v != from) {
            DBG("\t" << v << " from " << u);
            build_d(v, u, h + 1, t, d, to, tin);
        }
    }
}
//entry
void sol() {

    int n; scanf("%Ld", &n); n++;
    int logn = log2(n);
    vint2 jmp(n, vint(logn, 0));
    vint d(n, 0);
    vint2 to(n, vint{});
    vint tin(n, 0);
    for(int i = 1; i < n; ++i) {
        int t; scanf("%Ld", &t); t = max((int)0, t);
        jmp[i][0] = t;
        to[i].push_back(t);
        to[t].push_back(i);
    }
    int t = 0;
    build_d(0, 0, -1, t, d, to, tin);
    for(int i = 1; i < logn; ++i) {
        for(int j = 1; j < n; ++j) {
            jmp[j][i] = jmp[jmp[j][i - 1]][i - 1];
        }
    }
    int g; scanf("%Ld", &g);
    for(int i = 0; i < g; ++i) {
        int k; scanf("%Ld", &k);
        auto cmp = [&](int lhs, int rhs) {
            return tin[lhs] < tin[rhs];
        };
        vint a(k);
        for(int i = 0; i < k; ++i) {
            scanf("%Ld", &a[i]);
        }
        a.push_back(0); k++;
        sort(a.begin(), a.end(), cmp);
        int res = 0;
        for(int i = 1; i < k; ++i) {
            res += d[a[i - 1]] + d[a[i]] - 2*d[lca(a[i - 1], a[i], jmp, d)];
        }
        res += d[a[0]] + d[a[k - 1]] - 2*d[lca(a[0], a[k - 1], jmp, d)];
        // cout << res/2 << endl;
        printf("%d\n", res/2);
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
    //ios_base::sync_with_stdio(0);
    //cin.tie(0); cout.tie(0);
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
