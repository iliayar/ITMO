
// Generated at 2020-05-08 03:42:19.210779 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>
#include <ctime>
#include <cstdlib>
#include <queue>


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
#define FILE_IO ON
#define FILENAME "problem4"


const int MOD = 1e+9 + 7;

struct DFA
{


    DFA(int n)
    {
        acc.resize(n + 1, false);
        to.resize(n + 1);
    }

    void accept(int n)
    {
        acc[n] = true;
    }

    void add(int f, char c, int t)
    {
        to[f][c] = t;
    }

    int count(int l) {
        vector<int> cnt(acc.size(), 0);
        int res = 0;
        cnt[1] = 1;
        // DBG("AYAYAYA");
        for(int i = 0; i < l; ++i) {
            vector<int> t(acc.size(), 0);
            // DBG("i " << i);
            for(int j = 1; j < acc.size(); ++j) {
                // DBG("j " << j);
                for(auto p : to[j]) {
                    // DBG("to " << p.first << " " << p.second);
                    t[p.second] += cnt[j];
                    t[p.second] %= MOD;
                }
            }
            swap(t, cnt);
        }
        for(int j = 1; j < acc.size(); ++j) {
            if(acc[j]) {
                res += cnt[j];
                res %= MOD;
            }
        }
        return res;
    }

    bool check(string s)
    {
        int v = 1;
        for(char c : s) {
            if(to[v][c] != 0) {
                v = to[v][c];
            } else {
                return false;
            }
        }
        return acc[v];
    }

    vector<bool> acc;
    vector<map<char, int>> to;

};

//entry
void sol()
{
    int n, m, k, l; cin >> n >> m >> k >> l;
    DFA a(n);
    for(int i = 0; i < k; ++i) {
        int t; cin >> t;
        a.accept(t);
    }
    for(int i = 0; i < m; ++i) {
        int f, t;
        char c;
        cin >> f >> t >> c;
        a.add(f, c, t);
    }

    cout << a.count(l) << endl;
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
    cin.tie(0); cout.tie(0);
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
