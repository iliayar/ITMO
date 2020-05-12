
// Generated at 2020-05-12 00:46:57.674872 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <set>
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
#define FILENAME "problem5"

const int MOD = 1e9 + 7;

struct DFA
{
    DFA()
        : DFA(0)
    {}
    DFA(int n)
    {
        acc.resize(n + 1, false);
        to.resize(n + 1);
        size = n + 1;
    }

    void check_size(int n)
    {
        if(n >= size) {
            acc.resize(n + 1, false);
            to.resize(n + 1);
            size = n + 1;
        }
    }

    void accept(int n)
    {
        check_size(n);
        acc[n] = true;
    }

    void add(int f, char c, int t)
    {
        check_size(f);
        check_size(t);
        to[f][c].push_back(t);
    }

    int count(int l) {
        vector<int> cnt(acc.size(), 0);
        int res = 0;
        cnt[1] = 1;
        for(int i = 0; i < l; ++i) {
            vector<int> t(acc.size(), 0);
            for(int j = 1; j < acc.size(); ++j) {
                for(auto a : to[j]) {
                    for(int p : a.second) {
                        t[p] += cnt[j];
                        t[p] %= MOD;
                    }
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
        vector<bool> a[2];
        a[0].resize(acc.size(), false);
        a[1].resize(acc.size(), false);
        a[0][1] = true;
        for(char c : s) {
            for(int i = 1; i < a[0].size(); ++i) {
                if(a[0][i]) {
                    for(int j : to[i][c]) {
                        a[1][j] = true;
                    }
                }
                a[0][i] = false;
            }
            swap(a[0], a[1]);
        }
        for(int i = 1; i < a[0].size(); ++i) {
            if(a[0][i]) return true;
        }
        return false;
    }

    vector<bool> acc;
    vector<map<char, vector<int>>> to;
    size_t size;
};

struct NFA {

    NFA(int n) {
        acc.resize(n + 1, false);
        to.resize(n + 1);
    }

    void accept(int n) { acc[n] = true; }

    void add(int f, char c, int t) {
        // DBG("add " << f << " " << c << " " << t);
        to[f][c].push_back(t);
    }

    DFA* to_dfa()
    {
        map<set<int>, int> vs;
        DFA* res = new DFA();

        queue<set<int>> q;
        set<int> init = {1};
        vs[init] = 1;
        size_t s = 1;
        if(acc[1]) {
            res->accept(1);
        }
        q.push(init);
        while(!q.empty()) {
            set<int> cur = q.front();
            size_t cur_i = vs[cur];
            q.pop();
            for(char i = 'a'; i <= 'z'; ++i) {
                // DBG("for " << i);
                set<int> next;
                bool cur_acc = false;
                for(auto v : cur) {
                    for(int u : to[v][i]) {
                        next.insert(u);
                        cur_acc |= acc[u];
                    }
                }
                if(next.empty()) continue;
                size_t next_i = vs[next];
                if(next_i == 0) {
                    vs[next] = ++s;
                    q.push(next);
                    next_i = s;
                }
                // DBG("add " << cur_i << " " << i << " " << s);
                res->add(cur_i, i, next_i);
                if(cur_acc) res->accept(next_i);
            }
        }
        return res;
    }

    int count(int l) {
        vector<int> cnt(acc.size(), 0);
        int res = 0;
        cnt[1] = 1;
        for (int i = 0; i < l; ++i) {
            vector<int> t(acc.size(), 0);
            for (int j = 1; j < acc.size(); ++j) {
                for (auto a : to[j]) {
                    for (int p : a.second) {
                        t[p] += cnt[j];
                        t[p] %= MOD;
                    }
                }
            }
            swap(t, cnt);
        }
        for (int j = 1; j < acc.size(); ++j) {
            if (acc[j]) {
                res += cnt[j];
                res %= MOD;
            }
        }
        return res;
    }

    bool check(string s) {
        vector<bool> a[2];
        a[0].resize(acc.size(), false);
        a[1].resize(acc.size(), false);
        a[0][1] = true;
        for (char c : s) {
            for (int i = 1; i < a[0].size(); ++i) {
                if (a[0][i]) {
                    for (int j : to[i][c]) {
                        a[1][j] = true;
                    }
                }
                a[0][i] = false;
            }
            swap(a[0], a[1]);
        }
        for (int i = 1; i < a[0].size(); ++i) {
            if (a[0][i])
                return true;
        }
        return false;
    }

    vector<bool> acc;
    vector<map<char, vector<int>>> to;
};

//entry
void sol()
{
    int n, m, k, l; cin >> n >> m >> k >> l;
    NFA a(n);
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
    cout << a.to_dfa()->count(l) << endl;
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
