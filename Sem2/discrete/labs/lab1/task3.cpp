
// Generated at 2020-05-11 20:01:47.607937 
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
#define FILENAME "problem3"


const int MOD = 1e+9 + 7;

struct DFA
{


    DFA(int n)
    {
        to.resize(n + 1);
        from.resize(n + 1);
        size = n + 1;
    }

    void accept(int n)
    {
        acc.insert(n);
    }

    void add(int f, char c, int t)
    {
        to[f][c] = t;
        from[t][c].push_back(f);
    }

    void expand_to_acc(vector<bool> & to_acc, int v) {
        to_acc[v] = true;
        for(auto p : from[v]) {
            for(int u : p.second) {
                if(!to_acc[u])
                    expand_to_acc(to_acc, u);
            }
        }
    }

    bool check_loop(vector<int> & color,
                    vector<bool> & to_acc,
                    vector<int> & sorted,
                    int v)
    {
        color[v] = 1;
        for(auto u : to[v]) {
            if(to_acc[u.second]) {
                if(color[u.second] == 0 &&
                   check_loop(color, to_acc, sorted, u.second))
                    return true;
                if(color[u.second] == 1)
                    return true;
            }
        }
        color[v] = 2;
        sorted.push_back(v);
        return false;
    }

    int count()
    {
        DBG("AYAYAY");
        vector<bool> to_acc(size, false);
        for(int i = 1; i < size; ++i) {
            if(acc.find(i) != acc.end())
                to_acc[i] = true;
        }
        for(int i = 1; i < size; ++i) {
            if(to_acc[i])
                expand_to_acc(to_acc, i);
        }

        vector<int> color(size, 0);
        vector<int> sorted;
        if(check_loop(color, to_acc, sorted, 1)) {
            return -1;
        }
        vector<int> cnt(size, 0);
        cnt[1] = 1;
        reverse(sorted.begin(), sorted.end());
        for(int v : sorted) {
            for(auto p : from[v]) {
                for(int u : p.second) {
                    cnt[v] += cnt[u];
                    cnt[v] %= MOD;
                }
            }
        }
        int res = 0;
        for(int i = 1; i < size; ++i) {
            if(acc.find(i) != acc.end()) {
                res += cnt[i];
            }
        }
        return res;
    }

    int count(int l)
    {
        vector<int> cnt(size, 0);
        int res = 0;
        cnt[1] = 1;
        for(int i = 0; i < l; ++i) {
            vector<int> t(size, 0);
            for(int j = 1; j < size; ++j) {
                for(auto p : to[j]) {
                    t[p.second] += cnt[j];
                    t[p.second] %= MOD;
                }
            }
            swap(t, cnt);
        }
        for(int j = 1; j < size; ++j) {
            if(acc.find(j) != acc.end()) {
                res += cnt[j];
                res %= MOD;
            }
        }
        return res;
    }

    bool isomorph(DFA & other) {
        if(other.size != size)
            return false;
        vector<bool> was(size, false);
        vector<int> bi(size, -1);
        return isomorph_imp(other, 1, 1, was, bi);
    }

    bool isomorph_imp(DFA & other, int u, int v, vector<bool>& was, vector<int> & bi) {
        was[u] = true;

        if((acc.find(u) != acc.end()) ^ (other.acc.find(v) != other.acc.end()))
            return false;
        bi[u] = v;
        for(auto p : to[u]) {
            if(other.to[v][p.first] == 0)
                return false;
            if(was[p.second]) {
                if(other.to[v][p.first] != bi[p.second]) {
                    return false;
                }
            } else {
                if(!isomorph_imp(other, p.second, other.to[v][p.first], was, bi)) {
                    return false;
                }
            }
        }
        for(auto p : other.to[v]) {
            if(to[u][p.first] == 0)
                return false;
        }
        return true;
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
        return acc.find(v) != acc.end();
    }

    set<int> acc;
    vector<map<char, int>> to;
    vector<map<char, vector<int>>> from;
    int size;

};


DFA* input() {
    int n, m, k; cin >> n >> m >> k;
    DFA* a = new DFA(n);
    for(int i = 0; i < k; ++i) {
        int t; cin >> t;
        a->accept(t);
    }
    for(int i = 0; i < m; ++i) {
        int f, t;
        char c;
        cin >> f >> t >> c;
        a->add(f, c, t);
    }
    return a;
}

//entry
void sol()
{

    DFA* a = input();
    cout << a->count() << endl;
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
