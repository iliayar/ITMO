
// Generated at 2020-05-12 22:17:38.104577 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <set>
#include <unordered_set>
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
#define FILENAME "fastminimization"

const int MOD = 1e9 + 7;

struct DFA
{
    DFA(int n)
    {
        acc.resize(n + 1, false);
        to.resize(n + 1);
        from.resize(n + 1);
        size = n + 1;
    }

    void accept(int n)
    {
        acc[n] = true;
    }

    void add(int f, char c, int t)
    {
        // if(to[f][c] != 0) {
        //     to[f][c] = t;
        //     return;
        // }
        to[f][c] = t;
    }


    DFA* delete_unreachable() {
        unordered_set<int> reachable;
        queue<int> q;
        q.push(1);
        reachable.insert(1);
        while(!q.empty()) {
            int u = q.front();
            q.pop();
            for(char c = 'a'; c <= 'z'; ++c) {
                if(to[u][c] != 0) {
                    if(!reachable.count(to[u][c])) {
                        reachable.insert(to[u][c]);
                        q.push(to[u][c]);
                    }
                }
            }
        }
        int skipped = 0;
        DFA* res = new DFA(reachable.size());
        vector<int> assoc(size, 0);
        for(int i = 1; i < size; ++i) {
            if(!reachable.count(i)) {
                skipped++;
                continue;
            }
            assoc[i] = i - skipped;
        }
        for(int i = 1; i < size; ++i) {
            if(assoc[i] == 0) continue;
            if(acc[i]) res->accept(assoc[i]);
            for(char c = 'a'; c <= 'z'; ++c) {
                if(assoc[to[i][c]] == 0) continue;
                res->add(assoc[i], c, assoc[to[i][c]]);
            }
        }
        return res;
    }

    void expand() {
        if(expanded) return;
        expanded = true;
        for(int i = 0; i < size; ++i) {
            for(char c = 'a'; c <= 'z'; ++c) {
                from[to[i][c]][c].push_back(i);
            }
        }
    }

    int count(int l) {
        vector<int> cnt(acc.size(), 0);
        int res = 0;
        cnt[1] = 1;
        for(int i = 0; i < l; ++i) {
            vector<int> t(acc.size(), 0);
            for(int j = 1; j < acc.size(); ++j) {
                for(auto p : to[j]) {
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


    bool equal(DFA & other)
    {
        queue<pair<int, int>> q;
        vector<vector<bool>> was(size, vector<bool>(other.size, false));
        q.push({1, 1});
        while(!q.empty()) {
            auto [u , v] = q.front();
            q.pop();
            if(acc[u] ^ other.acc[v])
                return false;
            was[u][v] = true;
            for(char i = 'a'; i <= 'z'; ++i) {
                if((to[u][i] == 0) || (other.to[v][i] == 0))
                    continue;
                if(!was[to[u][i]][other.to[v][i]])
                    q.push({to[u][i], other.to[v][i]});
            }
        }
        return true;
    }

    vector<unordered_set<int>> split_equals()
    {
        expand();
        vector<unordered_set<int>> P(2);
        vector<int> cs(size);
        for(int i = 0; i < size; ++i) {
            if(acc[i]) {
                P[0].insert(i);
                cs[i] = 0;
            } else {
                P[1].insert(i);
                cs[i] = 1;
            }
        }
        queue<pair<unordered_set<int>, char>> q;
        for(char i = 'a'; i <= 'z'; ++i) {
            q.push({P[0], i});
            q.push({P[1], i});
        }
        while(!q.empty()) {
            auto [C , a] = q.front();
            q.pop();
            map<int, vector<int>> inv;
            for(auto u : C) {
                for(auto v : from[u][a]) {
                    int i = cs[v];
                    inv[i].push_back(v);
                }
            }
            for(auto p : inv) {
                if(p.second.size() < P[p.first].size()) {
                    P.push_back({});
                    int j = P.size() - 1;
                    for(auto r : p.second) {
                        P[p.first].erase(r);
                        P[j].insert(r);
                    }
                    if(P[j].size() > P[p.first].size()) {
                        swap(P[j], P[p.first]);
                    }
                    for(auto r : P[j]) {
                        cs[r] = j;
                    }
                    for(char c = 'a'; c <= 'z'; ++c) {
                        q.push({P[j], c});
                    }
                }
            }
        }

        for(int i = 0; i < P.size(); ++i) {
            if(P[i].count(0)) {
                swap(P[0], P[i]);
            }
            if(P[i].count(1)) {
                swap(P[1], P[i]);
            }
        }

        return P;
    }


    DFA * minimize() {
        auto classes = split_equals();
        // vector<int> prime(classes.size());
        // prime[0] = 0;
        // prime[1] = 1;
        // for(int i = 2; i < prime.size(); ++i) {
        //     prime[i] = *classes[i].begin();
        // }
        vector<int> assoc(size);
        for(int i = 0; i < classes.size(); ++i) {
            for(int v : classes[i]) {
                assoc[v] = i;
            }
        }
        DFA* res = new DFA(classes.size() - 1);
        for(int i = 0; i < classes.size(); ++i) {
            for(int v : classes[i]) {
                if(acc[v])
                    res->accept(i);
                for(char c = 'a'; c <= 'z'; ++c) {
                    for(int u : from[v][c]) {
                        res->add(assoc[u] , c, i);
                    }
                }
            }
        }
        return res;
    }


    void print(ostream & out) {
        int edge_n = 0,
            acc_n = 0;
        for(bool a : acc) {
            if(a) acc_n++;
        }
        for(int i = 1; i < size; ++i) {
            for(char c = 'a'; c <= 'z'; ++c) {
                if(to[i][c] != 0)
                    edge_n++;
            }
        }
        if(edge_n == 0) {
            out << "0 0 0" << endl;
            return;
        }
        out << size - 1 << " " << edge_n << " " << acc_n << endl;
        for(int i = 0; i < size; ++i) {
            if(acc[i]) out << i << " ";
        }
        out << endl;
        for(int i = 1; i < size; ++i) {
            for(char c = 'a'; c <= 'z'; ++c) {
                if(to[i][c] != 0)
                    out << i << " " << to[i][c] << " " << c << endl;
            }
        }

    }

    vector<bool> acc;
    vector<map<char, int>> to;
    vector<map<char, vector<int>>> from;
    size_t size;
    bool expanded = false;
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
    return a->delete_unreachable();
}

//entry
void sol()
{
    DFA* a = input();


    DBG_CODE(
        auto classes = a->split_equals();
        for(int i = 0; i < classes.size(); ++i) {
            cout << "class " << i << endl;
            cout << "\t";
            for(int c : classes[i]) {
                cout << c << " ";
            }
            cout << endl;
        }

    );

    a->minimize()->print(cout); // FIXME
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
