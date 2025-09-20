// Generated at 2020-06-08 22:42:16.885932 
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
#define FILENAME "automaton"
 
 
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
        from.resize(n + 1);
        size = n + 1;
    }
 
    void check_size(int n)
    {
        if(n >= size) {
            acc.resize(n + 1, false);
            to.resize(n + 1);
            from.resize(n + 1);
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
        //     prime[i] = *classes[i].begin();
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
 
struct NFA
{
 
    NFA()
    {
        // acc.resize(1, false);
        // to.resize(1);
    }
    NFA(int n)
    {
        acc.resize(n + 1, false);
        to.resize(n + 1);
    }
 
 
    void resize(int n)
    {
        acc.resize(n + 1, false);
        to.resize(n + 1);
    }
 
    void accept(int n)
    {
        // DBG("accept " << n);
        // if(acc.size() <= n) {
        //     resize(n);
        // }
        // DBG(acc.size());
        acc[n] = true;
    }
 
    void add(int f, char c, int t)
    {
        // DBG("add " << f << " " << c << " " << t);
        // if(to.size() <= max(f, t)) {
        //     resize(max(f, t));
        // }
        // DBG(to.size());
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
        DBG("check " << s);
        vector<bool> a[2];
        a[0].resize(acc.size(), false);
        a[1].resize(acc.size(), false);
        a[0][1] = true;
        for (char c : s) {
            for (int i = 1; i < a[0].size(); ++i) {
                if (a[0][i]) {
                    for (int j : to[i][c]) {
                        DBG(i << " " << c << " " << j);
                        a[1][j] = true;
                    }
                }
                a[0][i] = false;
            }
            swap(a[0], a[1]);
        }
        for (int i = 1; i < a[0].size(); ++i) {
            if (a[0][i] && acc[i])
                return true;
        }
        return false;
    }
 
    vector<bool> acc;
    vector<map<char, vector<int>>> to;
};
 
//entry
void sol() {
 
    map<char, int> a;
 
    int m = 3;
 
    int n;
    char start;
    cin >> n >> start;
    a[start] = 1;
 
 
    NFA* nfa = new NFA(30);
    nfa->accept(2);
    cin.get();
    for(int i = 0; i < n; ++i) {
        char f = cin.get();
        int& fn = a[f];
        if(fn == 0) fn = m++;
        cin.get(); //' '
        cin.get(); //'-'
        cin.get(); //'>'
        cin.get(); //' '
        char c = cin.get();
        char t = cin.get();
        if(t == '\n') {
            nfa->add(fn, c, 2);
        } else {
           int& tn = a[t];
           if(tn == 0) tn = m++;
           nfa->add(fn, c, tn);
           cin.get(); //"\n"
        }
    }
    int k; cin >> k;
    for(int i = 0; i < k; ++i) {
        string s; cin >> s;
        if(nfa->check(s)) {
            cout << "yes" << endl;
        } else {
            cout << "no" << endl;
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
