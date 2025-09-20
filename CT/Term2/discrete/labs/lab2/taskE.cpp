
// Generated at 2020-06-11 18:55:33.287057 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <set>
#include <unordered_set>
#include <cstdio>
#include <map>
#include <cctype>
#include <ctime>
#include <cstdlib>
#include <queue>
#include <cassert>


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
#define FILENAME "cf"


const int MOD = 1e+9 + 7;


struct Grammar
{
    struct State
    {
        bool terminal;
        int n;

        State(int n, bool terminal)
        : terminal(terminal)
        , n(n)
        {}

        friend bool operator==(const State& lhs, const State& rhs) {
            return lhs.n == rhs.n && lhs.terminal == rhs.terminal;
        }
        friend bool operator<(const State& lhs, const State& rhs) {
            if(lhs.terminal == rhs.terminal) {
                return lhs.n < rhs.n;
            } else {
                if(lhs.terminal) {
                    return true;
                } else {
                    return false;
                }
            }
        }

    };

    int start;
    int states_count;
    map<int, vector<vector<State>>> a;

    Grammar delete_useless()
    {
        Grammar g = *this;

        int n = 0;
        for(auto& p : a) {
            n += p.second.size();
        }

        vector<bool> reachable(g.states_count, false);
        reachable[g.start] = true;
        vector<bool> productable(g.states_count, false);
        for(auto& p : g.a) {
            for(auto& v : p.second) {
                bool flag = true;
                for(auto& t : v) {
                    if(!t.terminal) {
                        flag = false;
                    }
                }
                productable[p.first] = productable[p.first] | flag;
            }
        }
        for(int i = 0; i < n; ++i) {
            for(auto& p : g.a) {
                for(auto& v : p.second) {
                    bool flag = true;
                    for(auto& t : v) {
                        if(!t.terminal) {
                            flag &= productable[t.n];
                        }
                    }
                    productable[p.first] = productable[p.first] | flag;
                }
            }
        }
        for(auto& p : g.a) {
            if(!productable[p.first]) {
                p.second.clear();
            } else {
                p.second.erase(
                    remove_if(
                        p.second.begin(),
                        p.second.end(),
                        [&](auto& v) {
                            for(auto& t : v) {
                                if(!t.terminal) {
                                    if(!productable[t.n]) {
                                        return true;
                                    }
                                }
                            }
                            return false;
                        }),
                    p.second.end());
            }
        }
        for(int i = 0; i < n; ++i) {
            for(auto& p : g.a) {
                if(reachable[p.first]) {
                    for(auto& v : p.second) {
                        for(auto& t : v) {
                            if(!t.terminal) {
                                reachable[t.n] = true;
                            }
                        }
                    }
                }
            }
        }
        for(auto it = g.a.begin(); it != g.a.end();) {
            if(!reachable[it->first] || !productable[it->first]) {
                it = g.a.erase(it);
            } else {
                ++it;
            }
        }
        return g;
    }

    Grammar delete_chains()
    {
        Grammar g = *this;

        vector<set<vector<State>>> b(states_count);
        vector<set<vector<State>>> c(states_count);
        int n = 0;
        for(auto& p : a) {
            n += p.second.size();
        }
        for(int i = 0; i < n; ++i) {
            for(auto& p : a) {
                for(auto& v : p.second) {
                    if(v.size() == 2 || (v.size() == 1 && v[0].terminal)) {
                        b[p.first].insert(v);
                        c[p.first].insert(v);
                    }
                    if(v.size() == 1 && !v[0].terminal) {
                        c[p.first].insert(c[v[0].n].begin(), c[v[0].n].end());
                    }
                }
            }
        }
        for(int i = 0; i < c.size(); ++i) {
            for(vector<State> t : c[i]) {
                if(b[i].find(t) == b[i].end()) {
                    g.a[i].push_back(t);
                }
            }
        }
        for(auto& p : g.a) {
            p.second.erase(
                remove_if(
                    p.second.begin(),
                    p.second.end(),
                    [](auto& v) {
                        return (v.size() == 1 && !v[0].terminal);
                    }),
                p.second.end());
        }

        return g;
    }

    Grammar delete_epsilon()
    {
        Grammar g = *this;

        int n = 0;
        for(auto& p : a) {
            n += p.second.size();
        }
        vector<bool> eps(states_count, false);
        vector<set<vector<State>>> b(states_count);
        for(int i = 0; i < n; ++i) {
            for(auto& p : a) {
                for(auto &v : p.second) {
                    bool flag = true;
                    for(State t : v) {
                        if(t.terminal) {
                            flag &= false;
                        } else {
                            flag &= eps[t.n];
                        }
                    }
                    eps[p.first] = eps[p.first] || flag;
                }
            }
        }
        for(auto& p : a) {
            for(auto& v : p.second) {
                if(v.size() == 1) {
                    if(!v[0].terminal) {
                        if(eps[v[0].n]) {
                            b[p.first].insert({});
                        }
                    }
                } else if(v.size() == 2) {
                    if(eps[v[0].n]) {
                        b[p.first].insert({v[1]});
                    }
                    if(eps[v[1].n]) {
                        b[p.first].insert({v[0]});
                    }
                    if(eps[v[0].n] && eps[v[1].n]) {
                        b[p.first].insert({});
                    }
                }
            }
        }
        for(auto& p : g.a) {
            for(auto& v : p.second) {
                b[p.first].erase(v);
            }
        }

        for(int i = 0; i < states_count; ++i) {
            for(auto& v : b[i]) {
                g.a[i].push_back(v);
            }
        }

        for(auto& p : g.a) {
            p.second.erase(
                remove_if(
                    p.second.begin(),
                    p.second.end(),
                    [&](auto& v) {
                        return v.empty();
                    }),
                p.second.end());
        }
        if(eps[g.start]) {
            int s = g.states_count++;
            g.a[s].push_back({State(0, false)});
            g.a[s].push_back({});
            g.start = s;
        }

        return g;
    }

    Grammar replace_terminals()
    {
        Grammar g;
        map<int, bool> was;
        map<int, int> b;
        map<char, int> c;
        was[start] = true;
        b[start] = 0;
        g.start = 0;
        g.states_count = 1;

        for(auto& p : a) {
            if(!was[p.first]) {
                was[p.first] = true;
                b[p.first] = g.states_count++;
            }
            for(auto& v : p.second) {
                if(v.size() == 0 || (v.size() == 1 && v[0].terminal)) {
                    g.a[b[p.first]].push_back(v);
                    continue;
                }
                g.a[b[p.first]].push_back({});
                vector<State>& cur = g.a[b[p.first]].back();
                for(State t : v) {
                    if(t.terminal) {
                        if(c[t.n] == 0) {
                            c[t.n] = g.states_count++;
                            g.a[c[t.n]].push_back({ State(t.n, true) });
                        }
                        cur.push_back(State(c[t.n], false));
                    } else {
                        if(!was[t.n]) {
                            was[t.n] = true;
                            b[t.n] = g.states_count++;
                        }
                        cur.push_back(State(b[t.n], false));
                    }
                }
            }
        }

        return g;
    }


    Grammar delete_long()
    {
        Grammar g;
        map<int, bool> was;
        map<int, int> b;
        was[start] = true;
        b[start] = 0;
        g.start = 0;
        g.states_count = 1;

        for(auto& p : a) {
            if(!was[p.first]) {
                was[p.first] = true;
                b[p.first] = g.states_count++;
            }
            for(auto& v : p.second) {
                if(v.size() > 2) {
                    int prev = g.states_count++;
                    if(!was[v[v.size() - 2].n]) {
                        was[v[v.size() - 2].n] = true;
                        b[v[v.size() - 2].n] = g.states_count++;
                    }
                    if(!was[v[v.size() - 1].n]) {
                        was[v[v.size() - 1].n] = true;
                        b[v[v.size() - 1].n] = g.states_count++;
                    }
                    g.a[prev].push_back({State(b[v[v.size() - 2].n], false),
                                         State(b[v[v.size() - 1].n], false)});
                    for(int i = v.size() - 3; i > 0; --i) {
                        int prev1 = g.states_count++;
                        if(!was[v[i].n]) {
                            was[v[i].n] = true;
                            b[v[i].n] = g.states_count++;
                        }
                        g.a[prev1].push_back({State(b[v[i].n], false), State(prev, false)});
                        prev = prev1;
                    }
                    if(!was[v[0].n]) {
                        was[v[0].n] = true;
                        b[v[0].n] = g.states_count++;
                    }
                    g.a[b[p.first]].push_back({State(b[v[0].n], false), State(prev, false)});

                } else if(v.size() == 2){
                    if(!was[v[0].n]) {
                        was[v[0].n] = true;
                        b[v[0].n] = g.states_count++;
                    }
                    if(!was[v[1].n]) {
                        was[v[1].n] = true;
                        b[v[1].n] = g.states_count++;
                    }
                    g.a[b[p.first]].push_back({State(b[v[0].n], false),
                                               State(b[v[1].n], false)});
                } else if(v.size() == 1) {
                    if(!v[0].terminal) {
                        if(!was[v[0].n]) {
                            was[v[0].n] = true;
                            b[v[0].n] = g.states_count++;
                        }
                        g.a[b[p.first]].push_back({State(b[v[0].n], false)});
                    } else {
                       g.a[b[p.first]].push_back(v);
                   }
                } else {
                    g.a[b[p.first]].push_back({});
                }
            }
        }

        return g;
    }

    bool accept(string s)
    {
        DBG("accept " << s);
        int m = 0;
        bool epsilonStart = false;
        for(auto& p : a) {
            m = max(p.first, m);
            for(auto& v : p.second) {
                assert(v.size() <= 2);
                if(v.size() == 0) {
                    epsilonStart = true;
                    assert(p.first == start);
                } if(v.size() == 1) {
                    assert(v[0].terminal);
                } else if(v.size() == 2) {
                    assert(!v[0].terminal);
                    assert(!v[1].terminal);
                    m = max(m, max(v[0].n, v[1].n));
                }
            }
        }
        if(epsilonStart) {
            for(auto& p : a) {
                for(auto&v : p.second) {
                    if(v.size() == 2) {
                        assert(v[0].n != start);
                        assert(v[1].n != start);
                    }
                }
            }
        }
        vector<vector<vector<bool>>> dp (m + 1 , vector<vector<bool>>(s.length() + 1, vector<bool>(s.length() + 1, false)));
        for(auto& p : a) {
            for(auto& v : p.second) {
                if(v.size() == 2 || v.size() == 0) continue;
                for(int i = 0; i < s.length(); ++i) {
                    dp[p.first][i][i] = dp[p.first][i][i] | (s[i] == v[0].n);
                }
            }
        }
        for(int i = 0; i < s.length(); ++i) {
            for(auto& p : a) {
                for(int j = 0; j + i < s.length(); ++j) {
                    for(auto& v : p.second) {
                        if(v.size() <= 1) continue;
                        for(int k = j; k < j + i; ++k) {
                            dp[p.first][j][j + i] = dp[p.first][j][j + i]
                                | dp[v[0].n][j][k]*dp[v[1].n][k + 1][j + i];
                        }
                    }
                }
            }
        }
        return dp[start][0][s.length() - 1];
    }


    friend istream& operator>>(istream& in, Grammar& g)
    {
        int n;
        char start;
        vector<bool> was(30, false);
        map<char, int> b;
        in >> n >> start;
        was[start - 'A'] = true;
        g.start = 0;
        b[start] = 0;
        g.states_count = 1;
        in.get();
        for(int i = 0; i < n; ++i) {
            char f = in.get();
            if(!was[f - 'A']) {
                was[f - 'A'] = true;
                b[f] = g.states_count++;
            }
            f = b[f];
            in.get(); //' '
            in.get(); //'-'
            in.get(); //'>'
            char c = in.get(); //' '
            g.a[f].push_back({});
            vector<State>& cur = g.a[f].back();
            if(c == '\n') continue;
            for(c = in.get(); c != '\n' && c != -1; c = in.get()) {
                if(isupper(c)) {
                    if(!was[c - 'A']) {
                        was[c - 'A'] = true;
                        b[c] = g.states_count++;
                    }
                    cur.emplace_back(b[c], false);
                } else if(islower(c)) {
                    cur.emplace_back(c, true);
                }
            }
        }

        return in;
    }

    friend ostream& operator<<(ostream& out, Grammar& g)
    {
        int n = 0;
        for(auto& p : g.a) {
            n += p.second.size();
        }
        out << n << " " << static_cast<char>(g.start + 'A') << endl;
        for(auto& p : g.a) {
            for(auto& v : p.second) {
                out << static_cast<char>(p.first + 'A') << " -> ";
                for(State t : v) {
                    if(t.terminal) {
                        out << static_cast<char>(t.n);
                    } else {
                        out << static_cast<char>(t.n + 'A');
                    }
                    out << " ";
                }
                if(v.size() == 0) out << "eps ";
                out << endl;
            }
        }
        return out;
    }
};


//entry
void sol() {
    Grammar g; cin >> g;
    DBG("Initial" << endl << g);
    g = g.delete_useless();
    DBG("Delete useless rules" << endl << g);
    g = g.replace_terminals();
    DBG("Replaced terminals" << endl << g);
    g = g.delete_long();
    DBG("Delete long rules" << endl << g);
    g = g.delete_epsilon();
    DBG("Delete epsilone rules" << endl << g);
    g = g.delete_chains();
    DBG("Delete chain rules" << endl << g);
    g = g.delete_useless();
    DBG("Delete useless rules" << endl << g);
    string s; cin >> s;
    if(g.accept(s)) {
        cout << "yes" << endl;
    } else {
        cout << "no" << endl;
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
