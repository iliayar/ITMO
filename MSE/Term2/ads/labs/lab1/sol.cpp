#include "template.cpp"

struct R {
    vector<int> right;
    int diff;
};

void sol_case(int n, int m) {
    vector<vector<R>> g(n, vector<R>());
    for (int i = 0; i < m; ++i) {
        int left, k; cin >> left >> k; left--;
        g[left].emplace_back(vector<int>{}, 0);
        for (int j = 0; j < k; ++j) {
            string s; cin >> s;
            if (isalpha(s[0])) {
                if (s[0] == 'a') {
                    g[left].back().diff++;
                } else {
                    g[left].back().diff--;
                }
            } else {
                g[left].back().right.push_back(stoull(s) - 1);
            }
        }
    }

    vector<bool> finite(n, false);
    bool run = true;
    while (run) {
        run = false;
        for (int i = 0; i < n; ++i) {
            if (finite[i]) continue;
            for (auto& r : g[i]) {
                bool has_nonfinite = false;
                for (auto& nt : r.right) {
                    if (!finite[nt]) {
                        has_nonfinite = true;
                        break;
                    }
                }
                if (!has_nonfinite) {
                    finite[i] = true;
                    run = true;
                    break;
                }
            }
        }
    }

    if (!finite[0]) {
        cout << "NO" << endl;
        return;
    }

    vector<bool> was(n, false);
    vector<bool> reachable(n, false);
    reachable[0] = true;
    was[0] = true;
    queue<int> q;
    q.push(0);
    while (!q.empty()) {
        int l = q.front(); q.pop();
        for (auto& r : g[l]) {
            bool has_nonfinite = false;
            for (auto nt : r.right) {
                if (!finite[nt]) {
                    has_nonfinite = true;
                    break;
                }
            }
            if (has_nonfinite) continue;
            for (auto nt : r.right) {
                if (!was[nt]) {
                    q.push(nt);
                    was[nt] = true;
                    reachable[nt] = true;
                }
            }
        }
    }
    DBG() << reachable << endl;

    vector<double> d(n, -numeric_limits<double>::infinity());
    for (int i = 0; i < n; ++i) {
        for (auto& r : g[i]) {
            if (r.right.empty()) {
                if (r.diff > d[i]) {
                    d[i] = r.diff;
                }
            }
        }
    }
    double ns = 1.;
    double nn = ns;
    for (int i = 0; i < n; ++i, nn *= ns) {
        vector<double> dt(n, -numeric_limits<double>::infinity());
        for (int l = 0; l < n; ++l) {
            if (!finite[l]) continue;
            dt[l] = max(dt[l], d[l] / ns);
            for (auto& r : g[l]) {
                bool f = false;
                double dc = r.diff / nn;
                for (auto& nt : r.right) {
                    if (!finite[nt]) {
                        f = true;
                        break;
                    }
                    dc += d[nt] / ns;
                }
                if (f) continue;
                if (dt[l] < dc) {
                    dt[l] = dc;
                }
            }
        }
        swap(dt, d);
    }
    nn /= ns;

    for (int l = 0; l < n; ++l) {
        if (!finite[l] || !reachable[l]) continue;
        for (auto& r : g[l]) {
            bool f = false;
            double dc = r.diff / nn;
            for (auto& nt : r.right) {
                if (!finite[nt]) {
                    f = true;
                    break;
                }
                dc += d[nt];
            }
            if (f) continue;
            if (d[l] < dc) {
                cout << "YES" << endl;
                return;
            }
        }
    }
    DBG() << d << endl;

    if (d[0] > 0) {
        cout << "YES" << endl;
    } else {
        cout << "NO" << endl;
    }
}

//entry
void sol() {
    while (true) {
        int n, m; cin >> n >> m;
        if (n == 0 && m == 0) break;
        sol_case(n, m);
    }
}
