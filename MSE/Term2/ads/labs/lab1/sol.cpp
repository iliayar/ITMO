#include "template.cpp"

struct R {
    vector<int> right;
    int diff;
};

struct llong;
ostream& operator<<(ostream& out, llong const& n);

struct llong {
    constexpr static long long SIZE = 128;
    constexpr static long long BYTE = 1 << 16;
    long long d[SIZE];
    bool neg;

    llong(int n) {
        // DBG() << "llong(" << n << ")" << endl;
        neg = false;
        if (n < 0) {
            neg = true;
            n = -n;
        }
        for (int i = 0; i < SIZE; ++i) {
            d[i] = 0;
        }
        int i = 0;
        while (n > 0) {
            d[i++] = n % BYTE; 
            n /= BYTE;
        }
    }

    llong add_mod(llong const& other) const {
        // DBG() << "add_mod" << endl;
        llong res = *this;
        res.neg = false;
        for (int i = 0; i < SIZE; ++i) {
            res.d[i] += other.d[i];
            while (res.d[i] >= BYTE) {
                if (i + 1 >= SIZE) {
                    DBG() << "Overflow while adding " << *this << " + " << other << endl;
                    exit(67);
                }
                res.d[i] -= BYTE;
                res.d[i + 1] += 1;
            }
        }
        return res;
    }

    llong sub_mod(llong const& other) const {
        // DBG() << "sub_mod" << endl;
        if (other.gt_mod(*this)) {
            auto res = other.sub_mod(*this);
            res.neg = !res.neg;
            return res;
        }
        llong res = *this;
        res.neg = false;
        for (int i = 0; i < SIZE; ++i) {
            res.d[i] -= other.d[i];
            while (res.d[i] < 0) {
                if (i + 1 >= SIZE) exit(67);
                res.d[i] += BYTE;
                res.d[i + 1] -= 1;
            }

        }
        return res;
    }

    bool gt_mod(llong const& other) const {
        for (int i = SIZE - 1; i >= 0; --i) {
            if (d[i] > other.d[i]) {
                return true;
            } else if (d[i] < other.d[i]) {
                return false;
            }
        }
        return false;
    }

    llong operator+(llong const& other) const {
        // DBG() << "operator+" << endl;
        if (neg && other.neg) {
            auto res = add_mod(other);
            res.neg = true;
            return res;
        } else if (neg && !other.neg) {
            return other.sub_mod(*this);
        } else if (!neg && other.neg) {
            return sub_mod(other);
        } else {
            return add_mod(other);
        }
    }

    llong& operator+=(llong const& other) {
        *this = *this + other;
        return *this;
    }

    llong operator-(llong const& other) const {
        if (neg && other.neg) {
            return other.sub_mod(*this);
        } else if (neg && !other.neg) {
            auto res = add_mod(other);
            res.neg = true;
            return res;
        } else if (!neg && other.neg) {
            return add_mod(other);
        } else {
            return sub_mod(other);
        }
    }

    llong operator-() const {
        llong res = *this;
        res.neg = !res.neg;
        return res;
    }

    bool operator<(llong const& other) const {
        if (neg && other.neg) {
            return gt_mod(other);
        } else if (neg && !other.neg) {
            return true;
        } else if (!neg && other.neg) {
            return false;
        } else {
            return other.gt_mod(*this);
        }
    }

    bool operator==(llong const& other) const {
        bool is_zero = true;
        for (int i = 0; i < SIZE; ++i) {
            if (d[i] != other.d[i]) {
                return false;
            }
            if (d[i] != 0) {
                is_zero = false;
            }
        }

        if (is_zero) return true;
        if (other.neg == neg) return true;
        return false;
    }

    static llong inf() {
        llong res(0);
        for (int i = 0; i < SIZE; ++i) {
            res.d[i] = BYTE - 1;
        }
        return res;
    }
};

ostream& operator<<(ostream& out, llong const& n) {
    if (n.neg) cout << "-";
    for (int i = llong::SIZE - 1; i >= 0; --i) {
        out << n.d[i];
        if (i != 0) {
            cout << ":";
        }
    }
    return out;
}

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
    // DBG() << reachable << endl;

    auto neginf = -llong::inf();
    vector<llong> d(n, neginf);
    for (int i = 0; i < n; ++i) {
        for (auto& r : g[i]) {
            if (r.right.empty()) {
                if (d[i] < llong(r.diff)) {
                    d[i] = r.diff;
                }
            }
        }
    }
    // DBG() << d << endl;
    for (int i = 0; i < n; ++i) {
        for (int l = 0; l < n; ++l) {
            if (!finite[l]) continue;
            for (auto& r : g[l]) {
                bool f = false;
                llong dc = r.diff;
                for (auto& nt : r.right) {
                    if (!finite[nt] || d[nt] == neginf) {
                        f = true;
                        break;
                    }
                    dc += d[nt];
                }
                if (f) continue;
                if (d[l] < dc) {
                    d[l] = dc;
                }
            }
        }
        // DBG() << d << endl;
    }

    for (int l = 0; l < n; ++l) {
        if (!finite[l] || !reachable[l]) continue;
        for (auto& r : g[l]) {
            bool f = false;
            llong dc = r.diff;
            for (auto& nt : r.right) {
                if (!finite[nt] || d[nt] == neginf) {
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
    // DBG() << d << endl;

    if (llong(0) < d[0]) {
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
