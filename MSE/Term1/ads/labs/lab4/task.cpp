
// Generated at 2025-06-13 17:40:06.337309 
// By iliayar
#define _USE_MATH_DEFINES
#pragma comment(linker, "/STACK:36777216")
#include <iterator>
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <map>
#include <unordered_set>
#include <ctime>
#include <cstdlib>
#include <queue>
#include <set>
#include <deque>
#include <list>
#include <sstream>
#include <numeric>
#include <optional>
#include <variant>
#include <functional>

using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG_VAR true
#define DBG_CODE(x) x
#else
#define DBG_VAR false
#define DBG_CODE(x)
#endif

#define DBG() if (DBG_VAR) cout << "DBG: "

#define INF 1e+18
#define ALL(a) a.begin(), a.end()

using vint = vector<int>;
using vint2 = vector<vint>;

template <typename K, typename V>
struct map_pair {
    K k;
    V v;
};

template <typename T, typename K>
ostream &operator<<(ostream &out, pair<T, K> const& p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

template<typename T>
class Join {
  T& v;
  string const& separator;
  
public:
  
  Join(T v, string const& separator)
    : v(v), separator(separator)
  {}

  friend ostream& operator<<(ostream& out, Join<T> join) {
    for(auto it = join.v.cbegin(); it != join.v.cend(); ++it) {
      if(it != join.v.cbegin()) out << join.separator;
      out << *it;
    }
    return out;
  }
};

template <typename T>
ostream &operator<<(ostream &out, vector<T> v) {
  out << "[" << Join(v, ", ") << "]";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, map<K, V> m) {
  vector<map_pair<K, V>> v;
  transform(m.begin(), m.end(), back_inserter(v), [](pair<K, V> const& p){return map_pair<K, V>{p.first, p.second};});
  out << "{" << Join(v, ", ") << "}";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, map_pair<K, V> m) {
  out << m.k << ": " << m.v;
  return out;
}

template <typename K>
ostream &operator<<(ostream &out, set<K> s) {
  out << "{" << Join(s, ", ") << "}";
  return out;
}

//##################CODE BEGIN#############
void abort(std::string_view msg, int code = 0) {
    cout << "Aborted: " << msg << endl;
    exit(code);
}

template <typename T, typename Comparator = std::less<T>>
class heap {
public:
    using Id = size_t;

    heap(Comparator cmp = Comparator{}) 
        : data()
        , cmp(std::move(cmp)) {}


    heap(std::vector<T>&& data, Comparator cmp = Comparator{})
        : data()
        , cmp(std::move(cmp)) {
        for (auto& v : data) {
            push_impl(std::move(v));
        }
        for (size_t i = 0; i < this->data.size(); ++i) {
            prop_up(i);
        }
    }

    Id push(T x) {
        auto id = push_impl(std::move(x));
        prop_up(data.size() - 1);
        return id;
    }
    
    T pop() {
        if (data.empty()) abort("heap.pop");
        swap_impl(0, data.size() - 1);
        T r = pop_impl();
        prop_down(0);
        return r;
    }
    
    T& peek() {
        if (data.empty()) abort("heap.peek");
        return data.front().data;
    }

    bool empty() {
        return data.empty();
    }

    bool has(Id id) {
        if (id >= rev.size()) abort("heap.has");
        return (bool)rev[id];
    }

    T& get(Id id) {
        if (id >= rev.size() || !rev[id]) abort("heap.get");
        return data[*rev[id]].data;
    }

    T remove(Id id) {
        if (id >= rev.size() || !rev[id]) abort("heap.remove");
        auto i = *rev[id];
        swap_impl(i, data.size() - 1);
        T res = pop_impl();
        prop_down(prop_up(i));
        return res;
    }
private:
    struct Item {
        size_t index;
        T data;
    };

    Id push_impl(T&& v) {
        data.emplace_back(Item{rev.size(), std::move(v)});
        rev.emplace_back(data.size() - 1);
        return rev.size() - 1;
    }

    T pop_impl() {
        Item it = std::move(data.back());
        data.pop_back();
        rev[it.index] = std::nullopt;
        return std::move(it.data);
    }

    bool cmp_impl(size_t i, size_t j) {
        return cmp(data[i].data, data[j].data);
    }

    void swap_impl(size_t i, size_t j) {
        if (i == j) return;
        std::swap(data[i], data[j]);
        rev[data[i].index] = i;
        rev[data[j].index] = j;
    }

    size_t prop_up(size_t i) {
        while (i > 0) {
            if (cmp_impl(i, (i - 1) / 2)) {
                swap_impl(i, (i - 1) / 2);
                i = (i - 1) / 2;
            } else {
                break;
            }
        }
        return i;
    }
    
    void prop_down(size_t i) {
        while (true) {
            bool f = false;
            size_t ni = 0;
            if (i*2 + 1 < data.size() && cmp_impl(i*2 + 1, i)) {
                ni = i*2 + 1;
                f = true;
            }
            if (i*2 + 2 < data.size() && 
                cmp_impl(i*2 + 2, i) && 
                cmp_impl(i*2 + 2, i*2 + 1)) {
                ni = i*2 + 2;
                f = true;
            }
            if (!f) {
                break;
            }
            swap_impl(i, ni);
            i = ni;
        }
    }

private:
    vector<Item> data;
    Comparator cmp;

    vector<optional<size_t>> rev;
};

template <typename T>
class llist {
public:
    struct Node {
        T data;
        Node* prev;
        Node* next;
    };

    llist() : begin(nullptr) {}

    Node* insert(Node* prev, T data) {
        Node* node = new Node{std::move(data), prev, nullptr};
        if (prev) {
            if (prev->next) {
                prev->next->prev = node;
            }
            node->next = prev->next;
            prev->next = node;
        } else {
            node->next = begin;
            if (begin) {
                begin->prev = node;
            }
            begin = node;
        }
        return node;
    }

    void remove(Node* node) {
        if (!node) abort("llist.remove");
        if (!node->prev) {
            if (node != begin) abort("llist.remove");
            begin = begin->next;
        }
        if (node->prev) {
            node->prev->next = node->next;
        }
        if (node->next) {
            node->next->prev = node->prev;
        }
        delete node;
    }

    vector<T> to_vector() {
        Node* node = begin;
        vector<T> res;
        while (node) {
            res.push_back(node->data);
            node = node->next;
        }
        return res;
    }

private:
    Node* begin;
};

struct litem;
struct hitem {
    int begin;
    int size;
    llist<litem>::Node* node;
};

bool operator<(const hitem& lhs, const hitem& rhs) {
    return lhs.size > rhs.size;
}

ostream& operator<<(ostream& out, const hitem& i) {
    out << "hitem { begin = " << i.begin << ", size = " << i.size << "}";
    return out;
}

struct litem {
    int begin;
    int size;
    optional<heap<hitem>::Id> hid;
};

ostream& operator<<(ostream& out, const litem& i) {
    out << "litem { begin = " << i.begin << ", size = " << i.size << ", hid = ";
    if (i.hid) {
        out << *i.hid;
    } else {
        out << "none";
    }
    out << " }";
    return out;
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    heap<hitem> h;
    llist<litem> l;

    auto init_id = h.push(hitem{0, n, nullptr});
    auto init_node = l.insert(nullptr, litem{0, n, init_id});
    h.get(init_id).node = init_node;

    vector<llist<litem>::Node*> qs(m);
    for (int q = 0; q < m; ++q) {
        int a; cin >> a;
        DBG() << l.to_vector() << endl;
        DBG() << h.peek() << endl;

        if (a > 0) {
            if (h.peek().size >= a) {
                auto t = h.pop();
                auto hi = h.push(hitem{t.begin + a, t.size - a, nullptr});
                auto na = l.insert(t.node->prev, litem{t.begin, a, nullopt});
                // DBG() << "Alloc 1: " << l.to_vector() << endl;
                auto nf = l.insert(na, litem{t.begin + a, t.size - a, hi});
                // DBG() << "Alloc 2: " << l.to_vector() << endl;
                h.get(hi).node = nf;
                l.remove(t.node);
                // DBG() << "Alloc 3: " << l.to_vector() << endl;
                cout << t.begin + 1 << endl;
                qs[q] = na;
            } else {
                cout << -1 << endl;
                qs[q] = nullptr;
            }
        } else {
            qs[q] = nullptr;
            if (!qs[-a - 1]) {
                continue;
            }
            auto na = qs[-a - 1];
            auto prev = na->prev;
            int begin = na->data.begin;
            int size = na->data.size;
            DBG() << begin << " " << size << endl;
            if (na->prev && na->prev->data.hid) {
                DBG() << "Prev" << endl;
                auto t = h.remove(*na->prev->data.hid);
                begin = t.begin;
                size += t.size;
                prev = na->prev->prev;
                l.remove(na->prev);
            }
            if (na->next && na->next->data.hid) {
                DBG() << "Next" << endl;
                auto t = h.remove(*na->next->data.hid);
                size += t.size;
                l.remove(na->next);
            }
            l.remove(na);
            DBG() << "Freed " << begin << " " << size << endl;
            auto hi = h.push(hitem{begin, size, nullptr});
            auto nf = l.insert(prev, litem{begin, size, hi});
            h.get(hi).node = nf;
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
