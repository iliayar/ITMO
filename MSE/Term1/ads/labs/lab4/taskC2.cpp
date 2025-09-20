
// Generated at 2025-06-10 22:01:44.269960 
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
std::vector<std::pair<int, int>> ss;

template <typename T, typename Comparator = std::less<int>>
class heap {
public:
    heap(Comparator cmp = Comparator{}) 
        : data()
        , cmp(std::move(cmp)) {}


    heap(std::vector<T>&& data, Comparator cmp = Comparator{})
        : data(std::move(data))
        , cmp(std::move(cmp)) {
        for (size_t i = 0; i < this->data.size(); ++i) {
            prop_up(i);
        }
        DBG() << "Heap: " << this->data << endl;
    }

    void push(int x) {
        data.push_back(x);
        push_upd();
    }
    
    int pop() {
        if (data.empty()) exit(1);
        swap(0, data.size() - 1);
        int r = std::move(data.back());
        data.pop_back();
        prop_down(0);
        return r;
    }
    
    int peek() {
        if (data.empty()) exit(1);
        return data.front();
    }

    bool empty() {
        return data.empty();
    }
private:
    void push_upd() {
        prop_up(data.size() - 1);
    }

    size_t prop_up(size_t i) {
        while (i > 0) {
            if (cmp(data[i], data[(i - 1) / 2])) {
                swap(i, (i - 1) / 2);
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
            if (i*2 + 1 < data.size() && cmp(data[i*2 + 1], data[i])) {
                ni = i*2 + 1;
                f = true;
            }
            if (i*2 + 2 < data.size() && 
                cmp(data[i*2 + 2], data[i]) && 
                cmp(data[i*2 + 2], data[i*2 + 1])) {
                ni = i*2 + 2;
                f = true;
            }
            if (!f) {
                break;
            }
            swap(i, ni);
            i = ni;
        }
    }

    void swap(size_t i, size_t j) {
        if (i == j) return;
        std::swap(data[i], data[j]);
        ss.emplace_back(i, j);
    }

private:
    vint data;
    Comparator cmp;
};

//entry
void sol() {
    int n; cin >> n;
    vint a(n);
    for (int i = 0; i < n; ++i) {
        cin >> a[i];
    }

    heap<int> h(std::move(a));

    cout << ss.size() << endl;
    for (int i = 0; i < ss.size(); ++i) {
        cout << ss[i].first + 1 << " " << ss[i].second + 1 << endl;
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
