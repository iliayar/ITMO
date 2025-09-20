
// Generated at 2025-06-05 01:01:27.280118 
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

template <typename F> std::pair<int, int> bs(int l, int r, F pred) {
  while (r - l > 1) {
    int m = (l + r) / 2;
    if (pred(m)) {
      l = m;
    } else {
      r = m;
    }
  }

  if (!pred(l)) {
    l--;
    r--;
  }

  return {l, r};
}

//##################CODE BEGIN#############
constexpr int N = 30002;
constexpr int T = 10 * 60;

void heap_prop_up(vint& heap, int& hs) {
    int i = hs - 1;
    while (i > 0) {
        if (heap[i] < heap[(i - 1) / 2]) {
            swap(heap[i], heap[(i - 1) / 2]);
            i = (i - 1) / 2;
        }
        else {
            break;
        }
    }
}

void heap_prop_down(vint& heap, int& hs) {
    int i = 0;
    while (i < hs) {
        int ni = -1;
        if (i*2 + 2 < hs && heap[i] > heap[i*2 + 2]) {
            ni = i*2 + 2;
        }
        if (i*2 + 1 < hs && heap[i] > heap[i*2 + 1] && heap[i*2 + 2] > heap[i*2 + 1]) {
            ni = i*2 + 1;
        }
        if (ni == -1) {
            break;
        }
        swap(heap[i], heap[ni]);
        i = ni;
    }
}

void heap_push(vint& heap, int& hs, int x) {
    heap[hs++] = x;
    heap_prop_up(heap, hs);
}

int heap_pop(vint& heap, int& hs) {
    int r = heap[0];
    swap(heap[0], heap[--hs]);
    heap_prop_down(heap, hs);
    return r;
}

// entry
void sol() {
    string line;
    vint exp(N, 0);
    queue<pair<int, int>> q;

    vint heap(N, 0);
    int hs = 0;

    for (int i = 0; i < N; ++i) {
        heap_push(heap, hs, i);
    }

    while (getline(cin, line)) {
        stringstream ss(line);
        int time; ss >> time;
        char command; ss >> command;
        int block = 0; if (command == '.') ss >> block; block--;

        while (!q.empty() && q.front().first <= time) {
            auto i = q.front().second; q.pop();
            if (exp[i] <= time) {
                heap_push(heap, hs, i);
            }
        }

        if (command == '+') {
            int i = heap_pop(heap, hs);
            cout << i + 1 << endl;
            exp[i] = time + T;
            q.push({time + T, i});
        } else {
            if (exp[block] > time) {
                cout << "+" << endl;
                exp[block] = time + T;
                q.push({time + T, block});
            } else {
                cout << "-" << endl;
            }
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
