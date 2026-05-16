
// Generated at 2026-05-15 21:49:07.580152 
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
#include <bitset>
#include <memory>
#include <cassert>

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

#define FUNC(retTy, name, args...) std::function<retTy (args)> name = [&](args) -> retTy

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
ostream &operator<<(ostream &out, unordered_map<K, V> m) {
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

std::function<void()> finish = [](){ exit(0); };

//##################CODE BEGIN#############
struct Node {
  unordered_map<char, Node*> to;
  int term;
  Node* p;
  Node* suf;
  char c;
  int term_suf;
};
 
Node* root = new Node{{}, 0, 0, 0, '\x00', 0};
 
string get_word(Node* u) {
  string res = "";
  while(u != root) {
    res = u->c + res;
    u = u->p;
  }
  return res;
}
 
void print(Node* u, int d = 0) {
  for(auto [c, v] : u->to) {
    cout << string(d, ' ') << get_word(u) << " -> " << c << " " << v->term << " " << get_word(v->suf) << endl; 
    print(v, d + 2);
  }
}
 
void add_word(string s, int id) {
  Node* cur = root;
  
  for(char c : s) {
    if(cur->to.find(c) == cur->to.end()) {
      cur->to[c] = new Node{{}, 0, cur, 0, c};
    }
    cur = cur->to[c];
  }
  cur->term = 1;
}
 
void make_suf(Node* u) {
  if(u == root) {
    u->suf = 0;
    return;
  }
  char x = u->c;
  Node* v = u->p->suf;
  while(v != 0) {
    if(v->to.find(x) != v->to.end()) {
      u->suf = v->to[x];
      return;
    }
    v = v->suf;
  }
  u->suf = root;
}
 
void build_suf() {
  queue<Node*> q;
  q.push(root);
  while(!q.empty()) {
    Node* u = q.front(); q.pop();
    make_suf(u);
    for(auto [c, v] : u->to) {
      q.push(v);
    }
  }
  q.push(root);
  while(!q.empty()) {
    Node* u = q.front(); q.pop();
    if(u->suf != 0 && (u->suf->term_suf || u->suf->term)) {
      u->term_suf = 1;
    }
    for(auto [c, v] : u->to) {
      q.push(v);
    }
  }
}
//entry
void sol() {
  string t; cin >> t;
  int n; cin >> n;
  vector<string> words(n);
  for(int i = 0; i < n; ++i) {
    string s; cin >> s;
    add_word(s, i);
    words[i] = s;
  }
  build_suf();
  // DBG_CODE(print(root));
  Node* cur = root;
  unordered_set<Node*> res1;
  for(char c : t) {
    while(cur != root && cur->to.find(c) == cur->to.end()) {
      cur = cur->suf;
    }
    if(cur->to.find(c) != cur->to.end()) {
      cur = cur->to[c];
      if(cur->term || cur->term_suf) {
	Node* v = cur;
	while(v != 0) {
	  if(res1.find(v) != res1.end()) break;
	  if(v->term) {
	    res1.insert(v);
	  }
	  if(!v->term_suf) break;
	  v = v->suf;
	}
      }
    }
  }
  unordered_set<string> res;
  for(Node* u : res1) {
    res.insert(get_word(u));
  }
  for(int i = 0; i < n; ++i) {
    if(res.find(words[i]) != res.end()) cout << "Yes" << endl;
    else cout << "No" << endl;
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
    finish = [&]() {
        auto stop = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
        cout << duration.count() << " microseconds" << endl;
        exit(0);
    };
    #endif

    sol();
    finish();
}
