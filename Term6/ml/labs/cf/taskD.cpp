
// Generated at 2022-03-13 20:45:26.427414 
// By iliayar
#define _USE_MATH_DEFINES
#pragma comment(linker, "/STACK:36777216")
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


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

#define INF 1e+18

using vint = vector<int>;
using vint2 = vector<vint>;

template<typename T>
class Join {
  T& v;
  string& separator;
  
public:
  
  Join(T v, string separator)
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

template<typename T>
ostream& operator<<(ostream& out, vector<T> v) {
  out << Join(v, " ") << endl;
  return out;
}

template<typename T, typename K>
ostream& operator<<(ostream& out, pair<T, K> p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

//##################CODE BEGIN#############
struct Obj {
    vector<double> x;
    double y;
};

template <typename T>
int sign(T x) { return (T(0) < x) - (T(0) > x); }


// (|x - y| / (|x| + |y|))' = (|x-y|'*(|x| + |y|) - |x-y|*(|x| + |y|)')/ (|x| + |y|)*2


double calc_pred(vector<double> const& x, vint const& A) {
    double res = A[A.size() - 1];
    for (int i = 0; i < A.size() - 1; ++i) {
        res += x[i] * A[i];
    }
    return res;
}

double smape_der(double y, double yp) {
    double denom = fabs(y) + fabs(yp);
    return (sign(yp - y) * denom - abs(yp - y) * sign(yp)) / (denom * denom);
}

//entry
void sol() {
    cout.precision(17);

    int N, M; cin >> N >> M;
    
    vector<Obj> X;

    for (int i = 0; i < N; ++i) {
        vector<double> x;
        for (int j = 0; j < M; ++j) {
            int n; cin >> n;
            x.push_back(n);
        }
        int y; cin >> y;
        X.push_back({x, y});
    }

    vint A;

    for (int i = 0; i < M + 1; ++i) {
        int n; cin >> n;
        A.push_back(n);
    }

    for (auto& o : X) {
        double yp = calc_pred(o.x, A);
        double d = smape_der(o.y, yp);
        for (double x : o.x) {
            cout << x * d << " ";
        }
        cout << d << " ";
        cout << endl;
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
