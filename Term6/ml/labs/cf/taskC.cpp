
// Generated at 2022-03-07 15:58:54.373946 
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
const string kManhattan = "manhattan";
const string kEuclidean = "euclidean";
const string kChebyshev = "chebyshev";

const string kUniform = "uniform";
const string kTriangular = "triangular";
const string kEpanechnikov = "epanechnikov";
const string kQuartic = "quartic";
const string kTriWeight = "triweight";
const string kTricube = "tricube";
const string kGaussian = "gaussian";
const string kCosime = "cosine";
const string kLogistic = "logistic";
const string kSigmoid = "sigmoid";

const string kFixed = "fixed";
const string kVariable = "variable";

using vfloat = vector<double>;

struct Object {
    vfloat x;
    int y;

    friend ostream& operator<<(ostream& o, const Object& obj) {
        o << "([" << Join(obj.x, " ") << "], " << obj.y << ")";
        return o;
    }
};

struct Dist {
    virtual double calc(const vfloat& a, const vfloat& b) = 0;
};

struct DistEuclidean : Dist {
    double calc(const vfloat& a, const vfloat& b) override {
        double res = 0;
        for (int i = 0; i < a.size(); ++i) {
            res += (a[i] - b[i])*(a[i] - b[i]);
        }
        return sqrt(res);
    }
};

struct DistManhattan : Dist {
    double calc(const vfloat& a, const vfloat& b) override {
        double res = 0;
        for (int i = 0; i < a.size(); ++i) {
            res += fabs(a[i] - b[i]);
        }
        return res;
    }
};

struct DistChebyshev : Dist {
    double calc(const vfloat& a, const vfloat& b) override {
        double res = 0;
        for (int i = 0; i < a.size(); ++i) {
            res = max(res, fabs(a[i] - b[i]));
        }
        return res;
    }
};

struct Kern {
    virtual double calc(double x) = 0;
};

struct KernUniform : Kern {
    double calc(double x) override {
        if (fabs(x) >= 1) return 0;
        return 1./2.;
    }
};

struct KernGaussian : Kern {
    double calc(double x) override {
        return exp(- 1. * x * x / 2) / sqrt(2 * M_PI);
    }
};

struct KernTriangular : Kern {
    double calc(double x) override {
        if (fabs(x) >= 1) return 0;
        return 1 - fabs(x);
    }
};

struct KernEpanechnikov : Kern {
    double calc(double x) override {
        if (fabs(x) >= 1) return 0;
        return 3. * (1 - x*x) / 4.;
    }
};

struct KernQuartic : Kern {
    double calc(double x) override {
        if (fabs(x) >= 1) return 0;
        return 15. * (1 - x * x) * (1 - x * x) / 16.;
    }
};

struct KernTriweight : Kern {
    double calc(double x) override {
        if (fabs(x) >= 1) return 0;
        return 35. * (1 - x * x) * (1 - x * x) * (1 - x * x) / 32.;
    }
};

struct KernTricube : Kern {
    double calc(double x) override {
        if (fabs(x) >= 1) return 0;
        return 70. * (1 - fabs(x) * fabs(x) * fabs(x)) * (1 - fabs(x) * fabs(x) * fabs(x)) * (1 - fabs(x) * fabs(x) * fabs(x)) / 81.;
    }
};

struct KernCosine : Kern {
    double calc(double x) override {
        if (fabs(x) >= 1) return 0;
        return M_PI_4 * cos(M_PI_2 * x);
    }
};

struct KernLogistic : Kern {
    double calc(double x) override {
        // if (fabs(x) >= 1) return 0;
        return 1 / (exp(x) + 2 + exp(-x));
    }
};

struct KernSigmoid : Kern {
    double calc(double x) override {
        // if (fabs(x) >= 1) return 0;
        return M_2_PI / (exp(x) + exp(-x));
    }
};

Kern* kern_by_name(const string& s) {
    if (s == kUniform) return new KernUniform{};
    if (s == kTriangular) return new KernTriangular{};
    if (s == kEpanechnikov) return new KernEpanechnikov{};
    if (s == kQuartic) return new KernQuartic{};
    if (s == kTriWeight) return new KernTriweight{};
    if (s == kTricube) return new KernTricube{};
    if (s == kGaussian) return new KernGaussian{};
    if (s == kCosime) return new KernCosine{};
    if (s == kLogistic) return new KernLogistic{};
    if (s == kSigmoid) return new KernSigmoid{};
    exit(42);
}

Dist* dist_by_name(const string& s) {
    if (s == kManhattan) return new DistManhattan{};
    if (s == kEuclidean) return new DistEuclidean{};
    if (s == kChebyshev) return new DistChebyshev{};
    exit(42);
}

void vmul(vfloat& v, double k) {
    for (auto& e : v) {
        e *= k;
    }
}

vfloat vscal(const vfloat& v, double k) {
    vfloat res = v;
    vmul(res, k);
    return res;
}

void vadd(vfloat& x, const vfloat& b) {
    for (int i = 0; i < x.size(); ++i) {
        x[i] += b[i];
    }
}

vfloat vsum(const vfloat& a, const vfloat& b) {
    vfloat res = a;
    vadd(res, b);
    return res;
}

vfloat one_hot(int y, int m) {
    vfloat res(m, 0);
    res[y] = 1;
    return res;
}

//entry
void sol() {
    cout.precision(17);

    int N, M; cin >> N >> M;

    vector<Object> X;
    int nclasses = 0;
    double default_val = 0;

    for (int i = 0; i < N; ++i) {
        vfloat x;
        for (int j = 0; j < M; ++j) {
            int n; cin >> n;
            x.push_back(n); 
        }
        int y; cin >> y;
        X.push_back({std::move(x), y});
        nclasses = max(y + 1, nclasses);
        default_val += y;
    }

    vfloat q;
    for (int i = 0; i < M; ++i) {
        int n; cin >> n;
        q.push_back(n);
    }

    string dist_name, kern_name, win_type_name;
    cin >> dist_name >> kern_name >> win_type_name;

    int win_param; cin >> win_param;

    Dist* dist = dist_by_name(dist_name);
    Kern* kern = kern_by_name(kern_name);

    // WindowType* win_type = win_type_by_name(win_type_name, win_param, dist);

    sort(X.begin(), X.end(), [dist, &q](auto& a, auto& b) {
        auto da = dist->calc(a.x, q);
        auto db = dist->calc(b.x, q);
        return da < db;
    });

    DBG(X);

    double win;
    if (win_type_name == kFixed) {
        win = win_param; 
    } else if (win_type_name == kVariable) {
        win = dist->calc(X[win_param].x, q);
    } else {
        exit(42);
    }

    // vfloat res(nclasses, 0);
    double res = 0;
    double denom = 0;

    for (const auto& obj : X) {
        double d = dist->calc(obj.x, q);
        double c;
        if (win == 0) {
            if (d == 0) {
                c = kern->calc(0);
            } else {
                c = 0;
            }
        } else {
            c = kern->calc(d / win);
        }
        DBG(d << " " << d / win << " " << c);
        res += obj.y * c;
        // vadd(res, vscal(one_hot(obj.y, nclasses), c));
        denom += c;
    }
    // for (auto& x : res) {
        // x /= denom;
    // }
    if (res == 0 && denom == 0) {
        cout << default_val / X.size() << endl;
    } else {
        cout << res / denom << endl;
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
