#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>


using namespace std;

#define ON 1
#define OFF 0
#ifdef LOCAL
#define FILE_IO ON
#define FILENAME "local"
#else
#define FILE_IO  OFF
#define FILENAME "smth"
#endif

#define int long long
#define vint vector<int>
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl;
#else
#define DBG(x)
#endif

//CODE_HERE

signed main() {
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
