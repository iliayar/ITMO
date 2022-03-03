#include "template.cpp"

//entry
void sol() {

    int n, m, k; cin >> n >> m >> k;

    vector<vint> cs(m, vint{});
    for (int i = 0; i < n; ++i) {
        int j; cin >> j; j--;
        cs[j].push_back(i + 1);
    }


    vector<vint> res(k, vint{});

    int i = 0, j = 0;
    while (j < m) {
        if (cs[j].empty()) {
            j++;
            continue;
        }
        res[i].push_back(cs[j].back());
        cs[j].pop_back();
        i = (i + 1) % k;
    }

    for (int i = 0; i < k; ++i) {
        cout << res[i].size() << " " << res[i];
    }
}
