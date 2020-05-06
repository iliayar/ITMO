#include "template.cpp"

#define FILE_IO ON
#define FILENAME "problem3"

struct DFA
{


    DFA(int n)
    {
        acc.resize(n + 1, false);
        to.resize(n + 1);
    }

    void accept(int n)
    {
        acc[n] = true;
    }

    void add(int f, char c, int t)
    {
        to[f][c] = t;
    }

    int size() {
       vector<bool> was(acc.size(), false);
        return size_imp(1, was);
    }

    int size_imp(int v, vector<bool>& was) {
        was[v] = true;
        // TODO
        return 0;
    }

    bool check(string s)
    {
        int v = 1;
        for(char c : s) {
            if(to[v][c] != 0) {
                v = to[v][c];
            } else {
                return false;
            }
        }
        return acc[v];
    }

    vector<bool> acc;
    vector<map<char, int>> to;

};

//entry
void sol()
{
    string s; cin >> s;
    int n, m, k; cin >> n >> m >> k;
    DFA a(n);
    for(int i = 0; i < k; ++i) {
        int t; cin >> t;
        a.accept(t);
    }
    for(int i = 0; i < m; ++i) {
        int f, t;
        char c;
        cin >> f >> t >> c;
        a.add(f, c, t);
    }

    cout << a.size() << endl;
}
