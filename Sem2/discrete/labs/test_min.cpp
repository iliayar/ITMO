#include <stdlib.h>
#include <vector>
#include <fstream>
#include <iostream>
#include <vector>
#include <queue>
#include <unordered_set>
#include <unordered_map>
#include <set>
#include <utility>
using namespace std;

// OK

#define GRAMMAR_SIZE 26

struct automaton {
    int n, s;
    vector<vector<int> > edges;
    vector<int> terminal;
};

struct triple {
    int a, b, c;
    triple(){};
};

unordered_set<int> reachable_vertices(automaton aut) {
    unordered_set<int> reachable;
    queue<int> bfsq;

    bfsq.push(aut.s);
    reachable.insert(aut.s);
    while (!bfsq.empty()) {
        int curstate = bfsq.front();
        bfsq.pop();
        for (int i = 0; i < GRAMMAR_SIZE; i++) {
            int u = aut.edges[curstate][i];
            if (reachable.count(u) == 0) {
                reachable.insert(u);
                bfsq.push(u);
            }
        }
    }
    return reachable;
}

vector<unordered_set<int> > get_classes(automaton aut,
                                         const vector<vector<vector<int> > > backedges,
                                         const unordered_set<int> reachable) {
    vector<unordered_set<int> > classes;
    vector<int> class_arr(aut.n);
    unordered_set<int> F, QmF;
    for (int i = 0; i < aut.n; i++) {
        if (reachable.count(i) == 0) {
            class_arr[i] = -1;
        } else
        if (aut.terminal[i]) {
            F.insert(i);
            class_arr[i] = 0;
        } else {
            QmF.insert(i);
            class_arr[i] = 1;
        }
    }
    classes.push_back(F);
    classes.push_back(QmF);

    queue<pair<int, int> > Q;
    for (int c = 0; c < GRAMMAR_SIZE; c++) {
        Q.push(pair<int, int>(0, c));
        Q.push(pair<int, int>(1, c));
    }


    unordered_map<int, vector<int> > involved;
    while (!Q.empty()) {
        involved.clear();
        unordered_set<int> cur_set = classes[Q.front().first];
        int cur_char = Q.front().second;
        Q.pop();

        for (int q : cur_set) {
            for (int r : backedges[q][cur_char]) {
                int i = class_arr[r];
                if (i == -1) continue; // FIXME
                if (involved.count(i) == 0) {
                    involved.emplace(i, vector<int>(0));
                }
                involved[i].push_back(r);
            }
        }
        for (pair<int, vector<int> > i : involved) {
            int ii = i.first;
            if (i.second.size() < classes[ii].size()) {
                unordered_set<int> newset;
                int j = classes.size();
                classes.push_back(newset);
                for (int r : i.second) {
                    classes[ii].erase(r);
                    classes[j].insert(r);
                }
                if (classes[j].size() > classes[ii].size()) {
                    swap(classes[j], classes[ii]);
                }
                for (int r : classes[j]) {
                    class_arr[r] = j;
                }
                for (int c = 0; c < GRAMMAR_SIZE; c++) {
                    Q.push(pair<int, int>(j, c));
                }

            }
        }
    }



    // move start vertix to 1
    if (classes[1].count(aut.s) == 0) {
        for (int i = 0; i < classes.size(); i++) {
            if (i == 1) continue;
            if (classes[i].count(aut.s) > 0) {
                swap(classes[i], classes[1]);
                break;
            }
        }
    }
    // and stock to 0
    if (classes[0].count(0) == 0) {
        for (int i = 1; i < classes.size(); i++) {
            if (classes[i].count(0) > 0) {
                swap(classes[i], classes[0]);

                break;
            }
        }
    }

    return classes;
}

int main() {
    ifstream  fin("local.in");
    ostream& fout = cout;

    automaton aut;
    int n, m, k;
    fin >> n >> m >> k;

    // init
    aut.n = n + 1;
    aut.edges.resize(aut.n);
    aut.terminal.resize(aut.n);
    aut.s = 1;
    for (int i = 0 ; i < aut.n; i++) {
        aut.edges[i].resize(GRAMMAR_SIZE);
        aut.terminal[i] = false;
        for (int j = 0; j < GRAMMAR_SIZE; j++) aut.edges[i][j] = 0;
    }

    // input
    for (int i = 0; i < k; i++) {
        int termvalue;
        fin >> termvalue;
        aut.terminal[termvalue] = true;
    }
    for (int i = 0; i < m; i++) {
        int a, b;
        char c;
        fin >> a >> b >> c;
        // a--;  // we have additional '0' vertex
        aut.edges[a][c - 'a'] = b;
    }


    // backedges[from][char] == all vertices {to} that edges[to][char] = from
    vector<vector<vector<int> > > backedges(aut.n, vector<vector<int> >(GRAMMAR_SIZE));


    unordered_set<int> reachable = reachable_vertices(aut);
    for (int i = 0; i < aut.n; i++) {
        for (int c = 0; c < GRAMMAR_SIZE; c++) {
            backedges[aut.edges[i][c]][c].push_back(i);
        }
    }

    // get classes

    vector<unordered_set<int> > classes =
        get_classes(aut, backedges, reachable);


    for(int i = 0; i < classes.size(); ++i) {
        cout << "class " << i << endl;
        cout << "\t";
        for(int c : classes[i]) {
            cout << c << " ";
        }
        cout << endl;
    }
    
    vector<int> classes_vec(aut.n, -1);
    for (int i = 0; i < classes.size(); i++) {
        for (int vertex : classes[i]) {
            //cerr << "class[" << vertex << "] = " << i << endl;
            classes_vec[vertex] = i;
        }
    }

    // build autmin
    bool stock_reachable = reachable.count(0) > 0;
    automaton autmin;
    autmin.n = classes.size();
    autmin.edges.resize(autmin.n);
    autmin.terminal.resize(autmin.n);
    autmin.s = 1;

    for (int i = 0 ; i < autmin.n; i++) {
        autmin.edges[i].resize(GRAMMAR_SIZE);
        autmin.terminal[i] = false;
        for (int j = 0; j < GRAMMAR_SIZE; j++) autmin.edges[i][j] = 0;
    }

    for (int r : reachable) {
        if (classes_vec[r] == -1) continue;
        if (aut.terminal[r]) {
            autmin.terminal[classes_vec[r]] = true;;
        }
        for (int c = 0; c < GRAMMAR_SIZE; c++) {
            int u = classes_vec[aut.edges[r][c]];
            if (classes_vec[u] != -1) {
                autmin.edges[classes_vec[r]][c] = u;
            }
        }
    }

    int termn = 0;
    for (int i = 0; i < autmin.n; i++) if (autmin.terminal[i]) termn++;

    if (termn == 0) {
        fout << "0 0 0" << endl;
        // fout.close();
        return 0;
    }

    // general-purpose output (ignore stock)
    if (stock_reachable) {
        int autminm = 0;
        vector<triple> saved;
        for (int i = 0; i < autmin.n; i++) {
            for (int c = 0; c < GRAMMAR_SIZE; c++) {
                if (autmin.edges[i][c] == 0) continue;
                if (autmin.edges[i][c] == -1) continue;
                triple t;
                t.a = i;
                t.b = autmin.edges[i][c];
                t.c = c;
                saved.push_back(t);
                autminm++;
            }
        }

        fout << autmin.n - 1 << " "
             << autminm << " "
             << termn << endl;
        for (int i = 0; i < autmin.n; i++)
            if (autmin.terminal[i]) fout << i << " ";
        fout << endl;
        for (triple t : saved) {
            fout << t.a << " "
                 << t.b << " "
                 << (char) (t.c + 'a') << endl;

        }
        fout << endl;
    } else {
        int autminm = 0;
        vector<triple> saved;
        for (int i = 0; i < autmin.n; i++) {
            for (int c = 0; c < GRAMMAR_SIZE; c++) {
                if (autmin.edges[i][c] == -1) continue;
                triple t;
                t.a = i;
                t.b = autmin.edges[i][c];
                t.c = c;
                saved.push_back(t);
                autminm++;
            }
        }

        fout << autmin.n - 1 << " "
             << autminm << " "
             << termn << endl;
        for (int i = 0; i < autmin.n; i++)
            if (autmin.terminal[i]) fout << i << " ";
        fout << endl;
        for (triple t : saved) {
            fout << (t.a == 0 ? autmin.n : t.a) << " "
                 << (t.b == 0 ? autmin.n : t.b) << " "
                 << (char) (t.c + 'a') << endl;

        }
        fout << endl;
    }

    // fout.close();
}
