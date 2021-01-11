#include "comm.h"
#include <cstring>
#include <fstream>
#include <functional>
#include <iostream>
#include <set>
#include <string>
#include <vector>

void
error(std::string msg)
{
    std::cerr << msg << std::endl;
    std::cerr << Comm::USAGE;
    exit(1);
}

void
print_comm(std::pair<std::istream&, std::istream&> in, std::set<int>& excluded)
{
    Comm c(in);
    for (int e : excluded) {
        c.exclude(e);
    }
    std::cout << c;
}

int
main(int argc, char** argv)
{
    std::vector<std::string> inputs;
    std::set<int> excluded;
    for (int i = 1; i < argc; ++i) {
        if (strlen(argv[i]) > 0) {
            if (argv[i][0] == '-') {
                if (strlen(argv[i]) == 1) {
                    inputs.push_back("-");
                }
                for (size_t j = 1; j < strlen(argv[i]); ++j) {
                    int n = argv[i][j] - '1';
                    excluded.insert(n);
                }
            } else {
                inputs.push_back(std::string(argv[i]));
            }
        }
    }
    if (inputs.size() != 2)
        error("Wrong count of inputs");
    if (inputs[0] == "-" && inputs[1] == "-")
        error("Two stdin inputs not allowed");
    if (inputs[0] == "-" || inputs[1] == "-") {
        std::string filename = (inputs[0] == "-") ? inputs[1] : inputs[0];
        std::ifstream file(filename);
        if (!file)
            error("Could not open file " + filename);
        if (inputs[0] == "-") {
            print_comm({ std::cin, file }, excluded);
        } else {
            print_comm({ file, std::cin }, excluded);
        }
        file.close();
    } else {
        std::ifstream file1(inputs[0]);
        std::ifstream file2(inputs[1]);
        if (!file1)
            error("Could not open file " + inputs[0]);
        if (!file2)
            error("Could not open file " + inputs[1]);
        print_comm({ file1, file2 }, excluded);
        file1.close();
        file2.close();
    }
    return 0;
}
