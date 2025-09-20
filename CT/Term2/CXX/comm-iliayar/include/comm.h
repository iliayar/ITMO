#include <iostream>
#include <string_view>
#include <vector>

class Comm
{
  public:
    Comm(std::pair<std::istream&, std::istream&> inputs)
      : m_eof({ inputs.first.eof(), inputs.second.eof() })
      , m_lines({ "", "" })
      , m_inputs(inputs)
      , m_excluded(3, false)
    {
        read_next({ true, true });
    }

    void exclude(int n) { m_excluded[n] = true; }

    std::pair<std::string, bool> next()
    {
        if (empty())
            return { "", true };
        std::pair<bool, bool> to_read = { false, false };
        int column;
        if (m_eof.first) {
            to_read = { false, true };
        } else if (m_eof.second) {
            to_read = { true, false };
        } else if (m_lines.first < m_lines.second) {
            to_read = { true, false };
        } else if (m_lines.first > m_lines.second) {
            to_read = { false, true };
        } else {
            to_read = { true, true };
        }
        column = get_column_imp(to_read);
        std::string res = "";
        bool empty = true;
        for (int i = 0, j = 0; i < 3; ++i) {
            if (!m_excluded[i]) {
                if (j > 0)
                    res += "\t";
                if (i == column) {
                    if (column == 0) {
                        res += m_lines.first;
                    } else {
                        res += m_lines.second;
                    }
                    empty = false;
                    break;
                }
                j++;
            }
        }
        read_next(to_read);
        return { std::move(res), empty };
    }

    bool empty() { return m_eof.first && m_eof.second; }

    friend std::ostream& operator<<(std::ostream& o, Comm& comm)
    {
        while (!comm.empty()) {
            auto l = comm.next();
            if (l.second)
                continue;
            o << l.first << std::endl;
        }
        return o;
    }

    static constexpr std::string_view USAGE =
      "Usage: comm [OPTION] FILE1 FILE2\n\
Options:\n                                                              \
    -1 \t suppress column 1 (lines unique to FILE1)\n                   \
    -2 \t suppress column 2 (lines unique to FILE2)\n                   \
    -3 \t suppress column 3 (lines that appear in both files)";

  private:
    void read_next(const std::pair<bool, bool>& to_read)
    {
        if (to_read.first) {
            if (m_inputs.first.eof()) {
                m_eof.first = true;
            } else {
                std::getline(m_inputs.first, m_lines.first);
                if (m_lines.first == "" && m_inputs.first.eof()) {
                    m_eof.first = true;
                }
            }
        }
        if (to_read.second) {
            if (m_inputs.second.eof()) {
                m_eof.second = true;
            } else {
                std::getline(m_inputs.second, m_lines.second);
                if (m_lines.second == "" && m_inputs.second.eof()) {
                    m_eof.second = true;
                }
            }
        }
    }

    int get_column_imp(const std::pair<bool, bool>& p)
    {
        if (p.first && !p.second) {
            return 0;
        } else if (!p.first && p.second) {
            return 1;
        } else if (p.first && p.second) {
            return 2;
        }
        return -1;
    }

    std::pair<bool, bool> m_eof;
    std::pair<std::string, std::string> m_lines;
    std::pair<std::istream&, std::istream&> m_inputs;
    std::vector<bool> m_excluded;
};
