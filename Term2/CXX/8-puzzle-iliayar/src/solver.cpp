#include "solver.h"
#include "board.h"

#include <algorithm>
#include <memory>
#include <queue>
#include <unordered_map>

namespace {
using table_type = std::vector<std::vector<unsigned>>;

struct table_hash
{
    static const std::size_t BASE = 31;
    static const std::size_t MOD = 1337269;
    std::size_t operator()(const table_type& c) const
    {
        std::size_t res = 0;
        for (auto v : c) {
            for (int n : v) {
                res = (res + n) * BASE;
                res %= MOD;
            }
        }
        return res;
    }
};

struct Node
{
    const table_type& table;
    unsigned cost;
    unsigned h = 0;
    bool expanded = false;
    bool was = false;
    std::vector<std::weak_ptr<Node>> moves;
    std::weak_ptr<Node> from = std::shared_ptr<Node>(nullptr);

    Node(const Board& board)
      : table(board.array())
    {
        cost = Board::manhattan_imp(board.array());
    }

    Node(const table_type& table)
      : table(table)
    {
        cost = Board::manhattan_imp(table);
    }

    void expand(
      std::unordered_map<table_type, std::shared_ptr<Node>, table_hash>& nodes)
    {
        if (expanded)
            return;
        table_type init = table;
        const std::pair<unsigned, unsigned>& empty =
          Board::empty_cell_imp(init);
        unsigned size = init.size();
        expanded = true;
        auto try_move = [&](int dx, int dy) {
            int x = static_cast<int>(empty.first);
            int y = static_cast<int>(empty.second);

            if (x + dx >= 0 && x + dx < static_cast<int>(size) && y + dy >= 0 &&
                y + dy < static_cast<int>(size)) {
                std::swap(init[x][y], init[x + dx][y + dy]);
                if (const auto it = nodes.find(init); it != nodes.end()) {
                    moves.push_back(it->second);
                } else {
                    auto p =
                      nodes.emplace(init, std::shared_ptr<Node>(nullptr));
                    p.first->second = std::make_shared<Node>(p.first->first);
                    moves.push_back(p.first->second);
                }
                std::swap(init[x][y], init[x + dx][y + dy]);
            }
        };
        try_move(1, 0);
        try_move(-1, 0);
        try_move(0, 1);
        try_move(0, -1);
    }
};
} // namespace

Solver::Solver(const Board& board)
{
    if (!board.is_solvable())
        return;
    auto comp = [](std::weak_ptr<Node> a_weak, std::weak_ptr<Node> b_weak) {
        auto a = a_weak.lock();
        auto b = b_weak.lock();
        return (a->h + a->cost) > (b->h + b->cost);
    };
    std::priority_queue<std::weak_ptr<Node>,
                        std::vector<std::weak_ptr<Node>>,
                        decltype(comp)>
      q(comp);
    std::unordered_map<table_type, std::shared_ptr<Node>, table_hash> nodes;

    std::shared_ptr<Node>& root = nodes[board.array()];
    root = std::make_shared<Node>(board);
    q.push(root);
    root->was = true;

    while (!q.empty()) {
        std::shared_ptr<Node> cur = q.top().lock();

        if (Board::is_goal_imp(cur->table))
            break;

        q.pop();
        cur->expand(nodes);

        for (std::weak_ptr<Node>& m_weak : cur->moves) {
            std::shared_ptr<Node> m = m_weak.lock();
            if (m->was && m->h < cur->h + 1)
                continue;
            m->was = true;
            m->h = cur->h + 1;
            m->from = cur;
            q.push(m);
        }
    }
    std::shared_ptr<Node> cur = q.top().lock();
    while (cur != nullptr) {
        m_moves.emplace_back(cur->table);
        cur = cur->from.lock();
    }
    reverse(m_moves.begin(), m_moves.end());
    m_moves_cnt = m_moves.size() - 1;
}

std::size_t
Solver::moves() const
{
    return m_moves_cnt;
}
