#include "searcher.h"

#include <algorithm>
#include <functional>
#include <iostream>
#include <string>

namespace {
using Filename = Searcher::Filename;
using DocIterator = Searcher::DocIterator;
using BadQuery = Searcher::BadQuery;

std::string
adjust_word(const std::string& word)
{
    std::size_t i = 0;
    for (; i < word.length(); ++i) {
        if (std::isalnum(word[i])) {
            break;
        }
    }
    std::size_t j = word.length();
    for (; j > 0; --j) {
        if (std::isalnum(word[j - 1])) {
            break;
        }
    }
    if (j <= i)
        return "";
    return word.substr(i, j - i);
}

}
bool
Searcher::check_word_seq_imp(
  std::size_t doc_id,
  std::vector<std::size_t>& its,
  const std::vector<
    std::map<std::string,
             std::vector<std::pair<std::size_t, std::size_t>>>::const_iterator>&
    word_seq) const
{
    std::size_t i = 0;
    while (i < its.size()) {
        auto ocurs_it = word_seq[i];
        if (ocurs_it == m_data.end()) {
            return false;
        }
        auto ocurs = ocurs_it->second;
        if (its[i] >= ocurs.size() || ocurs[its[i]].first > doc_id) {
            return false;
        }
        if (i == 0) {
            while (its[i] < ocurs.size() && ocurs[its[i]].first != doc_id) {
                if (ocurs[its[i]].first > doc_id) {
                    return false;
                }
                its[i]++;
            }
            if (its[i] == ocurs.size()) {
                return false;
            }
        } else {
            auto prev_ocurs = word_seq[i - 1]->second;
            while (its[i] < ocurs.size()) {
                if (ocurs[its[i]].first > doc_id) {
                    return false;
                }
                if (ocurs[its[i]].first == doc_id &&
                    ocurs[its[i]].second > prev_ocurs[its[i - 1]].second) {
                    break;
                }
                its[i]++;
            }
            if (its[i] == ocurs.size()) {
                return false;
            }
            if (ocurs[its[i]].second > prev_ocurs[its[i - 1]].second + 1) {
                i--;
                its[i]++;
                continue;
            }
        }
        i++;
    }
    return true;
}

std::vector<std::vector<
  std::map<std::string,
           std::vector<std::pair<std::size_t, std::size_t>>>::const_iterator>>
Searcher::parse_query_imp(const std::string& query) const
{

    std::vector<std::vector<std::map<
      std::string,
      std::vector<std::pair<std::size_t, std::size_t>>>::const_iterator>>
      v_query;

    std::string cur_word = "";
    bool seq = false;
    for (std::size_t i = 0; i <= query.length(); ++i) {
        char c = i == query.length() ? '\n' : query[i];
        if (std::isspace(c) || c == '\"') {
            if (std::string word = adjust_word(cur_word); word != "") {
                if (seq) {
                    v_query[v_query.size() - 1].push_back(m_data.find(word));
                } else {
                    v_query.push_back({ m_data.find(word) });
                }
            }
            cur_word.clear();

            if (c == '\"') {
                seq ^= 1;
                if (seq) {
                    v_query.push_back({});
                }
            }
        } else {
            cur_word += c;
        }
    }

    if (seq) {
        throw BadQuery("Unmatched Parenthesis");
    }

    if (v_query.size() == 0 || v_query[0].size() == 0) {
        throw BadQuery("Empty Query");
    }

    return v_query;
}

void
Searcher::add_document(const Filename& filename, std::istream& inp)
{
    for (const Filename& doc : m_documents) {
        if (doc == filename) {
            return;
        }
    }
    std::string cur_word = "";
    std::size_t document_id = m_documents.size();
    m_documents.push_back(filename);
    std::size_t word_id = 0;
    while (inp || !cur_word.empty()) {
        char c = '\n';
        if (inp)
            inp.get(c);
        if (std::isspace(c)) {
            if (std::string word = adjust_word(cur_word); word != "") {
                m_data[word].emplace_back(document_id, word_id);
                word_id++;
            }
            cur_word.clear();
        } else {
            cur_word += c;
        }
    }
}

void
Searcher::remove_document(const Filename& filename)
{
    std::size_t document_id = 0;
    for (; document_id < m_documents.size(); ++document_id) {
        if (m_documents[document_id] == filename) {
            break;
        }
    }
    for (auto& pos : m_data) {
        auto begin = pos.second.begin();
        for (; begin != pos.second.end() && begin->first != document_id;
             begin++)
            ;
        auto end = begin;
        for (; end != pos.second.end() && end->first == document_id; end++)
            ;
        pos.second.erase(begin, end);
    }
}

std::pair<DocIterator, DocIterator>
Searcher::search(const std::string& query) const
{
    auto v_query = parse_query_imp(query);

    std::vector<Filename> res;

    std::vector<bool> excluded(m_documents.size(), false);

    for (const auto& word_seq : v_query) {
        std::vector<std::size_t> its(word_seq.size(), 0);
        for (std::size_t doc_id = 0; doc_id < m_documents.size(); ++doc_id) {
            if (!check_word_seq_imp(doc_id, its, word_seq)) {
                excluded[doc_id] = true;
            }
        }
    }

    for (std::size_t doc_id = 0; doc_id < excluded.size(); ++doc_id) {
        if (!excluded[doc_id]) {
            res.push_back(m_documents[doc_id]);
        }
    }

    return { { 0, res }, { res.size() } };
}
