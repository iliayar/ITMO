#include <cassert>
#include <iterator>
#include <map>
#include <string>
#include <utility>
#include <vector>

class Searcher
{
  public:
    using Filename = std::string; // or std::filesystem::path
    using iterator_category = std::forward_iterator_tag;

    // index modification
    void add_document(const Filename& filename, std::istream& strm);

    void remove_document(const Filename& filename);

    // queries
    class DocIterator
    {
      public:
        using value_type = const Filename;
        using iterator_category = std::forward_iterator_tag;
        using reference = value_type&;
        using pointer = value_type*;
        using difference_type = std::ptrdiff_t;

        DocIterator(std::size_t index, std::vector<Filename> documents = {})
          : index(index)
          , documents(std::move(documents))
        {}

        DocIterator operator++()
        {
            index++;
            return *this;
        }

        DocIterator operator++(int)
        {
            DocIterator res = *this;
            index++;
            return res;
        }

        friend bool operator==(const DocIterator& lhs, const DocIterator& rhs)
        {
            return lhs.index == rhs.index;
        }
        friend bool operator!=(const DocIterator& lhs, const DocIterator& rhs)
        {
            return lhs.index != rhs.index;
        }
        reference operator*() const
        {
            assert(index < documents.size());
            return documents[index];
        }
        pointer operator->() const
        {
            assert(index < documents.size());
            return &documents[index];
        }

      private:
        std::size_t index;
        const std::vector<Filename> documents;
    };

    class BadQuery : public std::exception
    {
      public:
        BadQuery(std::string msg)
          : m_msg("Search query syntax error: " + msg)
        {}

        const char* what() const throw() { return m_msg.c_str(); }

      private:
        std::string m_msg;
    };

    std::pair<DocIterator, DocIterator> search(const std::string& query) const;

  private:
    std::vector<std::vector<std::map<
      std::string,
      std::vector<std::pair<std::size_t, std::size_t>>>::const_iterator>>
    parse_query_imp(const std::string&) const;
    bool check_word_seq_imp(
      std::size_t,
      std::vector<std::size_t>&,
      const std::vector<std::map<
        std::string,
        std::vector<std::pair<std::size_t, std::size_t>>>::const_iterator>&)
      const;

    std::map<std::string, std::vector<std::pair<std::size_t, std::size_t>>>
      m_data;
    std::vector<Filename> m_documents;
};
