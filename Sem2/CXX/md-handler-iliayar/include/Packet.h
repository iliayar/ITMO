#pragma once

#include <stdint.h>
#include <iosfwd>

namespace md_handler {

class Packet
{
public:
    Packet()
    {
    }

    Packet(uint32_t seq_num, uint16_t msg_count)
        : m_seq_num(seq_num)
        , m_msg_count(msg_count)
    {
    }

    Packet(const Packet & packet) :
        m_seq_num(packet.m_seq_num),
        m_msg_count(packet.m_msg_count)
    {
    }

    uint32_t get_seq_num() const
    {
        return m_seq_num;
    }

    uint16_t get_msg_count() const
    {
        return m_msg_count;
    }

    Packet & operator=(const Packet & p)
    {
        m_seq_num = p.m_seq_num;
        m_msg_count = p.m_msg_count;
        return *this;
    }

private:
    uint32_t m_seq_num = 0;
    uint16_t m_msg_count = 0;

friend std::ostream & operator << (std::ostream & out, const Packet & p);

};

}
