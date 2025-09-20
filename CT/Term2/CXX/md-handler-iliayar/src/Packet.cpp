#include "Packet.h"

#include <ostream>

namespace md_handler {

std::ostream & operator << (std::ostream & str, const Packet & packet)
{
    str << "Packet{"
        << "seq_num=" << packet.m_seq_num
        << ", msg_count=" << packet.m_msg_count
        << "}";

    return str;
}

}
