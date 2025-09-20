#pragma once

#include "Packet.h"

#include <stdint.h>

namespace md_handler {

class IService
{
public:
    virtual ~IService() = default;
    /*
     * Function requests re-sending messages
     *
     * start_seq_num - sequence number of the first message
     * msg_count - total number of events following start_seq_num inclusive
     *
     */
    virtual void resend_messages(uint32_t start_seq_num, uint16_t msg_count) = 0;
    /*
     * Function for simulation of handling messages
     *
     */
    virtual void handle_message(uint32_t seq_num) = 0;
};

}
