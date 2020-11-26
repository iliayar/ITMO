#pragma once

#include "Packet.h"

#include <list>
#include <mutex>

namespace md_handler {

class IService;

class MdHandler
{
  public:
    enum class WaitingState
    {
        NOTHING,
        MISSED,
        RESTORED,
        WAITING
    };

    MdHandler(IService& service);
    void handle_packet(const Packet& packet);
    void handle_resend(const Packet& packet);

  private:
    void add_and_send(uint32_t, uint32_t);

    IService& m_service;
    std::list<std::pair<uint32_t, uint32_t>> m_data;
    uint32_t m_resend_num;
    uint32_t m_seq_num;
    std::mutex m_mutex;

    uint32_t m_waiting;
    WaitingState m_waiting_state;
};

}
