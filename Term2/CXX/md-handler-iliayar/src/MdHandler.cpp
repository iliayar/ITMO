#include "MdHandler.h"
#include "IService.h"

namespace md_handler {

MdHandler::MdHandler(IService& service)
  : m_service(service)
  , m_data()
  , m_resend_num(1)
  , m_seq_num(1)
  , m_waiting(0)
  , m_waiting_state(WaitingState::NOTHING)
{}

void
MdHandler::handle_packet(const Packet& packet)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    add_and_send(packet.get_seq_num(),
                 packet.get_msg_count() + packet.get_seq_num());

    WaitingState waiting_state = WaitingState::NOTHING;
    uint32_t heartbeat_fix = packet.get_msg_count() == 0 ? 1 : 0;

    if (m_waiting >= packet.get_seq_num() &&
        m_waiting < packet.get_seq_num() + packet.get_msg_count()) {
        waiting_state = WaitingState::RESTORED;
    } else if (m_waiting < packet.get_seq_num()) {
        waiting_state = WaitingState::MISSED;
    }

    if (m_waiting_state != WaitingState::WAITING) {
        while (m_resend_num < packet.get_seq_num()) {
            m_waiting = m_resend_num;
            m_waiting_state = WaitingState::WAITING;

            const int TIMEOUT = 1000000; // FIXME
            lock.unlock();
            for (int i = 0; i < TIMEOUT; ++i) {
                std::unique_lock<std::mutex> lock_inner(m_mutex);
                if (m_waiting_state != WaitingState::WAITING) {
                    break;
                }
            }
            lock.lock();
            if (m_waiting_state == WaitingState::WAITING ||
                m_waiting_state == WaitingState::MISSED) {
                break;
            }
        }
    }

    uint32_t resend_num =
      std::max(m_resend_num,
               packet.get_seq_num() + packet.get_msg_count() + heartbeat_fix);
    if (m_resend_num < packet.get_seq_num()) {
        m_service.resend_messages(
          m_resend_num, packet.get_seq_num() - m_resend_num + heartbeat_fix);

        // Waiting for resends
        m_resend_num = resend_num;
        if (m_resend_num > m_seq_num) {
            lock.unlock();
            while (true) {
                lock.lock();
                if (m_resend_num <= m_seq_num) {
                    break;
                }
                lock.unlock();
            }
        }
    }
    m_resend_num = resend_num;
    m_waiting_state = waiting_state;
    m_waiting = 0;
}

void
MdHandler::handle_resend(const Packet& packet)
{
    std::unique_lock<std::mutex> lock(m_mutex);
    add_and_send(packet.get_seq_num(),
                 packet.get_msg_count() + packet.get_seq_num());
}

// [begin, end)
void
MdHandler::add_and_send(uint32_t begin, uint32_t end)
{
    uint32_t last = std::max(begin, m_seq_num);
    auto it = m_data.begin();
    for (; it != m_data.end(); ++it) {
        if (last < std::min(it->first, end)) {
            m_data.insert(it, { last, std::min(it->first, end) });
        }
        last = it->second;
        if (last >= end) {
            break;
        }
    }
    if (last < end) {
        m_data.push_back({ last, end });
    }
    for (it = m_data.begin(); it != m_data.end();) {
        if (it->first <= m_seq_num) {
            for (; m_seq_num < it->second; ++m_seq_num) {
                m_service.handle_message(m_seq_num);
            }
            it = m_data.erase(it);
        } else {
            ++it;
        }
    }
}

}
