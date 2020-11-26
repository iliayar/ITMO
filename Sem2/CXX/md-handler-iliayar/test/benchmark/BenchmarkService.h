#pragma once

#include "Channel.h"
#include "IService.h"
#include "Log.h"
#include "MdHandler.h"

#include <atomic>
#include <condition_variable>
#include <mutex>

namespace md_handler::benchmark {

class Service : public IService
{
public:
    Service(uint32_t expected)
        : m_name("service")
        , m_expected(expected)
        , m_running(true)
        , m_gapped(false)
    {
    }

    void resend_messages(uint32_t start_seq_num, uint16_t msg_count) final
    {
        LOG("got a resend request "
                << "start_seq_num = " << start_seq_num
                << ", msg_count = " << msg_count
                << "; shutting down");

        shutdown(true);
    }

    void handle_message(uint32_t seq_num) final
    {
        if (!m_running) {
            return;
        }
        LOG("processing seq num: " << seq_num);
        uint32_t count = m_count;
        if (seq_num == count) {
            m_count.compare_exchange_strong(count, count + 1);
        }
        else {
            LOG("handle_message; expected seq num " << count << " but got " << seq_num << "; shutting down")
            shutdown(true);
        }
        if (seq_num == m_expected) {
            LOG("got expected number of messages: " << m_expected << " shutting down");
            shutdown(false);
        }
    }

    void shutdown(bool gapped)
    {
        std::unique_lock<std::mutex> lock(m_mutex);
        LOG("shutting down");
        m_running = false;
        m_gapped = gapped;
        m_cv.notify_all();
        LOG("shut down");
    }

    void wait()
    {
        for (;;) {
            std::unique_lock<std::mutex> lock(m_mutex);
            LOG("waiting for shutdown signal...");
            if (m_running) {
                m_cv.wait(lock);
            }
            else {
                break;
            }
        }
        LOG("waiting done");
    }

    uint32_t get_count()
    {
        if (m_count > 0) {
            return m_count - 1;
        }
        else {
            return 0;
        }
    }

    bool get_gapped()
    {
        return m_gapped;
    }

private:
    std::string m_name;
    bool m_log_enabled = false;

    std::atomic<uint32_t> m_count = 1;
    uint32_t m_expected = 0;

    std::mutex m_mutex;
    std::condition_variable m_cv;

    std::atomic<bool> m_running;
    bool m_gapped = false;
};

class ChannelListener : public IChannelListener
{
public:
    ChannelListener(MdHandler & handler)
        : m_handler(handler)
    {
    }

    void on_send_packet(const Packet & packet)
    {
        m_handler.handle_packet(packet);
    }

    void on_resend_packet(const Packet & packet)
    {
        m_handler.handle_resend(packet);
    }

private:
    MdHandler & m_handler;
};

}