#pragma once

#include "Log.h"
#include "MdHandler.h"
#include "Packet.h"

#include <atomic>
#include <deque>
#include <chrono>
#include <condition_variable>
#include <mutex>
#include <thread>

namespace md_handler {

struct LiveChannelType
{};

struct ReplayChannelType
{};

class IChannelListener
{
public:
    virtual void on_send_packet(const Packet & packet) = 0;
    virtual void on_resend_packet(const Packet & packet) = 0;
};

template <typename ChannelType>
class ChannelT
{
static constexpr uint64_t SEND_DELAY_US = 100; // delay in microseconds

using Pair = std::pair<uint32_t, uint16_t>;
using Queue = std::deque<Pair>;

public:
    ChannelT(const std::string & name, IChannelListener & listener)
        : m_name(name)
        , m_listener(listener)
    {
    }

    ChannelT(const std::string & name, IChannelListener & listener, uint64_t delay)
        : m_name(name)
        , m_listener(listener)
        , m_send_delay(delay)
    {
    }

    ChannelT(const std::string & name, IChannelListener & listener, uint64_t delay, [[maybe_unused]] size_t capacity)
        : m_name(name)
        , m_listener(listener)
        , m_send_delay(delay)
    {
    }

    ~ChannelT()
    {
        stop();
    }

    void start()
    {
        bool expected = false;
        if (m_running.compare_exchange_strong(expected, true)) {

            LOG("starting...");

            m_thread = std::thread(&ChannelT<ChannelType>::run, this);

            LOG("started");
        }
        else {
            LOG("already started");
        }
    }

    void stop()
    {
        bool expected = true;
        if (m_running.compare_exchange_strong(expected, false)) {

            LOG("stopping...");
            {
                // notify in case thread is waiting for messages
                std::unique_lock<std::mutex> lock(m_mutex);
                m_cv.notify_all();
            }

            if (m_thread.joinable()) {
                m_thread.join();
            }

            LOG("stopped");
        }
    }

    bool enqueue(uint32_t seq_num, uint16_t count)
    {
        if (!m_running) {
            std::cout << m_name << " stopping, "
                    << ", ignoring seq_num=" << seq_num
                    << ", count=" << count << "\n";

            LOG("stopping, ignoring seq_num=" << seq_num << ", count=" << count);
            return false;
        }

        bool was_empty = false;
        {
            std::unique_lock<std::mutex> lock(m_mutex);
            was_empty = m_queue.empty();
            m_queue.emplace_back(seq_num, count);
            LOG("enqueued packet: seq_num: " << seq_num << ", count=" << count);
        }

        if (was_empty) {
            LOG("queue was empty, waking up the thread");
            std::unique_lock<std::mutex> lock(m_mutex);
            m_cv.notify_all();
        }

        return true;
    }

    void set_logging(bool v)
    {
        m_log_enabled = v;
    }

private:
    void run()
    {
        while (m_running) {
            size_t size = 0;
            {
                // wait for packets
                for (;;) {
                    {
                        std::unique_lock<std::mutex> lock(m_mutex);
                        size = m_queue.size();
                        if (size == 0) {
                            LOG("waiting on packets to arrive");
                            m_cv.wait(lock);
                        }
                    }
                    if (!m_running) {
                        LOG("stop requested, exiting the run method");
                        break;
                    }
                    if (size > 0) {
                        LOG("thread woke up, the queue has " << size << " packets");
                        break;
                    }
                }
            }
            // send packets
            for (size_t i = 0; i < size; ++i) {
                Pair pair;
                {
                    std::unique_lock<std::mutex> lock(m_mutex);
                    pair = m_queue.front();
                    m_queue.pop_front();
                }

                // delay
                if (m_send_delay > 0) {
                    spin(m_send_delay);
                }

                send_packet(Packet(pair.first, pair.second));
            }
        }
    }

#define noop (void)0;

    void spin(uint64_t delay_us)
    {
        auto start = std::chrono::high_resolution_clock::now();
        for (;;) {
            noop;
            auto end = std::chrono::high_resolution_clock::now();
            auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
            if (static_cast<uint64_t>(duration.count()) >= delay_us) {
                break;
            }
        }
    }

#undef noop

    void send_packet(const Packet & packet);

private:
    std::string m_name;
    std::atomic<bool> m_running{false};
    IChannelListener & m_listener;

    uint64_t m_send_delay = SEND_DELAY_US;

    std::thread m_thread;

    std::mutex m_mutex;
    std::condition_variable m_cv;

    Queue m_queue;

    bool m_log_enabled{false};
};

template <>
void ChannelT<LiveChannelType>::send_packet(const Packet & packet)
{
    LOG("sending_packet: " << packet);
    m_listener.on_send_packet(packet);
}

template <>
void ChannelT<ReplayChannelType>::send_packet(const Packet & packet)
{
    LOG("re-sending_packet: " << packet);
    m_listener.on_resend_packet(packet);
}

using LiveChannel = ChannelT<LiveChannelType>;
using ReplayChannel = ChannelT<ReplayChannelType>;

}
