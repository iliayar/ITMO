#include "MdHandler.h"

#include "Channel.h"
#include "MockService.h"
#include "Packet.h"

#include <gtest/gtest.h>

#include <vector>

using ::testing::Exactly;

namespace md_handler::test {

namespace {

enum class Channel
{
    A,
    B
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

class MdHandlerTest : public ::testing::Test
{
using TestPacket = std::pair<uint32_t, uint16_t>;
using TestPackets = std::vector<TestPacket>;

public:
    MdHandlerTest()
        : m_mock_service()
        , m_handler(m_mock_service)
        , m_channel_listener(m_handler)
        , m_channel_a("channel_a", m_channel_listener)
        , m_channel_b("channel_b", m_channel_listener)
        , m_replay_channel("replay_channel", m_channel_listener)
    {
        m_channel_a.start();
        m_channel_b.start();
        m_replay_channel.start();
    }

    ~MdHandlerTest()
    {
        m_channel_a.stop();
        m_channel_b.stop();
        m_replay_channel.stop();
    }

    void TearDown() final
    {
        // hold the test execution to have the channel complete execution
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    }

protected:

    void send_packets(Channel channel, const TestPackets & test_packets)
    {
        switch(channel) {
        case Channel::A:
            enqueue_packets(m_channel_a, test_packets);
            break;
        case Channel::B:
            enqueue_packets(m_channel_b, test_packets);
            break;
        default:
            break;
        }
    }

    void expect_messages(const uint32_t start_seq_num, const uint32_t end_seq_num)
    {
        uint32_t seq_num = start_seq_num;
        while (seq_num <= end_seq_num) {
            EXPECT_CALL(m_mock_service, handle_message(seq_num++))
                .Times(Exactly(1));
        }
    }

    void expect_resend_request(uint32_t start_seq_num, uint16_t msg_count)
    {
        EXPECT_CALL(m_mock_service, resend_messages(start_seq_num, msg_count))
                .Times(Exactly(1));

        ON_CALL(m_mock_service, resend_messages(start_seq_num, msg_count))
                .WillByDefault([this, seq_num=start_seq_num, count=msg_count]() {
                    resend_messages(seq_num, count);
                });
    }

private:
    void resend_messages(uint32_t start_seq_num, uint16_t msg_count)
    {
        uint32_t seq_num = start_seq_num;
        uint32_t end_seq_num = start_seq_num + msg_count;
        uint16_t count = 1;

        while (seq_num < end_seq_num) {
            m_replay_channel.enqueue(seq_num, count);
            seq_num += count;
        }
    }

    template <typename Channel>
    void enqueue_packets(Channel & channel, const TestPackets & test_packets)
    {
        for (auto & [seq_num, msg_count] : test_packets) {
            channel.enqueue(seq_num, msg_count);
        }
    }

private:
    MockService m_mock_service;
    MdHandler m_handler;
    ChannelListener m_channel_listener;

    LiveChannel m_channel_a;
    LiveChannel m_channel_b;
    ReplayChannel m_replay_channel;
};

TEST_F(MdHandlerTest, no_gaps)
{
    expect_messages(1, 3); // range 1-3

    send_packets(Channel::A, {{1, 1}, {2, 1}, {3, 1}});
}

TEST_F(MdHandlerTest, redundant)
{
    expect_messages(1, 3); // range 1-3

    send_packets(Channel::A, {{1, 1}, {2, 1}, {3, 1}});
    send_packets(Channel::B, {{1, 1}, {2, 1}, {3, 1}});
}

TEST_F(MdHandlerTest, different_packaging)
{
    expect_messages(1, 4); // range 1-4

    send_packets(Channel::A, {{1, 1}, {2, 3}});
    send_packets(Channel::B, {{1, 3}, {4, 1}});
}

TEST_F(MdHandlerTest, heart_beat)
{
    expect_messages(1, 3); // range 1-3

    send_packets(Channel::A, {{1, 1}, {1, 0}, {2, 2}});
}

TEST_F(MdHandlerTest, heart_beats)
{
    expect_messages(1, 4); // range 1-4

    send_packets(Channel::A, {{1, 1}, {1, 0}, {2, 2}, {3, 0}, { 4, 1}});
}

TEST_F(MdHandlerTest, gap_at_start)
{
    expect_resend_request(1, 9);
    expect_messages(1, 12); // range 1-12

    send_packets(Channel::A, {{10, 1}, {11, 1}, {12, 1}});
}

TEST_F(MdHandlerTest, gap_in_middle)
{
    expect_resend_request(3, 8);
    expect_messages(1, 12); // range 1-12

    send_packets(Channel::A, {{1, 1}, {2, 1}, {10, 0}, {11, 1}, {12, 1}});
}

TEST_F(MdHandlerTest, multiple_gaps)
{
    expect_resend_request(1, 10);
    expect_resend_request(11, 10);

    expect_messages(1, 22); // range 1-22

    send_packets(Channel::A, {{10, 0}, {20, 0}, {21, 1}, {22, 1}});
}

TEST_F(MdHandlerTest, out_of_order)
{
    expect_resend_request(1, 2);
    expect_messages(1, 3); // range 1-3

    send_packets(Channel::A, {{2, 0}, {1, 0}, {2, 1}, {3, 1}});
}

TEST_F(MdHandlerTest, out_of_order_no_resend)
{
    expect_messages(1, 3); // range 1-3

    send_packets(Channel::A, {{2, 0}, {1, 1}, {2, 1}, {3, 1}});
    send_packets(Channel::B, {{1, 1}, {2, 1}, {2, 0}, {3, 1}});
}

TEST_F(MdHandlerTest, out_of_order_with_gap)
{
    expect_resend_request(1, 3);
    expect_resend_request(4, 7);

    expect_messages(1, 13); // range 1-13

    send_packets(Channel::A, {{3, 0}, {1, 1}, {2, 2}, {3, 0}, {10, 0}, {11, 3}});
    send_packets(Channel::B, {{3, 0}, {3, 0}, {3, 0}, {3, 0}, {10, 0}, {13, 0}});
}

TEST_F(MdHandlerTest, gap_closed_by_itself)
{
    expect_messages(1, 3); // range 1-3

    // for gaps of 1 message, the application should wait a while for the gap
    // to close from another channel, or while the gap has become more than 1 messages
    // gap for heartbeat (3, 0), should be closed automatically
    // from  channel B Packet(3, 1)
    send_packets(Channel::A, {{1, 1}, {2, 1}, {3, 0}, {3, 0}});
    send_packets(Channel::B, {{1, 1}, {2, 1}, {3, 1}, {3, 0}});
}

}
