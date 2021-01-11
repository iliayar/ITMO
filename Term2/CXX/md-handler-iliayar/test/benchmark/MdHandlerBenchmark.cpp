#include "BenchmarkService.h"
#include "Channel.h"
#include "MdHandler.h"

#include <benchmark/benchmark.h>

#include <stdexcept>

namespace md_handler::benchmark {

class MdHandlerBenchmark : public ::benchmark::Fixture
{
public:
// static constexpr uint32_t MESSAGES = 100 * 1000 * 1000;
static constexpr uint32_t MESSAGES = 1000 * 1000;

};

BENCHMARK_DEFINE_F(MdHandlerBenchmark, throughput)
(::benchmark::State & state)
{
    size_t delay = state.range(0);
    bool logging = false;

    for (auto __ : state) {

        Service service(MESSAGES);
        MdHandler handler(service);
        ChannelListener channel_listener(handler);

        LiveChannel channel_a("channel_a", channel_listener, delay);
        LiveChannel channel_b("channel_b", channel_listener, delay);

        channel_a.set_logging(logging);
        channel_b.set_logging(logging);

        channel_a.start();
        channel_b.start();

        auto start = std::chrono::high_resolution_clock::now();

        for (uint32_t i = 1; i <= MESSAGES; ++i) {
            channel_a.enqueue(i, 1);
            channel_b.enqueue(i, 1);
        }

        service.wait();

        channel_a.stop();
        channel_b.stop();

        auto end = std::chrono::high_resolution_clock::now();
        auto seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start);
        state.SetIterationTime(seconds.count());
        state.counters["Messages_Sent"] = MESSAGES;
        state.counters["Messages_Received"] = service.get_count();

//        if (service.get_gapped()) {
//            std::stringstream ss;
//            ss << "gap happened, processed " << service.get_count() << " out of " << MESSAGES;
//            throw std::runtime_error(std::move(ss).str());
//        }
    }
}

BENCHMARK_REGISTER_F(MdHandlerBenchmark, throughput)->UseManualTime()
->Arg(1000)->Arg(100)->Arg(10)->Arg(1);

}


BENCHMARK_MAIN();
