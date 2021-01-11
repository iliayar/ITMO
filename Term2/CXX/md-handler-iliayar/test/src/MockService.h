#pragma once

#include "IService.h"
#include "MdHandler.h"
#include "Packet.h"

#include <gmock/gmock.h>

namespace md_handler::test {

class MockService : public IService
{
public:
    virtual ~MockService() = default;

    MOCK_METHOD2(resend_messages, void(uint32_t, uint16_t));
    MOCK_METHOD1(handle_message, void(uint32_t));
};

}