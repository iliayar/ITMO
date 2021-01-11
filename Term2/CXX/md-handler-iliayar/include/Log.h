#pragma once

#include <iostream>
#include <sstream>

#define LOG(msg)                                    \
if (m_log_enabled) {                                \
    std::stringstream ss;                           \
    ss << "[" << m_name << "] " << msg << "\n";     \
    std::cout << std::move(ss).str();               \
}                                                   \

