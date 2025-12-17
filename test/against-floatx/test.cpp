#include "floatx.hpp"
#include <iostream>
#include <functional>
#include <cmath>
#include <cstdlib>

typedef flx::floatx<5,2> e5m2;
typedef flx::float_traits<e5m2>::backend_float bf;

e5m2 cons_fp8(uint8_t arg) {
    return flx::detail::construct_number<5,2>(std::bitset<8>(arg));
}

constexpr std::bitset<8> nanBits{0b01111110};
std::bitset<8> to_bits(e5m2 arg, bool normNaN = false) {
    std::bitset<8> argBits = flx::detail::get_fullbit_representation_BS<5,2>(bf(arg));
    if (normNaN && 
        ((argBits.to_ulong() >> 2) & 0b11111) == 0b11111 && 
        ((argBits.to_ulong() & 3) != 0)) {
        return nanBits;
    }
    return argBits;
}

void test_unop(std::string name, std::function<e5m2(e5m2)> f, std::string mode = "RNE") {
    for (uint16_t i = 0; i < (1 << 8); i++) {
        e5m2 a = cons_fp8(static_cast<uint8_t>(i));
        e5m2 c = f(a);
        std::cout << name << "," << mode << "," << \
            to_bits(a) << "," << "00000000" << "," << \
            to_bits(c, true) << "\n";
    }
}

void test_unop_alt(std::string name, std::function<e5m2(e5m2)> f, std::string mode = "RNE") {
    for (uint16_t i = 0; i < (1<<8); i++) {
        for (uint16_t j = 0; j < (1<<8); j++) {
            e5m2 a = cons_fp8(static_cast<uint8_t>(i));
            e5m2 b = cons_fp8(static_cast<uint8_t>(j));
            e5m2 c = f(a);
            std::cout << name << "," << "RNE" << "," << \
                to_bits(a) << "," << to_bits(b) << "," << \
                to_bits(c, true) << "\n";
        }
    }
}

void test_binop(std::string name, std::function<e5m2(e5m2,e5m2)> f) {
    for (uint16_t i = 0; i < (1<<8); i++) {
        for (uint16_t j = 0; j < (1<<8); j++) {
            e5m2 a = cons_fp8(static_cast<uint8_t>(i));
            e5m2 b = cons_fp8(static_cast<uint8_t>(j));
            e5m2 c = f(a,b);
            std::cout << name << "," << "RNE" << "," << \
                to_bits(a) << "," << to_bits(b) << "," << \
                to_bits(c, true) << "\n";
        }
    }
}

void test_predi(std::string name, std::function<bool(e5m2,e5m2)> f) {
    for (uint16_t i = 0; i < (1<<8); i++) {
        for (uint16_t j = 0; j < (1<<8); j++) {
            e5m2 a = cons_fp8(static_cast<uint8_t>(i));
            e5m2 b = cons_fp8(static_cast<uint8_t>(j));
            bool c = f(a,b);
            std::cout << name << "," << "RNE" << "," << \
                to_bits(a) << "," << to_bits(b) << "," << \
                (c ? "1" : "0") << "\n";
        }
    }
}

e5m2 ieee_max(e5m2 a, e5m2 b) {
    long double a2 = static_cast<long double>(a);
    long double b2 = static_cast<long double>(b);
    // Enforce that max(+0, -0) = +0
    if (a2 == 0 && b2 == 0) {
        if (std::signbit(a2))
            return b;
        return a;
    }
    return fmax(a2, b2);
}

e5m2 ieee_min(e5m2 a, e5m2 b) {
    long double a2 = static_cast<long double>(a);
    long double b2 = static_cast<long double>(b);
    // Enforce that min(+0, -0) = -0
    if (a2 == 0 && b2 == 0) {
        if (std::signbit(a2))
            return a;
        return b;
    }
    return fmin(a2, b2);
}


int main() {
    test_unop("abs", [](e5m2 a) { return std::fabs(static_cast<long double>(a)); });
    test_binop("add", [](e5m2 a, e5m2 b) { return a + b; });
    test_binop("div", [](e5m2 a, e5m2 b) { return a / b; });
    test_predi("lt" , [](e5m2 a, e5m2 b) { return a < b; });
    test_binop("max", [](e5m2 a, e5m2 b) { return ieee_max(a,b); });
    test_binop("min", [](e5m2 a, e5m2 b) { return ieee_min(a,b); });
    test_binop("mul", [](e5m2 a, e5m2 b) { return a * b; });
    test_unop("neg", [](e5m2 a) { return 0 - a; });
    test_binop("rem", [](e5m2 a, e5m2 b) { return remainderl(static_cast<long double>(a), static_cast<long double>(b)); });
    test_unop("roundToInt", [](e5m2 a) { return std::round(static_cast<long double>(a)); }, "RNA");
    test_unop("roundToInt", [](e5m2 a) { return rintl(static_cast<long double>(a)); });
    test_unop("sqrt", [](e5m2 a) { return sqrt(static_cast<long double>(a)); });
    test_binop("sub", [](e5m2 a, e5m2 b) { return a - b; });
    return 0;
}
