#include <cstddef>
#include "symfpu/baseTypes/simpleExecutable.h"
#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/add.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/remainder.h"
#include <bitset>
#include <functional>

using namespace symfpu::simpleExecutable;
typedef symfpu::unpackedFloat<traits> uf;
typedef traits::ubv ubv;
traits::rm modes[] = { 
  // traits::RNA(), 
  traits::RNE()
  // traits::RTN(), 
  // traits::RTP(), 
  // traits::RTZ() 
};

// Note: This fails assertions because symfpu assumes the exponent is shorter than the
// mantissa
void test_rounding(void) {
  // 10-bit E5M4 float
  traits::fpt inFormat(5,5);
  // 8-bit E5M2 float
  traits::fpt outFormat(5,3);
  for (traits::rm mode : modes) {
    for (uint64_t i = 0; i < (1 << 1); i++) {
      traits::ubv packed(10, i);
      uf unpacked(symfpu::unpack<traits>(inFormat, packed));
  
      uf rounded(symfpu::rounder<traits>(outFormat, mode, unpacked));
      traits::ubv repacked(symfpu::pack<traits>(outFormat, rounded));
      printf("%d\n", repacked.contents());
    }
  }
}

std::string to_mode(traits::rm mode) {
  if (mode == traits::RNA()) return "RNA";
  if (mode == traits::RNE()) return "RNE";
  if (mode == traits::RTN()) return "RTN";
  if (mode == traits::RTP()) return "RTP";
  if (mode == traits::RTZ()) return "RTZ";
  return "???";
}

// SymFPU already performs NaN normalisation
std::bitset<8> to_bits(ubv bitvec, bool normNaN = false) {
  std::bitset<8> result;
  uint64_t c = bitvec.contents();
  for (int i = 0; i < 8; i++) {
    result[7-i] = (c >> (7-i)) & 1;
  }
  return result;
}

// Test binary operation on 8 bits.
void test_binop(std::string name, 
  std::function<ubv(traits::rm, ubv, ubv)> f) {
  for (traits::rm mode : modes) {
    for (uint64_t i = 0; i < (1<<8); i++) {
      for (uint64_t j = 0; j < (1<<8); j++) {
          ubv packed1(8, i), packed2(8, j);
          ubv result = f(mode, packed1, packed2);
          std::cout << name << "," << to_mode(mode) << "," << \
              to_bits(packed1) << "," << to_bits(packed2) << "," << \
              to_bits(result, true) << "\n";
      }
    }
  }
}

// Test unary operation on 8 bits.
void test_unop(std::string name, 
  std::function<ubv(traits::rm, ubv)> f) {
  for (traits::rm mode : modes) {
    for (uint64_t i = 0; i < (1<<8); i++) {
        ubv packed1(8, i);
        ubv result = f(mode, packed1);
        std::cout << name << "," << to_mode(mode) << "," << \
            to_bits(packed1) << "," << "00000000" << "," << \
            to_bits(result, true) << "\n";
    }
  }
}

void test_unop_alt(std::string name, 
  std::function<ubv(traits::rm, ubv)> f) {
  for (traits::rm mode : modes) {
    for (uint64_t i = 0; i < (1<<8); i++) {
      for (uint64_t j = 0; j < (1<<8); j++) {
          ubv packed1(8, i), packed2(8, j);
          ubv result = f(mode, packed1);
          std::cout << name << "," << to_mode(mode) << "," << \
              to_bits(packed1) << "," << to_bits(packed2) << "," << \
              to_bits(result, true) << "\n";
      }
    }
  }
}

// Test binary operation on 8 bits (no rounding mode).
void test_binop_noround(std::string name, 
  std::function<ubv(ubv, ubv)> f) {
  for (uint64_t i = 0; i < (1<<8); i++) {
    for (uint64_t j = 0; j < (1<<8); j++) {
        ubv packed1(8, i), packed2(8, j);
        ubv result = f(packed1, packed2);
        std::cout << name << "," << "RNE" << "," << \
            to_bits(packed1) << "," << to_bits(packed2) << "," << \
            to_bits(result, true) << "\n";
    }
  }
}

// Test unary operation on 8 bits (no rounding mode).
void test_unop_noround(std::string name, 
  std::function<ubv(ubv)> f) {
  for (uint64_t i = 0; i < (1<<8); i++) {
      ubv packed1(8, i);
      ubv result = f(packed1);
      std::cout << name << "," << "RNE" << "," << \
          to_bits(packed1) << "," << "00000000" << "," << \
          to_bits(result, true) << "\n";
  }
}

// Test binary predicate on 8 bits.
// We should not need a rounding mode here.
void test_predi(std::string name, 
  std::function<bool(ubv, ubv)> f) {
  for (uint64_t i = 0; i < (1<<8); i++) {
    for (uint64_t j = 0; j < (1<<8); j++) {
        ubv packed1(8, i), packed2(8, j);
        bool result = f(packed1, packed2);
        std::cout << name << "," << "RNE" << "," << \
            to_bits(packed1) << "," << to_bits(packed2) << "," << \
            (result ? 1 : 0) << "\n";
    }
  }
}

traits::fpt e3m4(3,5);
int main() {
  test_unop_noround("abs", [](ubv a) {
    uf ua(symfpu::unpack<traits>(e3m4, a));
    uf uc(symfpu::absolute<traits>(e3m4, ua));
    return symfpu::pack<traits>(e3m4, uc);
  });

  test_binop("add", [](traits::rm mode, ubv a, ubv b) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b));
    
    uf uc(symfpu::add<traits>(e3m4, mode, ua, ub, traits::prop(true)));
    
    return symfpu::pack<traits>(e3m4, uc);
  });

  test_binop("div", [](traits::rm mode, ubv a, ubv b) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b));
    
    uf uc(symfpu::divide<traits>(e3m4, mode, ua, ub));
    
    return symfpu::pack<traits>(e3m4, uc);
  });

  test_predi("lt", [](ubv a, ubv b) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b));
    
    return symfpu::lessThan<traits>(e3m4, ua, ub);
  });
  test_binop_noround("max", [](ubv a, ubv b) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b));
    
    uf uc(symfpu::max<traits>(e3m4, ua, ub, ua.getSign()));
    
    return symfpu::pack<traits>(e3m4, uc);
  });

  test_binop_noround("min", [](ubv a, ubv b) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b));
    
    uf uc(symfpu::min<traits>(e3m4, ua, ub, ua.getSign()));
    
    return symfpu::pack<traits>(e3m4, uc);
  });

  test_binop("mul", [](traits::rm mode, ubv a, ubv b) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b));
    
    uf uc(symfpu::multiply<traits>(e3m4, mode, ua, ub));
    
    return symfpu::pack<traits>(e3m4, uc);
  });

  test_unop_noround("neg", [](ubv a) {
    uf ua(symfpu::unpack<traits>(e3m4, a));
    uf uc(symfpu::negate<traits>(e3m4, ua));
    return symfpu::pack<traits>(e3m4, uc);
  });

  // I think sqrt is actively broken rn
  // test_unop("sqrt", [](traits::rm mode, ubv a) {
  //   uf ua(symfpu::unpack<traits>(e3m4, a));
  //   uf uc(symfpu::sqrt<traits>(e3m4, mode, ua));
  //   return symfpu::pack<traits>(e3m4, uc);
  // });

  test_binop_noround("rem", [](ubv a, ubv b) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b));
    
    uf uc(symfpu::remainder<traits>(e3m4, ua, ub));
    
    return symfpu::pack<traits>(e3m4, uc);
  });

  test_binop("sub", [](traits::rm mode, ubv a, ubv b) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b));
    
    uf uc(symfpu::add<traits>(e3m4, mode, ua, ub, traits::prop(false)));
    
    return symfpu::pack<traits>(e3m4, uc);
  });
  
  // roundToInt is also broken rn
  // test_unop("roundToInt", [](traits::rm mode, ubv a) {
  //   uf ua(symfpu::unpack<traits>(e3m4, a));
  //   uf uc(symfpu::roundToIntegral<traits>(e3m4, mode, ua));
  //   return symfpu::pack<traits>(e3m4, uc);
  // });
  
  return 0;
}

