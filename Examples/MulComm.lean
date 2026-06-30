import Fp

namespace Example
theorem mul_comm (x y : PackedFloat 5 2) : x * y = y * x := by
    bv_decide
end Example
