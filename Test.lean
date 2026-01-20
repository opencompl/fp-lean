import Fp

structure OpResult where
  oper : String
  mode : RoundingMode
  result : List String

structure FP8Format where
  e : Nat
  m : Nat
  h8 : 1 + e + m = 8

namespace FP8Format
theorem h (f : FP8Format)
  : BitVec (1 + f.e + f.m) = BitVec 8 := by simp only [f.h8]
end FP8Format

def toDigits (b : BitVec n) : String :=
  let b' := b.reverse
  String.join ((List.finRange n).map (fun i => b'[i].toNat.digitChar.toString))

instance : Repr OpResult where
  reprPrec res _ :=
    let joinedResults := String.intercalate "," (res.result)
    f!"{res.oper},{repr res.mode},{joinedResults}"

def allRoundingModes : List RoundingMode :=
  [.RNA, .RNE, .RTN, .RTP, .RTZ]

def test_add (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "add"
    mode := m
    result := [a, b, f.h.mp (add a' b' m).toBits].map toDigits
  }

def test_sub (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "sub"
    mode := m
    result := [a, b, f.h.mp (sub a' b' m).toBits].map toDigits
  }

def test_div (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "div"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.div m a' b' ).toBits].map toDigits
  }

def test_mul (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "mul"
    mode := m
    result := [a, b, f.h.mp (PackedFloat.mul m a' b').toBits].map toDigits
  }

def test_lt (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "lt"
    mode := m
    result := [a, b].map toDigits ++ [(lt a' b').toNat.digitChar.toString]
  }

def test_min (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "min"
    mode := m
    result := [a, b, f.h.mp (flt_min a' b').toBits].map toDigits
  }

def test_max (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "max"
    mode := m
    result := [a, b, f.h.mp (flt_max a' b').toBits].map toDigits
  }

def test_neg (f : FP8Format) (m : RoundingMode) (a : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  {
    oper := "neg"
    mode := m
    result := [a, 0#8, f.h.mp (PackedFloat.toBits (neg a'))].map toDigits
  }

def test_abs (f : FP8Format) (m : RoundingMode) (a : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  {
    oper := "abs"
    mode := m
    result := [a, 0#8, f.h.mp (PackedFloat.toBits (abs a'))].map toDigits
  }

def test_roundToInt (f : FP8Format) (m : RoundingMode) (a : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  {
    oper := "roundToInt"
    mode := m
    result := [a, 0#8, f.h.mp (PackedFloat.toBits (roundToInt m a'))].map toDigits
  }

def test_sqrt (f : FP8Format) (m : RoundingMode) (a : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  {
    oper := "sqrt"
    mode := m
    result := [a, 0#8, f.h.mp (PackedFloat.toBits (sqrt a' m))].map toDigits
  }

def test_rem (f : FP8Format) (m : RoundingMode) (a b : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  {
    oper := "rem"
    mode := m
    result := [a, b, f.h.mp (remainder a' b').toBits].map toDigits
  }

def test_binop (f : RoundingMode → BitVec 8 → BitVec 8 → OpResult) : Thunk (List OpResult) :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).flatMap (fun a =>
      (List.range (2 ^ 8)).map (fun b =>
        f m (BitVec.ofNat 8 a) (BitVec.ofNat 8 b)
      )
    )
  )

def test_unop (f : RoundingMode → BitVec 8 → OpResult) : Thunk (List OpResult) :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).map (fun a => f m (BitVec.ofNat 8 a))
  )

def test_unop_multi (f : RoundingMode → BitVec 8 → OpResult) : Thunk (List OpResult) :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).flatMap (fun a =>
      (List.range (2 ^ 8)).map (fun _b =>
        f m (BitVec.ofNat 8 a)
      )
    )
  )

def test_all (f : FP8Format) : Thunk (List OpResult) :=
  List.flatten [
    Thunk.get $ test_unop  $ test_abs f,
    Thunk.get $ test_binop $ test_add f,
    Thunk.get $ test_binop $ test_div f,
    Thunk.get $ test_binop $ test_lt f,
    Thunk.get $ test_binop $ test_max f,
    Thunk.get $ test_binop $ test_min f,
    Thunk.get $ test_binop $ test_mul f,
    Thunk.get $ test_unop  $ test_neg f,
    Thunk.get $ test_binop $ test_rem f,
    Thunk.get $ test_unop  $ test_roundToInt f,
    Thunk.get $ test_unop  $ test_sqrt f,
    Thunk.get $ test_binop $ test_sub f
  ]

def test_fma (f : FP8Format) (m : RoundingMode) (a b c : BitVec 8) : OpResult :=
  let a' := PackedFloat.ofBits f.e f.m (f.h.mpr a)
  let b' := PackedFloat.ofBits f.e f.m (f.h.mpr b)
  let c' := PackedFloat.ofBits f.e f.m (f.h.mpr c)
  {
    oper := "fma"
    mode := m
    result := [a, b, c, f.h.mp (fma a' b' c' m).toBits].map toDigits
  }

def test_ternop (f : RoundingMode → BitVec 8 → BitVec 8 → BitVec 8 → OpResult) (_ : Unit) : Thunk (List OpResult) :=
  allRoundingModes.flatMap (fun m =>
    (List.range (2 ^ 8)).flatMap (fun a =>
      (List.range (2 ^ 8)).flatMap (fun b =>
        (List.range (2 ^ 8)).map (fun c =>
          f m (BitVec.ofNat 8 a) (BitVec.ofNat 8 b) (BitVec.ofNat 8 c)
        )
      )
    )
  )

def e5m2 : FP8Format where
  e := 5
  m := 2
  h8 := by omega

def e3m4 : FP8Format where
  e := 3
  m := 4
  h8 := by omega

def get_long_operation (arg : String) : Thunk (List OpResult) :=
  match arg with
  | "e5m2" => test_all e5m2
  | "e3m4" => test_all e3m4
  | "fma_e5m2"  => test_ternop (test_fma e5m2) ()
  | "fma_e3m4"  => test_ternop (test_fma e3m4) ()
  | "abs" => test_unop_multi $ (test_abs e3m4)
  | "add" => test_binop $ (test_add e3m4)
  | "div" => test_binop $ (test_div e3m4)
  | "lt" => test_binop $ (test_lt e3m4)
  | "max" => test_binop $ (test_max e3m4)
  | "min" => test_binop $ (test_min e3m4)
  | "mul" => test_binop $ (test_mul e3m4)
  | "neg" => test_unop_multi $ (test_neg e3m4)
  | "rem" => test_binop $ (test_rem e3m4)
  | "sqrt" => test_unop_multi $ (test_sqrt e3m4)
  | "sub" => test_binop $ (test_sub e3m4)
  | "roundToInt" => test_unop_multi $ (test_roundToInt e3m4)
  | _ => Thunk.pure []

def main (args : List String) : IO Unit := do
  for arg in args do
    for res in Thunk.get (get_long_operation arg) do
      IO.println (repr res)
  if args = [] then
    IO.println "Please provide an argument specifying the operation set to test."

/-- info: { sign := -, ex := 0x04#5, sig := 0x1#2 } -/
#guard_msgs in #eval add (PackedFloat.ofBits 5 2 0b00000011#8) (PackedFloat.ofBits 5 2 0b10010001#8) .RNE
/-- info: { sign := +, ex := 0x01#5, sig := 0x2#2 } -/
#guard_msgs in #eval EFixedPoint.round 5 2 .RNE (PackedFloat.toEFixed {sign := false, ex := 1#5, sig := 2#2})
/-- info: { sign := +, ex := 0x1f#5, sig := 0x2#2 } -/
#guard_msgs in #eval PackedFloat.mul .RTZ (PackedFloat.getZero 5 2) (PackedFloat.getInfinity 5 2 true)
/-- info: { sign := +, ex := 0x1f#5, sig := 0x0#2 } -/
#guard_msgs in #eval PackedFloat.div .RTZ oneE5M2 (PackedFloat.getZero 5 2)
/-- info: { sign := +, ex := 0x00#5, sig := 0x1#2 } -/
#guard_msgs in #eval PackedFloat.mul .RNE (PackedFloat.ofBits 5 2 0b00000001#8) (PackedFloat.ofBits 5 2 0b00111001#8)
