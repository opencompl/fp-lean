; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fmul_fneg1'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 11 53))
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun pz () (_ FloatingPoint 11 53))
(assert
 (let ((?x15 (fp.mul roundNearestTiesToEven x y)))
 (let ((?x9 (fp.rem (fp #b0 #b10000000100 #x5000000000000) pz)))
 (let ((?x16 (fp.sub roundNearestTiesToEven ?x9 ?x15)))
 (let ((?x13 (fp.mul roundNearestTiesToEven (fp.sub roundNearestTiesToEven (_ -zero 11 53) x) y)))
 (let ((?x14 (fp.add roundNearestTiesToEven ?x9 ?x13)))
 (and (distinct ?x14 ?x16) true)))))))
(check-sat)
