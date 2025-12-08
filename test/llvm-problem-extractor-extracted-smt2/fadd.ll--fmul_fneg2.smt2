; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fmul_fneg2'
; 
(set-info :status unknown)
(declare-fun py () (_ FloatingPoint 11 53))
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun pz () (_ FloatingPoint 11 53))
(assert
 (let ((?x9 (fp.rem (fp #b1 #b10000000100 #x5000000000000) py)))
 (let ((?x17 (fp.mul roundNearestTiesToEven x ?x9)))
 (let ((?x11 (fp.rem (fp #b0 #b10000000100 #x5000000000000) pz)))
 (let ((?x18 (fp.sub roundNearestTiesToEven ?x11 ?x17)))
 (let ((?x15 (fp.mul roundNearestTiesToEven ?x9 (fp.sub roundNearestTiesToEven (_ -zero 11 53) x))))
 (let ((?x16 (fp.add roundNearestTiesToEven ?x11 ?x15)))
 (and (distinct ?x16 ?x18) true))))))))
(check-sat)
