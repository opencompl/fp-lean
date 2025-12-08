; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_fdiv_factor_constant1'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 11 53))
(declare-fun x () (_ FloatingPoint 11 53))
(assert
 (let ((?x12 (fp.div roundNearestTiesToEven (fp.mul roundNearestTiesToEven x (fp #b0 #b10000000100 #x5000000000000)) y)))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.div roundNearestTiesToEven x y) (fp #b0 #b10000000100 #x5000000000000))))
 (and (distinct ?x10 ?x12) true))))
(check-sat)
