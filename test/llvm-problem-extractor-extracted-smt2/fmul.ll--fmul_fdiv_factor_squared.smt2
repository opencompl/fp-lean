; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_fdiv_factor_squared'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 11 53))
(declare-fun x () (_ FloatingPoint 11 53))
(assert
 (let ((?x8 (fp.div roundNearestTiesToEven x y)))
 (let ((?x9 (fp.mul roundNearestTiesToEven ?x8 ?x8)))
 (and (distinct ?x9 ?x9) true))))
(check-sat)
