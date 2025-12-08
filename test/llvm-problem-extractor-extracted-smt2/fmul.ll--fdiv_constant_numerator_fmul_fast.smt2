; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fdiv_constant_numerator_fmul_fast'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.div roundNearestTiesToEven (_ +zero 8 24) x)))
 (let ((?x9 (fp.mul roundNearestTiesToEven ?x8 (_ +zero 8 24))))
 (and (distinct ?x9 ?x8) true))))
(check-sat)
