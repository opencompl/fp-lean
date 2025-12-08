; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fdiv_constant_denominator_fmul_denorm_try_harder_extra_use'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.div roundNearestTiesToEven x (_ +zero 8 24))))
 (let ((?x10 (fp.add roundNearestTiesToEven ?x8 (fp.mul roundNearestTiesToEven ?x8 (_ +zero 8 24)))))
 (and (distinct ?x10 ?x10) true))))
(check-sat)
