; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varB_invalid4'
; 
(set-info :status unknown)
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun a () (_ FloatingPoint 8 24))
(assert
 (let ((?x11 (fp.mul roundNearestTiesToEven b b)))
 (let ((?x8 (fp.mul roundNearestTiesToEven a a)))
 (let ((?x10 (fp.mul roundNearestTiesToEven ?x8 (_ +zero 8 24))))
 (let ((?x14 (fp.add roundNearestTiesToEven ?x10 ?x11)))
 (let ((?x13 (fp.add roundNearestTiesToEven ?x10 (fp.add roundNearestTiesToEven ?x8 ?x11))))
 (and (distinct ?x13 ?x14) true)))))))
(check-sat)
