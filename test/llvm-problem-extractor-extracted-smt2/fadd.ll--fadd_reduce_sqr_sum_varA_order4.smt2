; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varA_order4'
; 
(set-info :status unknown)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert
 (let ((?x14 (fp.add roundNearestTiesToEven b a)))
 (let ((?x15 (fp.mul roundNearestTiesToEven ?x14 ?x14)))
 (let ((?x11 (fp.add roundNearestTiesToEven b (fp.mul roundNearestTiesToEven a (_ +zero 8 24)))))
 (let ((?x13 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven ?x11 b) (fp.mul roundNearestTiesToEven a a))))
 (and (distinct ?x13 ?x15) true))))))
(check-sat)
