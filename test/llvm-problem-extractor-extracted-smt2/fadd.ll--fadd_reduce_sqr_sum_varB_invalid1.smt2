; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varB_invalid1'
; 
(set-info :status unknown)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert
 (let ((?x11 (fp.mul roundNearestTiesToEven a a)))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven a b) (_ +zero 8 24))))
 (let ((?x15 (fp.add roundNearestTiesToEven ?x10 ?x11)))
 (let ((?x13 (fp.add roundNearestTiesToEven ?x11 (fp.mul roundNearestTiesToEven b a))))
 (let ((?x14 (fp.add roundNearestTiesToEven ?x10 ?x13)))
 (and (distinct ?x14 ?x15) true)))))))
(check-sat)
