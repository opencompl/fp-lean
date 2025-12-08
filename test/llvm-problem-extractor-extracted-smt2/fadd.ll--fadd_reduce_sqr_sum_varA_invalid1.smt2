; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varA_invalid1'
; 
(set-info :status unknown)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert
 (let ((?x11 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven a (_ +zero 8 24)) b)))
 (let ((?x15 (fp.mul roundNearestTiesToEven (fp.add roundNearestTiesToEven ?x11 a) a)))
 (let ((?x13 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven ?x11 a) (fp.mul roundNearestTiesToEven a a))))
 (and (distinct ?x13 ?x15) true)))))
(check-sat)
