; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varA_invalid3'
; 
(set-info :status unknown)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.mul roundNearestTiesToEven a a)))
 (let ((?x11 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven a (_ +zero 8 24)) b)))
 (let ((?x15 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven b ?x11) ?x8)))
 (let ((?x13 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven ?x11 b) ?x8)))
 (and (distinct ?x13 ?x15) true))))))
(check-sat)
