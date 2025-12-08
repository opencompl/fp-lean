; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varB_invalid3'
; 
(set-info :status unknown)
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun a () (_ FloatingPoint 8 24))
(assert
 (let ((?x13 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven a a) (fp.mul roundNearestTiesToEven b b))))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven a b) (_ +zero 8 24))))
 (let ((?x14 (fp.add roundNearestTiesToEven ?x10 ?x13)))
 (and (distinct ?x14 ?x14) true)))))
(check-sat)
