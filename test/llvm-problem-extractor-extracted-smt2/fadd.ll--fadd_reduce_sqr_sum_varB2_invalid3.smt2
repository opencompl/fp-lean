; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varB2_invalid3'
; 
(set-info :status unknown)
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun a () (_ FloatingPoint 8 24))
(assert
 (let ((?x13 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven a a) (fp.mul roundNearestTiesToEven b b))))
 (let ((?x9 (fp.mul roundNearestTiesToEven b (_ +zero 8 24))))
 (let ((?x16 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven b ?x9) ?x13)))
 (let ((?x14 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven ?x9 b) ?x13)))
 (and (distinct ?x14 ?x16) true))))))
(check-sat)
