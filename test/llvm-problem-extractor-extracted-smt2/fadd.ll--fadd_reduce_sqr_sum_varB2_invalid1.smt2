; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varB2_invalid1'
; 
(set-info :status unknown)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert
 (let ((?x9 (fp.mul roundNearestTiesToEven a (_ +zero 8 24))))
 (let ((?x13 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven a a) (fp.mul roundNearestTiesToEven b b))))
 (let ((?x16 (fp.add roundNearestTiesToEven ?x13 (fp.mul roundNearestTiesToEven a ?x9))))
 (let ((?x14 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven ?x9 a) ?x13)))
 (and (distinct ?x14 ?x16) true))))))
(check-sat)
