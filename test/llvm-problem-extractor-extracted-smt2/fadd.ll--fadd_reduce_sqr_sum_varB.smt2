; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varB'
; 
(set-info :status unknown)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert
 (let ((?x15 (fp.add roundNearestTiesToEven b a)))
 (let ((?x16 (fp.mul roundNearestTiesToEven ?x15 ?x15)))
 (let ((?x13 (fp.add roundNearestTiesToEven (fp.mul roundNearestTiesToEven a a) (fp.mul roundNearestTiesToEven b b))))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven a b) (_ +zero 8 24))))
 (let ((?x14 (fp.add roundNearestTiesToEven ?x10 ?x13)))
 (and (distinct ?x14 ?x16) true)))))))
(check-sat)
