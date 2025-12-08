; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_reduce_sqr_sum_varA_invalid2'
; 
(set-info :status unknown)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.mul roundNearestTiesToEven a a)))
 (let ((?x10 (fp.mul roundNearestTiesToEven a (_ +zero 8 24))))
 (let ((?x15 (fp.mul roundNearestTiesToEven b (fp.add roundNearestTiesToEven a ?x10))))
 (let ((?x16 (fp.add roundNearestTiesToEven ?x15 ?x8)))
 (let ((?x12 (fp.mul roundNearestTiesToEven (fp.add roundNearestTiesToEven ?x10 a) b)))
 (let ((?x13 (fp.add roundNearestTiesToEven ?x12 ?x8)))
 (and (distinct ?x13 ?x16) true))))))))
(check-sat)
