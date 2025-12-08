; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'unary_neg_mul_multi_use'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert
 (let ((?x7 (fp.neg x)))
 (let ((?x12 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven y ?x7) ?x7)))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven ?x7 y) ?x7)))
 (and (distinct ?x10 ?x12) true)))))
(check-sat)
