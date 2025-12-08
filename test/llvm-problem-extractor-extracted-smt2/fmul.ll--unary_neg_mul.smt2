; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'unary_neg_mul'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert
 (let ((?x7 (fp.neg x)))
 (let ((?x10 (fp.mul roundNearestTiesToEven y ?x7)))
 (let ((?x9 (fp.mul roundNearestTiesToEven ?x7 y)))
 (and (distinct ?x9 ?x10) true)))))
(check-sat)
