; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'unary_neg_unary_neg'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x11 (fp.mul roundNearestTiesToEven x y)))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.neg x) (fp.neg y))))
 (and (distinct ?x10 ?x11) true))))
(check-sat)
