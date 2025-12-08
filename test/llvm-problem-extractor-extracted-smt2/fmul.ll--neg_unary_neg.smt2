; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'neg_unary_neg'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x12 (fp.mul roundNearestTiesToEven x y)))
 (let ((?x10 (fp.neg y)))
 (let ((?x11 (fp.mul roundNearestTiesToEven (fp.sub roundNearestTiesToEven (_ +zero 8 24) x) ?x10)))
 (and (distinct ?x11 ?x12) true)))))
(check-sat)
