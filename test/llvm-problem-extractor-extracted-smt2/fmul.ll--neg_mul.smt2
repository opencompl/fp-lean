; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'neg_mul'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert
 (let ((?x11 (fp.neg x)))
 (let ((?x12 (fp.mul roundNearestTiesToEven y ?x11)))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.sub roundNearestTiesToEven (_ +zero 8 24) x) y)))
 (and (distinct ?x10 ?x12) true)))))
(check-sat)
