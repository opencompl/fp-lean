; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'neg_neg_nsz'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x12 (fp.mul roundNearestTiesToEven x y)))
 (let ((?x11 (fp.mul roundNearestTiesToEven (fp.sub roundNearestTiesToEven (_ +zero 8 24) x) (fp.sub roundNearestTiesToEven (_ +zero 8 24) y))))
 (and (distinct ?x11 ?x12) true))))
(check-sat)
