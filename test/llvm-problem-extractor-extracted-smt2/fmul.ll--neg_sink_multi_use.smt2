; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'neg_sink_multi_use'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert
 (let ((?x12 (fp.neg x)))
 (let ((?x14 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven y ?x12) ?x12)))
 (let ((?x9 (fp.sub roundNearestTiesToEven (_ +zero 8 24) x)))
 (let ((?x11 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven ?x9 y) ?x9)))
 (and (distinct ?x11 ?x14) true))))))
(check-sat)
