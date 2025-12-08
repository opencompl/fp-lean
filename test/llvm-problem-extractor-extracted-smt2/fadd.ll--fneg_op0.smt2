; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fneg_op0'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert
 (let ((?x11 (fp.sub roundNearestTiesToEven y x)))
 (let ((?x10 (fp.add roundNearestTiesToEven (fp.sub roundNearestTiesToEven (_ +zero 8 24) x) y)))
 (and (distinct ?x10 ?x11) true))))
(check-sat)
