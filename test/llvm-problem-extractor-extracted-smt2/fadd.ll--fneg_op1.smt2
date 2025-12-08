; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fneg_op1'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x11 (fp.sub roundNearestTiesToEven x y)))
 (let ((?x10 (fp.add roundNearestTiesToEven x (fp.sub roundNearestTiesToEven (_ +zero 8 24) y))))
 (and (distinct ?x10 ?x11) true))))
(check-sat)
