; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'test11'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x9 (fp.add roundNearestTiesToEven x (_ +zero 8 24))))
 (let ((?x12 (fp.add roundNearestTiesToEven ?x9 y)))
 (let ((?x11 (fp.add roundNearestTiesToEven ?x9 (fp.add roundNearestTiesToEven y (_ +zero 8 24)))))
 (and (distinct ?x11 ?x12) true)))))
(check-sat)
