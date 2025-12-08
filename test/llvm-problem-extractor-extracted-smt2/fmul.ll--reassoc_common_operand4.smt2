; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'reassoc_common_operand4'
; 
(set-info :status unknown)
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert
 (let ((?x9 (fp.div roundNearestTiesToEven x1 (_ +zero 8 24))))
 (let ((?x13 (fp.mul roundNearestTiesToEven y (fp.mul roundNearestTiesToEven ?x9 ?x9))))
 (let ((?x11 (fp.mul roundNearestTiesToEven ?x9 (fp.mul roundNearestTiesToEven y ?x9))))
 (and (distinct ?x11 ?x13) true)))))
(check-sat)
