; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_constant_reassociation'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.mul roundNearestTiesToEven x (_ +zero 8 24))))
 (let ((?x9 (fp.mul roundNearestTiesToEven ?x8 (_ +zero 8 24))))
 (and (distinct ?x9 ?x8) true))))
(check-sat)
