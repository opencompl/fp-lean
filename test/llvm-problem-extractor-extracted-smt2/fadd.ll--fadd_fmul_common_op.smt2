; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fadd.ll' from function 'fadd_fmul_common_op'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.mul roundNearestTiesToEven x (_ +zero 8 24))))
 (let ((?x9 (fp.add roundNearestTiesToEven ?x8 x)))
 (and (distinct ?x9 ?x8) true))))
(check-sat)
