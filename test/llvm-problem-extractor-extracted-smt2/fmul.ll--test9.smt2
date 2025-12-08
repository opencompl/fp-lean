; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'test9'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x9 (fp.neg x)))
 (let ((?x8 (fp.mul roundNearestTiesToEven x (_ +zero 8 24))))
 (and (distinct ?x8 ?x9) true))))
(check-sat)
