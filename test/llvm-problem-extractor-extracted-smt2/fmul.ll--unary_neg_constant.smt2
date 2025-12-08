; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'unary_neg_constant'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x10 (fp.mul roundNearestTiesToEven x (_ +zero 8 24))))
 (let ((?x9 (fp.mul roundNearestTiesToEven (fp.neg x) (_ +zero 8 24))))
 (and (distinct ?x9 ?x10) true))))
(check-sat)
