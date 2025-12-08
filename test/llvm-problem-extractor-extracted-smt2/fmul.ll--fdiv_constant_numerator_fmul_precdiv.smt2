; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fdiv_constant_numerator_fmul_precdiv'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x9 (fp.mul roundNearestTiesToEven (fp.div roundNearestTiesToEven (_ +zero 8 24) x) (_ +zero 8 24))))
 (and (distinct ?x9 ?x9) true)))
(check-sat)
