; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fabs_fabs'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x12 (fp.abs (fp.mul roundNearestTiesToEven x y))))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.abs x) (fp.abs y))))
 (and (distinct ?x10 ?x12) true))))
(check-sat)
