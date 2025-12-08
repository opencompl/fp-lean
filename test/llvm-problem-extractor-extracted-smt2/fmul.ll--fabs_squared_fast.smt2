; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fabs_squared_fast'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x9 (fp.mul roundNearestTiesToEven x x)))
 (let ((?x6 (fp.abs x)))
 (let ((?x8 (fp.mul roundNearestTiesToEven ?x6 ?x6)))
 (and (distinct ?x8 ?x9) true)))))
(check-sat)
