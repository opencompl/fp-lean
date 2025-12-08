; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'sqrt_squared2'
; 
(set-info :status unknown)
(declare-fun f () (_ FloatingPoint 11 53))
(assert
 (let ((?x7 (fp.sqrt roundNearestTiesToEven f)))
 (let ((?x10 (fp.mul roundNearestTiesToEven f ?x7)))
 (let ((?x9 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven ?x7 ?x7) ?x7)))
 (and (distinct ?x9 ?x10) true)))))
(check-sat)
