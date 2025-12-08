; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'common_factor'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.mul roundNearestTiesToEven x y)))
 (let ((?x9 (fp.mul roundNearestTiesToEven ?x8 x)))
 (let ((?x11 (fp.add roundNearestTiesToEven ?x8 ?x9)))
 (let ((?x10 (fp.add roundNearestTiesToEven ?x9 ?x8)))
 (and (distinct ?x10 ?x11) true))))))
(check-sat)
