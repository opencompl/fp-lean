; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_fdivs_factor'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 11 53))
(declare-fun w () (_ FloatingPoint 11 53))
(declare-fun z () (_ FloatingPoint 11 53))
(declare-fun x () (_ FloatingPoint 11 53))
(assert
 (let ((?x14 (fp.div roundNearestTiesToEven (fp.mul roundNearestTiesToEven x z) w)))
 (let ((?x15 (fp.div roundNearestTiesToEven ?x14 y)))
 (let ((?x12 (fp.mul roundNearestTiesToEven (fp.div roundNearestTiesToEven x y) (fp.div roundNearestTiesToEven z w))))
 (and (distinct ?x12 ?x15) true)))))
(check-sat)
