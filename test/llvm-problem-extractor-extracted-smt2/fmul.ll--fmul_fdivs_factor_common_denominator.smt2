; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_fdivs_factor_common_denominator'
; 
(set-info :status unknown)
(declare-fun z () (_ FloatingPoint 11 53))
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun y () (_ FloatingPoint 11 53))
(assert
 (let ((?x14 (fp.div roundNearestTiesToEven (fp.mul roundNearestTiesToEven y x) (fp.mul roundNearestTiesToEven z z))))
 (let ((?x11 (fp.mul roundNearestTiesToEven (fp.div roundNearestTiesToEven x z) (fp.div roundNearestTiesToEven y z))))
 (and (distinct ?x11 ?x14) true))))
(check-sat)
