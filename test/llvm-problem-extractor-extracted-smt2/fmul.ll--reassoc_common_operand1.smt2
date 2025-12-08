; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'reassoc_common_operand1'
; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x11 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven x x) y)))
 (let ((?x9 (fp.mul roundNearestTiesToEven (fp.mul roundNearestTiesToEven x y) x)))
 (and (distinct ?x9 ?x11) true))))
(check-sat)
