; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'mul_pos_zero_nnan'
; 
(set-info :status unknown)
(declare-fun a () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.mul roundNearestTiesToEven a (_ +zero 8 24))))
 (and (distinct ?x8 ?x8) true)))
(check-sat)
