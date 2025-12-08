; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_fsub_fmul_distribute'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.mul roundNearestTiesToEven x (_ +zero 8 24))))
 (let ((?x9 (fp.sub roundNearestTiesToEven (_ +zero 8 24) ?x8)))
 (let ((?x10 (fp.mul roundNearestTiesToEven ?x9 (_ +zero 8 24))))
 (and (distinct ?x10 ?x9) true)))))
(check-sat)
