; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_fsub_fmul_distribute2'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x8 (fp.mul roundNearestTiesToEven x (_ +zero 8 24))))
 (let ((?x11 (fp.add roundNearestTiesToEven ?x8 (_ +zero 8 24))))
 (let ((?x10 (fp.mul roundNearestTiesToEven (fp.sub roundNearestTiesToEven ?x8 (_ +zero 8 24)) (_ +zero 8 24))))
 (and (distinct ?x10 ?x11) true)))))
(check-sat)
