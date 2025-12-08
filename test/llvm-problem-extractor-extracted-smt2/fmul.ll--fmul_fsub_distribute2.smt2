; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_fsub_distribute2'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 8 24))
(assert
 (let ((?x10 (fp.mul roundNearestTiesToEven x (_ +zero 8 24))))
 (let ((?x11 (fp.sub roundNearestTiesToEven (_ +zero 8 24) ?x10)))
 (let ((?x9 (fp.mul roundNearestTiesToEven (fp.sub roundNearestTiesToEven (_ +zero 8 24) x) (_ +zero 8 24))))
 (and (distinct ?x9 ?x11) true)))))
(check-sat)
