; SMT-LIB extracted from file '../../llvm-project/llvm/test/Transforms/InstCombine/fmul.ll' from function 'fmul_fadd_fdiv_distribute2'
; 
(set-info :status unknown)
(declare-fun x () (_ FloatingPoint 11 53))
(assert
 (let ((?x16 (fp.add roundNearestTiesToEven (fp.div roundNearestTiesToEven x (fp #b0 #b11111111110 #x8000000000000)) (fp #b0 #b00000000011 #x4000000000000))))
 (let ((?x10 (fp.add roundNearestTiesToEven (fp.div roundNearestTiesToEven x (fp #b0 #b10000000000 #x8000000000000)) (fp #b0 #b10000000001 #x4000000000000))))
 (let ((?x12 (fp.mul roundNearestTiesToEven ?x10 (fp #b0 #b00000000001 #x0000000000000))))
 (and (distinct ?x12 ?x16) true)))))
(check-sat)
