(in-package "ACL2")
;;
;; Perhaps there is a way to focus the representation only on the
;; current counterexample?

;; T + b0 + b1 ... + bK = R

;;   R . bN < 0

;;   T . bN < 0
;;  bi . bN < 0
;;  bj . bN < 0
;;  bk . bN < 0

;; T + b0 + b1 ... + bK + a(bN) = R
;; [T + b0 + b1 ... + bK + a(bN)] bN >= 0
;; [T + b0 + b1 ... + bK + a(bN)] bi >= 0
;; [T + b0 + b1 ... + bK + a(bN)] bj >= 0
;; [T + b0 + b1 ... + bK + a(bN)] bk >= 0

;; Seems like we need merely select a value for alpha that satisfies
;; all of these inequalities.

;; We know that forall (K): R . bK >= 0

;; We will want to keep an inventory of 

;; We thus conclude that a positive value of alpha will always satisfy
;; these inequalities.

;; To expedite processing we will want to preserve the various inner
;; products that we compute.

;; This will also assist with the termination argument.

;; We can compute the inner product of T will all of the bases.

;; Select a negative one.
;;
;;      T
;; (a) b0
;;
;;         b1
;;      T  w1
;; (a) b0  x1

;;         b2
;;      T  w
;; (a) b0  x
;; (a) b1  x

;; As we add new bases, we will want to maintain the inner product of
;; each base with (R)

;;
;; For ease of consumption, skew the bases
;; - maintain orthoganality
;;
;; A base that is completely representable
;;
;; - If it is all negative       -> equality
;; - If it is partially negative -> bijection
;; - If it is all positive       -> ignore
;;
;; Bases with residuals become new bases
;; - and induce new skews
;;
;; Dealing with Bijections:
;;
;;  +<B> : ( +a -b +c -d )
;;  -<B> : ( -a +b -c +d )
;; 
;; If a new basis has non-zero dot product with a bijection:
;;
;; 
;; Argh! I still don't know what to do with "complete" vectors
;; 
;; OK .. I know.
;;
;; Each complete vector is decomposed into two parts: the
;; postive part and the negative part.
;; 
;; The negative set will be added to the "negative basis set"
;; 
;; The positive part will be represented in terms of the
;; negative set.  If it is ever completely represented, 
;; the entire vector must be zero.
;; 
;; Wow.  That is a long way to go just to figure out a 
;; free vector.
;; 
;; Note that no positive coefficients is consistent with
;; a + part that is completely covered (well, because the
;; + part is empty)
;;
;; I'm still not sure whether a single negative component
;; has the same properties as a basis swap.
;;
;;
;; 
