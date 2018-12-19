(in-package "ACL2")
;;
;; It feels like (M)ILP should be within reach.
;;
;; Don't worry .. I'm sure I'll see the error in my ways once I
;; actually try to do it.
;;
;; 1) Use a rational "shadow representation" to determine when new
;;    expressions are within the positive basis and to detect
;;    equalities.
;;
;;    When a base is not within the positive basis, we skew it
;;    and make it a new base.
;;
;;    Integer skews are based on transformations of the form:
;;
;;    | a b | such that ad - bc = +/- 1
;;    | c d |
;;
;;    Rather than rational skews which are of the form:
;;
;;    | 1 0 |
;;    | R 1 |
;;
;;        integer    | rational
;;
;;    b0: ax + by    :   x
;;    b1: cx + dy    :        y
;;
;;  v: A <= Ex + Fy  : -ax + by
;;
;;     In general:
;;
;;     A <= E(x0 + nI + zF) + F(y0 + nJ - zE)
;;     0 <= n
;;
;;     Under:
;;
;;     x = x0 + nI + zF
;;     y = y0 + nJ - zE
;;
;;     Where:
;;
;;     A = E(x0) + F(y0)
;;
;;     I = 1/E % F
;;     J = 1/F % E
;;
;;     Technically we can probably initially ignore x0,y0 
;;     and later incorporate them into 'n'
;;

;; 2) Maintain an integral solution at the intersection of the bases.
;;    When no such solution exists, it should be possible to construct
;;    an auxilliary condition that clips the current intersection and
;;    establishes a new one, relegating one of the existing bases to
;;    the pset.
;;
;; 3) Of course equalities result in a cob and remove a base.
;;
;; 4) 
;;
;; This development will require the following additional concepts:
;;
;; (integer-polyp x)
;; (poly-gcd x)
;; 
;; To do MILP we assign integer polys a lower rank than rational
;; polys.  In other words, rational polys are expressed in terms
;; of integer polys, not the other way around.  Probably easiest
;; to have a split representation:
;;
;; integral polys: (integer-coefficients)
;; rational polys: (integer-coefficients) . (rational-coefficients)
;;
;;
;; .. But, hey, how about we get a working LP first?
;;
