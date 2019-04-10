(in-package "ACL2")

(include-book "convex")
(include-book "all")

(def::un split-bases-rec (vector bases nbases zbases pbases)
  (declare (xargs :signature ((poly-p poly-listp poly-listp poly-listp poly-listp) 
                              poly-listp poly-listp poly-listp)
                  :congruence ((poly-equiv poly-list-equiv poly-list-equiv poly-list-equiv poly-list-equiv) 
                               poly-list-equiv poly-list-equiv poly-list-equiv)))
  (if (not (consp bases)) (mvlist nbases zbases pbases)
    (let ((base (poly-fix (car bases))))
      (let ((score (dot vector base)))
        (if (< score 0) (split-bases-rec vector (cdr bases) (cons base nbases) zbases pbases)
          (if (< 0 score) (split-bases-rec vector (cdr bases) nbases zbases (cons base pbases))
            (split-bases-rec vector (cdr bases) nbases (cons base zbases) pbases)))))))

(defmacro split (vector bases &key (nset 'nil) (zset 'nil) (pset 'nil))
  `(split-bases-rec ,vector ,bases ,nset ,zset ,pset))

;; The vector needs to be non-negative w/to *all* bases
;; - when we add a base, we cannot make any existing base (-)
;;
;; In other words, we have:
;;
;; V' = V0 + B0 + B1 + B2
;;
;; We can decompose the bases relative to each other.
;; 
;; B0 =      b0
;; B1 =  a01*b0 +     b1
;; B2 =  a02*b0 + a12*b1 +     b2
;; 
;;  V =   x0*B0 +  x1*B1 +  x2*B2 + V'
;;
;; B3 =   y0*B0 +  y1*B1 +  y2*B2 + b3
;; 
;; B3 has a (-) dot product with V'
;;
;; - if (b3 = <0>)
;;
;;   o You need to add more of one or more Bi
;; 
;;   o Perhaps you should replace one of the bases?
;; 
;;    V =   -  B0 -   8*B1 -   3*B2 + V'
;;
;;   B3 =    2*B0 -   1*B1 +   1*B2
;;
;;    V =    5*B0 -  11*B1          + V'
;;
;; Consider organizing the bases from (-) to (0) to (+) w/to vector
;; - We never want to make a (0) negative.
;;   o we can make it (+)
;;
;; - Choose a (-) vector
;; - Split the zero basis set 
;;
;; While (-) bases exist:
;;  1) Select a (-) basis
;;  2) find a residual vector that is non-negative w/to the zero basis set.
;;  3) add as much of the residual as possible until either
;;     a) all bases are non-negative
;;     b) A (+) basis becomes (0), goto 2

;; The nset should be getting smaller

;; I think you need to compute *all* of the possible residuals ..
;; and then add them together.

(def::un maximum-nneg-coeff (residual bprime coeff pset zres pres)
  (declare (xargs :signature ((poly-p poly-p rationalp poly-listp poly-listp poly-listp) rationalp poly-listp poly-listp)
                  :measure (len pset)
                  :congruence ((poly-equiv poly-equiv rfix-equiv poly-list-equiv nil nil)
                               equal equal equal)))
  (let ((coeff (rfix coeff))
        (zres  (poly-list-fix zres))
        (pres  (poly-list-fix pres))
        )
    ;;(if (zerop coeff) (mvlist coeff (append zres pres) nil)
    (if (not (consp pset)) (mvlist coeff zres pres)
      (let ((base     (poly-fix (car pset)))
            (residual (poly-fix residual))
            (bprime   (poly-fix bprime)))
        (let ((c1 (coeff bprime   base)))
          (if (<= 0 c1) (maximum-nneg-coeff residual bprime coeff (cdr pset) zres (cons base pres))
            (let ((c0 (coeff residual base)))
              ;; 0 <= (r + (- c)*prime) o base
              ;; 0 <= r*base + (- c)*prime*base
              ;; (- r*base)/(prime*base) <= (- c)
              (let ((coeff1 (/ c0 (- c1))))
                (cond
                 ((< coeff1 coeff) 
                  (maximum-nneg-coeff residual bprime coeff1 (cdr pset) (list base) (append zres pres)))
                 ((= coeff1 coeff)
                  (maximum-nneg-coeff residual bprime coeff (cdr pset) (cons base zres) pres))
                 (t
                  (maximum-nneg-coeff residual bprime coeff (cdr pset) zres (cons base pres))))))))))))

(def::signature maximum-nneg-coeff (t t t t t t) rationalp poly-listp poly-listp)

(defthm maximum-nneg-coeff-upper-bound
  (implies
   (and
    (all-positive (dot-list residual pset))
    (rationalp coeff)
    (<= 0 coeff))
   (<= (val 0 (maximum-nneg-coeff residual bprime coeff pset zres pres)) coeff))
  :rule-classes (:rewrite
                 :linear
                 (:forward-chaining :trigger-terms ((maximum-nneg-coeff residual bprime coeff pset zres pres))))
  :hints (("Goal" :induct (maximum-nneg-coeff residual bprime coeff pset zres pres)
           :in-theory (enable coeff)
           :do-not-induct t)))

 (defthm maximum-nneg-coeff-lower-bound
   (implies
    (and
     (all-positive (dot-list residual pset))
     (rationalp coeff)
     (<= 0 coeff))
    (<= 0 (val 0 (maximum-nneg-coeff residual bprime coeff pset zres pres))))
   :rule-classes (:rewrite
                  :linear
                 (:forward-chaining :trigger-terms ((maximum-nneg-coeff residual bprime coeff pset zres pres))))
  :hints (("Goal" :induct (maximum-nneg-coeff residual bprime coeff pset zres pres)
           :in-theory (enable coeff)
           :do-not-induct t)))

(defthm all-nonnegative-maximum-nneg-coeff
  (implies
   (and
    (all-positive (dot-list residual pset))
    (rationalp coeff)
    (<= 0 coeff))
   (all-non-negative (dot-list (add residual (scale bprime (val 0 (maximum-nneg-coeff residual bprime coeff pset zres pres)))) pset)))
  :hints (("Goal" :induct (maximum-nneg-coeff residual bprime coeff pset zres pres)
           :do-not '(generalize)
           :in-theory (enable coeff <---promote-denominators coeff <-+-promote-denominators)
           :nonlinearp t
           :do-not-induct t)))

(defthm all-zero-to-all-positive
  (implies
   (and
    (all-zero (dot-list (add residual (scale bprime coeff)) zres))
    (all-positive (dot-list residual zres))
    (all-negative (dot-list bprime zres))
    (rationalp coeff)
    (rationalp coeff1)
    (case-split (< coeff1 coeff))
    )
   (all-positive (dot-list (add residual (scale bprime coeff1)) zres)))
  :hints (("Goal" :nonlinearp t)))

(defthm all-positive-to-all-positive
  (implies
   (and
    (all-positive (dot-list (add residual (scale bprime coeff)) pres))
    (all-positive (dot-list residual pres))
    (rationalp coeff)
    (rationalp coeff1)
    (<= 0 coeff1)
    (case-split (< coeff1 coeff))
    )
   (all-positive (dot-list (add residual (scale bprime coeff1)) pres)))
  :hints (("Goal" :nonlinearp t
           :induct (dot-list residual pres))
          (and stable-under-simplificationp
               '(:nonlinearp t :cases ((<= 0 (DOT BPRIME (CAR PRES))))))))

(defthm all-zero-maximum-nneg-coeff
  (implies
   (and
    (all-positive (dot-list residual pset))
    (rationalp coeff)
    (<= 0 coeff)
    (all-negative (dot-list bprime zres))
    (all-positive (dot-list residual zres))
    (all-positive (dot-list residual pres))
    (all-zero (dot-list (add residual (scale bprime coeff)) zres))
    (all-positive (dot-list (add residual (scale bprime coeff)) pres)))
   (all-zero (dot-list (add residual (scale bprime (val 0 (maximum-nneg-coeff residual bprime coeff pset zres pres)))) 
                       (val 1 (maximum-nneg-coeff residual bprime coeff pset zres pres)))))
  :hints (("Goal" :induct (maximum-nneg-coeff residual bprime coeff pset zres pres)
           :do-not '(generalize)
           :in-theory (enable coeff <---promote-denominators coeff <-+-promote-denominators)
           :nonlinearp t
           :do-not-induct t)))

(defthm len-split-sum
  (equal (len (val 0 (split-bases-rec base list a b c)))
         (+ (- (len (val 1 (split-bases-rec base list a b c))))
            (- (len (val 2 (split-bases-rec base list a b c))))
            (len list) (len a) (len b) (len c))))

(defthm len-split-0
  (<= (len (val 0 (split-bases-rec base list a b c)))
      (+ (len list) (len a)))
  :rule-classes (:linear))

(defthm len-split-1
  (<= (len (val 1 (split-bases-rec base list a b c)))
      (+ (len list) (len b)))
  :rule-classes (:linear))

(defthm len-split-2
  (<= (len (val 2 (split-bases-rec base list a b c)))
      (+ (len list) (len c)))
  :rule-classes (:linear))

(in-theory (disable split-bases-rec))

(include-book "coi/defung/defung" :dir :system)

(in-theory (disable MAXIMUM-NNEG-COEFF DEFAULT-LESS-THAN-2 default-car default-cdr acl2-numberp-x))
(in-theory (disable |(< (- x) (- y))| |(equal (- x) (- y))|))
(in-theory (disable PREFER-POSITIVE-ADDENDS-EQUAL EQUALITY-PROMOTE-DENOMINATORS))
(in-theory (disable EXPT-MINUS DEFUNG::NORMALIZE-TRUE))
(in-theory (disable DOT-ADD-1 DOT-ZERO-1 ZERO-COEFF coeff-add-2 SCALE-BY-ZERO))
(in-theory (disable ADD-ZERO-2 ZERO-POLYP-SCALE all-positive))
(in-theory (disable MAXIMUM-NNEG-COEFF-UPPER-BOUND MAXIMUM-NNEG-COEFF-LOWER-BOUND))

(def::ung find-residual (residual nset zset pset v0)
  (declare (xargs ;;:measure (list (+ (len nset) (len zset) (len pset)) (len pset) (len nset))
                  ;;:well-founded-relation l<
                  ;;:hints (("Goal" :do-not-induct t))
                  :signature ((poly-p poly-listp poly-listp poly-listp poly-p) booleanp poly-p poly-listp poly-listp)
                  :default-value (mvlist nil (zero-poly) (append nset zset pset) nil)
                  ))
  (if (not (consp nset)) (mvlist t residual zset pset)
    (let ((b (car nset)))
      (metlist ((nz zz pz) (split b zset))
        (metlist ((ok bprime zz pz) (find-residual b nz zz pz b))
          (if (not ok) (mvlist ok bprime zz pz)
            (if (zero-polyp bprime) (mvlist t bprime (append nset zset pset) nil)
              (let ((coeff0 (- (coeff bprime residual))))
                (metlist ((coeff zres pres) (maximum-nneg-coeff residual bprime coeff0 pset nil nil))
                  (let ((residual (add residual (scale bprime coeff))))
                    (if (<= (dot residual v0) 0) (mvlist t (zero-poly) (append nset zset pset) nil)
                      (let ((pset (revappend pz pres))
                            (zset (revappend zz zres)))
                        (cond
                         ((not (equal coeff coeff0))
                          (metlist ((nset zset pset) (split residual nset :zset zset :pset pset))
                            (find-residual residual nset zset pset v0)))
                         (t
                          (metlist ((nset zset pset) (split residual (cdr nset) :zset (cons b zset) :pset pset))
                            (find-residual residual nset zset pset v0))))))))))))))))
  
#|

;; Can you include only bases with (-) contribution?
;; - I think not .. 


;; If the new basis is positive w/to an existing basis, it replaces the basis.
;; If the new basis is (-) w/to an existing basis, 

;; reduce the base by all of the (-) components

;; Nasty, double recursion
(def::un find-positive-residual (c bases basis-set)
  (declare (xargs :signature ((poly-p poly-listp poly-listp) poly-p)
                  :measure (list (+ (len bases) (len basis-set)) (len bases))
                  :well-founded-relation l<
                  ))
  (let ((cprime (residual-basis c basis-set)))
    (if (not (consp bases)) cprime 
      (let ((base (car bases)))
        (if (<= 0 (dot cprime base)) (find-positive-residual c (cdr bases) basis-set)
          (let ((base (find-positive-residual base basis-set nil)))
            (find-positive-residual c (cdr bases) (cons base basis-set))))))))
                                  
;; (defun alpha (v x y)
;;   ...)

;; (defthm result
;;   (implies
;;    (and
;;     (not (zero-polyp x))
;;     (not (zero-polyp y))
;;     (not (zero-polyp v))
;;     (equal (dot x v) 0)
;;     (equal (dot y v) 0)
;;     (and 
;;      (< 0 (dot x (alpha v x y)))
;;      (< 0 (dot y (alpha v x y)))))))

   
;;    0 (sum (dot c1) decompose-by-y
;;   ((poly-equiv x (add (residual x y) 

(def::un opposing-basis-set (c bases basis-set)
  (declare (xargs :signature ((poly-p poly-listp poly-listp) poly-listp)
                  :congruence ((poly-equiv nil nil) equal)
                  :measure (len bases)))
  (if (not (consp bases)) basis-set
    (let ((base (poly-fix (car bases)))
          (c    (poly-fix c)))
      (let ((base (residual-basis base basis-set)))
        ;;(if (zero-polyp base) (opposing-basis-set c (cdr bases) basis-set)
        (if (<= 0 (dot base c)) (opposing-basis-set c (cdr bases) basis-set)
          (opposing-basis-set c (cdr bases) (cons base basis-set)))))))

(def::signature opposing-basis-set (t t mutually-disjoint) mutually-disjoint)

(defthm beta
  (implies
   (and
    (syntaxp (not (equal (car z) 'residual-basis)))
    (mutually-disjoint list))
   (equal (dot z (residual-basis x list))
          (dot (residual-basis x list)
               (residual-basis z list))))
  :hints (("Goal" :use mutually-disjoint-dot-residual-basis)))

;; And we're back .. remember this?
;;
;; - two opposing basis vectors .. pinching the solution.
;; - remember: we can only add vectors to preserve linear relations
;; - 

(dot (add c z) b1) = 0
(dot (add c z) b2) = 0

(dot c b1) + (dot (ab1 + cb2) b1) = 0
(dot c b2) + (dot (ab1 + cb2) b2) = 0

(dot c b1) + a(dot b1 b1) + b(dot b1 b2) = 0
(dot c b2) + a(dot b1 b2) + b(dot b2 b2) = 0

  (<= 0 (DOT (RESIDUAL-BASIS C BASIS-SET) (car bases)))
|-
  (<= 0 (DOT (RESIDUAL-BASIS C (opposing-basis-set c rest BASIS-SET)) (car bases)))

;; 

(defthm residual-basis-of-opposint-basis-set
  (implies
   (mutually-disjoint basis-set)
   (all-non-negative (dot-list (residual-basis c (opposing-basis-set c bases basis-set)) bases))))
|#
