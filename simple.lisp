(in-package "ACL2")

;; So you have a bunch of basis polys (I) relative to some solution.
;; - you know forall (I) : 0 <= <sln,bI>
;; 
;; You are adding a new poly such that <sln,P> < 0
;;
;; Now, forall (J) : 0 = <sln,bJ> compute their dot product w/to P
;;
;; Gather the opposing bases
;;
;; - If all are positive, you are free to move
;; - If all are negative, you have found an equality.
;; - Else you need to remove the negative bases (N) from P
;;
;; Compute alpha for each negative base.
;;
;; <P + alpha(bN),bN> = 0 
;; alpha = (- <P,bN>)/<bN,bN>
;; 
;; Compute a delta vector as a weighted sum of pN:
;;
;;   delta = sum aN*pN
;;
;; I think you can (hopefully?) prove that this result is (+) w/to each basis.
;; 
;; <P + z*delta,bN> > 0
;;
;; as well as to the original vector :
;;
;; P' = P + z*delta
;;
;; <P',P> > 0
;;
;; .. although it is possible that this could be negative.  At this
;; point one might attempt to optimize the result to further reduce
;; the (-) impact.  If this solution is not forthcoming, however, we
;; might need to recur on the subproblem of finding a P' that does
;; satisfy all of these properties.
;;
;; Given a P' that satisfies these properties, we can step by P' until
;; we reach either our objective or a new set of zeros.

;; So, logically, we should problably express this as recursively
;; solving a problem of linear constraints.  From there we can
;; focus on optimizing the computational process.

(include-book "dot")
(include-book "all")

(fty::defprod+ base
 (
  (bias rationalp)
  (poly poly)
  ))

(def::type-list base)

(def::un linearize-around-vector (vector bases)
  (declare (xargs :signature ((poly-p base-listp) base-listp)
                  :congruence ((poly-equiv base-list-equiv) equal)))
  (if (not (consp bases)) nil
    (let ((base (car bases)))
      (cons (base (- (base->bias base) (dot vector (base->poly base))) (base->poly base))
            (linearize-around-vector vector (cdr bases))))))

(def::signatured linearize-around-vector (t t) base-listp)

(def::un zeroize-biases (bases)
  (declare (xargs :signature ((base-listp) base-listp)
                  :congruence ((base-list-equiv) equal)))
  (if (not (consp bases)) nil
    (let ((base (car bases)))
      (cons (base 0 (base->poly base))
            (zeroize-biases (cdr bases))))))

(def::signatured zeroize-biases (t) base-listp)

(def::und score-base (vector base)
  (declare (xargs :signature ((poly-p base-p) rationalp)
                  :congruence ((poly-equiv base-equiv) equal)))
  (- (base->bias base) (dot (base->poly base) vector)))

(def::un split-bases-rec (vector bases nbases zbases pbases)
  (declare (xargs :signature ((poly-p base-listp base-listp base-listp base-listp) 
                              base-listp base-listp base-listp)
                  :congruence ((poly-equiv base-list-equiv base-list-equiv base-list-equiv base-list-equiv) 
                               base-list-equiv base-list-equiv base-list-equiv)))
  (if (not (consp bases)) (mvlist nbases zbases pbases)
    (let ((base (base-fix! (car bases))))
      (let ((score (score-base vector base)))
        (if (< score 0) (split-bases-rec vector (cdr bases) (cons base nbases) zbases pbases)
          (if (< 0 score) (split-bases-rec vector (cdr bases) nbases zbases (cons base pbases))
            (split-bases-rec vector (cdr bases) nbases (cons base zbases) pbases)))))))

(def::und split-bases (vector bases)
  (declare (xargs :signature ((poly-p base-listp)  base-listp base-listp base-listp)
                  :congruence ((poly-equiv base-list-equiv) base-list-equiv base-list-equiv base-list-equiv)))
  (split-bases-rec vector bases nil nil nil))

;; positive alpha moves in the right direction
;; negative alpha moves in the wrong direction

;; c0 - sln*b     delta*b
;; -------------------------------
;; negative      - non-decreasing  : unbound     : 0
;; negative      - decreasing      : upper bound : -alpha
;; non-negative  - increasing      : lower bound : +alpha
;; non-negative  - non-increasing  : unbound     : 0

;; largest + alpha <= the abs of the largest - value

(def::un upper-bound (max list)
  (declare (xargs :measure (len list)
                  :signature ((rationalp rational-listp) rationalp)
                  :congruence ((rfix-equiv rational-list-equiv) equal)))
  (let ((max (rfix max)))
    (if (not (consp list)) max
      (let ((value (rfix (car list))))
        (if (<= value 0) (upper-bound max (cdr list))
          (upper-bound (max value max) (cdr list)))))))

(def::un lower-bound (min list)
  (declare (xargs :measure (len list)
                  :signature ((rationalp rational-listp) rationalp)
                  :congruence ((rfix-equiv rational-list-equiv) equal)))
  (let ((min (rfix min)))
    (if (not (consp list)) min
      (let ((value (rfix (car list))))
        (if (<= 0 value) (lower-bound min (cdr list))
          (lower-bound (min min (abs value)) (cdr list)))))))

;; if the largest positive is greater than the largest negative,
;; use the largest positive
;; else use the smallest negative

(def::un alpha-list (sln delta bases)
  (declare (xargs :signature ((poly-p poly-p base-listp) rational-listp)
                  :congruence ((poly-equiv poly-equiv base-list-equiv) equal)))
  (if (not (consp bases)) nil
    (let ((base (base-fix! (car bases))))
      ;; c0 <= (sln + alpha*delta)*b
      ;; c0 <= sln*b + alpha*delta*b
      ;; alpha = (c0 - sln*b)/(delta*b)
      (let ((n (- (base->bias base) (dot sln (base->poly base))))
            (d (dot delta (base->poly base))))
        (cond
         ;; negative      - decreasing      : upper bound : -alpha
         ((and (< n 0) (< d 0))
          (cons (- (/ n d)) (alpha-list sln delta (cdr bases))))
         ;; non-negative  - increasing      : lower bound : +alpha
         ((and (<= 0 n) (< 0 d))
          (cons (/ n d) (alpha-list sln delta (cdr bases))))
         (t
          (cons 0 (alpha-list sln delta (cdr bases)))))))))

(def::und alpha (sln delta bases)
  (declare (xargs :signature ((poly-p poly-p base-listp) rationalp)
                  :congruence ((poly-equiv poly-equiv base-list-equiv) equal)))
  (let ((alpha-list (alpha-list sln delta bases)))
    (let ((alpha (upper-bound 0 alpha-list)))
      (lower-bound alpha alpha-list))))

(def::un weighted-vector (vector nbases)
  (declare (xargs :signature ((poly-p base-listp) poly-p)
                  :congruence ((poly-equiv base-list-equiv) poly-equiv)))
  (if (not (consp nbases)) (zero-poly)
    (let ((base (base-fix! (car nbases))))
      (let ((poly (base->poly base)))
        (let ((dot (dot poly vector)))
          (if (= dot 0) (weighted-vector vector (cdr nbases))
            (add (scale poly (- (/ dot)))
                 (weighted-vector vector (cdr nbases)))))))))

(def::signatured weighted-vector (t t) poly-p)

(def::un sum-polys (nbases)
  (declare (xargs :signature ((base-listp) poly-p)
                  :signature-hints (("Goal" :in-theory (disable (sum-polys))))
                  :congruence ((base-list-equiv) poly-equiv)))
  (if (not (consp nbases)) (zero-poly)
    (let ((base (base-fix! (car nbases))))
      (add (base->poly base) (sum-polys (cdr nbases))))))

;; If we know that all individually are (-) w/to a
;; given vector then the sum must be (-) w/to that
;; same vector.

(def::un dot-base-list (vector list)
  (declare (xargs :signature ((poly-p base-listp) rational-listp)
                  :congruence ((poly-equiv base-list-equiv) equal)))
  (if (not (consp list)) nil
    (let ((base (base-fix! (car list))))
      (cons (dot vector (base->poly base))
            (dot-base-list vector (cdr list))))))

(defthm all-negative-dot-base-list
  (implies
   (and
    (all-negative (dot-base-list sln nbases))
    (consp nbases))
   (< (dot sln (sum-polys nbases)) 0)))
 
(defthmd all-non-positive-summary
  (implies
   (all-non-positive (dot-base-list poly list))
   (<= (dot poly (sum-polys list)) 0)))

;;
;; DAG -- oh .. this is a really nice result.
;;
(defthm three-sum-relations-generalization
  (or (zero-polyp (sum-polys nbases))
      (not (all-non-positive (dot-base-list (sum-polys nbases) nbases))))
  :hints (("Subgoal *1/3" :use ((:instance three-sum-relations
                                           (x (base->poly (car nbases)))
                                           (y (sum-polys (cdr nbases))))
                                (:instance all-non-positive-summary
                                           (poly (add (base->poly (car nbases)) (sum-polys (cdr nbases))))
                                           (list (cdr nbases)))))))

(def::signatured sum-polys (t) poly-p)

(defund non-nil-test (x)
  (declare (type t x))
  (not (not x)))

(include-book "coi/defung/defung" :dir :system)

(in-theory 
 (disable 
  BASE-OF-RFIX-BIAS-NORMALIZE-CONST
  BASE-OF-POLY-FIX-POLY-NORMALIZE-CONST
  DEFUNG::NORMALIZE-TRUE
  SCALE-BY-ZERO
  ADD-ZERO-1
  ADD-ZERO-2
  default-car
  default-cdr
  DEFAULT-UNARY-MINUS
  BASE->POLY$INLINE-OF-BASE-FIX-BASE-INSTANCE
  BASE->POLY$INLINE-OF-BASE-FIX-BASE-INSTANCE-NORMALIZE-CONST
  ))

;; 0 <= vector*(vector + delta)
;; (- vector*vector) <= vector*delta
(defmacro zero-delta (vector bases)
  `(let ((vector ,vector)
         (bases  ,bases))
     (metlist ((nbases zbases pbases) (split-bases vector bases))
       (declare (ignore zbases pbases))
       (if (null nbases) vector
         (let ((sln (weighted-vector vector nbases)))
           ;; So what we could deduce is that this result will be
           ;; negative (or positive) w/to all of the bases.  More to
           ;; the point, if they are all orthoganal, the result will
           ;; actually *be* the solution vector.
           (let ((bases (cons (base 0 vector) nbases)))
             (let ((bases (linearize-around-vector vector bases)))
               ;; sln is (+) w/to all of the bases except vector.  I
               ;; suspect that it will also make them "true" (nice
               ;; opportunity for a proof, dude).  The resulting
               ;; "sum-vector" will just be the vector.  There is also
               ;; a good chance that zbases will be empty.  
               ;;
               ;; But .. wait .. what if it isn't?  What if the bases
               ;; are orthoganal and, thus, every base is zero?  Then
               ;; we will get a call of zero-delta with vector, all
               ;; bases will be nbases, and we end up in an infinite
               ;; loop.
               ;;
               ;; vector: -x -y -z
               ;; nbases:  x
               ;;             y
               ;;                z
               ;;   sln:   x  y  z
               ;;
               (metlist ((unsat delta) (max-solution bases sln))
                 (if (non-nil-test unsat) (poly-fix unsat) delta)))))))))
  
(def::ung max-solution (bases sln)
  (declare (xargs :signature ((base-listp poly-p) t poly-p)
                  :default-value (mvlist (zero-poly) (zero-poly))
                  ))
  (metlist ((nbases zbases pbases) (split-bases sln bases))
    (declare (ignore pbases))
    (if (null nbases) (mvlist nil sln)
      (let ((vector (sum-polys nbases)))
        ;;
        ;; Of course this doesn't guarantee that
        ;; the result will be any closer to any
        ;; particular negative.
        ;;
        ;; To ensure that we would need to choose
        ;; just *one* negative base.
        ;;
        ;; If we do that, is there a "best" base?
        ;; One that "maximizes" the 
        ;;
        (let ((delta (zero-delta vector (zeroize-biases zbases))))
          (if (zero-polyp delta) (mvlist delta sln)
            (let ((alpha (alpha sln delta bases)))
              (let ((sln (add sln (scale delta alpha))))
                (max-solution bases sln)))))))))

;;
;; So we should probably have "a solution" and "the optimal"
;; solution.
;;
;; The difference is that "a solution" uses a vector consisting of a
;; sum of the negative components .. ie: it always tries to get
;; closer to a failing constraint.  You might even weigh it by
;; the alpha required to get there.  Or use the maximum.
;;
;; The optimal solution uses the gradiant as the vector ..  kinda
;; like we do here.  But it also always preserves the current
;; solution.
;; 
;;

;; I think we might want to argue that any zero base that becomes
;; positive will remain positive.

