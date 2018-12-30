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

(defun linearize-around-vector (vector bases)
  (if (not (consp bases)) nil
    (let ((base (car bases)))
      (cons (base (- (base->bias base) (dot vector (base->poly base))) (base->poly base))
            (linearize-around-vector vector (cdr bases))))))

(defun zeroize-biases (bases)
  (if (not (consp bases)) nil
    (let ((base (car bases)))
      (cons (base 0 (base->poly base))
            (zeroize-biases (cdr bases))))))

(defun split-bases-rec (vector bases nbases zbases pbases)
  (if (not (consp bases)) (mvlist nbases zbases pbases)
    (let ((base (car bases)))
      (let ((score (score-vector vector base)))
        (if (< score 0) (split-bases-rec vector bases (cons base nbases) zbases pbases)
          (if (< 0 score) (split-bases-rec vector bases nbases zbases (cons base pbases))
            (split-bases-rec vector bases nbases (cons base zbases) pbases)))))))

(defun split-bases (vector bases)
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

(defun upper-bound (max list)
  (if (not (consp list)) max
    (let ((value (car list)))
      (if (<= value 0) (upper-bound max (cdr list))
        (upper-bound (max value max) (cdr list))))))

(defun lower-bound (min list)
  (if (not (consp list)) min
    (let ((value (car list)))
      (if (<= 0 value) (lower-bound min (cdr list))
        (lower-bound (min min (abs value)) (cdr list))))))

;; if the largest positive is greater than the largest negative,
;; use the largest positive
;; else use the smallest negative

(defun alpha-list (sln delta bases)
  (if (not (consp bases)) nil
    (let ((base (car bases)))
      ;; c0 <= (sln + alpha*delta)*b
      ;; c0 <= sln*b + alpha*delta*b
      ;; alpha = (c0 - sln*b)/(delta*b)
      (let ((n (- (base->bias base) (dot sln (base->poly base))))
            (d (dot delta (base-poly base))))
        (cond
         ;; negative      - decreasing      : upper bound : -alpha
         ((and (< n 0) (< d 0))
          (cons (- (/ n d)) (alpha-list sln delta (cdr bases))))
         ;; non-negative  - increasing      : lower bound : +alpha
         ((and (<= 0 n) (< 0 d))
          (cons (/ n d) (alpha-list sln delta (cdr bases))))
         (t
          (cons 0 (alpha-list sln delta (cdr bases)))))))))

(defun alpha (sln delta bases)
  (let ((alpha-list (alpha-list sln delta bases)))
    (let ((alpha (upper-bound 0 alpha-list)))
      (lower-bound alpha alpha-list))))

(defun weighted-vector (vector nbases)
  (if (not (consp nbases)) (zero-vector)
    (let ((poly (base->poly (car nbases))))
      (add (scale poly (- (/ (dot poly vector))))
           (weighted-vector vector (cdr nbases))))))

;; 0 <= vector*(vector + delta)
;; (- vector*vector) <= vector*delta
(defmacro zero-delta (vector bases)
  `(let ((vector ,vector)
         (bases  ,bases))
     (metlist ((nbases zbases pbases) (split-bases vector bases))
       (declare (ignore zbases pbases))
       (if (null nbases) vector
         (let ((bases (cons (base 0 vector) nbases)))
           (let ((bases (linearize-around-vector vector nbases)))
             (metlist ((unsat delta) (max-solution vector zbases (zero-vector)))
               (or unsat delta))))))))
  
(defun max-solution (vector bases sln)
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
  (metlist ((nbases zbases pbases) (split-bases sln bases))
    (declare (ignore pbases))
    (if (null nbases) (mv nil sln)
      (let ((delta (zero-delta vector (zeroize-biases zbases))))
        (if (zero-polyp delta) (mv delta sln)
          (let ((alpha (alpha sln delta bases)))
            (let ((sln (add sln (scale delta alpha))))
              (max-solution vector bases sln))))))))
