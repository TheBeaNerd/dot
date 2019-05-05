(in-package "ACL2")

(include-book "residual")
(include-book "visualize")

(in-theory (disable FIND-RESIDUAL-DOMAIN-DEFINITION))

(defthm val-0-find-residual
  (iff (val 0 (find-residual residual nset zset pset v0))
       (find-residual-domain residual nset zset pset v0))
  :otf-flg t
  :hints ((and stable-under-simplificationp
               '(:in-theory (disable FIND-RESIDUAL-DEFINITION)))))

(defthm all-zero-dot-zero-poly
  (implies
   (zero-polyp poly)
   (all-zero (dot-list poly list))))

(defthm dot-list-revappend
  (equal (dot-list x (revappend a b))
         (revappend (dot-list x a)
                    (dot-list x b))))

(defthm primary-invariant
  (implies
   (and
    (find-residual-domain residual nset zset pset v0)
    (< 0 (dot residual v0))
    (all-negative (dot-list residual nset))
    (all-zero     (dot-list residual zset))
    (all-positive (dot-list residual pset)))
   (and
    (or (zero-polyp (val 1 (find-residual residual nset zset pset v0)))
        (< 0 (dot (val 1 (find-residual residual nset zset pset v0)) v0)))
    (all-zero     (dot-list (val 1 (find-residual residual nset zset pset v0))
                            (val 2 (find-residual residual nset zset pset v0))))
    (all-positive (dot-list (val 1 (find-residual residual nset zset pset v0))
                            (val 3 (find-residual residual nset zset pset v0))))
    ))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :induct (find-residual residual nset zset pset v0)
           :in-theory (e/d (all-positive-to-all-positive
                            ) (FIND-RESIDUAL-DEFINITION)))
          ))

          (and (< 0 (car (car id)))
               '(:do-not-induct t
                 :in-theory (disable FIND-RESIDUAL-DEFINITION
                                     (force))))))

              


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
