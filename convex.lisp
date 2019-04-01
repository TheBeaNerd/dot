(in-package "ACL2")

(include-book "dot")
(include-book "reciprocal")
(include-book "linearly-dependent")
(include-book "disjoint")

(defthm equal-dot-scale-0
  (iff (equal (dot (scale x a) y) 0)
       (or (equal (rfix a) 0)
           (equal (dot x y) 0))))

(defthm add-negative
  (poly-equiv (add x (scale x -1))
              (zero-poly))
  :hints (("Goal" :in-theory (enable poly-equiv-reduction))))

(defthm add-zero-poly
  (poly-equiv (add (zero-poly) x)
              x))

;;
;;
;;

(def::un residual (v b)
  (declare (xargs :signature ((poly-p poly-p) poly-p)
                  :congruence ((poly-equiv poly-equiv) poly-equiv)))
  ;; (v + ab)b = 0
  ;; vb + abb = 0
  ;; a = (- vb)/bb
  (add v (scale b (- (coeff v b)))))

(def::signature residual (t t) poly-p)

(defthm dot-residual
  (= (dot b (residual v b)) 0)
  :hints (("Goal" :in-theory (enable coeff))))

;;  |   z
;;  |  /
;;  | /
;;  |/
;;  +-------> x

(local (in-theory (disable EXPT-MINUS FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT)))

(defthm orthoganal-decomposition
  (poly-equiv z (add (scale             x  (coeff z x))
                     (scale (residual z x) (coeff z (residual z x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-equiv-reduction coeff))
          (and stable-under-simplificationp
               '(:in-theory (current-theory :here)
                 :cases ((linearly-dependent x z))))
          (and stable-under-simplificationp
               '(:use (:instance linearly-dependent-rewrite-equiv
                                 (y z))
                      :in-theory (disable ZERO-POLYP-SCALE)))
          ))
          
(defthm orthoganal-decomposition-hyp
  (hide 
   (rewrite-equiv
    (poly-equiv z (add (scale                    x  (coeff (hide z) x))
                       (scale (residual (hide z) x) (coeff (hide z) (residual (hide z) x)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable rewrite-equiv)
           :expand (:Free (x) (hide x))
           :use orthoganal-decomposition)))

#|
;;  (residual b p)
;;     ^
;;     |
;;     |   b
;;     |  /
;;     | /
;;     |/
;;     +-------> p

;; First decompose z by b ..
;; Then  decompose b by p.
;;
(poly-equiv z (add (scale             b  (coeff z b))
                   (scale (residual z b) (coeff z (residual z b)))))

(poly-equiv b (add (scale             p  (coeff b p))
                   (scale (residual b p) (coeff b (residual b p)))))

(poly-equiv z (add (add (scale             p          (coeff z p))
                        (scale (residual b p)         (coeff z (residual b p))))
                   (scale (residual z (residual b p)) (coeff z (residual z (residual b p))))))

|#


(defthm linearly-dependent-residual
  (implies
   (linearly-dependent x y)
   (poly-equiv (residual x y) 
               (zero-poly)))
  :hints (("Goal" :in-theory (e/d (zero-polyp-definition rfix linearly-dependent)
                                  (linearly-dependent-witness-instance)))
          (and stable-under-simplificationp
               '(:use linearly-dependent-witness-instance))))

(defthm zerop-residual-implies-linearly-dependent
  (implies
   (and
    (not (zero-polyp x))
    (not (zero-polyp y))
    (poly-equiv (residual x y) 
                (zero-poly)))
   (linearly-dependent x y))
  :hints (("Goal" :in-theory (enable residual zero-polyp-definition)
           :use (:instance linearly-dependent-suff
                           (a (coeff x y))))))

(defthm poly-equiv-residual-zero-is-linearly-dependent
  (iff (poly-equiv (residual x y) (zero-poly))
       (or (zero-polyp x)
           (linearly-dependent x y)))
  :hints (("Goal" :in-theory (disable residual)
           :cases ((zero-polyp y)))
          ("Subgoal 2.2" :in-theory (enable residual))
          ("Subgoal 1.3" :in-theory (enable residual))
          ("Subgoal 1.1" :in-theory (enable residual))
          ))

(defthm zero-polyp-residual
  (iff (zero-polyp (residual x y))
       (or (zero-polyp x)
           (linearly-dependent x y)))
  :hints (("Goal" :in-theory (e/d (zero-polyp-definition) (poly-equiv-residual-zero-is-linearly-dependent))
           :use poly-equiv-residual-zero-is-linearly-dependent
           )))
           
(defthm equal-dot-zero-implies-zero-polyp
  (iff (equal (dot x x) 0)
       (zero-polyp x)))

(in-theory (disable residual))

(defthm residual-add
  (implies
   (equal (dot p y) 0)
   (poly-equiv (residual (add x y) p)
               (add y (residual x p))))
  :hints (("Goal" :in-theory (enable residual))))

(defthm residual-scale
  (poly-equiv (residual (scale x a) b)
              (scale (residual x b) a))
  :hints (("Goal" :in-theory (enable residual))))

(defthm residual-scale-2
  (poly-equiv (residual b (scale x a))
              (if (= (rfix a) 0) b
                (residual b x)))
  :hints (("Goal" :in-theory (enable coeff residual))))

(defthmd linearly-dependent-poly-equiv-rewrite
  (implies
   (linearly-dependent x y)
   (hide (rewrite-equiv (poly-equiv x (scale y (linearly-dependent-witness (hide x) y))))))
  :hints (("Goal" :expand (:free (x) (hide x))
           :in-theory (enable zero-polyp-definition linearly-dependent))))

(defthm equal-dot-residual-zero-is-linearly-dependent
  (iff (equal (dot b (residual b p)) 0)
       (if (zero-polyp b) t
         (linearly-dependent b p)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable coeff residual))
          (and stable-under-simplificationp
               '(:in-theory (enable zero-polyp-definition linearly-dependent)))
          (and stable-under-simplificationp
               '(:use (:instance linearly-dependent-poly-equiv-rewrite
                                 (x b)
                                 (y p))))
          ))

(defthm linearly-dependent-transitivity
  (implies
   (and
    (linearly-dependent b p)
    (linearly-dependent z b))
   (linearly-dependent z p))
  :rule-classes (:forward-chaining))

(defthm linearly-dependent-dot-zero
  (implies
   (linearly-dependent z p)
   (iff (equal (dot p z) 0)
        (and (zero-polyp p)
             (zero-polyp z))))
  :hints ((and stable-under-simplificationp
               '(:use (:instance linearly-dependent-poly-equiv-rewrite
                                 (x z)
                                 (y p))))))

(defthmd hide-rewrite-equiv
  (equal (hide (rewrite-equiv x))
         (hide x))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthmd rewrite-hide-poly-equiv
  (equal (hide (poly-equiv x y))
         (hide (rewrite-equiv (poly-equiv x y))))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthm two-way-decomposition
  (poly-equiv (hide z) (add (scale             x  (coeff (hide z) x))
                            (scale (residual z x) (coeff (hide z) (hide (residual z x))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable rewrite-equiv)
           :expand (:Free (x) (hide x))
           :use orthoganal-decomposition)))

(defthm residual-add-1
  (poly-equiv (residual (add x y) z)
              (add (residual x z)
                   (residual y z)))
  :hints (("Goal" :in-theory (enable poly-equiv-reduction residual))))

(defthm residual-zero-poly
  (poly-equiv (residual x (zero-poly))
              x)
  :hints (("Goal" :in-theory (enable residual))))

(defthmd linearly-dependent-dot
  (implies
   (and
    (linearly-dependent b x)
    (equal (dot x y) 0))
   (equal (dot b y) 0))
  :hints (("Goal" :use (:instance linearly-dependent-poly-equiv-rewrite
                                  (x b)
                                  (y x)))))

(defthm dot-linearly-dependent-residual
  (implies
   (linearly-dependent x b)
   (equal (dot x (residual y b)) 0))
  :hints (("Goal" :use (:instance linearly-dependent-dot
                                  (y (residual y b))
                                  (b x)
                                  (x b)))))

(defthm residual-linearly-dependent-residual
  (implies
   (linearly-dependent x b)
   (poly-equiv (residual x (residual y b))
               x))
  :hints (("Goal" :expand (residual x (residual y b)))))

(defthm not-zero-poly-equiv-implies-not-zero-scale
  (implies
   (and
    (poly-equiv z (scale p a))
    (case-split (rationalp a))
    (not (zero-polyp z)))
   (not (equal a 0)))
  :rule-classes (:forward-chaining))

(defthm poly-equiv-scale-implies-linearly-dependent
  (implies
   (and
    (poly-equiv z (scale p a))
    (not (zero-polyp z)))
   (linearly-dependent z p))
  ;; DAG - I should not need this to be a rewrite!!
  :rule-classes (:rewrite :forward-chaining))

(defun sum-coeff (a b)
  (if (and (zero-polyp a) (zero-polyp b)) 0
    (if (zero-polyp a) (/ (dot b b))
      (if (zero-polyp b) (/ (dot a a))
        (let ((sum (+ (DOT A A)
                      (DOT A B)
                      (DOT A B)
                      (DOT B B))))
          (if (EQUAL sum 0) 0
            (/ sum)))))))

(defthm rationalp-sum-coeff
  (rationalp (sum-coeff a b))
  :rule-classes (:type-prescription :rewrite))

(defthm coeff-add-2
  (equal (coeff x (add a b))
         (* (sum-coeff a b)
            (+ (* (dot a a) (coeff x a))
               (* (dot b b) (coeff x b)))))
  :hints (("Goal" :in-theory (e/d (coeff) (fix)))))

(defthm equal-0-product
  (iff (equal (* x y) 0)
       (or (equal (fix x) 0)
           (equal (fix y) 0))))

(defthm poly-equiv-x-scale-x
  (iff (poly-equiv z (scale z m))
       (or (zero-polyp z)
           (equal (rfix m) 1)))
  :hints (("Subgoal 3" :use (:instance poly-equiv-implication
                                       (x z)
                                       (y (scale z m))
                                       (k z)))
          ("Subgoal 2" :in-theory (enable poly-equiv-reduction))))

(defthm scale-1
  (poly-equiv (scale x 1) x)
  :hints (("Goal" :in-theory (enable poly-equiv-reduction))))

(encapsulate
    ()

  (local
   (defthmd arith-reduction-helper-1
     (iff (equal (+ (dot a a) (dot b b) (* 2 (dot a b))) 0)
          (equal (dot (add a b) (add a b)) 0))
     :hints (("Goal" :in-theory (disable EQUAL-DOT-ZERO-IMPLIES-ZERO-POLYP)))))

  (defthm arith-reduction
    (iff (equal (+ (dot a a) (dot b b) (* 2 (dot a b))) 0)
         (poly-equiv a (scale b -1)))
    :hints (("Goal" :use arith-reduction-helper-1
             :in-theory (enable zero-polyp-definition))))

  )

(defthmd scaled-remainder-is-just-the-remainder
  (implies
   (equal (dot delta (add z delta)) 0)
   (poly-equiv (scale (add z delta) (coeff z (add z delta)))
               (add z delta)))
  :hints (("Goal" :in-theory (e/d (coeff inner-product-rewrite) ()))
          (and (equal (string-for-tilde-@-clause-id-phrase id) "Subgoal 1''")
               (skosimp-inst))
          ("Subgoal 2" :cases ((hide (rewrite-equiv (equal (DOT DELTA Z)  (- (DOT DELTA DELTA)))))))
          ("Subgoal 2.2" :expand (:free (x) (hide x)))
          ("Subgoal 2.1.2" :in-theory (enable poly-equiv-reduction))
          ("Subgoal 2.1.1" :in-theory (current-theory :here)
           :expand (:free (x y) (hide (rewrite-equiv (equal x y))))
           :use (:instance inner-product-rewrite
                           (x z)
                           (y delta)))
          ("Subgoal 2.1.1''" :use (:instance linearly-dependent-rewrite-equiv
                                             (x z)
                                             (y delta)))
          ))

(defthmd zero-dot-residual
  (equal (dot (SCALE B (- (COEFF V B))) (ADD V (SCALE B (- (COEFF V B)))))
         0)
  :hints (("Goal" :in-theory (enable coeff))))
     
(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm add-opposites
       (implies
        (equal (rfix a) (- (rfix b)))
        (poly-equiv (add (scale x a)
                         (scale x b))
                    (zero-poly))))
     
     (defthm add-zero
       (poly-equiv (add (zero-poly) x)
                   x))
     
     (defthm reverse-decomposition
       (poly-equiv z (add (scale x (coeff z x))
                          (scale (residual z x) (coeff z (residual z x)))))
       :hints (("Goal" :in-theory `((:CONGRUENCE POLY-EQUIV-IMPLIES-POLY-EQUIV-ADD-2)
                                    (:DEFINITION RESIDUAL)
                                    (:EQUIVALENCE POLY-EQUIV-IS-AN-EQUIVALENCE)
                                    (:FORWARD-CHAINING T-T-IMPLIES-RATIONALP-COEFF)
                                    (:REWRITE ADD-ADD-COMMUTE)
                                    (:REWRITE ADD-COMMUTE)
                                    (:REWRITE ADD-OPPOSITES)
                                    (:REWRITE ADD-ZERO)
                                    (:REWRITE RFIX-RATIONALP)
                                    (:REWRITE SCALED-REMAINDER-IS-JUST-THE-REMAINDER)
                                    (:REWRITE ZERO-DOT-RESIDUAL)))))

     ))

  )

(def::un residual-list (p bases)
  (declare (xargs :signature ((poly-p poly-listp) poly-listp)
                  :congruence ((poly-equiv poly-list-equiv) equal)))
  (if (not (consp bases)) nil
    (let ((base (poly-fix (car bases)))
          (p    (poly-fix p)))
      (cons (residual base p)
            (residual-list p (cdr bases))))))

(def::signature residual-list (t t) poly-listp)

(defthm len-residual-list
  (equal (len (residual-list p list))
         (len list)))

(defthm disjoint-from-all-residual-list
  (implies
   (and
    (equal (dot base x) 0)
    (disjoint-from-all base list))
   (disjoint-from-all base (residual-list x list)))
  :hints (("Goal" :in-theory (enable residual))))

(defthm disjoint-from-all-residual-list-same
  (disjoint-from-all base (residual-list base list)))

(def::un basis-set (bases)
  (declare (xargs :signature ((poly-listp) poly-listp)
                  :congruence ((poly-list-equiv) equal)
                  :congruence-hints ((and stable-under-simplificationp 
                                          '(:expand ((basis-set bases)
                                                     (basis-set bases-equal)))))
                  :measure (len bases)))
  (if (not (consp bases)) nil
    (let ((basis (poly-fix (car bases))))
      (let ((bases (residual-list basis (cdr bases))))
        (cons basis (basis-set bases))))))

(defthm disjoint-from-all-bais-set
  (implies
   (disjoint-from-all base list)
   (disjoint-from-all base (basis-set list))))

(defthm mutually-disjoint-basis-set
  (mutually-disjoint (basis-set list)))

;; ----------------------------------------

(def::un decompose-vector (z basis-list)
  (declare (xargs :signature ((poly-p poly-listp) poly-p)
                  :congruence ((poly-equiv poly-list-equiv) poly-equiv)))
  (if (not (consp basis-list)) (zero-poly)
    (let ((basis (poly-fix (car basis-list))))
      (add (scale basis (coeff z basis))
           (decompose-vector z (cdr basis-list))))))

(def::signature decompose-vector (t t) poly-p)

(defthm disjoint-from-all-dot-decompose-vector
  (implies
   (disjoint-from-all base list)
   (equal (dot base (decompose-vector z list))
          0)))

(defthm disjoint-from-all-coeff-decompose-vector
  (implies
   (disjoint-from-all base list)
   (equal (coeff (decompose-vector z list) base)
          0))
  :hints (("Goal" :in-theory (enable coeff))))

(defthmd mutually-disjoint-dot-decompose-vector
  (implies
   (mutually-disjoint list)
   (equal (dot x (decompose-vector z list))
          (dot (decompose-vector x list)
               (decompose-vector z list))))
  :hints (("Goal" :in-theory (disable EQUALITY-PROMOTE-DENOMINATORS))
          ("Subgoal *1/3'" :in-theory (enable coeff))))


(defthm mutually-disjoint-dot-decompose-vector-id
  (implies
   (force (mutually-disjoint list))
   (equal (dot z (decompose-vector z list))
          (dot (decompose-vector z list)
               (decompose-vector z list))))
  :hints (("Goal" :use (:instance mutually-disjoint-dot-decompose-vector
                                  (x z)))))

(defthm dot-decompose-vector-positive
  (implies
   (mutually-disjoint list)
   (<= 0 (dot z (decompose-vector z list))))
  :hints (("Goal" :in-theory (disable decompose-vector)))
  :rule-classes (:rewrite :linear))

;; ----------------------------------------

(def::un residual-basis (z basis-set)
  (declare (xargs :signature ((poly-p poly-listp) poly-p)
                  :congruence ((poly-equiv poly-list-equiv) poly-equiv)))
  (let ((delta (decompose-vector z basis-set)))
    (add z (scale delta -1))))

(defthm disjoint-from-all-residual-basis
  (implies
   (mutually-disjoint basis-set)
   (disjoint-from-all (residual-basis z basis-set) basis-set))
  :hints (("Goal" :in-theory (enable coeff))))

(defthmd mutually-disjoint-dot-residual-basis
  (implies
   (mutually-disjoint list)
   (equal (dot z (residual-basis x list))
          (dot (residual-basis x list)
               (residual-basis z list))))
  :hints (("Goal" :do-not-induct t
           :use (:instance mutually-disjoint-dot-decompose-vector))))

(defthm mutually-disjoint-dot-residual-basis-id
  (implies
   (mutually-disjoint list)
   (equal (dot z (residual-basis z list))
          (dot (residual-basis z list)
               (residual-basis z list))))
  :hints (("Goal" :use (:instance mutually-disjoint-dot-residual-basis
                                  (x z)))))

(defthm dot-residual-basis-positive
  (implies
   (mutually-disjoint list)
   (<= 0 (dot z (residual-basis z list))))
  :hints (("Goal" :in-theory (disable residual-basis)))
  :rule-classes (:rewrite :linear))

(def::signatured residual-basis (t t) poly-p)

(defthm zero-inner-product
  (implies
   (mutually-disjoint basis-list)
   (equal (dot (decompose-vector z basis-list)
               (residual-basis z basis-list))
          0))
  :hints (("Goal" :in-theory (enable residual-basis))))

;; ----------------------------------------

(def::un decompose-vector-completely (z basis-list)
  (declare (xargs :signature ((poly-p poly-listp) poly-p)
                  :congruence ((poly-equiv poly-list-equiv) poly-equiv)))
  (let ((delta (decompose-vector z basis-list)))
    (add delta (residual-basis z basis-list))))

(def::signatured decompose-vector-completely (t t) poly-p)

(defthmd multi-way-decomposition
  (implies
   (mutually-disjoint basis-list)
   (poly-equiv (decompose-vector-completely z basis-list) z))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable decompose-vector-completely))
          (and stable-under-simplificationp
               '(:in-theory (enable residual-basis)))))

(local
 (in-theory (e/d (residual-basis decompose-vector-completely) 
                 (MUTUALLY-DISJOINT-DOT-DECOMPOSE-VECTOR-id
                  multi-way-decomposition decompose-vector))))

(defthmd three-way-decomposition
  (hide (rewrite-equiv (poly-equiv z (decompose-vector-completely (hide z) (basis-set (list p b))))))
  :hints (("Goal" :in-theory (enable multi-way-decomposition)
           :expand (:free (x) (hide x)))))

(defcong poly-equiv poly-list-equiv (cons a x) 1)
(defcong poly-list-equiv poly-list-equiv (cons a x) 2)

(defthm poly-list-fix-cons
  (equal (poly-list-fix (cons x list))
         (cons (poly-fix x)
               (poly-list-fix list))))

(defthm dot-member-residual-basis
  (implies
   (and
    (member-equal (poly-fix p) (poly-list-fix list))
    (mutually-disjoint list))
   (equal (dot p (residual-basis z list))
          0))
  :hints (("Goal" :in-theory (enable 
                              decompose-vector
                              residual-basis
                              list::memberp
                              coeff
                              ))))

(defthmd dot-unhide-expanded-vectors
  (implies
   (syntaxp (or (equal z 'b) (equal z 'z)))
   (and (equal (dot (hide z) x)
               (dot z x))
        (equal (dot x (hide z))
               (dot x z))))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthmd coeff-unhide-expanded-vectors
  (implies
   (syntaxp (or (equal z 'b) (equal z 'z)))
   (equal (coeff (hide z) x)
          (coeff z x)))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthm double-residual
  (poly-equiv (residual (residual x p) p)
              (residual x p))
  :hints (("Goal" :in-theory (enable residual))))

#+joe
(defthm fred
  (implies
   (and
    (< 0 (dot b s))
    (< (dot p s) 0)
    (< (dot p b) 0)
    (< (dot (residual b p) s) 0)
    (zero-polyp (residual-basis s (basis-set (list p b))))
    )
   (not
    (and
     ;;(not (zero-polyp z))
     (< 0 (dot b z))
     (< 0 (dot p z))
     (< 0 (dot s z))
     )))
  :hints (("Goal" :use (:instance orthoganal-decomposition-hyp
                                  (z b)
                                  (x p)))
          (and stable-under-simplificationp
               '(:in-theory (enable bag::memberp
                                    decompose-vector-completely)
                            :expand ((:free (x) (basis-set x))
                                     )
                            :use ((:instance three-way-decomposition
                                             (b (hide b)))
                                  (:instance three-way-decomposition
                                             (z s)
                                             (b (hide b)))
                                  )))
          (and stable-under-simplificationp
               '(:in-theory (enable 
                             bag::memberp 
                             coeff-unhide-expanded-vectors
                             decompose-vector-completely
                             )))
          #+joe
          (and stable-under-simplificationp
               '(:in-theory (enable 
                             bag::memberp 
                             dot-unhide-expanded-vectors
                             coeff-unhide-expanded-vectors
                             )))
          ))

