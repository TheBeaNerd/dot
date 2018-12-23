(in-package "ACL2")
(include-book "dot")
(include-book "hints")

;; Everything old is new again.

(defun vector-decomposition-relation (vector delta residual)
  (poly-equiv vector (add delta residual)))

(defthm scale-zero
  (implies
   (zero-polyp z)
   (poly-equiv (scale z alpha)
               z))
  :hints ((skosimp-inst)))

(def::un decompose-over-bases (vector base0 base01)
  (let ((alpha01 (coeff base0 base01)))
    (let ((base1 (add base01 (scale base0 (- alpha01)))))
      ;; base0 =          base0
      ;; base01 = alpha01*base0 + base1
      (let* ((coeff1 (coeff base1 vector))
             (coeff0 (coeff base0 vector)))
        ;; gamma*base0 + coeff1*base01
        ;; gamma*base0 + coeff1*(alpha01*base0 + base1)
        ;; (gamma + coeff1*alpha01)*base0 + coeff1*base1
        ;; (gamma + coeff1*alpha01) = coeff0
        ;; gamma = coeff0 - coeff1*alpha01
        (let ((coeff0 (- coeff0 (* coeff1 alpha01))))
          (let ((delta (add (scale base0 coeff0) (scale base01 coeff1))))
            (let ((residual (add vector (scale delta -1))))
              (mv vector delta residual))))))))

(include-book "arithmetic-5/top" :dir :system)
(in-theory (disable INTEGERP-MINUS-X))

(defun product-denominators (x)
  (case-match x
    (('unary-/ d) d)
    (('binary-+ l r)
     (let ((la (product-denominators l))
           (ra (product-denominators r)))
       (or la ra)))
    (('unary-- y) 
     (product-denominators y))
    (('binary-/ n d)
     (let ((la (product-denominators n)))
       (if (not la) d `(binary-* ,la ,d))))
    (('binary-* l r)
     (let ((la (product-denominators l))
           (ra (product-denominators r)))
       (if (and la ra)
           `(binary-* ,la ,ra)
         (or la ra))))
    (& nil)))

(defun bind-denominators (a x y)
  (let ((ax (product-denominators x))
        (ay (product-denominators y)))
    (if ax (acons a ax nil)
      (if ay (acons a ay nil)
        nil))))

(defthm promote-denominators
  (implies
   (and
    (acl2-numberp x)
    (acl2-numberp y)
    (bind-free (bind-denominators 'a x y) (a))
    (acl2-numberp a)
    (case-split (not (equal a 0)))
    (equal ax (* a x))
    (equal ay (* a y)))
   (iff (equal x y)
        (equal ax ay))))

(defthm known-zero-reciporicals-should-be-zero
  (implies
   (case-split (equal x 0))
   (equal (/ x) 0)))

(defthm zero-polyp-scale
  (iff (zero-polyp (scale x a))
       (if (= (rfix a) 0) t (zero-polyp x)))
  :hints (("Goal" :in-theory (enable zero-polyp-definition))
          (skosimp-inst)
          (and stable-under-simplificationp
               '(:in-theory (enable hide-poly-equiv)))))

(include-book "coi/quantification/quantification" :dir :system)

(def::un-sk linearly-dependent (x y)
  (exists (a) (and (not (equal (rfix a) 0)) (zero-polyp (add x (scale y (- (rfix a))))))))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthmd linearly-dependent-zeros-1
       (implies
        (and
         (linearly-dependent x y)
         (zero-polyp y))
        (zero-polyp x)))
     
     (defthmd linearly-dependent-zeros-2
       (implies
        (and
         (linearly-dependent x y)
         (zero-polyp x))
        (zero-polyp y)))
     
     (defthm equal-to-iff
       (implies
        (or (booleanp x) (booleanp y))
        (iff (equal x y)
             (and (booleanp x)
                  (booleanp y)
                  (iff x y)))))
     
     (defthmd linearly-dependent-zero-iff
       (implies
        (linearly-dependent x y)
        (or (and (zero-polyp x)
                 (zero-polyp y))
            (and (not (zero-polyp x))
                 (not (zero-polyp y)))))
       :hints (("Goal" :in-theory (e/d (linearly-dependent-zeros-1 linearly-dependent-zeros-2)
                                       (linearly-dependent)
                                       ))))
     
     (defthm linear-dependence-commutes
       (implies
        (linearly-dependent x y)
        (linearly-dependent y x))
       :hints (("Goal" :in-theory (e/d (zero-polyp-definition) (linearly-dependent))
                :expand (linearly-dependent x y))
               (and stable-under-simplificationp
                    '(:use (:instance linearly-dependent-suff
                                      (a (/ (rfix hide)))
                                      (x y)
                                      (y x))))
               (skosimp-inst)))
     
     (defthm linear-dependence-transitive
       (implies
        (and
         (linearly-dependent x y)
         (linearly-dependent y z))
        (linearly-dependent x z))
       :hints (("Goal" :in-theory (e/d (zero-polyp-definition) (linearly-dependent))
                :expand ((linearly-dependent x y)
                         (linearly-dependent y z)))
               (and stable-under-simplificationp
                    '(:use (:instance linearly-dependent-suff
                                      (a (* (rfix hide) (rfix hide15)))
                                      (x x)
                                      (y z))))
               (skosimp-inst)))
     
     (defthm linearly-dependent-x-x
       (linearly-dependent x x)
       :hints (("Goal" :in-theory (e/d (zero-polyp-definition) (linearly-dependent))
                :use (:instance linearly-dependent-suff
                                (a 1)
                                (x x)
                                (y x)))
               (skosimp-inst)))
     
     ))

  (defequiv linearly-dependent
    :hints (("Goal" :in-theory (disable linearly-dependent LINEARLY-DEPENDENT-BY-MULTIPLICITY))
            (and stable-under-simplificationp
                 '(:in-theory (enable linearly-dependent)))))
  
  (in-theory (disable linearly-dependent LINEARLY-DEPENDENT-BY-MULTIPLICITY))
  
  (defcong linearly-dependent equal (zero-polyp x) 1
    :hints (("Goal" :use (:instance linearly-dependent-zero-iff
                                    (x x)
                                    (y x-equiv)))))

  )

(defthm linearly-dependent-witness-instance
  (implies
   (and
    (linearly-dependent x y)
    (not (and (zero-polyp x)
              (zero-polyp y))))
   (equal (linearly-dependent-witness x y)
          (coeff y x)))
  :hints (("Goal" :in-theory (enable zero-polyp-definition linearly-dependent))
          (and stable-under-simplificationp
               '(:in-theory (e/d (rfix coeff)
                                 (POLY-EQUIV-IMPLIES-EQUAL-DOT-2
                                  POLY-EQUIV-IMPLIES-EQUAL-ZERO-POLYP-1
                                  ZERO-POLYP-DEFINITION
                                  linearly-dependent-is-an-equivalence))
                 :use (:instance poly-equiv-implication
                                 (x (add x (scale y (- (rfix (linearly-dependent-witness x y))))))
                                 (y (zero-poly))
                                 (k y))))
          ))

(defthm not-linearly-dependent-implies-not-both-zero
  (implies
   (not (linearly-dependent x y))
   (or (not (zero-polyp x))
       (not (zero-polyp y))))
  :hints (("Goal" :use (:instance linearly-dependent-suff
                                  (a 1))))
  :rule-classes (:forward-chaining))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthmd inner-product-implication-helper
       (implies
        (and
         (equal (dot base0 delta) 0)
         (not (equal (dot base0 base0) 0))
         (poly-equiv base1 (add delta (scale base0 alpha)))
         (not (equal (dot delta delta) 0))
         (equal (* (dot base0 base0)
                   (dot base1 base1))
                (expt (dot base0 base1) 2)))
        (poly-equiv base0 base1)))
     
     (defthmd zero-dot-to-zero-polyp
       (iff (equal (dot x x) 0)
            (zero-polyp x)))
     
     ))

  (defthm inner-product-implication
    (implies
     (and
      (not (linearly-dependent base0 base1))
      (case-split (and (not (zero-polyp base0))
                       (not (zero-polyp base1)))))
     (iff (equal (* (dot base0 base0)
                    (dot base1 base1))
                 (expt (dot base0 base1) 2))
          (poly-equiv base0 base1)))
    :hints (
            ("Goal" :in-theory nil
             :use (:instance inner-product-implication-helper
                             (base0 base0)
                             (base1 base1)
                             (delta (add base1 (scale base0 (- (coeff base0 base1)))))
                             (alpha (coeff base0 base1))))
            ("Subgoal 10" :in-theory (enable coeff))
            ("Subgoal 9" :in-theory (enable coeff))
            ("Subgoal 8" :in-theory (enable coeff zero-dot-to-zero-polyp)
                               :use (:instance linearly-dependent-suff
                                               (x base1)
                                               (y base0)
                                               (a (coeff base0 base1))))
            ("Subgoal 7" :in-theory (enable coeff zero-dot-to-zero-polyp)
                               :use (:instance linearly-dependent-suff
                                               (x base1)
                                               (y base0)
                                               (a (coeff base0 base1))))
            ("Subgoal 6" :in-theory (enable coeff))
            ("Subgoal 5" :in-theory (enable coeff poly-equiv-reduction))
            ("Subgoal 4" :in-theory (current-theory :here))
            ("Subgoal 3" :in-theory (current-theory :here))
            ("Subgoal 2" :in-theory (current-theory :here))
            ("Subgoal 1" :in-theory (current-theory :here))
            ))
                                                     
  )
    
(defthm decompose-over-bases-enforces-vector-decompositon-relation
  (vector-decomposition-relation
   (val 0 (decompose-over-bases vector base0 base01))
   (val 1 (decompose-over-bases vector base0 base01))
   (val 2 (decompose-over-bases vector base0 base01)))
  :hints ((skosimp-inst)))

(defthmd linearly-dependent-implies-equal-scale
  (implies
   (linearly-dependent base0 base01)
   (hide (rewrite-equiv (poly-equiv base0 (scale base01 (rfix (linearly-dependent-witness base0 base01)))))))
  :hints (("Goal" :expand (:free (x) (hide x))
           :in-theory (enable zero-polyp-definition linearly-dependent))
          (skosimp-inst)))

(defthm residual-is-zero-on-bases
  (and (= (dot (val 2 (decompose-over-bases vector base0 base01)) base0 ) 0)
       (= (dot (val 2 (decompose-over-bases vector base0 base01)) base01) 0))
  :hints (("Goal" :in-theory (enable coeff))
          (and stable-under-simplificationp
               '(:cases ((linearly-dependent base0 base01))))
          (and stable-under-simplificationp
               '(:in-theory (disable ZERO-POLYP-SCALE linearly-dependent-witness-instance)
                 :use linearly-dependent-implies-equal-scale))
          ))

(in-theory (disable decompose-over-bases))

#|

(def::un restrict (vector delta residual base0)
  (let ((dot (dot residual base0)))
    (if (<= 0 dot) (mv vector delta residual (list base0))
      (let ((coeff (/ dot (self-dot base0))))
        (let ((residual (add residual (scale base0 coeff))))
          (let ((dot (dot residual vector)))
            (if (< 0 dot) (mv vector (add delta (scale base0 (- coeff))) residual nil)
              (let ((alpha (coeff delta base0)))
                (let ((base1 (add delta (scale base0 (- alpha)))))
                  ;; base0 =       base0
                  ;; delta = alpha*base0 + base1
                  (let* ((coeff1 (coeff vector base1))
                         (coeff0 (coeff vector base0)))
                    ;; gamma*coeff1 + alpha*coeff0 = 0
                    ;; gamma = (- alpha*coeff0)/coeff1
                    (let ((gamma (/ (- (* alpha coeff0)) coeff1)))
                      (let ((delta (add (scale base0 gamma) (scale delta coeff1))))
                        (let ((residual (add vector (scale delta -1))))
                          (mv vector delta residual nil))))))))))))))


(defthm vector-decompositon-is-preserved
  (implies
   (vector-decomposition-relation vector delta residual)
   (vector-decomposition-relation
    (val 0 (restrict vector delta residual base0))
    (val 1 (restrict vector delta residual base0))
    (val 2 (restrict vector delta residual base0))))
  :hints ((skosimp-inst)))

(defthm residual-is-positive-on-vector
  (implies
   (and
    (vector-decomposition-relation vector delta residual)
    (< 0 (dot vector residual)))
   (implies
    (not (zero-polyp (val 2 (restrict vector delta residual base0))))
    (< 0 (dot (val 2 (restrict vector delta residual base0))
              (val 0 (restrict vector delta residual base0))))))
  :hints (("Goal" :in-theory (enable coeff))))

(defthm residual-is-not-negative-on-base0
  (<= 0 (dot (val 2 (restrict vector delta residual base0)) base0)))

(defthm residual-is-not-negative-on-delta
  (<= 0 (dot (val 2 (restrict vector delta residual base0)) delta)))

|#
