(in-package "ACL2")
(include-book "dot")
(include-book "hints")
(local (include-book "reciprocal"))

;; Everything old is new again.

(defthm scale-zero
  (implies
   (zero-polyp z)
   (poly-equiv (scale z alpha)
               z))
  :hints ((skosimp-inst)))

(defthm poly-equiv-add-zero
  (iff (poly-equiv (add x y) (zero-poly))
       (poly-equiv x (scale y -1)))
  :hints ((skosimp-inst)))

(defthm zero-polyp-scale
  (iff (zero-polyp (scale x a))
       (if (= (rfix a) 0) t (zero-polyp x)))
  :hints (("Goal" :in-theory (enable zero-polyp-definition))
          (skosimp-inst)
          (and stable-under-simplificationp
               '(:in-theory (enable hide-poly-equiv)))))

(include-book "coi/quantification/quantification" :dir :system)

(def::un-sk linearly-dependent (x y)
  (exists (a) (and (not (equal (rfix a) 0)) (zero-polyp (add x (scale y (- (rfix a)))))))
  :strengthen t)

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

(defthm poly-equiv-zero-scale
  (iff (poly-equiv (zero-poly) (scale y a))
       (if (equal (rfix a) 0) t (poly-equiv y (zero-poly))))
  :hints ((skosimp-inst)))

(defthm linearly-dependent-witness-instance
  (implies
   (and
    (linearly-dependent x y)
    (not (and (zero-polyp x)
              (zero-polyp y))))
   (equal (linearly-dependent-witness x y)
          (coeff x y)))
  :hints (("Goal" :in-theory (enable zero-polyp-definition linearly-dependent))
          (and stable-under-simplificationp
               '(:in-theory (e/d (rfix coeff)
                                 (POLY-EQUIV-IMPLIES-EQUAL-DOT-2
                                  POLY-EQUIV-IMPLIES-EQUAL-ZERO-POLYP-1
                                  ZERO-POLYP-DEFINITION
                                  linearly-dependent-is-an-equivalence))
                :use (:instance poly-equiv-implication
                                (x x)
                                (y (scale y (linearly-dependent-witness x y)))
                                (k y))
                            ))
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
                             (delta (add base1 (scale base0 (- (coeff base1 base0)))))
                             (alpha (coeff base1 base0))))
            ("Subgoal 10" :in-theory (enable coeff))
            ("Subgoal 9" :in-theory (enable coeff))
            ("Subgoal 8" :in-theory (enable coeff zero-dot-to-zero-polyp)
                               :use (:instance linearly-dependent-suff
                                               (x base1)
                                               (y base0)
                                               (a (coeff base1 base0))))
            ("Subgoal 7" :in-theory (enable coeff zero-dot-to-zero-polyp)
                               :use (:instance linearly-dependent-suff
                                               (x base1)
                                               (y base0)
                                               (a (coeff base1 base0))))
            ("Subgoal 6" :in-theory (enable coeff))
            ("Subgoal 5" :in-theory (enable coeff poly-equiv-reduction))
            ("Subgoal 4" :in-theory (current-theory :here))
            ("Subgoal 3" :in-theory (current-theory :here))
            ("Subgoal 2" :in-theory (current-theory :here))
            ("Subgoal 1" :in-theory (current-theory :here))
            ))
                                                     
  )

(include-book "coi/quantification/quantified-congruence" :dir :system)

(quant::congruence linearly-dependent (x y)
  (exists (a) (and (not (equal (rfix a) 0)) (zero-polyp (add x (scale y (- (rfix a)))))))
  :congruences ((x poly-equiv)
                (y poly-equiv))
  ;; :hyps (lambda (x1 y1 x2 y2) 
  ;;         (and (poly-equiv x1 x2)
  ;;              (poly-equiv y1 y2)))
  )

(defcong poly-equiv iff (linearly-dependent x y) 1
  :hints (("Goal" :use (:instance LINEARLY-DEPENDENT-CONGRUENCE
                                  (x x)
                                  (x1 x-equiv)
                                  (y y)
                                  (y1 y)))))

(defcong poly-equiv iff (linearly-dependent x y) 2
  :hints (("Goal" :use (:instance LINEARLY-DEPENDENT-CONGRUENCE
                                  (x x)
                                  (x1 x)
                                  (y y)
                                  (y1 y-equiv)))))

(defthm linearly-dependent-scale
  (iff (linearly-dependent z (scale p a))
       (if (= (rfix a) 0) (zero-polyp z)
         (linearly-dependent z p)))
  :hints (("Subgoal 2" :in-theory (enable zero-polyp-definition rfix)
           :use (:instance linearly-dependent-suff
                           (x (scale p a))
                           (y p)
                           (a (rfix a))))
          ("Subgoal 1" :in-theory (enable zero-polyp-definition rfix)
           :use (:instance linearly-dependent-suff
                           (x (scale p a))
                           (y p)
                           (a (rfix a))))))

(defthmd linearly-dependent-rewrite-equiv
  (implies
   (linearly-dependent x y)
   (and (not (equal (linearly-dependent-witness (hide x) y) 0))
        (hide (rewrite-equiv (poly-equiv x (scale y (linearly-dependent-witness (hide x) y)))))))
  :hints (("Goal" :in-theory (enable zero-polyp-definition linearly-dependent)
           :expand (:free (x) (hide x)))))

(defthmd inner-product-rewrite
  (iff (equal (* (dot x x)
                 (dot y y))
              (expt (dot x y) 2))
       (if (zero-polyp x) t
         (if (zero-polyp y) t
           (if (linearly-dependent x y) t
             (poly-equiv x y)))))
  :otf-flg t
  :hints ((and stable-under-simplificationp
               '(:cases ((zero-polyp x))))
          (and stable-under-simplificationp
               '(:cases ((zero-polyp y))))
          (and stable-under-simplificationp
               '(:in-theory (disable ZERO-POLYP-SCALE)
                            :use linearly-dependent-rewrite-equiv))))
