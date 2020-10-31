(in-package "ACL2")

(include-book "pot")
(include-book "disjoint")

(def::type-list rational
  :type-fix rfix
  :type-p   rationalp
  :define-type-list nil
  :witness acl2::defthm
  )

;; So a basis set is organized as follows 
;;
;;    P0 =  B0
;; ^  P1 = c10  B1
;; |  P2 = c20 c21  B2
;;    P3 = c30 c31 c32  B3
;;                <--

(fty::defprod+ basis
  (
   (base   poly-p)
   (coeffs rational-listp)
   (poly   poly-p)
   ))

(in-theory (disable BASIS->BASE$INLINE-OF-BASIS-FIX-BASIS-INSTANCE-NORMALIZE-CONST))
(in-theory (disable BASIS->POLY$INLINE-OF-BASIS-FIX-BASIS-INSTANCE-NORMALIZE-CONST))

(def::type-list basis)

(defthm open-consp-rational-list-equiv-1
  (implies (and
            (syntaxp (and (symbolp x) (symbolp y)))
            (or (consp x) (consp y)))
           (equal (rational-list-equiv x y)
                  (and (consp x)
                       (consp y)
                       (equal (rfix (car x)) (rfix (car y)))
                       (rational-list-equiv (cdr x) (cdr y)))))
  )
(in-theory (disable open-consp-rational-list-equiv))
(in-theory (enable equal-rfix-to-rfix-equiv))

(def::un basis-list-polys (bases)
  (declare (xargs :signature ((t) poly-listp)
                  :congruence ((basis-list-equiv) equal)))
  (if (not (consp bases)) nil
    (let ((basis (basis-fix! (car bases))))
      (cons (basis->poly basis)
            (basis-list-polys (cdr bases))))))

(def::un basis-list-bases (bases)
  (declare (xargs :signature ((t) poly-listp)
                  :congruence ((basis-list-equiv) equal)))
  (if (not (consp bases)) nil
    (let ((basis (basis-fix! (car bases))))
      (cons (basis->base basis)
            (basis-list-bases (cdr bases))))))

(def::un reconstruct-partial (coeffs bases)
  (declare (xargs :guard (equal (len coeffs) (len bases))
                  :congruence ((rational-list-equiv basis-list-equiv) poly-equiv)
                  :signature ((rational-listp basis-listp) poly-p)
                  :signature-hints (("Goal" :in-theory (disable (reconstruct-partial))))))
  (cond
   ((and (consp coeffs) (consp bases))
    (let ((coeff (rfix (car coeffs)))
          (basis (car bases)))
      (add (scale (basis->poly basis) coeff)
           (reconstruct-partial (cdr coeffs) (cdr bases)))))
   (t (zero-poly))))

(in-theory (disable (reconstruct-partial)))

(def::un wf-basis-p (basis)
  (declare (type t basis))
  (and (basis-p basis)
       (not (zero-polyp (basis->base basis)))))

(def::un wf-basis-entry (basis bases)
  (declare (type t basis bases))
  (and (wf-basis-p basis)
       (equal (len (basis->coeffs basis)) (len bases))
       (all-zero (dot-list (basis->base basis)
                           (basis-list-bases bases)))
       (poly-equiv (basis->poly basis)
                   (add (basis->base basis)
                        (reconstruct-partial  
                         (basis->coeffs basis) 
                         (basis-list-fix bases))))))

(def::un wf-basis-listp (bases)
  (declare (type t bases))
  (if (not (consp bases)) (null bases)
    (let ((basis (car bases)))
      (and (wf-basis-entry basis (cdr bases))
           (wf-basis-listp (cdr bases))))))

(defthm wf-basis-listp-implies-basis-listp
  (implies
   (wf-basis-listp list)
   (basis-listp list))
  :rule-classes (:forward-chaining))

;; (def::un repair-residual (residual coeffs bases)
;;   (declare (xargs :signature ((poly-p rational-listp basis-listp) poly-p)
;;                   :measure (len bases)))
;;   (if (not (and (consp coeffs) (consp bases))) (poly-fix residual)
;;     (let ((basis (car bases))
;;           (coeff (rfix (car coeffs))))
;;       (if (<= 0 coeff) (repair-residual residual (cdr coeffs) (cdr bases))
;;         ;; poly = base + (coeffs * bases)
;;         (let ((coeff (- coeff)))
;;           (let ((residual (add residual (scale (basis->poly basis) coeff))))
;;             (let ((coeffs (add-coefficients (cdr coeffs) (scale-coefficients coeff (basis->coeffs basis)))))
;;               (repair-residual residual coeffs (cdr bases)))))))))

;; (def::un effective-coefficients (coeffs bases)
;;   (declare (xargs :signature ((rational-listp basis-listp) rational-listp)
;;                   :measure (len bases)))
;;   (if (not (and (consp coeffs) (consp bases))) nil
;;     (let ((basis (car bases))
;;           (coeff (rfix (car coeffs))))
;;       (if (<= 0 coeff) (effective-coefficients (cdr coeffs) (cdr bases))
;;         ;; poly = base + (coeffs * bases)
;;         (cons (- coeff)
;;               (let ((coeffs (add-coefficients (cdr coeffs) (scale-coefficients coeff (basis->coeffs basis)))))
;;                 (effective-coefficients coeffs (cdr bases))))))))

(def::un poly-representation (poly bases)
  (declare (xargs :signature ((poly-p basis-listp) poly-p rational-listp)
                  :congruence ((poly-equiv basis-list-equiv) poly-equiv equal)))
  (if (not (consp bases)) (mvlist poly nil)
    (let ((basis (basis-fix! (car bases))))
      (let ((coeff (coeff poly (basis->base basis))))
        (let ((poly (add poly (scale (basis->poly basis) (- coeff)))))
          (metlist ((poly coeffs) (poly-representation poly (cdr bases)))
            (mvlist poly (cons coeff coeffs))))))))

;; What *is* important is that base of the current poly
;; is disjoint from the remaining polys.

(include-book "visualize")

(defthm add-associate
  (poly-equiv (add (add x y) z)
              (add x (add y z))))

(encapsulate
    ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm scale-plus
    (implies
     (and (rationalp a) (rationalp b))
     (poly-equiv (scale x (+ a b))
                 (add (scale x a)
                      (scale x b))))
    :hints (("Goal" :in-theory (enable poly-equiv-reduction))))
  )

(defthm poly-representation-add
  (poly-equiv (val 0 (poly-representation (add x y) bases))
              (add (val 0 (poly-representation x bases))
                   (val 0 (poly-representation y bases)))))

(defthm add-opposites
  (implies
   (rationalp a)
   (poly-equiv (add (scale x a)
                    (scale x (- a)))
               (zero-poly)))
    :hints (("Goal" :in-theory (enable poly-equiv-reduction))))

(defthm reconstruct-partial-poly-representatation
  (implies
   (wf-basis-listp bases)
   (poly-equiv (add (val 0 (poly-representation poly bases)) 
                    (reconstruct-partial (val 1 (poly-representation poly bases)) bases))
               poly)))

(defthm len-poly-representation-coeffs
  (equal (len (val 1 (poly-representation poly bases)))
         (len bases)))

(defthm poly-representation-scale
  (poly-equiv (val 0 (poly-representation (scale p a) bases))
              (scale (val 0 (poly-representation p bases))
                     a)))

;; 

;; (defthm equiv-in-terms-of-base
;;   (poly-equiv (basis->base (car bases))
;;               (add (basis->poly basis)
;;                    (scale (reconstruct-partial  
;;                            (basis->coeffs basis) 
;;                            (basis-list-fix (cdr bases))) -1)))

;;   :hints ((rewrite-equiv-hint poly-equiv)
;;           (and stable-under-simplificationp
;;                '(:in-theory (enable poly-equiv-reduction)))))

;; So 

(defthm dot-base-reconstruct-partial-polys
  (implies
   (and
    (wf-basis-listp bases)
    (all-zero (dot-list base (basis-list-polys bases))))
   (equal (dot base (reconstruct-partial coeffs bases)) 0)))

(include-book "coi/util/rewrite-equiv" :dir :system)

(defthm all-zero-dot-list-basis-list-polys
  (implies
   (and
    (all-zero (dot-list base (basis-list-bases bases)))
    (wf-basis-listp bases))
   (all-zero (dot-list base (basis-list-polys bases))))
  :rule-classes (:rewrite :forward-chaining)
  :hints ((rewrite-equiv-hint poly-equiv)))

(defthm dot-disjoint-base-poly-representation
  (implies
   (and
    (syntaxp (not (equal base `(val (quote 0) (poly-representation ,poly ,bases)))))
    (all-zero (dot-list base (basis-list-polys bases))))
   (equal (dot base (val 0 (poly-representation poly bases)))
          (dot base poly))))

(defthm poly-representation-disjoint-poly
  (implies
   (all-zero (dot-list poly (basis-list-bases bases)))
   (poly-equiv (val 0 (poly-representation poly bases))
               poly)))

(defthm add-scale-2
  (implies
   (rfix-equiv r (double-rewrite (+ (rfix a) (rfix b))))
   (poly-equiv (add (scale p a)
                    (add (scale p b)
                         z))
               (add (scale p r) z))))

(defthm add-scale-1
  (implies
   (rfix-equiv r (double-rewrite (+ (rfix a) (rfix b))))
   (poly-equiv (add (scale p a)
                    (scale p b))
               (scale p r))))

(defthm add-scale-0
  (implies
   (rfix-equiv r (double-rewrite (+ 1 (rfix a))))
   (poly-equiv (add p (scale p a))
               (scale p r)))
  :hints (("Goal" :in-theory (e/d (poly-equiv-reduction)
                                  (add-scale-1)))))

(defthm poly-representation-zero-poly
  (implies
   (zero-polyp z)
   (poly-equiv (val 0 (poly-representation z bases))
               (zero-poly))))

(in-theory (disable SCALE-PLUS))

(include-book "arithmetic-5/top" :dir :system)

(defthm poly-equiv-add-same
  (iff (poly-equiv (add base x)
                   (add base y))
       (poly-equiv x y))
  :hints (("Subgoal 1" :in-theory (disable  POLY-EQUIV-IMPLIES-EQUAL-DOT-2)
           :use ((:instance POLY-EQUIV-REDUCTION)
                 (:instance poly-equiv-implication
                            (x (add base x))
                            (y (add base y))
                            (k (POLY-EQUIV-WITNESS X Y)))))))

(defthm poly-equiv-add-base
  (iff (poly-equiv (add base x)
                   base)
       (zero-polyp x))
  :hints (("Goal" :cases ((zero-polyp base)))
          ("Subgoal 2.1" :in-theory (disable POLY-EQUIV-IMPLIES-EQUAL-DOT-2
                                             POLY-EQUIV-IMPLIES-EQUAL-DOT-1)
           :use ((:instance POLY-EQUIV-IMPLIES-EQUAL-DOT-1
                            (x base)
                            (x-equiv (add base x))
                            (y x))))))

(defthmd zero-polyp-dot-k
  (implies
   (zero-polyp x)
   (equal (dot k x) 0)))

(defthm zero-polyp-scale
  (iff (zero-polyp (scale poly a))
       (or (zero-polyp poly)
           (equal (rfix a) 0)))
  :hints (("Subgoal 3" :use (:instance zero-polyp-dot-k
                                       (x (scale poly a))
                                       (k poly)))
          ("Subgoal 1" :in-theory (enable ZERO-POLYP-DEFINITION
                                          poly-equiv-reduction))))

(defthm zero-polyp-add
  (iff (zero-polyp (add x y))
       (poly-equiv x (scale y -1)))
  :hints (("Goal" :in-theory (enable ZERO-POLYP-DEFINITION))
          (skosimp-inst)))

(defthmd all-zero-dot-list-scale
  (iff (all-zero (dot-list (scale p a) list))
       (or (equal (rfix a) 0)
           (all-zero (dot-list p list))))
  :hints (("Goal" :in-theory (e/d (rfix-equiv)
                                  (EQUAL-RFIX-TO-RFIX-EQUIV)))))

(defthm all-zero-dot-list-scale-case-split
  (implies
   (case-split (not (equal (rfix a) 0)))
   (iff (all-zero (dot-list (scale p a) list))
        (all-zero (dot-list p list))))
  :hints (("Goal" :in-theory (enable all-zero-dot-list-scale))))

(defthm all-zero-dot-list-add
  (implies
   (all-zero (dot-list base basis-list))
   (iff (all-zero (dot-list (add poly base) basis-list))
        (all-zero (dot-list poly basis-list)))))

(defthm coeff-poly-base
  (implies
   (and
    (POLY-EQUIV poly (ADD base (RECONSTRUCT-PARTIAL coeffs bases)))
    (wf-basis-listp bases)
    (all-zero (dot-list base (basis-list-bases bases))))
   (equal (coeff poly base) 
          (if (or (zero-polyp poly) (zero-polyp base)) 0 1)))
  :hints (("Goal" :induct (RECONSTRUCT-PARTIAL coeffs bases)
           :do-not-induct t)))

(defthm poly-equiv-scale-zero-poly
  (iff (poly-equiv (scale p a) (zero-poly))
       (or (equal (rfix a) 0)
           (poly-equiv p (zero-poly))))
  :hints ((skosimp-inst)))

(defthm val0-poly-representation-reconstruct-partial
  (implies
   (wf-basis-listp bases)
   (poly-equiv (val 0 (poly-representation (reconstruct-partial coeffs bases) bases))
               (zero-poly)))
  :hints (("Goal" :induct (reconstruct-partial coeffs bases)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:expand (:free (poly) (POLY-REPRESENTATION poly BASES))))
          ;;(rewrite-equiv-hint poly-equiv)))
          ))

(defthm denormal-coeff
  (equal (* (coeff poly base)
            (dot base base))
         (dot poly base))
  :hints (("Goal" :in-theory (enable coeff))))

(defthm zero-coeff-to-zero-dot
  (implies
   (case-split (not (zero-polyp base)))
   (iff (equal (coeff poly base) 0)
        (equal (dot poly base) 0)))
  :hints (("Goal" :in-theory (enable coeff))))

(defthm all-zero-dot-list-base-poly-representation
  (implies
   (wf-basis-listp bases)
   (all-zero (dot-list (val 0 (poly-representation poly bases))
                       (basis-list-bases bases))))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((poly-representation poly bases))))
  :hints (("Goal" :induct (poly-representation poly bases)
           :in-theory (e/d (rfix-equiv)
                           (EQUAL-RFIX-TO-RFIX-EQUIV)))
          (rewrite-equiv-hint poly-equiv)))

(def::und add-poly-to-bases (poly bases)
  (declare (xargs :signature ((poly-p wf-basis-listp) wf-basis-listp)))
  (metlist ((base coeffs) (poly-representation poly bases))
    (if (zero-polyp base) bases
      (cons (basis base coeffs poly) bases))))

(defthm non-zero-dot-implies-non-zero-poly
  (implies
   (not (equal (dot x y) 0))
   (and (not (zero-polyp x))
        (not (zero-polyp y))))
  :rule-classes (:forward-chaining))

(encapsulate
    ()

  (local
   (defthmd add-non-zero-poly-to-bases-helper
     (implies
      (and
       (not (equal (dot base (val 0 (poly-representation poly bases))) 0))
       (wf-basis-listp bases)
       (all-zero (dot-list base (basis-list-bases bases))))
      (equal (add-poly-to-bases poly bases)
             (metlist ((base coeffs) (poly-representation poly bases))
               (cons (basis base coeffs poly) bases))))
     :hints (("Goal" :do-not-induct t :in-theory (e/d (add-poly-to-bases)
                                                      (dot-disjoint-base-poly-representation))))))

  (defthm add-non-zero-poly-to-bases
    (implies
     (and
      (not (equal (dot base poly) 0))
      (wf-basis-listp bases)
      (all-zero (dot-list base (basis-list-bases bases))))
     (equal (add-poly-to-bases poly bases)
            (metlist ((base coeffs) (poly-representation poly bases))
              (cons (basis base coeffs poly) bases))))
    :hints (("Goal" :use add-non-zero-poly-to-bases-helper
             :in-theory `(all-zero-dot-list-basis-list-polys
                          dot-disjoint-base-poly-representation))))

  )

(def::un scale-coefficients (coeff clist)
  (declare (xargs :signature ((rationalp rational-listp) rational-listp)))
  (if (not (consp clist)) nil
    (let ((c (car clist)))
      (cons (* (rfix coeff) (rfix c))
            (scale-coefficients coeff (cdr clist))))))

(def::signature scale-coefficients (t t) rational-listp)

(defthm len-scale-coefficients
  (equal (len (scale-coefficients coeff clist))
         (len clist)))

(def::un add-coefficients (clist1 clist2)
  (declare (xargs :signature ((rational-listp rational-listp) rational-listp)))
  (if (not (and (consp clist1) (consp clist2))) nil
    (let ((c1 (car clist1))
          (c2 (car clist2)))
      (cons (+ (rfix c1) (rfix c2))
            (add-coefficients (cdr clist1) (cdr clist2))))))

(def::signature add-coefficients (t t) rational-listp)

(defthm len-add-coefficients
  (equal (len (add-coefficients clist1 clist2))
         (min (len clist1) (len clist2))))

(defthm scale-zero-poly
  (implies
   (zero-polyp zpoly)
   (poly-equiv (scale zpoly m) zpoly)))

(encapsulate
    ()

  (local
   (defthmd non-zero-val-0-poly-representation-helper
     (implies
      (and
       (not (equal (dot base poly) 0))
       (wf-basis-listp bases)
       (all-zero (dot-list base (basis-list-bases bases))))
      (not (zero-polyp (val 0 (poly-representation poly bases)))))
     :hints (("Goal" :in-theory (e/d (ZERO-POLYP-DEFINITION)
                                     (POLY-EQUIV-IMPLIES-EQUAL-DOT-2))
              :use (:instance poly-equiv-implication
                              (x (val 0 (poly-representation poly bases)))
                              (y (zero-poly))
                              (k base))
              :do-not-induct t))))

  (defthm non-zero-val-0-poly-representation
    (implies
     (and
      (< (coeff base poly) 0)
      (wf-basis-listp bases)
      (all-zero (dot-list base (basis-list-bases bases))))
     (not (zero-polyp (val 0 (poly-representation poly bases)))))
    :hints (("Goal" :use non-zero-val-0-poly-representation-helper)))

  )

;; (dot (add (basis->base basis) (scale base (- (coeff poly (basis->base basis))))) poly)

(def::un update-fred (poly basis bases)
  (declare (xargs :signature ((poly-p wf-basis-p wf-basis-listp) basis-p basis-listp)
                  :signature-hints (("Goal" :do-not-induct t))))
  (let ((coeff (coeff poly (basis->base basis))))
    (if (<= 0 coeff) (mv basis bases)
      (metlist ((poly-base coeffs) (poly-representation poly bases))
        ;; Technically just compensating for the magnitude of base
        (let ((coeff (coeff (basis->base basis) poly-base)))
          (let ((basis->base  (add (basis->base basis) (scale poly-base (- coeff))))
                (basis->coeff (cons coeff (add-coefficients (basis->coeffs basis) (scale-coefficients (- coeff) coeffs))))
                (basis->poly  (basis->poly basis)))
            (if (zero-polyp basis->base) (mv basis bases)
              (mv (basis basis->base basis->coeff basis->poly)
                  (cons (basis poly-base coeffs poly) bases)))))))))

(defthm all-zero-dot-list-add-2
  (implies (all-zero (dot-list base basis-list))
           (iff (all-zero (dot-list (add base poly) basis-list))
                (all-zero (dot-list poly basis-list))))
  :hints (("goal" :in-theory (disable all-zero-dot-list-add)
           :use all-zero-dot-list-add)))

(defthm all-zero-scale-coefficients
  (implies
   (equal (rfix m) 0)
   (all-zero (scale-coefficients m list))))

(defthm all-all-zero-coefficients
  (implies
   (and (all-zero y) (force (equal (len x) (len y))))
   (equal (add-coefficients x y)
          (rational-list-fix x))))

(defthm reconstruct-partial-add-coefficients
  (implies
   (force (equal (len x) (len y)))
   (poly-equiv (reconstruct-partial (add-coefficients x y) bases)
               (add (reconstruct-partial x bases)
                    (reconstruct-partial y bases)))))

(defthm reconstruct-partial-scale-coefficients
  (poly-equiv (reconstruct-partial (scale-coefficients m list) bases)
              (scale (reconstruct-partial list bases) m)))

(defthm reconstruct-scaled-partial-poly-representatation
  (implies
   (wf-basis-listp bases)
   (poly-equiv (add (scale (val 0 (poly-representation poly bases)) m)
                    (scale (reconstruct-partial (val 1 (poly-representation poly bases)) bases) m))
               (scale poly m))))

(defthm wf-basis-entry-update-fred
  (implies
   (and
    (wf-basis-listp bases)
    (wf-basis-entry basis bases))
   (wf-basis-entry (val 0 (update-fred poly basis bases))
                   (val 1 (update-fred poly basis bases))))
  :hints (("Goal" :in-theory (e/d (rfix-equiv)
                                  (equal-rfix-TO-RFIX-EQUIV))
           :do-not-induct t)))

;; To remove a base, we eliminate its 
;;
;;    P0 =  B0
;; ^  P1 = c10  B1
;; |  P2 = c20 c21  B2
;;    P3 = c30 c31 c32  B3
;;                <--

(def::und extract-nth (n coeffs)
  (declare (xargs :signature ((natp rational-listp) rationalp rational-listp)))
  (if (not (consp coeffs)) (mv 0 nil)
    (if (zp n) (mv (rfix (car coeffs)) (cdr coeffs))
      (extract-nth (1- (nfix n)) (cdr coeffs)))))

(def::und drop-nth-poly-basis (n nth-poly basis)
  (declare (xargs :signature ((natp poly-p basis-p) basis-p)))
  (let ((coeffs (basis->coeffs basis))
        (base   (basis->base   basis))
        (poly   (basis->poly   basis)))
    (met ((m coeffs) (extract-nth n coeffs))
      (let ((base (add base (scale nth-poly m))))
        (basis base coeffs poly)))))

(def::signature drop-nth-poly-basis (t t t) basis-p
  :hints (("Goal" :in-theory (enable drop-nth-poly-basis))))

(defthm wf-basis-drop-nth-poly-basis
  (implies
   (and
    (wf-basis-p basis)
    (equal (dot nth-poly (basis->base basis)) 0))
   (wf-basis-p (drop-nth-poly-basis n nth-poly basis)))
  :hints (("Goal" :in-theory (enable drop-nth-poly-basis))))

(def::un drop-nth-poly (n nth-poly bases)
  (declare (xargs :signature ((natp poly-p basis-listp) basis-listp)))
  (if (not (consp bases)) nil
    (if (zp n) (cdr bases)
      (let ((basis (drop-nth-poly-basis n nth-poly (car bases))))
        (cons basis (drop-nth-poly (1- n) nth-poly (cdr bases)))))))

(defthm len-drop-nth-poly
  (equal (len (drop-nth-poly n nth-poly bases))
         (if (< (nfix n) (len bases)) (1- (len bases))
           (len bases))))

(defthm all-zero-dot-list-drop-nth-poly
  (implies
   (and
    (equal (dot base nth-poly) 0)
    (all-zero (dot-list base (basis-list-bases bases))))
   (all-zero (dot-list base (basis-list-bases (drop-nth-poly n nth-poly bases)))))
  :hints (("goal" :in-theory (enable drop-nth-poly-basis)
           :induct (drop-nth-poly n nth-poly bases))))

#+joe
(defthm all-zero-dot-list-nth-poly-drop-nth-poly
  (implies
   (and
    (poly-equiv nth-poly (basis->poly (nth n bases)))
    (wf-basis-listp bases))
   (all-zero (dot-list nth-poly (basis-list-bases (drop-nth-poly n nth-poly bases)))))
  :hints (("Goal" :in-theory (enable drop-nth-poly-basis)
           :do-not-induct t
           :induct (drop-nth-poly n nth-poly bases))))

(defthm all-zero-dot-list-zero-poly
  (implies
   (zero-polyp zpoly)
   (all-zero (dot-list zpoly list))))

(defthm wf-basis-list-drop-nth-poly
  (implies
   (and
    (< (nfix n) (len bases))
    (poly-equiv nth-poly (basis->poly (nth n bases)))
    (all-zero (dot-list nth-poly (firstn n (basis-list-bases bases))))
    (wf-basis-listp bases))
   (wf-basis-listp (drop-nth-poly n nth-poly bases)))
  :hints (("Goal" :in-theory (enable drop-nth-poly-basis)
           :induct (drop-nth-poly n nth-poly bases)
           :do-not-induct t)))

;; ** So the problem is that if you simply remove nth-poly from each
;; base the bases are no longer disjoint.  In other words: it isn't so
;; simple.

;; So what do we need to do?

;; Pk = a*P0 + b*Pi + c*PN + <Bk>
;; Pm = d*P0 + e*Pi + f*PN + g*Pk + <Bm>

;; Pk = a*P0 + c*PN + < b*Pi + Bk >  <<- This is disjoint from all previous bases
;;
;; <Pm,b*Bi + Bk> b*
;;
;; Pm = d*P0 + f*PN +          g*Bk + e*Pi + <Bm>

;;  V
;;  1 2
;;  3 4 5
;;  6 7 8 9
;;  a b c d e
;;  f g h i j k
;; --------------
;;  l m n o p q r
;;  + - - - - - -

;; What if we moved the base one at a time?

;;  Pi : W Bi
;;  Pj : X  a  Bj

Pj = X + aPi + Bj
   = X + a(W + Bi) + Bj
   = (X + a*W) + < (aBi + Bj) >

(aBi + Bj)(wBi + mBj) = 0

aw + m = 0
     m = -aw

Pi = (W - (X + aW)  +   1(Pj) +  < Bi - Bj >
   = W - (X + aW) + (X + a*W) + (aBi + Bj) + (1-a)*Bi - Bj
   = W + (aBi + Bj) + (1-a)*Bi - Bj
   = W + Bi

    wPi + mPj

;; So we need to invert the matrix ..

;; If we were dealing with the bases, rather than the polys,
;; 

;;  0            V <- removing this one ..
;;  0 2          1 
;;  0 4 5        3 
;;  0 7 8 9      6 
;;  0 b c d e    a 
;;  0 g h i j k  f 
;; ----------------
;;  0 m n o p q l+r

;;  0            V
;;  0 2          1 <- use to remove MSB
;;  0 X 5        0 
;;  0 X 8 9      0 
;;  0 X c d e    0 
;;  0 X h i j k  0 
;; ----------------
;;  0 X n o p q l+r

;;  0            V
;;  0 2 W X Y Z  0
;;  0 X 5        0 
;;  0 X 8 9      0 
;;  0 X c d e    0 
;;  0 X h i j k  0 
;; ----------------
;;  0 X n o p q l+r <- use to remove MSB residual

;;  0            V
;;  0 2 W X Y 0  0
;;  0 X 5        0 
;;  0 X 8 9      0 
;;  0 X c d e    0 
;;  0 X h i j k  0  <- use to remove 2nd residual
;; ----------------
;;  0 X n o p q l+r

;;  0            V
;;  0 2 W X 0 0  0
;;  0 X 5        0 
;;  0 X 8 9      0 
;;  0 X c d e    0  <- use to remove 3rd residual
;;  0 X h i j k  0
;; ----------------
;;  0 X n o p q l+r


;;  0            V
;;  0 2 0 0 0 0  0
;;  0 X 5        0 
;;  0 X 8 9      0 
;;  0 X c d e    0  <- use to remove 3rd residual
;;  0 X h i j k  0
;; ----------------
;;  0 X n o p q l+r

;; What if we used

;; But do you have any reason to believe that the resulting
;; basis sets are actually disjoint?


;; What if we replaced basis (i) with basis (n)
;; 

;; p0: w
;; p1: A x       <- remove
;; p2: B C y
;; --:-----
;; p3: D E F z
;;  c: - + - - r

;; [ a b c ] [ d e f g ] <b>

;; p1 = A*p0 + x
;; p3 = D*p0 + E*p1 + F*p2 + z

;; p1 = (-D*p0 - F*p2 - z + p3)/E

;; Of course you could just recompute everything from
;; first principles.
;;

;; V = -a*P0 +b*P1 -c*P2 + <R>
;; V = -a*P0 -c*P2 + <R + b*P1>
;;
;; Conversely, you could compute the inner product as the product of
;; all of the positive coefficients (as opposed to just the last
;; positive coefficient) .. since technically that is what you will
;; have as a residual when you are done.
;; 

(def::un reconstruct-positive (coeffs bases)
  (declare (xargs :guard (equal (len coeffs) (len bases))
                  :congruence ((rational-list-equiv basis-list-equiv) poly-equiv)
                  :signature ((rational-listp basis-listp) poly-p)
                  :signature-hints (("Goal" :in-theory (disable (reconstruct-partial))))))
  (cond
   ((and (consp coeffs) (consp bases))
    (let ((coeff (rfix       (car coeffs)))
          (basis (basis-fix! (car bases))))
      (cond
       ((<= coeff 0) (reconstruct-partial (cdr coeffs) (cdr bases)))
       (t 
        (add (scale (basis->poly basis) coeff)
             (reconstruct-partial (cdr coeffs) (cdr bases)))))))
   (t (zero-poly))))

(def::un update-zed (poly basis bases)
  (declare (xargs :signature ((poly-p wf-basis-p wf-basis-listp) basis-p basis-listp)
                  :signature-hints (("Goal" :do-not-induct t))))
  (let ((base0 (add (basis->base basis) (reconstruct-positive coeffs bases))))
    (let ((coeff (coeff poly base0)))
      (if (<= 0 coeff) (mv nil basis bases)
        (metlist ((poly-base coeffs) (poly-representation poly bases))
          ;; Technically just compensating for the magnitude of base
          (let ((coeff (coeff base0 poly-base)))
            (let ((basis->base  (add (basis->base basis) (scale poly-base (- coeff))))
                  (basis->coeff (cons coeff (add-coefficients (basis->coeffs basis) (scale-coefficients (- coeff) coeffs))))
                  (basis->poly  (basis->poly basis)))
              (if (zero-polyp basis->base) (mv basis bases)
                (mv (basis basis->base basis->coeff basis->poly)
                    (cons (basis poly-base coeffs poly) bases))))))))))

;; So where are we going with all this?
;;
;; Right .. so we don't want the reference vector 
;; expressed in terms of positive coefficients.
;;
;; For now we can just recompute the basis set.
;; 
;; a  b  p0
;; c  d  e  p1
;; a  b  p0 

;; 2 0
;; 3 1

;; Given the following set of equations:

;; a = 3w + x
;; b = 2w + 4a + z

;; We want to swap the row positions of (a) and (b).
;; We do this as follows:
;;
;; 1. Solve for a in terms of b (using b)
;; 2. Substitute the definiton of (a) into b
;;

;; a = -1/2(w) + 1/4(b) - 1/4(z)
;; b = 2w + 4(3w + x) + z

;; b =   14(w) + (4x + z)
;; a = -1/2(w) + 1/4(b) - 1/4(z)

;; Except now the residuals aren't right ..

;; b =   14(w) + (4x + z)
;; a = -1/2(w) + 1/4(b) - 1/4(z)

;; I really don't see a way to do this that is any more efficient than
;; simply re-computing the basis set.

;; When we replay we actually move the (defun replay)
;; 

(defun attempt-constraints (hit list rest basis bases)
  (if (not (consp list)) (mv hit rest basis bases)
    (let ((poly (car list)))
      (cond
       ((< (dot poly (basis->base basis)) 0)
        (met (() )
          (attempt-constraints hit list rest basis bases)))
       (t
        (attempt-constraints hit (cdr list) (cons poly rest) basis bases))))))

(defun fred (list basis bases)
  (met ((hit list basis bases) (attempt-constraints nil list basis basis))
    (cond 
     ((not hit) ;; all non-negative
      (mv list basis bases))
     (t (fred list basis bases)))))

  
