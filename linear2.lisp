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

(def::un wf-basis-list (bases)
  (declare (type t bases)
           (xargs :congruence ((basis-list-equiv) equal)))
  (if (not (consp bases)) t
    (let ((basis (basis-fix! (car bases))))
      (and (equal (len (basis->coeffs basis)) (len (cdr bases)))
           (all-zero (dot-list (basis->base basis)
                               (basis-list-polys (cdr bases))))
           (poly-equiv (basis->poly basis)
                       (add (basis->base basis)
                            (reconstruct-partial  
                             (basis->coeffs basis) 
                             (basis-list-fix (cdr bases)))))
           (wf-basis-list (cdr bases))))))

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
   (wf-basis-list bases)
   (poly-equiv (add (val 0 (poly-representation poly bases)) 
                    (reconstruct-partial (val 1 (poly-representation poly bases)) bases))
               poly)))

