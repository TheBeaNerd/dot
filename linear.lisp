(in-package "ACL2")

(include-book "pot")

;; If there is a solution to all these polys, the vector from the
;; current solution to it must be positive w/to all the zero and
;; negative polys.

(def::un sub (x y)
  (declare (xargs :signature ((poly-p poly-p) poly-p)
                  :congruence ((poly-equiv poly-equiv) poly-equiv)))
  (add x (scale y -1)))

(defthm single-poly-case
  (implies
   (and
    (rationalp n)
    (not (< n (dot poly sln0)))
    (< n (dot poly sln)))
   (< 0 (dot poly (sub sln sln0)))))

(defun non-zero-poly-listp (plist)
  (declare (type t plist))
  (if (not (consp plist)) t
    (and (not (zero-polyp (car plist)))
         (non-zero-poly-listp (cdr plist)))))

;; Given a list of non-zero polys
;; 
;; (b2 (a1  a0  ) . p2)
;;     (b1 (a0  ) . p1)
;;         (b0 () . p0)

(def::type-list rational
  :type-fix rfix
  :type-p   rationalp
  :define-type-list nil
  :witness acl2::defthm
  )

(fty::defprod+ basis
  (
   (base   poly-p)
   (coeffs rational-listp)
   (poly   poly-p)
   ))

(in-theory (disable BASIS->BASE$INLINE-OF-BASIS-FIX-X-NORMALIZE-CONST))
(in-theory (disable BASIS->POLY$INLINE-OF-BASIS-FIX-X-NORMALIZE-CONST))

(def::type-list basis)

(def::un zero-dotsp (residual bases)
  (declare (type t residual bases)
           (xargs :congruence ((poly-equiv basis-list-equiv) equal)))
  (if (not (consp bases)) t
    (let ((basis (basis-fix! (car bases))))
      (and (equal (dot (poly-fix residual) (basis->base basis)) 0)
           (zero-dotsp residual (cdr bases))))))

(def::un non-negative-dotsp (residual bases)
  (declare (type t residual bases)
           (xargs :congruence ((poly-equiv basis-list-equiv) equal)))
  (if (not (consp bases)) t
    (let ((basis (basis-fix! (car bases))))
      (and (equal (dot (poly-fix residual) (basis->poly basis)) 0)
           (non-negative-dotsp residual (cdr bases))))))

(def::un reconstruct-partial (partial coeffs bases)
  (declare (xargs :guard (equal (len coeffs) (len bases))
                  :congruence ((poly-equiv rational-list-equiv basis-list-equiv) poly-equiv)
                  :signature ((poly-p rational-listp basis-listp) poly-p)))
  (cond
   ((and (consp coeffs) (consp bases))
    (let ((coeff (rfix (car coeffs)))
          (basis (car bases)))
      (let ((partial (add partial (scale (basis->base basis) coeff))))
        (reconstruct-partial partial (cdr coeffs) (cdr bases)))))
   (t partial)))

(def::un wf-basis-list (bases)
  (declare (type t bases)
           (xargs :congruence ((basis-list-equiv) equal)))
  (if (not (consp bases)) t
    (let ((basis (basis-fix! (car bases))))
      (and (equal (len (basis->coeffs basis)) (len (cdr bases)))
           (poly-equiv (basis->poly basis)
                       (reconstruct-partial (basis->base basis) 
                                            (basis->coeffs basis) 
                                            (basis-list-fix (cdr bases))))
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

(def::un repair-residual (residual coeffs bases)
  (declare (xargs :signature ((poly-p rational-listp basis-listp) poly-p)
                  :measure (len bases)))
  (if (not (and (consp coeffs) (consp bases))) (poly-fix residual)
    (let ((basis (car bases))
          (coeff (rfix (car coeffs))))
      (if (<= 0 coeff) (repair-residual residual (cdr coeffs) (cdr bases))
        ;; poly = base + (coeffs * bases)
        (let ((coeff (- coeff)))
          (let ((residual (add residual (scale (basis->poly basis) coeff))))
            (let ((coeffs (add-coefficients (cdr coeffs) (scale-coefficients coeff (basis->coeffs basis)))))
              (repair-residual residual coeffs (cdr bases)))))))))

(def::un effective-coefficients (coeffs bases)
  (declare (xargs :signature ((rational-listp basis-listp) rational-listp)
                  :measure (len bases)))
  (if (not (and (consp coeffs) (consp bases))) nil
    (let ((basis (car bases))
          (coeff (rfix (car coeffs))))
      (if (<= 0 coeff) (effective-coefficients (cdr coeffs) (cdr bases))
        ;; poly = base + (coeffs * bases)
        (cons (- coeff)
              (let ((coeffs (add-coefficients (cdr coeffs) (scale-coefficients coeff (basis->coeffs basis)))))
                (effective-coefficients coeffs (cdr bases))))))))

;; What we want when this is all over is for the result to have a
;; positive inner product with all the polys.

#+joe
(def::un reduce (vector residual rest again bases)
  (declare (xargs :signature ((poly-p poly-p poly-listp poly-listp basis-listp) 
                              poly-p poly-listp basis-listp)))
  (if (not (consp rest)) (mv residual again bases)
    (let ((zed (car rest)))
      (let ((dot (dot residual zed)))
        (cond
         ((<= 0 zed)
          (reduce residual (cdr rest) (cons zed again) bases))
         (t
          ;; zed = base + (coeffs * bases)
          (met ((base coeffs) (factor-base zed bases))
            ;; (equal (dot residual base) dot)
            (let ((coeff (/ (- dot) (self-dot base))))
              (let ((residual (add residual (scale zed coeff))))
                (let ((coeffs (scale-coefficients coeff coeffs)))
                  (let ((residual (repair-residual residual coeffs bases)))
                    (let ((bases (cons (basis ) bases)))
                      (if (zero-polyp residual) (mv residual again bases)
                        (reduce vector residual (revappend again (cdr rest)) nil bases))))))))))))))
