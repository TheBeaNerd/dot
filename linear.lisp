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


;; (def::un reduce-vector (vector plist bases)
;;   (if (not (consp list)) vector
;;     ..))
