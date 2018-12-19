(in-package "ACL2")

(include-book "linear")
#|

(def::un reconstruct-partial-offset (coeffs bases)
  (declare (xargs :guard (equal (len coeffs) (len bases))
                  :congruence ((rational-list-equiv basis-list-equiv) poly-equiv)
                  :signature ((rational-listp basis-listp) poly-p)
                  :signature-hints (("Goal" :in-theory (disable (reconstruct-partial-offset))))))
  (cond
   ((and (consp coeffs) (consp bases))
    (let ((coeff (rfix (car coeffs)))
          (basis (car bases)))
      (add (scale (basis->base basis) coeff)
           (reconstruct-partial-offset (cdr coeffs) (cdr bases)))))
   (t (zero-poly))))

(defthm reconstruct-partial-definition
  (poly-equiv (reconstruct-partial residual coeffs bases)
              (add residual (reconstruct-partial-offset coeffs bases))))


(def::un repair-residual-offset (coeffs bases)
  (declare (xargs :signature ((rational-listp basis-listp) poly-p)
                  :measure (len bases)
                  :signature-hints (("Goal" :in-theory (disable (repair-residual-offset))))))
  (if (not (and (consp coeffs) (consp bases))) (zero-poly)
    (let ((basis (car bases))
          (coeff (rfix (car coeffs))))
      (if (<= 0 coeff) (repair-residual-offset (cdr coeffs) (cdr bases))
        ;; poly = base + (coeffs * bases)
        (let ((coeff (- coeff)))
          (let ((coeffs (add-coefficients (cdr coeffs) (scale-coefficients coeff (basis->coeffs basis)))))
            (add (scale (basis->poly basis) coeff)
                 (repair-residual-offset coeffs (cdr bases)))))))))

(defthm repair-residual-definition
  (poly-equiv (repair-residual residual coeffs bases)
              (add residual (repair-residual-offset coeffs bases))))


#+joe
(def::un-sk poly-equiv-quant (x y)
  (forall (z) (equal (dot x z) (dot y z))))

(defun len-len-len-induction (x y bases)
  (if (and (consp x) (consp y) (consp bases))
      (len-len-len-induction (cdr x) (cdr y) (cdr bases))
    (and (not (consp x))
         (not (consp y))
         (not (consp bases)))))

(defthmd equal-len
  (implies
   (len-len-len-induction x y z)
   (and (equal (len x) (len y))
        (equal (len x) (len z)))))

(defthm reconstruct-partial-offset-add-coefficients
  (implies
   (len-len-len-induction x y bases)
   (poly-equiv (reconstruct-partial-offset (add-coefficients x y) bases)
               (add (reconstruct-partial-offset x bases)
                    (reconstruct-partial-offset y bases))))
  :hints (("Goal" :induct (len-len-len-induction x y bases)
           :do-not-induct t
           :do-not '(generalize))
          (skosimp-inst)))

;; OK .. back to the hard part .. we need to express what we are
;; actually doing .. in a more primitive manner.

;; Is there any other property that we care about?
;; The resulting vector is positive w/to 

(defthm alpha-beta
  (implies
   (wf-basis-list bases)
   (non-negative-dotsp (repair-residual-offset coeffs bases) bases)))

#+joe
(defthm repair-residual-abstraction
  (implies
   (wf-basis-list bases)
   (poly-equiv (repair-residual-offset coeffs bases)
               (reconstruct-partial-offset (effective-coefficients coeffs bases) bases)))
  :hints (("Goal" :induct (repair-residual-offset coeffs bases)
           :expand ((effective-coefficients coeffs bases))
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))
          (skosimp-inst)))


#+joe
(defthm non-negative-dotsp-repair-residual
  (implies
   (and
    (non-negative-dotsp residual bases)
    (wf-basis-list bases))
   (non-negative-dotsp (repair-residual residuasl coeffs bases) bases))
  :hints (("Goal" :induct (repair-residual residuasl coeffs bases)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))
|#
