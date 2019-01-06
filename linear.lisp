(in-package "ACL2")

(include-book "pot")

;; 1) skew/rewrite new vector
;; 2) decompose vector
;; 3) take action

;; A skew change of basis matrix is has the following form:

;; |x'| = | 1 0 || x |
;; |y'|   | c 1 || y |

(fty::defprod+ skew
  (
   (x  poly-p)
   (c  rationalp)
   (y  non-zero-polyp)
   )
  )

(def::type-list skew)

(def::un skew-list-poly (vector skews)
  (declare (xargs :signature ((poly-p skew-listp) poly-p)
                  :congruence ((poly-equiv skew-list-equiv) poly-equiv)))
  (if (not (consp skews)) vector
    (let ((skew (skew-fix (car skews))))
      (let ((vector (skew-poly vector (skew->x skew) (skew->c skew) (skew->y skew))))
        (skew-list-poly vector (cdr skews))))))

(def::un poly-coefficients (poly bases)
  (declare (xargs :signature ((poly-p non-zero-poly-listp) rational-listp)
                  :congruence ((poly-equiv non-zero-poly-list-equiv) equal)))
  (if (not (consp bases)) nil
    (let ((base (non-zero-poly-fix (car bases))))
      (let ((c (coeff base poly)))
        (cons c (poly-coefficients poly (cdr bases)))))))

(defthm len-poly-coefficients
  (equal (len (poly-coefficients poly bases))
         (len bases)))

(def::un reconstruct-poly (coeffs bases)
  (declare (xargs :signature ((rational-listp non-zero-poly-listp) poly-p)
                  :congruence ((rational-list-equiv non-zero-poly-list-equiv) poly-equiv)
                  :signature-hints (("Goal" :in-theory (disable (reconstruct-poly))))
                  :congruence-hints (("Goal" :in-theory (e/d (equal-rfix-to-rfix-equiv) ((reconstruct-poly)))))))
  (if (not (and (consp coeffs) (consp bases))) (zero-poly)
    (add (scale (non-zero-poly-fix (car bases)) (rfix (car coeffs)))
         (reconstruct-poly (cdr coeffs) (cdr bases)))))
      
(def::un disjoint-from-all (poly bases)
  (declare (type t poly bases)
           (xargs :congruence ((poly-equiv non-zero-poly-list-equiv) equal)))
  (if (not (consp bases)) t
    (and (= (dot (poly-fix poly) (non-zero-poly-fix (car bases))) 0)
         (disjoint-from-all poly (cdr bases)))))

(def::un mutually-disjoint (bases)
  (declare (type t bases)
           (xargs :congruence ((non-zero-poly-list-equiv) equal)))
  (if (not (consp bases)) t
    (and (disjoint-from-all (non-zero-poly-fix (car bases)) (cdr bases))
         (mutually-disjoint (cdr bases)))))

(defthm drop-irrelevant-addend
  (implies
   (disjoint-from-all x bases)
   (equal (disjoint-from-all (add a (add b x)) bases)
          (disjoint-from-all (add a b) bases))))

#|

(include-book "arithmetic-5/top" :dir :system)

(defthm decomposition-is-disjoint-from-all-bases
  (implies
   (mutually-disjoint bases)
   (disjoint-from-all (add poly (scale (reconstruct-poly (poly-coefficients poly bases) bases) -1))
                      bases))
  :hints (("Goal" :in-theory (enable coeff))))

(def::un all-zero (x)
  (declare (type t x)
           (xargs :congruence ((rational-list-equiv) equal)))
  (if (not (consp x)) t
    (and (= (rfix (car x)) 0)
         (all-zero (cdr x)))))

(def::un all-non-negative (x)
  (declare (type t x)
           (xargs :congruence ((rational-list-equiv) equal)))
  (if (not (consp x)) t
    (and (<= 0 (rfix (car x)))
         (all-non-negative (cdr x)))))
 
(def::un keep-non-negative-coefficients (x)
  (declare (xargs :signature ((t) rational-listp)
                  :congruence ((rational-list-equiv) rational-list-equiv)))
  (if (not (consp x)) nil
    (if (<= 0 (rfix (car x)))
        (cons (rfix (car x))
              (keep-non-negative-coefficients (cdr x)))
      (cons 0 (keep-non-negative-coefficients (cdr x))))))

(def::un keep-non-positive-coefficients (x)
  (declare (xargs :signature ((t) rational-listp)
                  :congruence ((rational-list-equiv) rational-list-equiv)))
  (if (not (consp x)) nil
    (if (<= (rfix (car x)) 0)
        (cons (rfix (car x))
              (keep-non-positive-coefficients (cdr x)))
      (cons 0 (keep-non-positive-coefficients (cdr x))))))

(defthmd keep-both-splits-list-conservatively
  (poly-equiv (reconstruct-poly x bases)
              (add (reconstruct-poly (keep-non-negative-coefficients x) bases)
                   (reconstruct-poly (keep-non-positive-coefficients x) bases))))

(def::un find-first-non-zero-contribution (coeffs)
  (declare (xargs :signature ((t) natp)
                  :congruence ((rational-list-equiv) equal)))
  (if (not (consp coeffs)) 1
    (let ((coeff (rfix (car coeffs))))
      (if (not (= coeff 0)) 0
        (1+ (find-first-non-zero-contribution (cdr coeffs)))))))

(def::und make-skew ()


  (replace-nth-base n base bases)
  

;; equiv
;; 


(defun add-poly (poly bases)
  (if (zero-polyp poly) bases
    (let ((coeffs (poly-coefficients poly bases)))
      (if (all-zero coeffs) (cons poly bases)
        (let ((residual (add poly (scale (reconstruct-poly coeffs bases) -1))))
          (cond
           ((zero-polyp residual) 
            ((all-negative coeffs)
             ..)
            (t
             bases))
           (t
            ;; We need to do some repair
            ((zero-poly-p residual)
             (if (all-non-negative coeffs) bases
               (let ((n (find-first-non-zero-contribution coeffs)))
                 (cond
                  ((< n (len coeffs))
                   ..)
                  ()))))
            (t
        (if (all-
            ((all-negative coeffs)
          ;; equality
          ;; at least one negative
          
          (
    

;;  x
;;     y
;;        z
;; -x -y -z

;;



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



;; Given a list of non-zero basis polys
;; 
;; (b2 (a1  a0  ) . p2)
;;     (b1 (a0  ) . p1)
;;         (b0 () . p0)
;; 
;; The polys (p0 .. pn) each contribute unique bases (b0 .. bn).
;; 
;; While the bases are mutually disjoint ..
;;
;; the basis polys themselves may be linearly dependent.
;; 
;; We require, however, that the dependencies all be positive.
;; 
;; The coefficients stored in this structure are the coefficients
;; with respect to the bais polys, not just their bases.
;;
;; The following algorithm is used to decompose a new poly (V) into
;; basis poly coefficients ..
;;
;; Initially:
;;
;;            X = V 
;;   (cN .. c0) = (0 .. 0)
;;
;; V =                   X                                               + (cN .. c0)(pN .. p0)'
;;
;; If X == 0, return (X, (cN .. c0))
;;
;; If (cN .. c0) is empty, return (X,())
;;
;;   pN = bN + (aN-1 .. a0)(pN-1 .. p0)'
;;
;;   bN = pN - (aN-1 .. a0)(pN-1 .. p0)'
;;
;;   xN = (<X,bN>/<bN,bN>
;;
;;   Add and subtract pN from X ..
;;
;; V = (xN)(pN)'      + (X - (xN)(pN))                                   + (cN .. c0)(pN .. p0)'
;;
;;   Expand pN ..
;;
;;   = (xN)(pN)'      + (X - (xN)(bN   + (aN-1 .. a0)(pN-1 .. p0)'))     + (cN .. c0)(pN .. p0)'
;;
;;   Distribute xN ..
;;
;;   = (xN)(pN)'      + (X - (xN)(bN)) + (- xN)(aN-1 .. a0)(pN-1 .. p0)' + (cN .. c0)(pN .. p0)'
;;
;;   Move cN*pN to the left ..
;;
;;   = (xN + cN)(pN)' + (X - (xN)(bN)) + (- xN)(aN-1 .. a0)(pN-1 .. p0)' + (cN-1 .. c0)(pN-1 .. p0)'
;;
;;   Collect the coefficients of (pN-1 .. p0) ..
;;
;;   = (xN + cN)(pN)' + (X - (xN)(bN)) +             ((- xN)(aN-1 .. a0) + (cN-1 .. c0))(pN-1 .. p0)'
;;
;;   dI = (- xN)*aI + cI
;;
;;    Y = (X - (xN)(bN))
;;
;;   Abstract using the definitions of dI and Y ..
;;
;; V = (xN + cN)(pN)' + Y                                                + (dN-1 .. d0)(pN-1 .. p0)'
;;
;; So this gives us the leading coefficient of V .. (xN + cN) ..
;;
;; .. and the process recurs on R = Y + (dN-1 .. d0)(pN-1 .. p0)'
;;

;;
;; Adding a new poly base, V
;;
;; Consider the decomposition V = (aN .. a0)(pN .. p0)' + R
;;
;; If forall I: (aI < 0) then 
;;
;;   If (R == 0) then (aN .. a0)(pN .. p0)' = 0
;; 
;;   else skew R and p(N+1) = (aN .. a0) + R
;;
;; else if exits I: (aI < 0) then
;;
;;   If (R == 0) then skew largest J : (aJ > 0)
;;
;;   else skew R and p(N+1) = (aN .. a0) + R
;;
;; else
;;  
;;  If (R /= 0) then p(N+1) = (aN .. a0) + R
;;

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
|#
