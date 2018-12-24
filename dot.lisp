(in-package "ACL2")

(include-book "util")
(include-book "hints")

(defun rfix-equiv (x y)
  (equal (rfix x) (rfix y)))

(defequiv rfix-equiv)

(defthm rfix-equiv-rfix
  (rfix-equiv (rfix x) x))

(defcong rfix-equiv equal (rfix x) 1)

(def::signature rfix (t) rationalp)

(defthmd equal-rfix-to-rfix-equiv
  (iff (equal (rfix x) y)
       (and
        (rationalp y)
        (rfix-equiv x y))))

(defthm rationalp-*
  (implies
   (and
    (rationalp x)
    (rationalp y))
   (rationalp (* x y))))

(defthm rationalp-+
  (implies
   (and
    (rationalp x)
    (rationalp y))
   (rationalp (+ x y))))

(defthm rfix-rationalp
  (implies
   (rationalp x)
   (equal (rfix x) x)))

(in-theory (disable rfix))
(in-theory (disable rfix-equiv))

(def::type-list rational
  :define-type-list nil
  :type-fix rfix
  :witness defthm
  )

(defthm non-negative-square
  (implies
   (rationalp x)
   (<= 0 (* x x)))
  :rule-classes :linear)

(defthm positive-square
  (implies
   (and
    (rationalp x)
    (not (equal x 0)))
   (< 0 (* x x)))
  :rule-classes :linear)

(defthm non-negative-expt
  (implies
   (rationalp x)
   (<= 0 (expt x 2)))
  :rule-classes (:rewrite :linear (:forward-chaining :trigger-terms ((expt x 2))))
  :hints (("Goal" :expand (:free (n) (expt x n)))))

(defthm positive-expt
  (implies
   (and
    (rationalp x)
    (not (equal x 0)))
   (< 0 (expt x 2)))
  :rule-classes (:rewrite :linear (:forward-chaining :trigger-terms ((expt x 2))))
  :hints (("Goal" :expand (:free (n) (expt x n)))))

(encapsulate
    (
     ((zero-polyp *)   => * :formals   (x) :guard t)
     ((zero-poly)      => * :formals    () :guard t)
     ((non-zero-poly)  => * :formals    () :guard t)
     ((poly-p *)       => * :formals   (x) :guard t)
     ((poly-equiv * *) => * :formals (x y) :guard t)
     ((poly-equiv-witness * *) => *)
     ((poly-fix *)     => * :formals   (x) :guard t)
     ((dot * *)        => * :formals (x y) :guard (and (poly-p x) (poly-p y)))
     ((add * *)        => * :formals (x y) :guard (and (poly-p x) (poly-p y)))
     ((scale * *)      => * :formals (x m) :guard (and (poly-p x) (rationalp m)))
     )
  
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (encapsulate
       ()
     
     (defun poly-p (x)
       (rationalp x))
     
     (defun poly-equiv (x y)
       (equal (rfix x) (rfix y)))
     
     (defun poly-fix (x)
       (rfix x))

     (defun zero-polyp (x)
       (equal (rfix x) 0))
     
     (defun zero-poly () 0)
     (defun non-zero-poly () 1)
     
     (defun dot (x y)
       (* (rfix x) (rfix y)))
     
     (defun add (x y)
       (+ (rfix x) (rfix y)))
     
     (defun scale (x m)
       (* (rfix m) (rfix x)))
     
     (defun-sk poly-equiv-sk (x y)
       (forall (k) (equal (dot k x) (dot k y))))

     (defun poly-equiv-witness (x y)
       (poly-equiv-sk-witness x y))

     ))
  
  (defequiv poly-equiv)

  (def::signature zero-poly () poly-p)
  (def::signature non-zero-poly () poly-p)
  (def::signature dot      (t t) rationalp)
  (def::signature add      (t t) poly-p)
  (def::signature scale    (t t) poly-p)
  (def::signature poly-fix   (t) poly-p)
  (def::signature zero-polyp (t) booleanp)

  (defcong rfix-equiv poly-equiv (scale x m) 2)
  (defcong poly-equiv poly-equiv (scale x m) 1)

  (defcong poly-equiv equal (dot x y) 1)
  (defcong poly-equiv equal (dot x y) 2)
  
  (defcong poly-equiv poly-equiv (add x y) 1)
  (defcong poly-equiv poly-equiv (add x y) 2)
  
  (defcong poly-equiv equal (zero-polyp x) 1)

  (defcong poly-equiv equal (poly-fix x) 1)

  (defthm poly-equiv-poly-fix
    (poly-equiv (poly-fix x) x))

  (defthm poly-fix-poly-p
    (implies
     (poly-p x)
     (equal (poly-fix x) x)))

  (defthm dot-commute
    (equal (dot x y)
           (dot y x)))
  
  (defthm add-commute
    (poly-equiv (add x y)
           (add y x)))

  (defthmd zero-polyp-definition
    (equal (zero-polyp x)
           (poly-equiv x (zero-poly))))

  (defthm zero-polyp-zero-poly
    (zero-polyp (zero-poly)))

  (defthm not-zero-polyp-non-zero-poly
    (not (zero-polyp (non-zero-poly))))

  (defthm zero-poly-implication
    (implies
     (zero-polyp x)
     (poly-equiv x (zero-poly)))
    :rule-classes (:forward-chaining))

  (defthm zero-dot-zero-poly
    (implies
     (equal (dot x x) 0)
     (zero-polyp x))
    :rule-classes (:forward-chaining))

  (defthm scale-by-zero
    (implies
     (equal (rfix m) 0)
     (poly-equiv (scale x m)
                 (zero-poly))))

  (defthm scale-scale
    (poly-equiv (scale (scale x m) n)
                (scale x (* (rfix m) (rfix n)))))

  (defthm scale-add
    (poly-equiv (scale (add x y) m)
                (add (scale x m) (scale y m))))

  (defthm add-add
    (poly-equiv (add (add x y) z)
                (add x (add y z))))

  (defthm add-add-commute
    (poly-equiv (add x (add y z))
                (add y (add x z))))

  (defthm dot-add-1
    (equal (dot (add x y) z)
           (+ (dot x z) (dot y z))))

  (defthm dot-add-2
    (equal (dot z (add x y))
           (+ (dot x z) (dot y z))))

  (defthm dot-scale-1
    (equal (dot (scale x m) y)
           (* (rfix m) (dot x y))))

  (defthm dot-scale-2
    (equal (dot x (scale y m))
           (* (rfix m) (dot x y))))

  (defthm dot-zero-1
    (implies
     (zero-polyp x)
     (equal (dot x y)
            0)))

  (defthm dot-zero-2
    (implies
     (zero-polyp y)
     (equal (dot x y)
            0)))

  (defthm add-zero-1
    (implies
     (zero-polyp x)
     (poly-equiv (add x y) y)))

  (defthm add-zero-2
    (implies
     (zero-polyp y)
     (poly-equiv (add x y) x)))

  (defthm non-negative-self-dot
    (<= 0 (dot x x))
    :rule-classes :linear)
     
  (defthm positive-self-dot
    (implies
     (not (zero-polyp x))
     (< 0 (dot x x)))
    :rule-classes :linear)

  (defthmd poly-equiv-reduction
    (equal (poly-equiv x y)
           (let ((k (poly-equiv-witness x y)))
             (equal (dot k x) (dot k y))))
    :rule-classes (:definition)
    :hints (("Goal" :use (:instance poly-equiv-sk-necc
                                    (k 1)))))

  (defthmd poly-equiv-implication
    (implies
     (poly-equiv x y)
     (equal (dot k x) (dot k y)))
    :hints (("Goal" :use (:instance poly-equiv-sk-necc
                                    (k 1)))))

  )

(defun self-dot (x)
  (dot x x))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthmd dot-zero
   (implies
    (not (zero-polyp x))
    (equal (dot x (add y (scale x (/ (- (dot x y)) (self-dot x)))))
           0))))

;; (include-book "coi/quantification/quantification" :dir :system)

;; (def::un-sk dot1 (a x)
;;   (forall (sln) (< a (dot x sln))))

;; (def::un-sk dot2 (a x b y)
;;   (forall (sln)
;;           (and (< a (dot x sln))
;;                (< b (dot y sln)))))

;; (defthm these-are-the-same
;;   (iff (and (dot1 a x)
;;             (dot1 b y))
;;        (dot2 a x b y))
;;   :hints (("Goal" :in-theory (disable dot1 dot2 default-less-than-1 dot-commute))
;;           ("Subgoal 3.2'" :use (:instance dot1-necc (a a) (x x) (sln hide)))
;;           ("Subgoal 3.1'" :use (:instance dot1-necc (a b) (x y) (sln hide)))
;;           ("Subgoal 2''" :use (:instance dot2-necc (sln hide)))
;;           ("Subgoal 1''" :use (:instance dot2-necc (sln hide)))
;;           ))

(local
 (defthmd sumba-wumba
   (implies
    (and
     (rationalp a)
     (rationalp b)
     (< a (dot x sln))
     (< b (dot y sln)))
    (< (+ a b) (dot (add x y) sln)))
   ))

(fty::deffixtype poly
  :pred   poly-p
  :fix    poly-fix
  :equiv  poly-equiv
  :define nil
  )

(def::type-list poly
  :type-fix poly-fix)

(def::un zero-poly-fix (x)
  (declare (xargs :signature ((t) zero-polyp)
                  :congruence ((poly-equiv) poly-equiv)))
  (if (zero-polyp x) x (zero-poly)))

(fty::deffixtype zero-poly
  :pred   zero-polyp
  :fix    zero-poly-fix
  :equiv  zero-poly-equiv
  :define t
  )

(in-theory (disable zero-poly-fix))

(def::type+ non-zero-polyp (x)
  (declare (xargs :type-name non-zero-poly
                  :type-witness (non-zero-poly)))
  (and (poly-p x)
       (not (zero-polyp x))))

(def::type-list non-zero-poly
  :type-p non-zero-polyp
  :type-fix non-zero-poly-fix
  )

;; ==================================================================

(def::un coeff (base poly)
  (declare (xargs :signature ((poly-p poly-p) rationalp)
                  :congruence ((poly-equiv poly-equiv) equal)
                  :guard (not (zero-polyp base))))
  (/ (dot poly base)
     (dot base base)))

(defthm zero-coeff-1
  (implies
   (zero-polyp x)
   (equal (coeff x y) 0)))

(defthm zero-coeff-2
  (implies
   (zero-polyp y)
   (equal (coeff x y) 0)))

(defthm coeff-scale
  (equal (coeff x (scale y a))
         (* (coeff x y) (rfix a))))

(defthm self-coeff
  (equal (coeff x x) 
         (if (zero-polyp x) 0 1)))

(defthm zero-coeff
  (implies
   (equal (dot x y) 0)
   (equal (coeff x y) 0)))

(defthm coeff-add
  (equal (coeff base (add p1 p2))
         (+ (coeff base p1) (coeff base p2))))

(def::signatured coeff (t t) rationalp)

;; ==================================================================

(def::un skew-poly (poly x coeff y)
  (declare (xargs :signature ((poly-p poly-p rationalp poly-p) poly-p)
                  :guard (not (zero-polyp y))
                  :congruence ((poly-equiv poly-equiv rfix-equiv poly-equiv) poly-equiv)))
  (add poly (scale x (* (rfix coeff) (coeff y poly)))))

(defthmd skew-poly-works
  (implies
   (and
    (not (zero-polyp y))
    (not (equal (rfix cy) 0))
    (equal (dot y x) 0)
    (equal py (add (scale x cx) (scale y cy))))
   (equal (dot (skew-poly py x (/ (- (rfix cx)) (coeff y py))  y) sln)
          (dot (scale y cy) sln))))

(defthmd skew-poly-is-invertable
  (implies
   (and
    (not (zero-polyp y))
    (equal (dot y x) 0)
    (equal p1 (skew-poly p0 x coeff y))
    (equal p2 (skew-poly p1 x (- (rfix coeff)) y)))
   (equal (dot p0 sln)
          (dot p2 sln))))

;;(in-theory (enable rfix-equiv))

;; Change of basis:
;;
;; |  1  0 ||x| = |   |
;; | -2  1 ||y|   |   |
;; | -7  2 |      | 0 |
;;
;;
;; |  1  0 ||x'| = |x|
;; |  2  1 ||y'|   |y|
;;
;;
;; |x'| = |  1  0 ||x|
;; |y'|   | -2  1 ||y|
;;
;; |  1  0 ||  1  0 ||x'| = |   |
;; | -2  1 ||  2  1 ||y'|   |   |
;; | -7  2 |                | 0 |
;;
;; |  1   0 ||x'| = |   |
;; |  0   1 ||y'|   |   |
;; | -3   2 |       | 0 |
;;
;; |x'| = | 2 |
;; |y'|   | 3 |
;;
;; |x| = |  1  0 || 2 | = | 2 |
;; |y|   |  2  1 || 3 |   | 7 |
;;
;; OK .. well, that worked.

(defthmd skew-poly-solution
  (implies
   (and
    (not (zero-polyp y))
    (not (zero-polyp x))
    )
   (equal (dot (skew-poly pn x coeff y) sln) 
          (dot pn (skew-poly sln y (/ (* (dot x x) (rfix coeff)) (dot y y)) x))))
  :hints (("Goal" :in-theory (enable coeff))))

(defthmd skew-poly-as-equality
  (equal (dot (skew-poly poly x -1 x) x)
         0)
  :hints (("Goal" :in-theory (enable coeff))))

(def::signatured skew-poly (t t t t) poly-p)

;; ==================================================================

(defun hide-poly-equiv (x y)
  (poly-equiv x y))

(defthmd do-hide-poly-equiv
  (equal (poly-equiv x y)
         (hide-poly-equiv x y)))

(defthm hide-poly-equiv-implies
  (implies
   (hide-poly-equiv x y)
   (iff (poly-equiv x y) t)))

(defthmd hide-poly-equiv-reduction
  (equal (hide-poly-equiv x y)
         (let ((k (poly-equiv-witness x y)))
           (equal (dot k x) (dot k y))))
  :hints (("Goal" :in-theory (enable poly-equiv-reduction)))
  :rule-classes (:definition))

(in-theory (disable hide-poly-equiv))

#+joe
(defstub zed (x) nil)
#+joe
(trace$ skosimp-inst-hint)
#+joe
(defthm try-this
  (implies
   (poly-equiv (zed a) (zed b))
   (poly-equiv a b))
  :rule-classes nil
  :hints ((skosimp-inst)))

