(in-package "ACL2")

(include-book "util")

(defun rfix-equiv (x y)
  (equal (rfix x) (rfix y)))

(defequiv rfix-equiv)

(defthm rfix-equiv-rfix
  (rfix-equiv (rfix x) x))

(defcong rfix-equiv equal (rfix x) 1)

(def::signature rfix (t) rationalp)

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
  :hints (("Goal" :expand (:free (n) (expt x n)))))

(defthm positive-expt
  (implies
   (and
    (rationalp x)
    (not (equal x 0)))
   (< 0 (expt x 2)))
  :hints (("Goal" :expand (:free (n) (expt x n)))))

(encapsulate
    (
     ((zero-polyp *)   => * :formals   (x) :guard t)
     ((zero-poly)      => * :formals    () :guard t)
     ((poly-p *)       => * :formals   (x) :guard t)
     ((poly-equiv * *) => * :formals (x y) :guard t)
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
     
     (defun dot (x y)
       (* (rfix x) (rfix y)))
     
     (defun add (x y)
       (+ (rfix x) (rfix y)))
     
     (defun scale (x m)
       (* (rfix m) (rfix x)))
     
     ))
  
  (defequiv poly-equiv)

  (def::signature zero-poly () poly-p)
  (def::signature dot    (t t) rationalp)
  (def::signature add    (t t) poly-p)
  (def::signature scale  (t t) poly-p)
  (def::signature poly-fix (t) poly-p)
  
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

  (defthm zero-polyp-zero-poly
    (zero-polyp (zero-poly)))

  (defthm zero-dot-zero-poly
    (implies
     (equal (dot x x) 0)
     (poly-equiv x (zero-poly)))
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
 (defthm sumba-wumba
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
