(in-package "ACL2")

(include-book "util")

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

