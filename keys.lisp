(in-package "ACL2")

(include-book "dot")

(include-book "arithmetic-5/top" :dir :system)

(in-theory (disable INTEGERP-MINUS-X))
(in-theory (disable EQUAL-RFIX-TO-RFIX-EQUIV))

(defthm empty-solution
  (implies
   (and
    (and (rationalp a) (rationalp b) (rationalp c) (rationalp d))
    (<= a (rfix x))
    (<= b (rfix y))
    (<= c (rfix z))
    (<= d (+ (- (rfix x)) (- (rfix y)) (- (rfix z))))
    (< 0 (+ a b c d)))
   nil)
  :rule-classes nil)

(defthm single-solution
  (implies
   (and
    (and (rationalp a) (rationalp b) (rationalp c) (rationalp d))
    (<= a (rfix x))
    (<= b (rfix y))
    (<= c (rfix z))
    (<= d (+ (- (rfix x)) (- (rfix y)) (- (rfix z))))
    (equal 0 (+ a b c d)))
   (equal d (+ (- (rfix x)) (- (rfix y)) (- (rfix z)))))
  :rule-classes nil)


;; y = y' + x

;; p = ax + by + rp
;; s = cx + dy + rs

;; y = y' + ex

;; p' = (a + be)x + by' + rp

;; s' =       vx + wy' + rs

;; y' = y - ex

;; s' =       vx + wy' + rs

;; (a + be)(v) + b(w) = 0

;; y' = y - ex

;; project solutio onto old basis (y - ex)

;; You need to increase both x and y.

;; Question: if we have a solution to the new system, how do we find a
;; solution to the orignal system?  Well, isn't it obvious?

