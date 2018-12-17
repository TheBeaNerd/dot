(in-package "ACL2")

(include-book "dot")

(include-book "arithmetic-5/top" :dir :system)

(in-theory (disable INTEGERP-MINUS-X))
(in-theory (disable EQUAL-RFIX-TO-RFIX-EQUIV))

(defthmd cornered
  (implies
   (and
    (<= 0 (rfix x))
    (<= 0 (rfix y))
    (<= 0 (rfix z))
    (<= 0 (+ (- (rfix x)) (- (rfix x)) (- (rfix x)))))
   (equal (+ (rfix x) (rfix x) (rfix x)) 0)))

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

(defun coeff (base poly)
  (/ (dot poly base)
     (dot base base)))

(defthm coeff-scale
  (equal (coeff x (scale x a))
         (if (zero-polyp x) 0
           (rfix a))))

(defun skew (poly x coeff y)
  (add poly (scale x (* (rfix coeff) (coeff y poly)))))

#+joe
(defun unskew (poly x coeff y)
  (add poly (scale x (- (* coeff (coeff y poly))))))

(defthmd skew-works
  (implies
   (and
    (not (zero-polyp y))
    (not (equal (rfix cy) 0))
    (equal (dot y x) 0)
    (equal py (add (scale x cx) (scale y cy))))
   (equal (dot (skew py x (/ (- (rfix cx)) (coeff y py))  y) sln)
          (dot (scale y cy) sln))))

(defthmd skew-is-invertable
  (implies
   (and
    (not (zero-polyp y))
    (equal (dot y x) 0)
    (equal p1 (skew p0 x coeff y))
    (equal p2 (skew p1 x (- (rfix coeff)) y)))
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

(defthmd skew-solution
  (implies
   (and
    (not (zero-polyp y))
    (not (zero-polyp x))
    )
   (equal (dot (skew pn x coeff y) sln) 
          (dot pn (skew sln y (/ (* (dot x x) (rfix coeff)) (dot y y)) x)))))
