(in-package "ACL2")

(include-book "dot")

(include-book "arithmetic-5/top" :dir :system)

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

;; y = y' + x

;; p = (a + b)x + by' + rp

;; s =        vx   vy     vr   
;; y' = y - x

;; x = ac
;; y = bd

;; p' = ax + by + rp

;; | 1 0 |
;; | a 1 |

;; dag
;; (defthm skew-solution
;;   (implies
;;    (and
;;     (not (equal (dot y y) 0))
;;     (not (equal (dot x x) 0))
;;     (rationalp vx)
;;     (rationalp vy)
;;     (equal (dot y x) 0)
;;     (equal (dot x rp) 0)
;;     (equal (dot x rs) 0)
;;     (equal (dot y rp) 0)
;;     (equal (dot y rs) 0)
;;     (rationalp alpha)
;;     (equal p    (add (scale x cx) (add (scale y cy) rp)))
;;     (equal sln  (add (scale x (/ vx (dot x x))) (add (scale y (/ vy (dot y y))) rs)))
;;     (equal (dot (add p (scale x (/ (dot p y) (dot y y)))) sln) 0)
;;     (equal alpha (/ (* vx (rfix cy)) (dot x x)))
;;     )
;;    (equal (dot p (add sln (scale y alpha))) 0)))

(defthmd invertable-skew
  (implies
   (and
    (not (equal (dot y y) 0))
    (equal (dot y x) 0)
    (equal p1 (add p0 (scale x (/ (dot p0 y) (dot y y)))))
    (equal p2 (add p1 (scale x (/ (- (dot p1 y)) (dot y y))))))
   (equal (dot p0 sln)
          (dot p2 sln))))

