(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)
(in-theory (disable INTEGERP-MINUS-X))
(include-book "coi/util/skip-rewrite" :dir :system)

(defun unique-append (x y)
  (if (not (consp x)) y
    (if (member-equal (car x) y)
        (unique-append (cdr x) y)
      (cons (car x) (unique-append (cdr x) y)))))

(defun remove-all (x y)
  (if (not (consp x)) y
    (let ((y (remove-equal (car x) y)))
      (remove-all (cdr x) y))))

(defun list-of-products (x)
  (case-match x
    (('binary-* a b)
     (let ((a (list-of-products a))
           (b (list-of-products b)))
       (append a b)))
    (& (list x))))

(defun product-of-list (a y)
  (if (not (consp y)) a
    (product-of-list `(binary-* ,(car y) ,a) (cdr y))))

(defun product-denominators (x)
  (case-match x
    (('unary-/ d) (list-of-products d))
    (('binary-+ l r)
     (let ((la (product-denominators l))
           (ra (product-denominators r)))
       (or la ra)))
    (('unary-- y) 
     (product-denominators y))
    (('binary-/ n d)
     (let ((ld (list-of-products d)))
       (remove-all (list-of-products n) ld)))
    (('expt x ('quote v))
     (if (< v 0) (list-of-products x) nil))
    (('binary-* l r)
     (let ((la (product-denominators l))
           (ra (product-denominators r)))
       (let ((ra (remove-all (list-of-products l) ra)))
         (or la ra))))
    (& nil)))

(defun bind-denominators (a x y)
  (let ((ax (product-denominators x))
        (ay (product-denominators y)))
    (let ((d (or ax ay)))
      (if (not (consp d)) nil
        (acons a (product-of-list (car d) (cdr d)) nil)))))

(defthm equality-promote-denominators
  (implies
   (and
    (acl2-numberp x)
    (acl2-numberp y)
    (bind-free (bind-denominators 'a x y) (a))
    (equal z (double-rewrite a))
    (acl2-numberp z)
    (case-split (not (equal z 0)))
    (equal ax (* z x))
    (equal ay (* z y)))
   (iff (equal x y)
        (skip-rewrite (equal ax ay)))))

(defthmd <-+-promote-denominators
  (implies
   (and
    (acl2-numberp x)
    (acl2-numberp y)
    (bind-free (bind-denominators 'a x y) (a))
    (rationalp a)
    (case-split (< 0 a))
    (equal ax (* a x))
    (equal ay (* a y)))
   (iff (< x y)
        (< ax ay)))
  :hints (("Goal" :nonlinearp t)))

(defthmd <---promote-denominators
  (implies
   (and
    (acl2-numberp x)
    (acl2-numberp y)
    (bind-free (bind-denominators 'a x y) (a))
    (rationalp a)
    (case-split (< a 0))
    (equal ax (* a x))
    (equal ay (* a y)))
   (iff (< x y)
        (< ay ax))))

(defthm known-zero-reciporicals-should-be-zero
  (implies
   (case-split (equal x 0))
   (equal (/ x) 0)))

