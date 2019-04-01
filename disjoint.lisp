(in-package "ACL2")

(include-book "dot")
(include-book "all")

;; (def::un disjoint-from-all (poly bases)
;;   (declare (type t poly bases)
;;            (xargs :congruence ((poly-equiv non-zero-poly-list-equiv) equal)))
;;   (if (not (consp bases)) t
;;     (and (= (dot (poly-fix poly) (non-zero-poly-fix (car bases))) 0)
;;          (disjoint-from-all poly (cdr bases)))))

;; (def::un mutually-disjoint (bases)
;;   (declare (type t bases)
;;            (xargs :congruence ((non-zero-poly-list-equiv) equal)))
;;   (if (not (consp bases)) t
;;     (and (disjoint-from-all (non-zero-poly-fix (car bases)) (cdr bases))
;;          (mutually-disjoint (cdr bases)))))

;; (defthm drop-irrelevant-addend
;;   (implies
;;    (disjoint-from-all x bases)
;;    (equal (disjoint-from-all (add a (add b x)) bases)
;;           (disjoint-from-all (add a b) bases))))

(def::un disjoint-from-all (poly bases)
  (declare (type t poly bases)
           (xargs :congruence ((poly-equiv poly-list-equiv) equal)))
  (if (not (consp bases)) t
    (and (= (dot (poly-fix poly) (poly-fix (car bases))) 0)
         (disjoint-from-all poly (cdr bases)))))

(defthm disjoint-from-all-cons
  (equal (disjoint-from-all base (cons x list))
         (and (equal (DOT base x) 0)
              (disjoint-from-all base list))))

(defthm disjoint-from-all-append
  (iff (disjoint-from-all x (append y z))
       (and (disjoint-from-all x y)
            (disjoint-from-all x z))))

(def::un all-disjoint-from-all (list bases)
  (declare (type t list bases)
           (xargs :congruence ((poly-list-equiv poly-list-equiv) equal)))
  (if (not (consp list)) t
    (and (disjoint-from-all (car list) bases)
         (all-disjoint-from-all (cdr list) bases))))

(defthm all-disjoint-from-all-commutes
  (equal (all-disjoint-from-all x y)
         (all-disjoint-from-all y x)))

(defthm all-disjoint-from-all-cons-2
  (implies
   (consp y)
   (iff (all-disjoint-from-all x y)
        (and
         (disjoint-from-all (car y) x)
         (all-disjoint-from-all x (cdr y))))))

(defthm all-disjoint-from-all-null-2
  (implies
   (not (consp y))
   (all-disjoint-from-all x y)))

(defthm all-disjoint-from-all-append-2
  (iff (all-disjoint-from-all x (append y z))
       (and (all-disjoint-from-all x y)
            (all-disjoint-from-all x z))))

(defthm all-disjoint-from-all-append-1
  (iff (all-disjoint-from-all (append y z) x)
       (and (all-disjoint-from-all y x)
            (all-disjoint-from-all z x))))

(def::un mutually-disjoint (bases)
  (declare (type t bases)
           (xargs :congruence ((poly-list-equiv) equal)))
  (if (not (consp bases)) t
    (and (disjoint-from-all (poly-fix (car bases)) (cdr bases))
         (mutually-disjoint (cdr bases)))))

(defthm mutually-disjoint-cons
  (equal (mutually-disjoint (cons x list))
         (AND (DISJOINT-FROM-ALL x list)
              (MUTUALLY-DISJOINT list))))

(defthm mutually-disjoint-append
  (iff (mutually-disjoint (append x y))
       (and (mutually-disjoint x)
            (mutually-disjoint y)
            (all-disjoint-from-all x y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm drop-irrelevant-addend
  (implies
   (disjoint-from-all x bases)
   (equal (disjoint-from-all (add a (add b x)) bases)
          (disjoint-from-all (add a b) bases))))

;; ----

(def::un mutually-non-negative (bases)
  (declare (type t bases)
           (xargs :congruence ((poly-list-equiv) equal)))
  (if (not (consp bases)) t
    (and (all-non-negative (dot-list (poly-fix (car bases)) (cdr bases)))
         (mutually-non-negative (cdr bases)))))

(defthm mutually-non-negative-cons
  (equal (mutually-non-negative (cons x list))
         (AND (all-non-negative (dot-list (poly-fix x) list))
              (MUTUALLY-non-negative list))))
