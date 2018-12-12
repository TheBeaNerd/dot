(in-package "ACL2")

(include-book "dot")

(defun strict-operator-p (x)
  (declare (type t x))
  (equal x '<))

(defun inclusive-operator-p (x)
  (declare (type t x))
  (equal x '<=))

(defun operator-p (x)
  (declare (type t x))
  (or (strict-operator-p x)
      (inclusive-operator-p x)))

(def::un operator-fix (x)
  (declare (xargs :signature ((t) operator-p)))
  (if (operator-p x) x '<=))

(def::type-equiv operator)

(defthm strict-operator-implies-operator
  (implies
   (strict-operator-p x)
   (operator-p x))
  :rule-classes (:forward-chaining))

(fty::defprod+ ineq
  (
   (operator operator-p)
   (bound    rationalp)
   (poly     poly-p)
   ))

;; (defun weak-ineq-p (x)
;;   (declare (type t x))
;;   (and (consp x)
;;        (consp (cdr x))
;;        (consp (cddr x))
;;        (null (cdddr x))))

;; (in-theory (disable (operator-fix) operator-p))

;; (def::und ineq-operator (x)
;;   (declare (xargs :signature ((t) operator-p)))
;;   (if (weak-ineq-p x) (operator-fix (car x))
;;     (operator-fix nil)))

;; (def::und ineq-bound (x)
;;   (declare (xargs :signature ((t) rationalp)))
;;   (if (weak-ineq-p x) (rfix (cadr x))
;;     0))

;; (def::und ineq-poly (x)
;;   (declare (xargs :signature ((t) poly-p)))
;;   (if (weak-ineq-p x) (poly-fix (caddr x))
;;     (zero-poly)))

;; (defun ineq-p (x)
;;   (declare (type t x))
;;   (and (weak-ineq-p x)
;;        (operator-p (car x))
;;        (rationalp (cadr x))
;;        (poly-p (caddr x))))

;; (def::und ineq (operator bound poly)
;;   (declare (xargs :signature ((operator-p rationalp poly-p) ineq-p)
;;                   :congruence ((operator-equiv rfix-equiv poly-equiv) equal)))
;;   (list (operator-fix operator) (rfix bound) (poly-fix poly)))

;; (def::signature ineq (t t t) ineq-p
;;   :hints (("Goal" :in-theory (enable ineq operator-fix))))

;; (in-theory (disable ineq-p))

(def::und ineq-default ()
  (declare (xargs :signature (() ineq-p)))
  (ineq '<= 0 (zero-poly)))

;; (def::und ineq-fix (x)
;;   (declare (xargs :signature ((t) ineq-p)))
;;   (ineq (ineq->operator x)
;;         (ineq->bound x)
;;         (ineq->poly x)))

;; (defthm ineq-fix-ineq-p
;;   (implies
;;    (ineq-p x)
;;    (equal (ineq-fix x) x))
;;   :hints (("Goal" :in-theory (enable
;;                               ineq-p
;;                               ineq-fix
;;                               ineq
;;                               ineq-operator
;;                               ineq-bound
;;                               ineq-poly
;;                               ))))

;; (def::type-equiv ineq)

;; (defcong ineq-equiv equal (ineq-operator x) 1
;;   :hints (("Goal" :in-theory (enable ineq ineq-equiv ineq-fix))))

;; (defcong ineq-equiv equal (ineq-bound x) 1
;;   :hints (("Goal" :in-theory (enable ineq ineq-equiv ineq-fix))))

;; (defcong ineq-equiv equal (ineq-poly x) 1
;;   :hints (("Goal" :in-theory (enable ineq ineq-equiv ineq-fix))))

(def::un score-poly (poly sln)
  (declare (xargs :signature ((poly-p poly-p) rationalp)
                  :congruence ((poly-equiv poly-equiv) equal)))
  (dot poly sln))

(def::signatured score-poly (t t) rationalp)

(def::un score-ineq (x sln)
  (declare (xargs :signature ((ineq-p poly-p) rationalp)
                  :congruence ((ineq-equiv poly-equiv) equal)))
  (let ((bound  (ineq->bound x))
        (poly   (ineq->poly x)))
    (- (score-poly poly sln) bound)))

(def::signatured score-ineq (t t) rationalp)

(def::und eval-ineq (x sln)
  (declare (xargs :signature ((ineq-p poly-p) booleanp)
                  :congruence ((ineq-equiv poly-equiv) equal)))
  (let ((strict (strict-operator-p (ineq->operator x))))
    (let ((score (score-ineq x sln)))
      (if strict (< 0 score)
        (<= 0 score)))))

(defun ineq-listp (x)
  (declare (type t x))
  (if (not (consp x)) t
    (and (ineq-p (car x))
         (ineq-listp (cdr x)))))

(def::un ineq-list-fix (x)
  (declare (xargs :signature ((t) ineq-listp)))
  (if (not (consp x)) x
    (cons (ineq-fix! (car x))
          (ineq-list-fix (cdr x)))))

(def::type-equiv ineq-list
  :type-p ineq-listp
  :type-equiv ineq-list-fix-equiv
  )

(in-theory (enable ineq-listp ineq-list-fix))

(include-book "coi/quantification/quantification" :dir :system)

(def::un-sk ineq-member-equiv (x y)
  (forall (a) (iff (member-equal a (ineq-list-fix x))
                   (member-equal a (ineq-list-fix y))))
  :strengthen t)

(include-book "coi/quantification/quantified-congruence" :dir :system)

(quant::congruence ineq-member-equiv (x y)
  (forall (a) (iff (member-equal a (ineq-list-fix x))
                   (member-equal a (ineq-list-fix y))))
  :hyps (lambda (x y x1 y1) (and (ineq-list-fix-equiv x x1)
                                 (ineq-list-fix-equiv y y1))))

(defequiv ineq-member-equiv
  :hints ((quant::inst?)))

(in-theory (disable ineq-member-equiv))

(defcong ineq-list-fix-equiv equal (ineq-member-equiv x y) 1
  :hints (("Goal" :use (:instance ineq-member-equiv-congruence
                                  (x  x)
                                  (x1 x-equiv)
                                  (y  y)
                                  (y1 y)))))

(defcong ineq-list-fix-equiv equal (ineq-member-equiv x y) 2
  :hints (("Goal" :use (:instance ineq-member-equiv-congruence
                                  (x  x)
                                  (x1 x)
                                  (y  y)
                                  (y1 y-equiv)))))

(include-book "coi/util/deffix" :dir :system)

(def::fix ineq-member-fix ineq-member-equiv
  :type ineq-listp
  :type-fix ineq-list-fix
  )

(defthm ineq-list-fix-append
  (equal (ineq-list-fix (append x y))
         (append (ineq-list-fix x) 
                 (ineq-list-fix y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm yay
  (ineq-member-equiv (append x y) (append y x)))

(defun eval-ineq-list (list sln)
  (declare (type (satisfies ineq-listp) list)
           (type (satisfies poly-p) sln))
  (if (not (consp list)) t
    (and (eval-ineq (car list) sln)
         (eval-ineq-list (cdr list) sln))))

;; You want to move this direction to simplify the proofs ..

;; (defun remove-ineq (a list)
;;   (remove a (ineq-list-fix list)))

;; (defun member-ineq (a list)
;;   (member-equal a (ineq-list-fix list)))

;; (defthm ineq-list-remove
;;   (implies
;;    (ineq-listp list)
;;    (ineq-listp (remove-equal a list))))

;; (defthm zed
;;   (equal (list::memberp hide (remove a list))
;;          (if (equal hide a) nil
;;            (list::memberp hide list))))

;; (defcong ineq-member-equiv ineq-member-equiv (remove-ineq a list) 2)
;; (defcong ineq-member-equiv ineq-member-equiv (member-ineq a list) 2)

;; (defthm 
;;   (implies
;;    (list::memberp a (ineq-list-fix list))
;;    (iff (eval-ineq-list list sln)
;;         (and (eval-ineq a sln)
;;              (eval-ineq-list (remove a (ineq-list-fix list)) sln)))))
