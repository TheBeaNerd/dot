(in-package "ACL2")

(include-book "types")

(def::un all-non-positive (list)
  (declare (xargs :signature ((rational-listp) booleanp)
                  :congruence ((rational-list-equiv) equal)))
  (if (not (consp list)) t
    (let ((entry (rfix (car list))))
      (and (<= entry 0)
           (all-non-positive (cdr list))))))

(def::un all-non-negative (list)
  (declare (xargs :signature ((rational-listp) booleanp)
                  :congruence ((rational-list-equiv) equal)))
  (if (not (consp list)) t
    (let ((entry (rfix (car list))))
      (and (<= 0 entry)
           (all-non-negative (cdr list))))))

(def::un all-negative (list)
  (declare (xargs :signature ((rational-listp) booleanp)
                  :congruence ((rational-list-equiv) equal)))
  (if (not (consp list)) t
    (let ((entry (rfix (car list))))
      (and (< entry 0)
           (all-negative (cdr list))))))

(def::un all-positive (list)
  (declare (xargs :signature ((rational-listp) booleanp)
                  :congruence ((rational-list-equiv) equal)))
  (if (not (consp list)) t
    (let ((entry (rfix (car list))))
      (and (< 0 entry)
           (all-positive (cdr list))))))

(def::un all-zero (list)
  (declare (xargs :signature ((rational-listp) booleanp)
                  :congruence ((rational-list-equiv) equal)))
  (if (not (consp list)) t
    (let ((entry (rfix (car list))))
      (and (equal 0 entry)
           (all-zero (cdr list))))))

(defthm all-positive-implies-all-non-negative
  (implies
   (all-positive list)
   (all-non-negative list))
  :rule-classes (:forward-chaining))

(defthm all-positive-append
  (equal (all-positive (append x y))
         (and (all-positive x)
              (all-positive y))))

(defthm all-zero-append
  (equal (all-zero (append x y))
         (and (all-zero x)
              (all-zero y))))

(defthm all-negative-append
  (equal (all-negative (append x y))
         (and (all-negative x)
              (all-negative y))))

(defthm all-positive-revappend
  (equal (all-positive (revappend x y))
         (and (all-positive x)
              (all-positive y)))
  :hints (("Goal" :induct (revappend x y))))

(defthm all-zero-revappend
  (equal (all-zero (revappend x y))
         (and (all-zero x)
              (all-zero y)))
  :hints (("Goal" :induct (revappend x y))))

(defthm all-negative-revappend
  (equal (all-negative (revappend x y))
         (and (all-negative x)
              (all-negative y)))
  :hints (("Goal" :induct (revappend x y))))

