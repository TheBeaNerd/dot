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
