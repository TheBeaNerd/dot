(in-package "ACL2")
(include-book "util")

;; visualize lambda abstracts a clause

;; (defun index-assoc (key alist)
;;   (if (not (consp alist)) 0
;;     (if (equal key (caar alist)) (len alist)
;;       (index-assoc key (cdr alist)))))

(defmacro sudo-termp-macro (term)
  `(let ((term ,term))
     (if (consp term)
         (and (symbolp (car term))
              (or (equal (car term) 'quote)
                  (sudo-term-listp (cdr term))))
       (or (symbolp term)
           (integerp term)))))

(defun sudo-term-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (sudo-termp-macro (car list))
         (sudo-term-listp (cdr list)))))

(defun sudo-termp (term)
  (declare (type t term))
  (sudo-termp-macro term))

(defthm sudo-term-listp-definition
  (equal (sudo-term-listp list)
         (if (not (consp list)) (null list)
           (and (sudo-termp (car list))
                (sudo-term-listp (cdr list)))))
  :rule-classes (:definition))

(in-theory (disable (:induction sudo-term-listp)))

(defthm sudo-term-induction T
  :rule-classes ((:induction :pattern (sudo-term-listp list)
                             :scheme (len list))))

(defthm sudo-termp-cons
  (implies
   (consp term)
   (iff (sudo-termp term)
        (sudo-termp-macro term))))

(defthm symbolp-implies-sudo-termp
  (implies
   (symbolp term)
   (sudo-termp term)))

(in-theory (disable (:definition sudo-term-listp) sudo-termp))

(defun map-alistp (alist)
  (declare (type t alist))
  (if (not (consp alist)) (null alist)
    (let ((entry (car alist)))
      (and (consp entry)
           (symbolp (car entry))
           (consp (cdr entry))
           (sudo-termp (cadr entry))
           (null (cddr entry))
           (map-alistp (cdr alist))))))

(defun unmap-alistp (alist)
  (declare (type t alist))
  (if (not (consp alist)) (null alist)
    (let ((entry (car alist)))
      (and (consp entry)
           (sudo-termp (car entry))
           (symbolp (cdr entry))
           (unmap-alistp (cdr alist))))))

(defthm symbolp-cdr-assoc-unmap-alistp
  (implies
   (and
    (unmap-alistp alist)
    (assoc-equal term alist))
   (symbolp (cdr (assoc-equal term alist)))))

(def::und safe-symbol (s)
  (declare (xargs :signature ((t) symbolp)))
  (if (or (not (symbolp s)) (equal (symbol-package-name s) "COMMON-LISP")) 'defthm s))

(def::und symbolize (name number)
  (declare (xargs :signature ((symbolp integerp) symbolp)))
  (packn-pos (list name '_ number) (safe-symbol name)))

(def::und insert-alist (key alist)
  (declare (xargs :signature ((sudo-termp unmap-alistp) symbolp unmap-alistp)))
  (let ((val (if (symbolp key) key (symbolize 'quote (1+ (len alist))))))
    (let ((hit (assoc-equal key alist)))
      (if (null hit) (mv val (cons (cons key val) alist))
        (mv (cdr hit) alist)))))

(def::und cache-alist (fn args alist)
  (declare (xargs :signature ((symbolp sudo-term-listp unmap-alistp) symbolp unmap-alistp)))
  (let ((term (cons fn args)))
    (let ((hit (assoc-equal term alist)))
      (if hit (mv (cdr hit) alist)
        (let ((var (symbolize fn (1+ (len alist)))))
          (mv var (cons (cons term var) alist)))))))

(defmacro visualization-alist-macro (term alist)
  `(let ((term ,term)
         (alist ,alist))
     (if (not (consp term)) (insert-alist term alist)
       (let ((fn (car term)))
         (cond
          ((equal fn 'quote) (insert-alist term alist))
          (t
           (met ((arglist alist) (visualization-alist-list (cdr term) alist))
             (cache-alist fn arglist alist))))))))

(def::un visualization-alist-list (args alist)
  (declare (xargs :signature ((sudo-term-listp unmap-alistp) sudo-term-listp unmap-alistp)))
  (if (not (consp args)) (mv nil alist)
    (let ((term (car args)))
      (met ((term alist) (visualization-alist-macro term alist))
        (met ((args alist) (visualization-alist-list (cdr args) alist))
          (mv (cons term args) alist))))))
    
(def::und visualization-alist (term alist)
  (declare (xargs :signature ((sudo-termp unmap-alistp) symbolp unmap-alistp)))
  (visualization-alist-macro term alist))

(def::und invert-alist (alist res)
  (declare (xargs :signature ((unmap-alistp map-alistp) map-alistp)))
  (if (not (consp alist)) res
    (invert-alist (cdr alist) (cons (cons (cdar alist) (cons (caar alist) nil)) res))))

(def::un instances-list (key list)
  (declare (xargs :signature ((symbolp sudo-term-listp) integerp)))
  (if (not (consp list)) 0
    (+ (if (equal key (car list)) 1 0)
       (instances-list key (cdr list)))))

(def::un instances-alist (key alist)
  (declare (xargs :signature ((symbolp map-alistp) integerp)))
  (if (not (consp alist)) 0
    (let ((term (cadar alist)))
      (+ (if (quotep term) 0
           (if (consp term) (instances-list key (cdr term)) 
             (if (equal term key) 1
               0)))
         (instances-alist key (cdr alist))))))

(def::und alpha-reduce-list (key value list)
  (declare (xargs :signature ((symbolp sudo-termp sudo-term-listp) sudo-term-listp)))
  (if (not (consp list)) nil
    (cons (if (equal key (car list)) value (car list))
          (alpha-reduce-list key value (cdr list)))))

(def::und alpha-reduce-alist (key value alist)
  (declare (xargs :signature ((symbolp sudo-termp map-alistp) map-alistp)))
  (if (not (consp alist)) nil
    (let ((term (cadar alist)))
      (let ((term (if (quotep term) term
                    (if (consp term) (cons (car term) (alpha-reduce-list key value (cdr term)))
                      (if (equal term key) value
                        term)))))
        (cons (cons (caar alist) (list term))
              (alpha-reduce-alist key value (cdr alist)))))))
  
(defthm len-alpha-reduce-alist
  (equal (len (alpha-reduce-alist key value alist))
         (len alist))
  :hints (("Goal" :in-theory (enable alpha-reduce-alist))))

(def::und alpha-reduce-heuristics (alist)
  (declare (xargs :measure (len alist)
                  :signature ((map-alistp) map-alistp)))
  (if (not (consp alist)) nil
    (let ((key (caar alist))
          (val (cadar alist)))
      (let ((hit (instances-alist key (cdr alist))))
        (cond
         ((or (equal hit 1)
              (symbolp val)
              (integerp val)
              (and (consp val)
                   (or (equal (len (cdr val)) 1)
                       (equal (car val) 'quote)
                       (equal (car val) 'val)
                       (equal (car val) 'car)
                       (equal (car val) 'cdr))))
          (let ((alist (alpha-reduce-alist key val (cdr alist))))
            (alpha-reduce-heuristics alist)))
         (t
          (cons (cons key (list val)) (alpha-reduce-heuristics (cdr alist)))))))))

(defthm map-alistp-implies-alistp
  (implies
   (map-alistp x)
   (alistp x))
  :rule-classes (:rewrite :forward-chaining))

(def::un extract-assoc-map (key alist)
  (declare (xargs :signature ((symbolp map-alistp) sudo-termp map-alistp)))
  (if (not (consp alist)) (mv key alist)
    (let ((entry (car alist)))
      (if (equal key (car entry)) (mv (cadr entry) (cdr alist))
        (met ((term alist) (extract-assoc-map key (cdr alist)))
          (mv term (cons entry alist)))))))

(def::und visualize (term)
  (declare (xargs :signature ((sudo-termp) sudo-termp map-alistp)))
  (met ((var alist) (visualization-alist term nil))
    (let ((alist (invert-alist alist nil)))
      (let ((alist (alpha-reduce-heuristics alist)))
        (met ((term alist) (extract-assoc-map var alist))
          (mv term alist))))))

(defun let-bind (term alist)
  (if (not (consp alist)) term
    (let ((entry (car alist)))
      `(let ((,(car entry) ,(cadr entry)))
         ,(let-bind term (cdr alist))))))

(defun let-bind-viz (term)
  (met ((term alist) (visualize term))
    (let-bind term alist)))

