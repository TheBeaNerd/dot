(in-package "ACL2")

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "coi/util/defun" :dir :system)
(include-book "workshops/2018/greve-gacek/types" :dir :system)

(defun add-rule-classes (name instance body)
  (if (not (consp body)) nil
    (let ((entry (car body)))
      (let ((access (packn-pos (list name '-> (car entry)) name)))
        (cons `(,@entry :rule-classes (:rewrite (:forward-chaining :trigger-terms ((,access ,instance)))))
              (add-rule-classes name instance (cdr body)))))))

(defmacro fty::defprod+ (name body &rest args)
  (let ((name-p      (packn-pos (list name '-p)      name))
        (name-fix    (packn-pos (list name '-fix)    name))
        (name-fix!   (packn-pos (list name '-fix!)   name))
        (name-equiv  (packn-pos (list name '-equiv)  name))
        (name-equiv! (packn-pos (list name '-equiv!) name))
        (name-instance (packn-pos (list name '-instance) name))
        )
    `(progn
       
       (fty::defprod ,name
         ,(add-rule-classes name name-instance body)
         ,@args
         :xvar ,name-instance
         )
       
       (def::un ,name-fix! (x)
         (declare (xargs :signature ((t) ,name-p)))
         (with-guard-checking :none (ec-call (,name-fix x))))
       
       (defun ,name-equiv! (x y)
         (declare (type t x y))
         (with-guard-checking :none (ec-call (,name-equiv x y))))
       
       )))

(defmacro def::type-equiv (type &key (type-p 'nil) (type-equiv 'nil) (disable 't))
  (let* ((type-p     (or type-p (packn-pos (list type '-p) type)))
         (type-fix   (packn-pos (list type '-fix) type))
         (type-equiv (or type-equiv (packn-pos (list type '-equiv) type)))
         (fix-type-p (packn-pos (list type-fix '- type-p) type))
         (equiv-fix  (packn-pos (list type-equiv '- type-fix) type))
         )
    `(encapsulate
         ()

       (defun ,type-equiv (x y)
         (declare (type t x y))
         (equal (,type-fix x) (,type-fix y)))

       (defequiv ,type-equiv)

       (defcong ,type-equiv equal (,type-fix x) 1)

       (defthm ,fix-type-p
         (implies
          (,type-p x)
          (equal (,type-fix x) x)))

       (defthm ,equiv-fix
         (,type-equiv (,type-fix x) x))

       (in-theory (disable ,type-equiv))
       ,@(and disable `((in-theory (disable ,type-p ,type-fix))))

       (fty::deffixtype ,type
         :pred   ,type-p
         :fix    ,type-fix
         :equiv  ,type-equiv
         :define nil
         )

       )))

(defmacro def::type-list (type &key (define-type-list 't) (type-p 'nil) (type-fix 'nil) (witness 'nil))
  (let ((witness (or witness type)))
    (let ((type-p        (or type-p (packn-pos (list type '-p)     witness)))
          (type-list     (packn-pos (list type '-list)  witness))
          (type-listp    (packn-pos (list type '-listp) witness))
          (type-fix      (or type-fix (packn-pos (list type '-fix!)  witness)))
          (type-list-fix (packn-pos (list type '-list-fix) witness))
          (type-list-equiv (packn-pos (list type '-list-equiv) witness))
          )
      `(encapsulate
           ()
         
         ,@(and define-type-list
                `((defun ,type-listp (x)
                    (declare (type t x))
                    (if (not (consp x)) (null x)
                      (and (,type-p (car x))
                           (,type-listp (cdr x)))))))
         
         (def::un ,type-list-fix (x)
           (declare (xargs :signature ((t) ,type-listp)))
           (if (not (consp x)) nil
             (cons (,type-fix (car x))
                   (,type-list-fix (cdr x)))))
         
         (def::type-equiv ,type-list
           :type-p ,type-listp
           :disable nil
           )
         
         (defthm ,(packn-pos (list 'iff- type-list-fix) witness)
           (iff (,type-list-fix x)
                (consp x)))

         (defthm ,(packn-pos (list 'open-consp- type-list-equiv) witness)
           (implies
            (or (consp x) (consp y))
            (equal (,type-list-equiv x y)
                   (and (consp x)
                        (consp y)
                        (equal (,type-fix (car x))
                               (,type-fix (car y)))
                        (,type-list-equiv (cdr x) (cdr y)))))
           :hints (("Goal" :in-theory (enable ,type-list-equiv))))
         
         (defthm ,(packn-pos (list 'open- type-list-equiv) witness)
           (implies
            (or (not (consp x)) (not (consp y)))
            (equal (,type-list-equiv x y)
                   (and (not (consp x)) (not (consp y)))))
           :hints (("Goal" :in-theory (enable ,type-list-equiv))))
         
         (defcong ,type-list-equiv iff (consp x) 1)
         
         (encapsulate
             ()
           
           (local
            (defthm ,(packn-pos (list 'len- type-list-fix) witness)
              (equal (len (,type-list-fix x))
                     (len x))))
           
           (local
            (defthmd ,(packn-pos (list 'len- type-list-fix '-helper) witness)
              (implies
               (equal y (,type-list-fix x))
               (equal (len x)
                      (len y)))))
           
           (defcong ,type-list-equiv equal (len x) 1
             :hints (("Goal" :do-not-induct t
                      :in-theory (enable ,type-list-equiv)
                      :use (:instance ,(packn-pos (list 'len- type-list-fix '-helper) witness)
                                      (x (,type-list-fix x))
                                      (y (,type-list-fix x-equiv))))))
           
           )

         ))))
  
