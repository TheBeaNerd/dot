(in-package "ACL2")

(include-book "coi/util/mv-nth" :dir :system)
(include-book "coi/generalize/generalize" :dir :system)

(defun find-quant (quant clause tlist nlist)
  (if (not (consp clause)) (mv tlist nlist)
    (let ((entry (car clause)))
      (case-match entry
        (('not (fn . args))
         (if (eq fn quant)
             (find-quant quant (cdr clause) tlist (cons args nlist))
           (find-quant quant (cdr clause) tlist nlist)))
        ((fn . args)
         (if (eq fn quant)
             (find-quant quant (cdr clause) (cons args tlist) nlist)
           (find-quant quant (cdr clause) tlist nlist)))
        (&
         (find-quant quant (cdr clause) tlist nlist))))))

(defun bind-vars (vars args)
  (if (not (and (consp vars) (consp args))) nil
    (cons (cons (car vars) (cons (car args) nil))
          (bind-vars (cdr vars) (cdr args)))))

(defun use-instances (thm bindings free witness targs)
  (if (not (consp targs)) nil
    (let ((args (car targs)))
      (cons `(:instance ,thm 
                        ,@bindings
                        (,free (,witness ,@args)))
            (use-instances thm bindings free witness (cdr targs))))))

(defun use-hints (thm free witness vars nargs targs)
  (if (not (consp nargs)) nil
    (let ((args (car nargs)))
      (revappend (use-instances thm (bind-vars vars args) free witness targs)
                 (use-hints thm free witness vars (cdr nargs) targs)))))

(defun restrict-hints (vars arglist)
  (if (not (consp arglist)) nil
    (let ((args (car arglist)))
      (cons `(,@(bind-vars vars args))
            (restrict-hints vars (cdr arglist))))))

(defun generalization-hints (witness arglist)
  (if (not (consp arglist)) nil
    (let ((args (car arglist)))
      (cons (cons `(,witness ,@args) `(lambda (x) (quote t)))
            (generalization-hints witness (cdr arglist))))))

(defun skosimp-inst-hint (clause fn defn hide-defn thm witness vars free)
  (met ((targs nargs) (find-quant fn clause nil nil))
    (if (not (consp targs)) nil
      `(:computed-hint-replacement 
        ((and stable-under-simplificationp
              '(:computed-hint-replacement
                ((and stable-under-simplificationp
                      '(:clause-processor (acl2::generalize-list-clause-processor-wrapper clause '(,@(generalization-hints witness targs))))))
                :use (,@(use-hints thm free witness vars nargs targs))
                :in-theory (enable ,defn)
                :do-not '(preprocess)
                :restrict ((,defn ,@(restrict-hints vars targs))))))
        :in-theory (enable ,hide-defn)
        :do-not '(preprocess)
        :restrict ((,hide-defn ,@(restrict-hints vars (append nargs targs))))
        ))))


(defmacro skosimp-inst (&key (fn        'poly-equiv)
                             (witness   'poly-equiv-witness)
                             (defn      'hide-poly-equiv-reduction)
                             (hide-defn 'do-hide-poly-equiv)
                             (thm       'poly-equiv-implication)
                             (vars      '(x y))
                             (free      'k)
                             )
  `(and stable-under-simplificationp
        (skosimp-inst-hint clause 
                           ',fn
                           ',defn
                           ',hide-defn
                           ',thm
                           ',witness
                           ',vars
                           ',free)))
