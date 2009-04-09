;;; Copyright (c) 2009, Volkan YAZICI <volkan.yazici@gmail.com>
;;; All rights reserved.

;;; Redistribution  and  use  in  source  and  binary  forms,  with  or  without
;;; modification, are permitted provided that the following conditions are met:

;;; - Redistributions  of source code  must retain  the above  copyright notice,
;;;   this list of conditions and the following disclaimer.

;;; - Redistributions in binary form  must reproduce the above copyright notice,
;;;   this list of conditions and  the following disclaimer in the documentation
;;;   and/or other materials provided with the distribution.

;;; THIS SOFTWARE IS PROVIDED BY  THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;;; AND ANY  EXPRESS OR IMPLIED WARRANTIES,  INCLUDING, BUT NOT  LIMITED TO, THE
;;; IMPLIED WARRANTIES  OF MERCHANTABILITY AND FITNESS FOR  A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO  EVENT SHALL THE  COPYRIGHT OWNER OR  CONTRIBUTORS BE
;;; LIABLE  FOR  ANY  DIRECT,   INDIRECT,  INCIDENTAL,  SPECIAL,  EXEMPLARY,  OR
;;; CONSEQUENTIAL  DAMAGES  (INCLUDING,  BUT  NOT  LIMITED  TO,  PROCUREMENT  OF
;;; SUBSTITUTE GOODS  OR SERVICES;  LOSS OF USE,  DATA, OR PROFITS;  OR BUSINESS
;;; INTERRUPTION)  HOWEVER CAUSED  AND ON  ANY THEORY  OF LIABILITY,  WHETHER IN
;;; CONTRACT,  STRICT LIABILITY,  OR  TORT (INCLUDING  NEGLIGENCE OR  OTHERWISE)
;;; ARISING IN ANY WAY  OUT OF THE USE OF THIS SOFTWARE,  EVEN IF ADVISED OF THE
;;; POSSIBILITY OF SUCH DAMAGE.

(in-package :binomial-heap)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Convenient Debugging Related Routines
;;;

(defun sexp->tree (sexp)
  "Converts supplied `SEXP' of `(KEY &KEY SIBLING CHILD)' form into appropriate
`BINOMIAL-TREE' instance."
  (labels ((%convert (sexp parent)
             (when sexp
               (let* ((plist (rest sexp))
                      (parent
                       (make-instance
                        'binomial-tree
                        :parent parent
                        :sibling (%convert (getf plist :sibling) parent)
                        :key (first sexp))))
                 (setf (child-of parent) (%convert (getf plist :child) parent))
                 (setf (degree-of parent)
                       (if (child-of parent)
                           (1+ (degree-of (child-of parent)))
                           0))
                 parent))))
    (%convert sexp nil)))

(defun tree->sexp (tree)
  "Converts supplied `BINOMIAL-TREE' into `(KEY &KEY SIBLING CHILD)' compound
form."
  (when tree
    (nconc
     (list (key-of tree))
     (when-let (child (tree->sexp (child-of tree))) (list :child child))
     (when-let (sibling (tree->sexp (sibling-of tree))) (list :sibling sibling)))))

(defun print-tree (x)
  "Utility function to print binomial tree in a human-readable(?) format."
  (labels ((%print (x depth)
             (when x
               (loop repeat depth  do (format t "  "))
               (format t "-> (~2D) ~S~%" (degree-of x) (key-of x))
               (%print (child-of x) (1+ depth))
               (%print (sibling-of x) depth))))
    (%print x 0)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Common Tree Routines
;;;

(defun link-siblings (trees)
  "Constructs `SIBLING' slots of given list of `BINOMIAL-TREE's to provide given
order."
  (when trees
    (prog1 (first trees)
      (labels ((%link (trees)
                 (when trees
                   (setf (sibling-of (first trees)) (second trees))
                   (%link (rest trees)))))
        (%link trees)))))

(defun sibling-list (tree)
  "Returns reversed list of child and its consequent siblings of supplied `TREE'
of type `BINOMIAL-TREE'."
  (labels ((%traverse (tree accum)
             (if tree
                 (%traverse (sibling-of tree) (cons tree accum))
                 accum)))
    (%traverse tree nil)))

(defun merge-siblings (x y)
  "Merges given two `BINOMIAL-TREE's and their related siblings into a single
`BINOMIAL-TREE' sibling list."
  (link-siblings
   (merge 'list (nreverse (sibling-list x)) (nreverse (sibling-list y))
          #'< :key #'degree-of)))

(defun link-trees (x y)
  "Makes `X' the child of `Y'."
  (setf (parent-of x) y
        (sibling-of x) (child-of y)
        (child-of y) x)
  (incf (degree-of y)))

(defun unite-root-lists (test x y)
  "Unites given `X' and `Y' `BINOMIAL-TREE's and their related siblings into a
single `BINOMIAL-TREE'."
  (when (or x y)
    (labels ((%unite (prev-x curr-x next-x head)
               (if next-x
                   (cond
                     ;; Case 1 & 2
                     ((or (not (= (degree-of curr-x) (degree-of next-x)))
                          (and (sibling-of next-x)
                               (= (degree-of next-x)
                                  (degree-of (sibling-of next-x)))))
                      (%unite curr-x next-x (sibling-of next-x) head))
                     ;; Case 3
                     ((funcall test (key-of curr-x) (key-of next-x))
                      (setf (sibling-of curr-x) (sibling-of next-x))
                      (link-trees next-x curr-x)
                      (%unite prev-x curr-x (sibling-of curr-x) head))
                     ;; Case 4
                     (t
                      (when prev-x (setf (sibling-of prev-x) next-x))
                      (link-trees curr-x next-x)
                      (%unite prev-x next-x (sibling-of next-x)
                              (if (eql head curr-x) next-x head))))
                   ;; Finally, return the `HEAD'.
                   head)))
      (let ((curr-x (merge-siblings x y)))
        (%unite nil curr-x (sibling-of curr-x) curr-x)))))

(defun unsafe-unite-root-lists (test x y)
  "Identical to `UNITE-ROOT-LISTS' except that this function doesn't handle Case
2 condition and break the loop in Case 1. (Case 1 & 2 are redundant while adding
a single node to a root list.)"
  (when (or x y)
    (labels ((%unite (prev-x curr-x next-x head)
               (if next-x
                   (cond
                     ;; Case 1
                     ((not (= (degree-of curr-x) (degree-of next-x)))
                      head)
                     ;; Case 3
                     ((funcall test (key-of curr-x) (key-of next-x))
                      (setf (sibling-of curr-x) (sibling-of next-x))
                      (link-trees next-x curr-x)
                      (%unite prev-x curr-x (sibling-of curr-x) head))
                     ;; Case 4
                     (t
                      (when prev-x
                        (setf (sibling-of prev-x) next-x))
                      (link-trees curr-x next-x)
                      (%unite prev-x next-x (sibling-of next-x)
                              (if (eql curr-x head) next-x head))))
                   ;; Finally, return the `HEAD'.
                   head)))
      (let ((curr-x (merge-siblings x y)))
        (%unite nil curr-x (sibling-of curr-x) curr-x)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Tree Operations
;;;

(defun insert-key (heap key)
  "Creates a new `BINOMIAL-TREE' for `KEY' and inserts this node to the
`BINOMIAL-HEAP' pointed by `HEAP'. Function returns the `KEY'."
  (prog1 key
    (setf (head-of heap)
          (unsafe-unite-root-lists
           (test-of heap)
           (head-of heap)
           (make-instance 'binomial-tree :key key)))))

(defun get-prior-to-extremum (head test)
  "Finds the `BINOMIAL-TREE' prior to the extremum in the sibling list pointed
by `HEAD'. Function returns `NIL' in case of no extremum or extremum at the
beginning."
  (loop with extremum-prev
        with extremum-curr = head
        for prev = head then curr
        for curr = (sibling-of prev) then (sibling-of curr)
        while curr
        do (when (funcall test (key-of curr) (key-of extremum-curr))
             (setq extremum-prev prev
                   extremum-curr curr))
        finally (return extremum-prev)))

(defun get-extremum-key (heap)
  "Finds the `BINOMIAL-TREE' with the extremum value and its `KEY'
field. Function returns `NIL' in case of no items found."
  (when-let (head (head-of heap))
    (let ((prior (get-prior-to-extremum (head-of heap) (test-of heap))))
      (if prior
          (key-of (sibling-of prior))
          (when head (key-of head))))))

(defun extract-extremum-key (heap)
  "Extracts the extremum value from the `BINOMIAL-HEAP' pointed by
`HEAP'. Function returns the `KEY' field of the extracted `BINOMIAL-TREE'
instance."
  (when (head-of heap)
    (let ((prev (get-prior-to-extremum (head-of heap) (test-of heap))))
      (if prev
          (let ((curr (sibling-of prev)))
            (prog1 (key-of curr)
              ;; After removing extremum from the root list, unite the root list
              ;; and children of the extremum.
              (setf (sibling-of prev) (sibling-of curr))
              (setf (head-of heap)
                    (unite-root-lists
                     (test-of heap)
                     (head-of heap)
                     (link-siblings (sibling-list (child-of curr)))))))
          ;; Oops! We find extremum at the beginning of the root list.
          (prog1 (key-of (head-of heap))
            (setf (head-of heap)
                  (unite-root-lists
                   heap
                   (sibling-of (head-of heap))
                   (link-siblings
                    (sibling-list
                     (child-of (head-of heap)))))))))))

(defun unite-heaps (x y)
  "Unites given two heaps of type `BINOMIAL-HEAP' into a single one. (Assuming
`TEST' functions of each heap are equivalent.)"
  (prog1 x
    (setf (head-of x)
          (unite-root-lists (test-of x) (head-of x) (head-of y)))))
