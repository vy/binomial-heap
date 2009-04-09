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
;;; Common Class Definitions
;;;

(defclass binomial-heap ()
  ((head
    :initarg  :head
    :accessor head-of
    :initform nil
    :type     list)
   (test
    :initarg  :test
    :accessor test-of
    :type     function))
  (:documentation "Binomial heap container."))

(defclass binomial-tree ()
  ((parent
    :initarg  :parent
    :accessor parent-of
    :initform nil
    :type     binomial-tree)
   (degree
    :initarg  :degree
    :accessor degree-of
    :initform 0
    :type     (integer 0 *))
   (child
    :initarg  :child
    :accessor child-of
    :initform nil
    :type     binomial-tree)
   (sibling
    :initarg  :sibling
    :accessor sibling-of
    :initform nil
    :type     binomial-tree)
   (key
    :initarg :key
    :accessor key-of))
  (:documentation "Binomial tree container."))

(defmethod print-object ((self binomial-tree) stream)
  (print-unreadable-object (self stream :identity t :type t) 
    (format stream ":KEY ~A :DEGREE ~D" (key-of self) (degree-of self))))
