;;; primref.ss
;;; Copyright 1984-2017 Cisco Systems, Inc.
;;; 
;;; Licensed under the Apache License, Version 2.0 (the "License");
;;; you may not use this file except in compliance with the License.
;;; You may obtain a copy of the License at
;;; 
;;; http://www.apache.org/licenses/LICENSE-2.0
;;; 
;;; Unless required by applicable law or agreed to in writing, software
;;; distributed under the License is distributed on an "AS IS" BASIS,
;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;; See the License for the specific language governing permissions and
;;; limitations under the License.

(update-record-type (primref make-primref primref?) (primref-name primref-flags primref-arity primref-signatures) ()
  ; new record definition, with stub for missing accessor
  (define-record-type primref
    (nongenerative #{primref a0xltlrcpeygsahopkplcn-3})
    (sealed #t)
    (fields name flags arity signatures))
  ; old record definition, with stub for missing accessor
  (begin
    (define-record-type primref
      (nongenerative #{primref a0xltlrcpeygsahopkplcn-2})
      (sealed #t)
      (fields name flags arity))
    (define (primref-signatures x) 'signature))
)

(define primref-level
  (lambda (pr)
    (if (all-set? (prim-mask unsafe) (primref-flags pr)) 3 2)))
