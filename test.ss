;;; cp0.ms
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

(display
  (+ 1 2)
)
(newline)

(display
  (expand/optimize
    '(lambda (x)
       (call-with-values (lambda ()
                           (call-with-values (lambda () (unbox x))
                             (case-lambda
                               [(x) (values x #f)]
                               [args (values args #t)])))
         (lambda (l apply?)
           (newline)
           (if apply?
               (apply values l)
               l)))))
)
(newline)

(display
  (expand/optimize
    '(lambda (x)
       (call-with-values (lambda ()
                           (call-with-values (lambda () (unbox x))
                             (case-lambda
                               [args (values args #t)])))
         (lambda (l apply?)
           (newline)
           (if apply?
               (apply values l)
               l)))))
)
(newline)

(display
  (expand/optimize
    '(lambda (x)
       (call-with-values (lambda ()
                           (call-with-values (lambda () (unbox x))
                             (case-lambda
                               [args args])))
         (lambda (l)
           (newline)
           (apply values l)))))
)
(newline)

(display
  (expand/optimize
    '(lambda (x)
       (call-with-values (lambda ()
                           (call-with-values (lambda () (unbox x))
                             list))
         (lambda (l)
           (newline)
           (apply values l)))))
)
(newline)


