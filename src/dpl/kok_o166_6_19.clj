(ns dpl.core)
(reset-assumption-base)
(add-to-signature P non-logical-signature)
(add-to-signature Q non-logical-signature)
(add-to-signature R non-logical-signature)

(assert! ($'(or P Q)))
(assert! ($'(or (not Q) R)))

;; Goal is (or P R)
(! (compose
    (assume Q
            (compose
             (assume (not Q)
                     (compose
                      (assume (not R) (absurd Q (not Q)))
                      (compose (false-elim)
                               (compose (modus-tollens (if (not R) False)
                                                       (not False))
                                        (compose (double-negation (not (not R)))
                                                 (or-intro P R))))))
             (compose (assume R (or-intro P R))
                      (or-elim (or (not Q) R)
                               (if (not Q) (or P R))
                               (if R (or P R))))))
    (compose (assume P (or-intro P R))
             (or-elim (or P Q)
                      (if P (or P R))
                      (if Q (or P R))))))

(! (assume P (or-intro P R)))

(! (assume P (assume Q (claim Q))))

(! (assume-all P Q R (compose (claim R) (both P Q))))

(! (assume-all P Q R
               (compose-all (both P Q) (claim P))))