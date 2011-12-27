(ns dpl.core)
(reset-assumption-base)
(add-to-signature  P non-logical-signature)
(add-to-signature Q non-logical-signature)
(assert! ($'(or P Q)))

(! (compose (assume P
                    (or-intro P (not (not Q))))
            (compose (assume Q
                             (compose
                              (double-negation Q)
                              (or-intro P (not (not Q)))))
                     (or-elim (or P Q)
                              (if P (or P (not (not Q))))
                              (if Q (or P (not (not Q))))))))

*assumption-base*
