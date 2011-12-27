(ns dpl.core)
(add-to-signature P  non-logical-signature)
(add-to-signature Q  non-logical-signature)
(add-to-signature R  non-logical-signature)
(add-to-signature S  non-logical-signature)
(assert! ($'(or (and P Q) (and R S))))



(! (compose (assume (and P Q)
                    (compose (right-and (and P Q)) (or-intro Q S)))
            (compose (assume (and R S)
                             (compose (right-and (and R S)) (or-intro Q S)))
                     (or-elim (or (and P Q) (and R S))
                              (if (and P Q) (or Q S))
                              (if (and R S) (or Q S)))))) 
