(ns dpl.core)
(reset-assumption-base)
(declare-propositions H E Ma My)
(assert! ($'(and (if H (and E Ma))
                 (if (not H) (and (not E) (not Ma))))))
(assert! ($'(if (not H) (not My))))

(! (compose-all
    (assume H
            (compose-all (left-and (and (if H (and E Ma))
                                                    (if (not H) (and (not E) (not Ma)))))
                         (modus-ponens (if H (and E Ma))
                                       H)
                         (right-and (and E Ma))
                         (or-intro Ma My)))
    (assume (or Ma My)
            (compose-all (assume My
                                 
                                 (compose-all (assume (not H)
                                                      (compose (modus-ponens (if (not H) (not My)) (not H))
                                                               (absurd My (not My))))
                                              (false-elim)
                                              (modus-tollens (if (not H) False) (not False))
                                              (double-negation (not (not H)))))
                         (assume Ma (compose-all
                                     (assume (not H)
                                             (compose-all
                                              (right-and (and (if H (and E Ma))
                                                              (if (not H) (and (not E) (not Ma)))))
                                              (modus-ponens (if (not H) (and (not E) (not Ma))) (not H))
                                              (left-and (and (not E) (not Ma)))
                                              (absurd Ma (not Ma))))
                                     (false-elim)
                                     (modus-tollens (if (not H) False) (not False))
                                     (double-negation (not (not H)))))
                         (or-elim (or Ma My)
                                  (if Ma H)
                                  (if My H))))
    (equivalence (if H (or Ma My)) (if (or Ma My) H))))

*assumption-base*