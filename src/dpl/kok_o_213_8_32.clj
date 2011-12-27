(ns dpl.core)
(reset-assumption-base)
(declare-propositions H E D My Ma R)
(assert! ($'(if H (and E D))))
(assert! ($'(if (or E My) R)))
(assert! ($'(if Ma (not R))))
(! (assume-all
    H
    (compose-all
     (modus-ponens (if H (and E D)) H )
     (left-and (and E D))
     (or-intro E My)
     (modus-ponens (if (or E My) R) (or E My))
     (false-elim)
     (assume Ma (absurd R (not R)))
     (modus-tollens (if Ma False) (not False)))))

*assumption-base*