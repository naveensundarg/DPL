(ns dpl.core)
(reset-assumption-base)
(declare-propositions P Q)

(!(assume-all P Q
               (claim P)))