import BstLean.Part160MFU
import BstLean.Part160MFPR
import BstLean.Part160MFInt
import BstLean.Part160MFApp
import BstLean.Part160MFNum
import BstLean.Part160MFCentre

/-!
# Part 160 (files `MF*`): the centre charge with the integrated mean-field remainder

Top module of the files `Part160MFU`, `Part160MFPR`, `Part160MFInt`, `Part160MFApp`,
`Part160MFNum`, `Part160MFCentre`. Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-05-centre.tex`, changes (A) (Lemma `t7:p05:PR`) and (C) (Lemma `t7:p05:MF`),
and the mean bound of Lemma `t7:p05:MA`. Changes (B) (the improved `‖H‖_HS` constant) and (D)
(the smaller deviation of `|𝐝|`) are NOT in these files.
-/

open BstLean.Part160 in
#print axioms Ures_exp
open BstLean.Part160 in
#print axioms PRvec_exp
open BstLean.Part160 in
#print axioms lemmaMF_int
open BstLean.Part160 in
#print axioms MA_i_int
open BstLean.Part160 in
#print axioms xiCI_le16
open BstLean.Part160 in
#print axioms centre16_int
open BstLean.Part160 in
#print axioms centre50k_int
