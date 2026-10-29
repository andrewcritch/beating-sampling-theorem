import BstLean.Part160Ledger2Gen
import BstLean.Part160Ledger2A
import BstLean.Part160Ledger2B
import BstLean.Part160Ledger2C

/-!
# Part 160 (file `Ledger2`): the ledger with optimized exponents, a table of frame constants

Top file of the `Ledger2` group. Do not use `sorry`, `native_decide` or `axiom`.

`Part160Ledger` gives the threshold `n ≥ 16384·c_f/1.743 ≈ 9400·c_f` (scaled exponents). With
exponents `τ_±` chosen for each frame constant `c_f` the threshold `n₀(c_f)` is smaller:

| `c_f` | `τ_+` | `τ_-` | `e_+` | `e_-` | `n₀` | theorem |
|---|---|---|---|---|---|---|
| 4 | 0.098203 | −0.246726 | 2.334036e-4 | 2.203849e-4 | 28 000 | `classifier_frame_4` |
| 4.5 | 0.090095 | −0.223761 | 2.139548e-4 | 2.006173e-4 | 30 500 | `classifier_frame_45` |
| 5 | 0.083238 | −0.204571 | 1.975230e-4 | 1.840416e-4 | 33 500 | `classifier_frame_5` |
| 5.5 | 0.077362 | −0.188331 | 1.834523e-4 | 1.699551e-4 | 36 000 | `classifier_frame_55` |
| 6 | 0.072267 | −0.174421 | 1.712648e-4 | 1.578442e-4 | 38 500 | `classifier_frame_6` |
| 6.5 | 0.067807 | −0.162381 | 1.606044e-4 | 1.473254e-4 | 41 500 | `classifier_frame_65` |
| 7 | 0.063869 | −0.151876 | 1.511995e-4 | 1.381074e-4 | 44 000 | `classifier_frame_7` |
| 7.5 | 0.060366 | −0.142621 | 1.428398e-4 | 1.299652e-4 | 46 500 | `classifier_frame_75` |
| 7.75 | 0.058756 | −0.138401 | 1.389987e-4 | 1.262409e-4 | 48 000 | `classifier_frame_775` |
| 8 | 0.057230 | −0.134416 | 1.353596e-4 | 1.227224e-4 | 49 500 | `classifier_frame_8` |
| 8.5 | 0.054405 | −0.127096 | 1.286266e-4 | 1.162388e-4 | 52 000 | `classifier_frame_85` |
| 9 | 0.051847 | −0.120521 | 1.225337e-4 | 1.104018e-4 | 54 500 | `classifier_frame_9` |
| 10.6 | 0.045071 | −0.103376 | 1.064134e-4 | 9.51014e-5 | 63 500 | `classifier_frame_106` |
| 18 | 0.028112 | −0.062236 | 6.6192e-5 | 5.78973e-5 | 103 000 | `classifier_frame_18` |

In each row: `E_+(c_f, τ_+) ≤ −e_+`, `E_-(c_f, τ_-) ≤ −e_-`, and
`exp(−n₀ e_+) + exp(−n₀ e_-) ≤ 0.003699`, so that with charges `≤ 0.0063` the failure
probability is at most `0.0063 + 0.003699 + 10⁻⁶ = 1/100`.
-/

open BstLean.Part160 in
#print axioms classifier_networks_frameconst2
open BstLean.Part160 in
#print axioms frame_entry
open BstLean.Part160 in
#print axioms classifier_frame_775
open BstLean.Part160 in
#print axioms classifier_frame_5
open BstLean.Part160 in
#print axioms classifier_frame_4
open BstLean.Part160 in
#print axioms classifier_frame_18
