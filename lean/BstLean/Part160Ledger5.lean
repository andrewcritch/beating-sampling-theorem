import BstLean.Part160Ledger4
import BstLean.Part160Ledger2J
import BstLean.Part160Ledger2K

/-!
# Part 160 (file `Ledger5`): the ledger table for the frame constants `2.50` to `2.95`

Do not use `sorry`, `native_decide` or `axiom`. As `Part160Ledger4` (`n₀` a multiple of 250,
tail budget `0.003699`, charges `≤ 0.0063`, frame constant written `<three digits> / 100 / n`).

| `c_f` | `n₀` | theorem |
|---|---|---|
| 2.95 | 22500 | `classifier_frame_295` |
| 2.9 | 22250 | `classifier_frame_290` |
| 2.85 | 21750 | `classifier_frame_285` |
| 2.8 | 21500 | `classifier_frame_280` |
| 2.75 | 21250 | `classifier_frame_275` |
| 2.7 | 21000 | `classifier_frame_270` |
| 2.65 | 20750 | `classifier_frame_265` |
| 2.6 | 20500 | `classifier_frame_260` |
| 2.55 | 20250 | `classifier_frame_255` |
| 2.5 | 20000 | `classifier_frame_250` |
-/

open BstLean.Part160 in
#print axioms classifier_frame_295
open BstLean.Part160 in
#print axioms classifier_frame_250
