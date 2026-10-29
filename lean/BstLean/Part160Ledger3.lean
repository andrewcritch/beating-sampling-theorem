import BstLean.Part160Ledger2
import BstLean.Part160Ledger2D
import BstLean.Part160Ledger2E

/-!
# Part 160 (file `Ledger3`): more entries of the ledger table

Do not use `sorry`, `native_decide` or `axiom`. As `Part160Ledger2`, with `n₀` rounded up to a
multiple of 250 and the frame constant written as `<three digits> / 100 / n`.

| `c_f` | `n₀` | theorem |
|---|---|---|
| 4.1 | 28 500 | `classifier_frame_410` |
| 4.2 | 29 000 | `classifier_frame_420` |
| 4.25 | 29 250 | `classifier_frame_425` |
| 4.3 | 29 500 | `classifier_frame_430` |
| 4.35 | 29 750 | `classifier_frame_435` |
| 4.4 | 30 000 | `classifier_frame_440` |
| 4.45 | 30 250 | `classifier_frame_445` |
| 4.55 | 30 750 | `classifier_frame_455` |
| 4.6 | 31 000 | `classifier_frame_460` |
| 5.6 | 36 500 | `classifier_frame_560` |
| 5.65 | 36 750 | `classifier_frame_565` |
| 5.7 | 37 000 | `classifier_frame_570` |
-/

open BstLean.Part160 in
#print axioms classifier_frame_565
open BstLean.Part160 in
#print axioms classifier_frame_410
