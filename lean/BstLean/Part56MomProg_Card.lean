import BstLean.Part56MomProg_Assemble

/-! Size bounds for the index types. -/

namespace BstLean.Part56.MomProg

open BstLean.Part56
open BstLean.Part41 (Mono)

theorem card_key_le (k d : ℕ) : Fintype.card (KeyRK k d) ≤ (k + 1) ^ 2 * (d + 1) ^ k := by
  classical
  rw [Fintype.card_sigma]
  calc (∑ il : Fin (k + 1) × Fin (k + 1),
        Fintype.card (Fin ((il.1 : ℕ) - 2 * (il.2 : ℕ)) → Fin (d + 1)))
      ≤ ∑ _il : Fin (k + 1) × Fin (k + 1), (d + 1) ^ k := by
        apply Finset.sum_le_sum
        intro il _
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        apply Nat.pow_le_pow_right (by omega)
        have := il.1.isLt; omega
    _ = (k + 1) ^ 2 * (d + 1) ^ k := by
        simp [Fintype.card_prod, Fintype.card_fin, sq]

theorem card_mono_le (n d : ℕ) : Fintype.card (Mono n d) ≤ (n + 1) ^ d := by
  rw [card_mono']; exact choose_le_pow' n d

end BstLean.Part56.MomProg
