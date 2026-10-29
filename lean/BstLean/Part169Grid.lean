import BstLean.Part169Pass

/-!
# Part 169 (file `Grid`): the nearest node of the program's grid

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-01-statement-program.tex`, step 6 (clip `s` to `[L, H]`, select the node of
its cell); `theorem7-08-bias.tex`, formula `t7:p08:grid` ("comparing a sample with its cell
centre"), which uses `|s − s_g| ≤ Δ_cell/2`.

* `nodeIdx_lt`: the node index is below `J`.
* **`nodeIdx_near`**: for `L < H`, `J ≥ 1` and `s ∈ [L, H]`, `|s − (L + (g + 1/2)Δ)| ≤ Δ/2`,
  `Δ = (H − L)/J`, `g = nodeIdx J L H s`.
* **`gIdx_near`**: the same for the program's grid: `|s − s_g| ≤ Δ/2` on `[L, H]`.
-/

namespace BstLean.Part169

open BstLean.Part157

variable {n : ℕ}

lemma nodeIdx_lt {J : ℕ} (hJ : 1 ≤ J) (L H s : ℝ) : nodeIdx J L H s < J := by
  unfold nodeIdx; omega

/-- **The nearest node**: on `[L, H]` the selected node is within half a cell. -/
theorem nodeIdx_near {J : ℕ} (hJ : 1 ≤ J) {L H s : ℝ} (hLH : L < H) (hs1 : L ≤ s) (hs2 : s ≤ H) :
    |s - (L + ((nodeIdx J L H s : ℕ) + 1 / 2) * ((H - L) / J))| ≤ (H - L) / J / 2 := by
  set Δ := (H - L) / (J : ℝ) with hΔ
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hΔ0 : 0 < Δ := div_pos (by linarith) (by linarith)
  have hcl : max L (min H s) = s := by
    rw [min_eq_right hs2, max_eq_right hs1]
  set t := (s - L) / Δ with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hΔ0.le
  have htJ : t ≤ J := by
    rw [ht, div_le_iff₀ hΔ0, hΔ]; field_simp; linarith
  have hidx : nodeIdx J L H s = min (J - 1) ⌊t⌋₊ := by
    unfold nodeIdx; rw [hcl]
  have hs_eq : s = L + t * Δ := by rw [ht]; field_simp; ring
  -- `|t − (g + 1/2)| ≤ 1/2`
  have key : |t - ((nodeIdx J L H s : ℕ) + 1 / 2 : ℝ)| ≤ 1 / 2 := by
    rw [hidx]
    by_cases hc : ⌊t⌋₊ ≤ J - 1
    · rw [min_eq_right hc]
      have h1 := Nat.floor_le ht0
      have h2 := Nat.lt_floor_add_one t
      rw [abs_le]; constructor <;> linarith
    · push Not at hc
      rw [min_eq_left hc.le]
      have hJt : (J : ℝ) ≤ t := by
        have : J ≤ ⌊t⌋₊ := by omega
        have h3 : ((J : ℕ) : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast this
        exact h3.trans (Nat.floor_le ht0)
      have htJ' : t = J := le_antisymm htJ hJt
      have : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
        rw [Nat.cast_sub hJ]; simp
      rw [this, htJ', abs_le]; constructor <;> linarith
  have e : s - (L + ((nodeIdx J L H s : ℕ) + 1 / 2) * Δ) =
      (t - ((nodeIdx J L H s : ℕ) + 1 / 2 : ℝ)) * Δ := by rw [hs_eq]; ring
  rw [e, abs_mul, abs_of_pos hΔ0]
  calc |t - ((nodeIdx J L H s : ℕ) + 1 / 2 : ℝ)| * Δ ≤ 1 / 2 * Δ :=
        mul_le_mul_of_nonneg_right key hΔ0.le
    _ = Δ / 2 := by ring

/-- **The program's grid**: for `L < H` and `s ∈ [L, H]`, the node `s_g` of the cell of `s`
satisfies `|s − s_g| ≤ Δ/2`, and `g < J_s = 512 n` (for `n ≥ 1`). -/
theorem gIdx_near (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hLH : nodeL c < nodeH c)
    (hs1 : nodeL c ≤ s) (hs2 : s ≤ nodeH c) :
    |s - nodeS c (gIdx c s)| ≤ nodeD c / 2 ∧ gIdx c s < Js n := by
  have hJ : 1 ≤ Js n := by unfold Js; omega
  exact ⟨nodeIdx_near hJ hLH hs1 hs2, nodeIdx_lt hJ _ _ _⟩

end BstLean.Part169
