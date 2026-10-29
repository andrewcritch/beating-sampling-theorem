import BstLean.Part56Low

/-!
# Part 64: the lower bound on `S` with explicit constants (copy of `Part56Low_Moment` and
`Part56Low_Assemble` with the witnesses stated)

* `θL64 C = 1/(4 e^{2(C+1)} + 1)`, `aL64 k C = θ^k/2`, `nL64 C = ⌊C⌋₊ + 4` (in place of `exists_nat_gt`):
  `angular_moment64`.
* `cL64 d k C = aL64 k C / ((k+1)³ · weightBound d k)`: `propLow64 : PropLow56 d k C (cL64 d k C) (nL64 C)`.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part64

open MeasureTheory BstLean.Part29 BstLean.Part41 BstLean.Part56

/-- `θ = 1/(4 e^{2(C+1)} + 1)`. -/
noncomputable def θL64 (C : ℝ) : ℝ := (4 * Real.exp (2 * (C + 1)) + 1)⁻¹

/-- The angular moment `a = θ^k/2`. -/
noncomputable def aL64 (k : ℕ) (C : ℝ) : ℝ := θL64 C ^ k / 2

/-- The explicit threshold `⌊C⌋₊ + 1 + 3` (the `N + 3` of `angular_moment_uniform` with `N = ⌊C⌋₊ + 1`). -/
noncomputable def nL64 (C : ℝ) : ℕ := (⌊C⌋₊ + 1) + 3

lemma aL64_pos (k : ℕ) (C : ℝ) : 0 < aL64 k C := by
  unfold aL64 θL64; positivity

lemma angular_moment64 (k : ℕ) (C : ℝ) :
    ∀ n : ℕ, nL64 C ≤ n → ∀ v : Fin n → ℝ, UnitV v →
        ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
          aL64 k C ≤ ∫ x, (1 - (∑ i, x i * v i) ^ 2) ^ k ∂lawRK n t v := by
  set N : ℕ := ⌊C⌋₊ + 1 with hNdef
  have hN : C < N := by rw [hNdef]; push_cast; exact Nat.lt_floor_add_one C
  unfold nL64 aL64 θL64
  rw [← hNdef]
  set L := Real.exp (2 * (C + 1)) with hLdef
  have hL : 0 < L := Real.exp_pos _
  set θ := (4 * L + 1)⁻¹ with hθdef
  have hθ : 0 < θ := by rw [hθdef]; positivity
  intro n hn v hv t ht htC
  cases n with
  | zero => omega
  | succ m =>
    have hq : (Real.sqrt (1 + 2 * L))⁻¹ ≤ Real.exp (-(C + 1)) := by
      have he : L = Real.exp (C + 1) ^ 2 := by
        dsimp only [L]
        rw [show 2 * (C + 1) = (C + 1) + (C + 1) by ring, Real.exp_add, pow_two]
      have hs : Real.exp (C + 1) ≤ Real.sqrt (1 + 2 * L) := by
        calc
          _ = Real.sqrt (Real.exp (C + 1) ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
          _ ≤ _ := Real.sqrt_le_sqrt (by rw [← he]; linarith [hL])
      rw [Real.exp_neg]
      exact inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _) |>.mpr hs
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (Real.sqrt (1 + 2 * L))⁻¹) hq m
    have htail : Real.exp (C * (m + 1)) * Real.sqrt 2 *
        ((Real.sqrt (1 + 2 * L))⁻¹) ^ m ≤ 1 / 2 := by
      calc
        _ ≤ Real.exp (C * (m + 1)) * Real.sqrt 2 * (Real.exp (-(C + 1))) ^ m :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = Real.sqrt 2 * Real.exp (C - m) := by
          rw [← Real.exp_nat_mul]
          calc
            _ = Real.sqrt 2 * (Real.exp (C * (m + 1)) * Real.exp ((m : ℝ) * -(C + 1))) := by ring
            _ = _ := by rw [← Real.exp_add]; congr 2; ring
        _ ≤ Real.sqrt 2 * Real.exp (-2) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)
          have hm : (N : ℝ) + 2 ≤ m := by exact_mod_cast (show N + 2 ≤ m by omega)
          linarith
        _ ≤ 1 / 2 := by
          have he : 3 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
          have hs : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          rw [Real.exp_neg, ← div_eq_mul_inv]
          apply (div_le_iff₀ (Real.exp_pos _)).mpr
          linarith
    have h := BstLean.Part56.LowTransport.rankOne_moment_bound m k C L hL t ht (by simpa using htC) v hv
    apply le_trans ?_ h
    rw [hθdef]
    nlinarith [pow_pos hθ k]



/-- The explicit floor constant `cL64 d k C = aL64 k C / ((k+1)³ · weightBound d k)`. -/
noncomputable def cL64 (d k : ℕ) (C : ℝ) : ℝ :=
  aL64 k C / ((k + 1 : ℝ) ^ 3 * BstLean.Part56.LowCoefficients.weightBound d k)

lemma cL64_pos (d k : ℕ) (C : ℝ) : 0 < cL64 d k C :=
  div_pos (aL64_pos k C) (mul_pos (by positivity) (BstLean.Part56.LowCoefficients.weightBound_pos d k))

open BstLean.Part36 BstLean.Part53 in
open BstLean.Part56.LowIntegration BstLean.Part56.LowCoefficients BstLean.Part56.LowScale in
/-- **Lower bound on `S`** with explicit constants. -/
theorem propLow64 (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (C : ℝ) :
    PropLow56 d k C (cL64 d k C) (nL64 C) := by
  have hAngular := angular_moment64 k C
  have ha := aL64_pos k C
  have hn0 : 1 ≤ nL64 C := by unfold nL64; omega
  set a := aL64 k C
  set n0 := nL64 C
  let B : ℝ := (k + 1 : ℝ) ^ 3 * weightBound d k
  show PropLow56 d k C (a / B) n0
  have hB : 0 < B := mul_pos (by positivity) (weightBound_pos d k)
  intro n hn v hv t ht htC f0 T hT
  have hn1 : 1 ≤ n := hn0.trans hn
  have hμ := (BstLean.Part50.binghamA_antipodal hn1 (rk1 t v)).sph
  have h := integrated_coefficient_lower (d := d) hμ k hn1 (hk.trans hkd) f0 T hT v hv
  have hm := hAngular n hn v hv t ht htC
  have hnSum : normSum k (scaleT (sg n d) (TF k f0 T)) =
      ∑ j ∈ Finset.Icc 1 k, frob (T j) / DD n d ^ j := by
    unfold normSum
    apply Finset.sum_congr rfl
    intro j hj
    exact normalized_frob d k j hn1 (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 f0 T
  have hl := mul_le_mul_of_nonneg_right hm (normSum_nonneg k (scaleT (sg n d) (TF k f0 T)))
  rw [hnSum] at h hl
  have hnPow : 0 < (n : ℝ) ^ ((k - 1) / 2) := pow_pos (by exact_mod_cast hn1) _
  apply (div_le_iff₀ hnPow).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hB).mpr
  have hfin := hl.trans h
  dsimp only [B, lawRK] at *
  convert hfin using 1 <;> ring


end BstLean.Part64
