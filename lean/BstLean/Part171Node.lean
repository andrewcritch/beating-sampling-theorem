import BstLean.Part171Mom

/-!
# Part 171 (file `Node`): the bias at one node, from the node statistics

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `t7:p08:biasmom`. At a node with `‖A₁‖_op ≤ O` and
`S₋ ≤ ς² ≤ S₊`, `DstN ≤ D_m`, `hUN ≤ H_m`, `V2N ≤ V_m`, `piN ≤ P_m`:

* **`node_biasF`**: `biasF⁸ ≤ n⁴m³ Σ_j (A₀ + A₁ρ_j + A₂ρ_j²)⁸`, `ρ_j = |ζ_j|`;
* **`node_biasW`**: `biasW⁸ ≤ m⁷ Σ_j (A₀' + A₁'ρ_j + A₂'ρ_j²)⁸`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (phiG phiG_pos)
open BstLean.Part170 (biasF biasW hB tA aLat bOfY measurable_aLat aLat_normSq_le vmean_aLat G2)
open BstLean.Part137 (psiS)

variable {n : ℕ}

lemma abs_add_abs_le (a b : ℝ) : |a| + |b| ≤ √2 * √(a ^ 2 + b ^ 2) := by
  have h : (|a| + |b|) ^ 2 ≤ (√2 * √(a ^ 2 + b ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
    nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h

lemma DstN_nonneg (c : Ret n) (g : ℕ) : 0 ≤ DstN c g :=
  integral_nonneg fun _ => by positivity

lemma V2N_nonneg (c : Ret n) (g : ℕ) : 0 ≤ V2N c g :=
  integral_nonneg fun _ => sq_nonneg _

lemma hUN_nonneg (c : Ret n) (g : ℕ) : 0 ≤ hUN c g := abs_nonneg _

lemma piN_nonneg (c : Ret n) (g : ℕ) : 0 ≤ piN c g := measureReal_nonneg

/-- `|(M₀ā)_j| ≤ (|ξ₁_j| + |ξ₂_j|)√t_A O`. -/
lemma abs_M0abar_le (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) (ξ₁ ξ₂ : Fin (mA n) → ℝ) (j : Fin (mA n)) :
    |(M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j| ≤ (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) := by
  set s := nodeS c g
  set a := aLat c s
  have ha := measurable_aLat c s
  have haO : ∀ v, √(normSq (a v)) ≤ O := fun v => by
    calc √(normSq (a v)) ≤ √(O ^ 2) := Real.sqrt_le_sqrt (aLat_normSq_le hn c hs h1 v)
      _ = O := Real.sqrt_sq hO
  have hK : ∀ v, ‖a v‖ ≤ O := by
    intro v
    rw [pi_norm_le_iff_of_nonneg hO]
    intro i; rw [Real.norm_eq_abs]; exact (BstLean.Part170.abs_le_sqrt_normSq _ i).trans (haO v)
  have hAv : ∀ v, |(M0 c g ξ₁ ξ₂ *ᵥ a v) j| ≤ (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) := fun v =>
    (abs_M0_le c g ξ₁ ξ₂ (a v) j).trans (by gcongr; exact haO v)
  have hmean : ∫ v, (M0 c g ξ₁ ξ₂ *ᵥ a v) j ∂stdGauss (Fin (n - 1)) =
      (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j := by
    rw [int_mulVec ha hK _ j, vmean_aLat]
  rw [← hmean]
  have := norm_integral_le_of_norm_le_const (μ := stdGauss (Fin (n - 1)))
    (f := fun v => (M0 c g ξ₁ ξ₂ *ᵥ a v) j) (C := (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O))
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hAv v)
  simpa [Real.norm_eq_abs] using this

/-- `ρ_j = |ζ_j| = √(ξ₁_j² + ξ₂_j²)`. -/
noncomputable def rhoJ {m : ℕ} (ξ₁ ξ₂ : Fin m → ℝ) (j : Fin m) : ℝ := √(ξ₁ j ^ 2 + ξ₂ j ^ 2)

lemma rhoJ_sq {m : ℕ} (ξ₁ ξ₂ : Fin m → ℝ) (j : Fin m) : rhoJ ξ₁ ξ₂ j ^ 2 = ξ₁ j ^ 2 + ξ₂ j ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The node statistics hypotheses. -/
structure NodeStat (c : Ret n) (g : ℕ) (Smin Smax Dm Hm Vm Pm : ℝ) : Prop where
  hS1 : Smin ≤ vsig2 c (nodeS c g)
  hS2 : vsig2 c (nodeS c g) ≤ Smax
  hD : DstN c g ≤ Dm
  hH : hUN c g ≤ Hm
  hV : V2N c g ≤ Vm
  hP : piN c g ≤ Pm

/-- **The location bias at a node**: `biasF⁸ ≤ n⁴m³ Σ_j (A₀ + A₁ρ_j + A₂ρ_j²)⁸`. -/
theorem node_biasF (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm) (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    biasF c g ξ₁ ξ₂ ^ 8 ≤ (n : ℝ) ^ 4 * ((mA n : ℕ) : ℝ) ^ 3 *
      ∑ j, (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm + AF1 √Smin Dm Vm Pm (√(tA n) * O) *
        rhoJ ξ₁ ξ₂ j + AF2 √Smin Dm * rhoJ ξ₁ ξ₂ j ^ 2) ^ 8 := by
  set s := nodeS c g
  have hv : 0 < vsig2 c s := hSm.trans_le H.hS1
  rw [biasF_rows hn c g hs h1]
  set b := bOfY c (M0 c g ξ₁ ξ₂ *ᵥ hB c)
  set x : Fin (mA n) → ℝ := fun j => ∫ v, psiS (√(wT c g v)) ((M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j)
      ∂stdGauss (Fin (n - 1)) - psiS √(vsig2 c s) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j) with hx
  set P : Fin (mA n) → ℝ := fun j => AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AF1 √Smin Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j + AF2 √Smin Dm * rhoJ ξ₁ ξ₂ j ^ 2 with hP
  have hxP : ∀ j, |x j| ≤ P j := by
    intro j
    have R := rowF (row_stat hn c g hs hO h1 hv ξ₁ ξ₂ j) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j)
    have e : ∀ v, (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j + ((M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j -
        (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j) = (M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j := fun v => by
      simp only [s]; ring
    simp only [e] at R
    refine R.trans ?_
    have hρ : 0 ≤ rhoJ ξ₁ ξ₂ j := Real.sqrt_nonneg _
    have hC : 0 ≤ √(tA n) * O := mul_nonneg (Real.sqrt_nonneg _) hO
    have hsum := abs_add_abs_le (ξ₁ j) (ξ₂ j)
    refine TF_le (Real.sqrt_pos.mpr hSm) (Real.sqrt_le_sqrt H.hS1) hρ hC (by positivity) ?_
      (by have := vsig2_nonneg c s; have := tA_nonneg n; positivity) (by linarith [H.hS2])
      (mul_nonneg (by positivity) (DstN_nonneg c g)) ?_ (hUN_nonneg c g) H.hH (V2N_nonneg c g)
      H.hV (piN_nonneg c g) H.hP
    · have : (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) ≤ √2 * rhoJ ξ₁ ξ₂ j * (√(tA n) * O) :=
        mul_le_mul_of_nonneg_right hsum hC
      unfold rhoJ at *
      nlinarith
    · rw [rhoJ_sq]
      exact mul_le_mul_of_nonneg_left H.hD (by positivity)
  have hP0 : ∀ j, 0 ≤ P j := fun j => (abs_nonneg _).trans (hxP j)
  have hκ : |(n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j| ≤ √(n : ℝ) * √(∑ j, x j ^ 2) := by
    rw [abs_mul]
    have h1' := BstLean.Part130.abs_dot_le b x
    have h2 := BstLean.Part170.kappa_b_le n b
    calc |(n : ℝ) / (√(n : ℝ) * √(normSq b))| * |∑ j, b j * x j|
        ≤ |(n : ℝ) / (√(n : ℝ) * √(normSq b))| * (√(normSq b) * √(normSq x)) := by gcongr
      _ = (|(n : ℝ) / (√(n : ℝ) * √(normSq b))| * √(normSq b)) * √(normSq x) := by ring
      _ ≤ √(n : ℝ) * √(normSq x) := by gcongr
      _ = √(n : ℝ) * √(∑ j, x j ^ 2) := rfl
  have hS0 : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have step1 : ((n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j) ^ 8 ≤
      (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := by
    rw [← Even.pow_abs (by decide)]
    calc |(n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j| ^ 8
        ≤ (√(n : ℝ) * √(∑ j, x j ^ 2)) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) hκ _
      _ = ((√(n : ℝ)) ^ 2) ^ 4 * ((√(∑ j, x j ^ 2)) ^ 2) ^ 4 := by ring
      _ = (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt hS0]
  have step2 : (∑ j, x j ^ 2) ^ 4 ≤ ((mA n : ℕ) : ℝ) ^ 3 * ∑ j, P j ^ 8 := by
    have := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := fun j => x j ^ 2)
      (fun j _ => sq_nonneg _) 3
    simp only [Finset.card_univ, Fintype.card_fin] at this
    refine this.trans ?_
    gcongr with j
    rw [← pow_mul]
    calc x j ^ (2 * (3 + 1)) = |x j| ^ 8 := by rw [Even.pow_abs (by decide)]
      _ ≤ P j ^ 8 := pow_le_pow_left₀ (abs_nonneg _) (hxP j) 8
  calc _ ≤ (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := step1
    _ ≤ (n : ℝ) ^ 4 * (((mA n : ℕ) : ℝ) ^ 3 * ∑ j, P j ^ 8) := by gcongr
    _ = _ := by ring

/-- **The energy bias at a node**: `biasW⁸ ≤ m⁷ Σ_j (A₀' + A₁'ρ_j + A₂'ρ_j²)⁸`. -/
theorem node_biasW (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm) (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    biasW c g ξ₁ ξ₂ ^ 8 ≤ ((mA n : ℕ) : ℝ) ^ 7 *
      ∑ j, (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
        AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j +
        AW2 Dm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j ^ 2) ^ 8 := by
  set s := nodeS c g
  have hv : 0 < vsig2 c s := hSm.trans_le H.hS1
  rw [biasW_rows hn c g hs h1]
  set y : Fin (mA n) → ℝ := fun j => ∫ v, G2 (√(wT c g v)) ((M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j)
      ∂stdGauss (Fin (n - 1)) - G2 √(vsig2 c s) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j) with hy
  set Q : Fin (mA n) → ℝ := fun j => AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j +
      AW2 Dm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j ^ 2 with hQ
  have hyQ : ∀ j, |y j| ≤ Q j := by
    intro j
    have R := rowW (row_stat hn c g hs hO h1 hv ξ₁ ξ₂ j) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j)
    have e : ∀ v, (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j + ((M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j -
        (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j) = (M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j := fun v => by
      simp only [s]; ring
    simp only [e] at R
    refine R.trans ?_
    have hρ : 0 ≤ rhoJ ξ₁ ξ₂ j := Real.sqrt_nonneg _
    have hC : 0 ≤ √(tA n) * O := mul_nonneg (Real.sqrt_nonneg _) hO
    have hsum := abs_add_abs_le (ξ₁ j) (ξ₂ j)
    have hsum' : (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) ≤ √2 * rhoJ ξ₁ ξ₂ j * (√(tA n) * O) :=
      mul_le_mul_of_nonneg_right hsum hC
    refine TW_le (Real.sqrt_pos.mpr hSm) (Real.sqrt_le_sqrt H.hS1) (Real.sqrt_le_sqrt H.hS2) hρ hC
      ?_ (by positivity) ?_
      (by have := vsig2_nonneg c s; have := tA_nonneg n; positivity) (by linarith [H.hS2])
      (mul_nonneg (by positivity) (DstN_nonneg c g)) ?_ (hUN_nonneg c g) H.hH (V2N_nonneg c g)
      H.hV (piN_nonneg c g) H.hP
    · have := abs_M0abar_le hn c g hs hO h1 ξ₁ ξ₂ j
      unfold rhoJ at *
      nlinarith
    · unfold rhoJ at *
      nlinarith
    · rw [rhoJ_sq]
      exact mul_le_mul_of_nonneg_left H.hD (by positivity)
  have hS : |∑ j, y j| ≤ ∑ j, |y j| := Finset.abs_sum_le_sum_abs _ _
  have step : (∑ j, |y j|) ^ 8 ≤ ((mA n : ℕ) : ℝ) ^ 7 * ∑ j, |y j| ^ 8 := by
    have := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := fun j => |y j|)
      (fun j _ => abs_nonneg _) 7
    simpa only [Finset.card_univ, Fintype.card_fin] using this
  calc (∑ j, y j) ^ 8 = |∑ j, y j| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ (∑ j, |y j|) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) hS 8
    _ ≤ ((mA n : ℕ) : ℝ) ^ 7 * ∑ j, |y j| ^ 8 := step
    _ ≤ _ := by
      gcongr with j
      exact hyQ j

end BstLean.Part171
