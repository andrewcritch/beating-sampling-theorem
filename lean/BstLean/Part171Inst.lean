import BstLean.Part171Bias

/-!
# Part 171 (file `Inst`): the statistics of a node and the row statistics

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `δ_v = z_U·(F_s(v) − F̄)`, `E_v δ_v = 0`, `E_v δ_v² ≤ |ζ|²h_U`,
`v_v = |Π_{U^⊥}F_s(v)|²`, `E_v(v_v − ς²) = −h_U`, `E_v(v_v − ς²)² = V₂`, `π_g = P_v(v_v < ς²/2)`.

The plane part of the second layer acts on a vector `y` by
`(M₀y)_j = ξ₁_j q₁(y) + ξ₂_j q₂(y)` (`M0_mulVec`), with the two linear forms `q₁`, `q₂`
(the coordinates of `√t_A y` along `ĥ` and `r̂`). The statistics of a node (functions of the
World data and `A₁` only) are
* `DstN c g = E_v (q₁(a − ā)² + q₂(a − ā)²)` (the paper's `h_U` in the form that bounds `E δ²`);
* `hUN c g = |E_v (wT − ς²)|` (the paper's `h_U` in the form of the mean of `v_v − ς²`);
* `V2N c g = E_v (wT − ς²)²` (the paper's `V₂`);
* `piN c g = P_v(wT < ς²/2)` (the paper's `π_g`).

* **`row_stat`**: at a node with `‖A₁‖_op ≤ O` and `ς² > 0`, row `j` satisfies `RowStat` with
  `Δ = 2(|ξ₁_j| + |ξ₂_j|)√t_A O`, `Γ = t_A O² + ς²`, `D = (ξ₁_j² + ξ₂_j²)·DstN`, `h = hUN`,
  `V₂ = V2N`, `π = piN`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part134 (res projPerp glue projPerp_mulVec lam)
open BstLean.Part167 (perp normSq_perp_le)
open BstLean.Part170 (Mpl hB tA aLat vmean vmean_aLat aLat_normSq_le measurable_aLat)

variable {n : ℕ}
noncomputable def q1 (c : Ret n) (y : Fin (mA n) → ℝ) : ℝ :=
  (normSq (hB c))⁻¹ * (hB c ⬝ᵥ y) * (√(tA n) * √(normSq (hB c)))
noncomputable def q2 (c : Ret n) (g : ℕ) (y : Fin (mA n) → ℝ) : ℝ :=
  (normSq (res (hB c) (a1Bar c (nodeS c g))))⁻¹ *
    (res (hB c) (a1Bar c (nodeS c g)) ⬝ᵥ res (hB c) y) *
    (√(tA n) * √(normSq (res (hB c) (a1Bar c (nodeS c g)))))
lemma M0_mulVec (c : Ret n) (g : ℕ) (ξ₁ ξ₂ y : Fin (mA n) → ℝ) (j : Fin (mA n)) :
    (M0 c g ξ₁ ξ₂ *ᵥ y) j = ξ₁ j * q1 c y + ξ₂ j * q2 c g y := by
  unfold M0 Mpl BstLean.Part157.reb glue q1 q2 cOf
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, projPerp_mulVec, Matrix.add_mulVec,
    Matrix.zero_mul, Matrix.zero_mulVec, add_zero]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

lemma normSq_nonneg' {ι : Type*} [Fintype ι] (y : ι → ℝ) : 0 ≤ normSq y := by
  unfold normSq; positivity

lemma inv_mul_sqrt_sq_le {B : ℝ} (hB : 0 ≤ B) : B⁻¹ * (√B * √B) ≤ 1 := by
  rw [Real.mul_self_sqrt hB]
  rcases hB.lt_or_eq with h | h
  · rw [inv_mul_cancel₀ h.ne']
  · rw [← h]; simp

lemma abs_q1_le (c : Ret n) (y : Fin (mA n) → ℝ) : |q1 c y| ≤ √(tA n) * √(normSq y) := by
  unfold q1
  set B := normSq (hB c)
  have hB0 : 0 ≤ B := normSq_nonneg' _
  have hd := BstLean.Part170.abs_dot_le (hB c) y
  rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hB0),
    abs_of_nonneg (by positivity : 0 ≤ √(tA n) * √B)]
  calc B⁻¹ * |hB c ⬝ᵥ y| * (√(tA n) * √B) ≤ B⁻¹ * (√B * √(normSq y)) * (√(tA n) * √B) := by
        gcongr
    _ = (B⁻¹ * (√B * √B)) * (√(tA n) * √(normSq y)) := by ring
    _ ≤ 1 * (√(tA n) * √(normSq y)) := by gcongr; exact inv_mul_sqrt_sq_le hB0
    _ = _ := one_mul _

lemma normSq_res_le (h y : Fin (mA n) → ℝ) : normSq (res h y) ≤ normSq y := by
  rw [← BstLean.Part170.perp_eq_res]; exact normSq_perp_le _ _

lemma abs_q2_le (c : Ret n) (g : ℕ) (y : Fin (mA n) → ℝ) :
    |q2 c g y| ≤ √(tA n) * √(normSq y) := by
  unfold q2
  set r := res (hB c) (a1Bar c (nodeS c g))
  set B := normSq r
  have hB0 : 0 ≤ B := normSq_nonneg' _
  have hd := BstLean.Part170.abs_dot_le r (res (hB c) y)
  have hres : √(normSq (res (hB c) y)) ≤ √(normSq y) := Real.sqrt_le_sqrt (normSq_res_le _ _)
  rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hB0),
    abs_of_nonneg (by positivity : 0 ≤ √(tA n) * √B)]
  calc B⁻¹ * |r ⬝ᵥ res (hB c) y| * (√(tA n) * √B) ≤ B⁻¹ * (√B * √(normSq y)) * (√(tA n) * √B) := by
        gcongr; exact hd.trans (by gcongr)
    _ = (B⁻¹ * (√B * √B)) * (√(tA n) * √(normSq y)) := by ring
    _ ≤ 1 * (√(tA n) * √(normSq y)) := by gcongr; exact inv_mul_sqrt_sq_le hB0
    _ = _ := one_mul _

lemma continuous_q1 (c : Ret n) : Continuous (q1 c) := by
  unfold q1; fun_prop

lemma continuous_res (h : Fin (mA n) → ℝ) : Continuous (res h) := by
  unfold res lam; fun_prop

lemma continuous_q2 (c : Ret n) (g : ℕ) : Continuous (q2 c g) := by
  unfold q2
  have := continuous_res (n := n) (hB c)
  fun_prop

/-- `|(M₀y)_j| ≤ (|ξ₁_j| + |ξ₂_j|)√t_A|y|`. -/
lemma abs_M0_le (c : Ret n) (g : ℕ) (ξ₁ ξ₂ y : Fin (mA n) → ℝ) (j : Fin (mA n)) :
    |(M0 c g ξ₁ ξ₂ *ᵥ y) j| ≤ (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * √(normSq y)) := by
  rw [M0_mulVec]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, add_mul]
  gcongr
  · exact abs_q1_le c y
  · exact abs_q2_le c g y

/-- The mean of a coordinate of `M a(v)`. -/
lemma int_mulVec {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
    {m : ℕ} {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (M : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    ∫ v, (M *ᵥ a v) j ∂μ = (M *ᵥ vmean μ a) j := by
  have hi : ∀ k, Integrable (fun v => M j k * a v k) μ := fun k =>
    (BstLean.Part171.bdd_int ((measurable_pi_apply k).comp ha) (C := K) (fun v =>
      (norm_le_pi_norm (a v) k).trans (hK v))).const_mul _
  simp only [Matrix.mulVec, dotProduct, vmean]
  rw [integral_finsetSum _ fun k _ => hi k]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

/-- `DstN c g = E_v(q₁(a − ā)² + q₂(a − ā)²)`. -/
noncomputable def DstN (c : Ret n) (g : ℕ) : ℝ :=
  ∫ v, (q1 c (aLat c (nodeS c g) v - a1Bar c (nodeS c g)) ^ 2 +
    q2 c g (aLat c (nodeS c g) v - a1Bar c (nodeS c g)) ^ 2) ∂stdGauss (Fin (n - 1))

/-- `hUN c g = |E_v(wT − ς²)|`. -/
noncomputable def hUN (c : Ret n) (g : ℕ) : ℝ :=
  |∫ v, (wT c g v - vsig2 c (nodeS c g)) ∂stdGauss (Fin (n - 1))|

/-- `V2N c g = E_v(wT − ς²)²`. -/
noncomputable def V2N (c : Ret n) (g : ℕ) : ℝ :=
  ∫ v, (wT c g v - vsig2 c (nodeS c g)) ^ 2 ∂stdGauss (Fin (n - 1))

/-- `piN c g = P_v(wT < ς²/2)`. -/
noncomputable def piN (c : Ret n) (g : ℕ) : ℝ :=
  (stdGauss (Fin (n - 1))).real {v | wT c g v < vsig2 c (nodeS c g) / 2}

lemma vsig2_nonneg (c : Ret n) (s : ℝ) : 0 ≤ vsig2 c s := le_max_left _ _

/-- **The statistics of one row** at a node. -/
theorem row_stat (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) (hv : 0 < vsig2 c (nodeS c g)) (ξ₁ ξ₂ : Fin (mA n) → ℝ) (j : Fin (mA n)) :
    RowStat (stdGauss (Fin (n - 1)))
      (fun v => (M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j - (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j)
      (wT c g) √(vsig2 c (nodeS c g)) (2 * ((|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O)))
      (tA n * O ^ 2 + vsig2 c (nodeS c g)) ((ξ₁ j ^ 2 + ξ₂ j ^ 2) * DstN c g) (hUN c g)
      (V2N c g) (piN c g) := by
  set s := nodeS c g
  set M₀ := M0 c g ξ₁ ξ₂
  set a := aLat c s
  set ā := a1Bar c s
  have ha := measurable_aLat c s
  have hsq : √(vsig2 c s) ^ 2 = vsig2 c s := Real.sq_sqrt (vsig2_nonneg c s)
  have haO : ∀ v, √(normSq (a v)) ≤ O := fun v => by
    calc √(normSq (a v)) ≤ √(O ^ 2) := Real.sqrt_le_sqrt (aLat_normSq_le hn c hs h1 v)
      _ = O := Real.sqrt_sq hO
  have hK : ∀ v, ‖a v‖ ≤ O := by
    intro v
    rw [pi_norm_le_iff_of_nonneg hO]
    intro i; rw [Real.norm_eq_abs]; exact (BstLean.Part170.abs_le_sqrt_normSq _ i).trans (haO v)
  have hmA : Measurable (fun v => (M₀ *ᵥ a v) j) :=
    (measurable_pi_apply j).comp ((Continuous.matrix_mulVec continuous_const
      continuous_id).measurable.comp ha)
  set C := (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) with hC
  have hAv : ∀ v, |(M₀ *ᵥ a v) j| ≤ C := fun v =>
    (abs_M0_le c g ξ₁ ξ₂ (a v) j).trans (by rw [hC]; gcongr; exact haO v)
  have hmean : ∫ v, (M₀ *ᵥ a v) j ∂stdGauss (Fin (n - 1)) = (M₀ *ᵥ ā) j := by
    rw [int_mulVec ha hK M₀ j, vmean_aLat]
  have hAbar : |(M₀ *ᵥ ā) j| ≤ C := by
    rw [← hmean]
    have := norm_integral_le_of_norm_le_const (μ := stdGauss (Fin (n - 1)))
      (f := fun v => (M₀ *ᵥ a v) j) (C := C)
      (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hAv v)
    simpa [Real.norm_eq_abs] using this
  have iA : Integrable (fun v => (M₀ *ᵥ a v) j) (stdGauss (Fin (n - 1))) :=
    BstLean.Part171.bdd_int hmA hAv
  have hwT0 : ∀ v, 0 ≤ wT c g v := fun v => by
    unfold wT; exact mul_nonneg (BstLean.Part171.tA_nonneg n) (normSq_nonneg' _)
  have hwTΓ : ∀ v, wT c g v ≤ tA n * O ^ 2 := fun v => by
    unfold wT
    exact mul_le_mul_of_nonneg_left ((normSq_perp_le _ _).trans ((normSq_perp_le _ _).trans
      (aLat_normSq_le hn c hs h1 v))) (BstLean.Part171.tA_nonneg n)
  -- the factorization of δ
  have hδq : ∀ v, (M₀ *ᵥ a v) j - (M₀ *ᵥ ā) j =
      ξ₁ j * q1 c (a v - ā) + ξ₂ j * q2 c g (a v - ā) := by
    intro v
    rw [← M0_mulVec, Matrix.mulVec_sub]; rfl
  have mq : Measurable (fun v => q1 c (a v - ā) ^ 2 + q2 c g (a v - ā) ^ 2) := by
    have h1' : Measurable (fun v => a v - ā) := ha.sub_const _
    exact (((continuous_q1 c).measurable.comp h1').pow_const 2).add
      (((continuous_q2 c g).measurable.comp h1').pow_const 2)
  have hqb : ∀ v, |q1 c (a v - ā) ^ 2 + q2 c g (a v - ā) ^ 2| ≤
      2 * (√(tA n) * (O + √(normSq ā))) ^ 2 := by
    intro v
    have hy : √(normSq (a v - ā)) ≤ O + √(normSq ā) := by
      have := BstLean.Part170.normSq_add_le' (n := n) (a v) (-ā)
      have e : a v + -ā = a v - ā := by abel
      rw [e] at this
      have e2 : normSq (-ā) = normSq ā := by unfold normSq; simp
      rw [e2] at this
      calc √(normSq (a v - ā)) ≤ √((√(normSq (a v)) + √(normSq ā)) ^ 2) := Real.sqrt_le_sqrt this
        _ = √(normSq (a v)) + √(normSq ā) := Real.sqrt_sq (by positivity)
        _ ≤ O + √(normSq ā) := by linarith [haO v]
    have b1 := (abs_q1_le c (a v - ā)).trans (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))
    have b2 := (abs_q2_le c g (a v - ā)).trans (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))
    rw [abs_of_nonneg (by positivity)]
    have c1 : q1 c (a v - ā) ^ 2 ≤ (√(tA n) * (O + √(normSq ā))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b1 2
    have c2 : q2 c g (a v - ā) ^ 2 ≤ (√(tA n) * (O + √(normSq ā))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b2 2
    linarith
  have iq := BstLean.Part171.bdd_int (μ := stdGauss (Fin (n - 1))) mq hqb
  refine
    { mδ := hmA.sub_const _
      mw := ?_
      hs := Real.sqrt_pos.mpr hv
      hΔ := by positivity
      hδb := fun v => ?_
      hw0 := hwT0
      hwΓ := fun v => by linarith [hwTΓ v, vsig2_nonneg c s]
      hsΓ := by rw [hsq]; linarith [mul_nonneg (BstLean.Part171.tA_nonneg n) (sq_nonneg O)]
      hδ0 := ?_
      hD := ?_
      hh := by rw [hsq]; exact le_rfl
      hV := by rw [hsq]; exact le_rfl
      hπ := by rw [hsq]; exact le_rfl }
  · unfold wT
    exact measurable_const.mul (BstLean.Part130.continuous_normSq.measurable.comp
      ((BstLean.Part167.measurable_perp _).comp ((BstLean.Part167.measurable_perp _).comp ha)))
  · refine (abs_sub _ _).trans ?_
    linarith [hAv v]
  · rw [integral_sub iA (integrable_const _), hmean]; simp
  · have hpt : ∀ v, ((M₀ *ᵥ a v) j - (M₀ *ᵥ ā) j) ^ 2 ≤
        (ξ₁ j ^ 2 + ξ₂ j ^ 2) * (q1 c (a v - ā) ^ 2 + q2 c g (a v - ā) ^ 2) := by
      intro v
      rw [hδq v]
      nlinarith [sq_nonneg (ξ₁ j * q2 c g (a v - ā) - ξ₂ j * q1 c (a v - ā))]
    have iδ2 : Integrable (fun v => ((M₀ *ᵥ a v) j - (M₀ *ᵥ ā) j) ^ 2) (stdGauss (Fin (n - 1))) :=
      BstLean.Part171.bdd_int ((hmA.sub_const _).pow_const 2) (C := (2 * C) ^ 2) (fun v =>
        BstLean.Part171.sq_abs_le ((abs_sub _ _).trans (by linarith [hAv v])))
    calc ∫ v, ((M₀ *ᵥ a v) j - (M₀ *ᵥ ā) j) ^ 2 ∂stdGauss (Fin (n - 1))
        ≤ ∫ v, (ξ₁ j ^ 2 + ξ₂ j ^ 2) * (q1 c (a v - ā) ^ 2 + q2 c g (a v - ā) ^ 2)
            ∂stdGauss (Fin (n - 1)) := integral_mono iδ2 (iq.const_mul _) hpt
      _ = (ξ₁ j ^ 2 + ξ₂ j ^ 2) * DstN c g := by rw [integral_const_mul]; rfl

end BstLean.Part171
