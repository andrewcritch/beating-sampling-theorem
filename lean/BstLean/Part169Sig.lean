import BstLean.Part169Op
import BstLean.Part109LinErr
import BstLean.Part107WickA

/-!
# Part 169 (file `Sig`): the upper bound of `ς²` with no new event

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, formula `t7:p08:sigma` (upper half): `ς(s)² ≤ (1 − s²)σ₀²`;
"ReLU contracts variance, so its variance is at most the linear variance". The paper bounds
the linear variance with a Hilbert–Schmidt event (charge `e^{−18}`). Here the bound uses the
operator norm only: `‖A₁‖_F² ≤ n‖A₁‖²_op`, and Lean's event `Eop` is already in `goodD`. So no
new event is needed.

* `dir_sq_mean`: for `V = G/|G|`, `G` standard Gaussian in `ℝ^k`: `E(w·V)² = |w|²/k`.
* `var_le_mse`: `E F² − (E F)² ≤ E(F − κ)²` for every constant `κ`.
* **`vsig2_le`**: `ς(s)² ≤ t_A(1 − s²)·n·‖A₁‖²_op/(n − 1)` for `s² ≤ 1`.
* `sig0sq n = t_A·n·O₁²/(n − 1)`; **`hvs_goodD`**: on `goodD`, `ς(s_g)² ≤ sig0sq n` at every node.
* `MomY`: `MomX` without the upper `ς` hypothesis; **`classifier_paper_momY80k`**.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI xLat hhMat uHat consV hh_normSq)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)

variable {n : ℕ}

/-- **Second moment of a uniform direction**: `E(w·V)² = |w|²/k`. -/
theorem dir_sq_mean {k : ℕ} (hk : 1 ≤ k) (w : Fin k → ℝ) :
    ∫ G, (∑ j, w j * unitF53 G j) ^ 2 ∂stdGauss (Fin k) = (∑ j, w j ^ 2) / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have mf : Measurable (fun u : Fin k → ℝ => (∑ j, w j * u j) ^ 2) := by fun_prop
  have h := BstLean.Part162.polar_integral_mul (ι := Fin k) (fun u => (∑ j, w j * u j) ^ 2)
    (fun r => r ^ 2) mf (measurable_id.pow_const 2)
  have e1 : ∀ G : Fin k → ℝ, (∑ j, w j * unitF53 G j) ^ 2 * radF53 G ^ 2 =
      (∑ j, w j * G j) ^ 2 := by
    intro G
    have hG := BstLean.Part162.unitF_smul G
    have : ∑ j, w j * G j = radF53 G * ∑ j, w j * unitF53 G j := by
      conv_lhs => rw [← hG]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]; ring
  simp only [e1] at h
  rw [BstLean.Part109.le_lin_sq] at h
  have e2 : ∫ G, radF53 G ^ 2 ∂stdGauss (Fin k) = k := by
    simp only [BstLean.Part162.radF_sq]
    rw [BstLean.Part107.normSq_mom1]; simp
  rw [e2] at h
  rw [eq_div_iff hkR.ne']
  linarith

/-- **Variance at most the mean square about any constant.** -/
lemma var_le_mse {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {F : α → ℝ} (i1 : Integrable F μ) (i2 : Integrable (fun x => F x ^ 2) μ) (κ : ℝ) :
    ∫ x, F x ^ 2 ∂μ - (∫ x, F x ∂μ) ^ 2 ≤ ∫ x, (F x - κ) ^ 2 ∂μ := by
  have e : ∫ x, (F x - κ) ^ 2 ∂μ = ∫ x, F x ^ 2 ∂μ - 2 * κ * ∫ x, F x ∂μ + κ ^ 2 := by
    have : (fun x => (F x - κ) ^ 2) = fun x => F x ^ 2 - 2 * κ * F x + κ ^ 2 := by
      funext x; ring
    have hi : Integrable (fun x => F x ^ 2 - 2 * κ * F x) μ := i2.sub (i1.const_mul _)
    rw [this, integral_add (f := fun x => F x ^ 2 - 2 * κ * F x) hi (integrable_const _),
      integral_sub i2 (i1.const_mul _), integral_const_mul, integral_const, smul_eq_mul,
      probReal_univ, one_mul]
  rw [e]; nlinarith [sq_nonneg (∫ x, F x ∂μ - κ)]

/-- The sum against `consV`: `Σ_k f_k (consV z g)_k = f₀ z + Σ_j f_{j+1} g_j`. -/
lemma sum_mul_consV (hn : 1 ≤ n) (f : Fin n → ℝ) (z : ℝ) (g : Fin (n - 1) → ℝ) :
    ∑ k, f k * consV z g k = f ⟨0, by omega⟩ * z + ∑ j : Fin (n - 1), f ⟨j + 1, by omega⟩ * g j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  congr 1

/-- `Σ_k Σ_i (A H)_{ik}² ≤ n·‖A‖²_op` (`H` an isometry). -/
lemma frob_AH_le (c : Ret n) :
    ∑ i, ∑ k, (A1 c * hhMat (uHat c)) i k ^ 2 ≤ n * BstLean.Part152.opN (A1 c) ^ 2 := by
  classical
  rw [Finset.sum_comm]
  have hk : ∀ k : Fin n, ∑ i, (A1 c * hhMat (uHat c)) i k ^ 2 ≤
      BstLean.Part152.opN (A1 c) ^ 2 := by
    intro k
    have e : ∀ i, (A1 c * hhMat (uHat c)) i k =
        ((A1 c).mulVec ((hhMat (uHat c)).mulVec (Pi.single k 1))) i := by
      intro i; rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl
    simp only [e]
    have h1 := opB_of_opN (A1 c) (le_refl _) ((hhMat (uHat c)).mulVec (Pi.single k 1))
    rw [hh_normSq] at h1
    have h2 : normSq (Pi.single k (1 : ℝ) : Fin n → ℝ) = 1 := by
      unfold normSq; rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [h2, mul_one] at h1
    exact h1
  calc ∑ k, ∑ i, (A1 c * hhMat (uHat c)) i k ^ 2 ≤ ∑ _k : Fin n, BstLean.Part152.opN (A1 c) ^ 2 :=
        Finset.sum_le_sum fun k _ => hk k
    _ = n * BstLean.Part152.opN (A1 c) ^ 2 := by simp

/-- **The upper bound of `ς²`** (no event): `ς(s)² ≤ t_A(1 − s²)·n‖A₁‖²_op/(n − 1)`. -/
theorem vsig2_le (hn : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ 2 / (mA n : ℝ) * ((1 - s ^ 2) * (n * BstLean.Part152.opN (A1 c) ^ 2) /
      ((n : ℝ) - 1)) := by
  have hn1 : 1 ≤ n := by omega
  have hk : 1 ≤ n - 1 := by omega
  have hnm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1]; simp
  have hn1R : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set B := A1 c * hhMat (uHat c) with hB
  set ν := stdGauss (Fin (n - 1))
  have hs1 : 0 ≤ 1 - s ^ 2 := by linarith
  -- the row preactivation
  have hY : ∀ i v, (A1 c).mulVec (xLat c s (unitF53 v)) i =
      B i ⟨0, by omega⟩ * s + √(1 - s ^ 2) *
        ∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ * unitF53 v j := by
    intro i v
    unfold xLat
    rw [Matrix.mulVec_mulVec, ← hB]
    change ∑ k, B i k * consV s (√(1 - s ^ 2) • unitF53 v) k = _
    rw [sum_mul_consV hn1]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring
  -- bounds and integrability
  have hxb : ∀ v, normSq (xLat c s (unitF53 v)) ≤ 1 := fun v => normSq_xLat_le' hn1 c hs v
  have hrowb : ∀ i v, |(A1 c).mulVec (xLat c s (unitF53 v)) i| ≤ √(∑ k, A1 c i k ^ 2) := by
    intro i v
    have h := BstLean.Part130.abs_dot_le (fun k => A1 c i k) (xLat c s (unitF53 v))
    have h2 : √(normSq (xLat c s (unitF53 v))) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hxb v
    calc |(A1 c).mulVec (xLat c s (unitF53 v)) i| = |∑ k, A1 c i k * xLat c s (unitF53 v) k| := rfl
      _ ≤ √(normSq (fun k => A1 c i k)) * √(normSq (xLat c s (unitF53 v))) := h
      _ ≤ √(∑ k, A1 c i k ^ 2) * 1 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have mrow : ∀ i, Measurable (fun v => relu ((A1 c).mulVec (xLat c s (unitF53 v)) i)) :=
    fun i => measurable_relu.comp ((measurable_pi_apply i).comp
      ((BstLean.Part149.measurable_mulVec_left (A1 c)).comp
        (BstLean.Part161.measurable_xLat_comp c measurable_const measurable_unitF)))
  have brow : ∀ i v, |relu ((A1 c).mulVec (xLat c s (unitF53 v)) i)| ≤ √(∑ k, A1 c i k ^ 2) :=
    fun i v => by
      have := BstLean.Part142.abs_relu_sub_le ((A1 c).mulVec (xLat c s (unitF53 v)) i) 0
      simp only [sub_zero, relu, max_self] at this
      exact (by simpa [relu] using this : |relu _| ≤ _).trans (hrowb i v)
  have i1 : ∀ i, Integrable (fun v => relu ((A1 c).mulVec (xLat c s (unitF53 v)) i)) ν :=
    fun i => Integrable.mono' (integrable_const _) (mrow i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact brow i v)
  have i2 : ∀ i, Integrable (fun v => relu ((A1 c).mulVec (xLat c s (unitF53 v)) i) ^ 2) ν :=
    fun i => Integrable.mono' (integrable_const ((√(∑ k, A1 c i k ^ 2)) ^ 2))
      ((mrow i).pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (brow i v) 2)
  -- one row
  have hrow : ∀ i, e1Bar c s i - a1Bar c s i ^ 2 ≤
      (1 - s ^ 2) * (∑ k, B i k ^ 2) / ((n : ℝ) - 1) := by
    intro i
    have hv := var_le_mse (i1 i) (i2 i) (relu (B i ⟨0, by omega⟩ * s))
    refine hv.trans ?_
    have hpt : ∀ v, (relu ((A1 c).mulVec (xLat c s (unitF53 v)) i) -
        relu (B i ⟨0, by omega⟩ * s)) ^ 2 ≤
        (1 - s ^ 2) * (∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ * unitF53 v j) ^ 2 := by
      intro v
      have h := BstLean.Part142.abs_relu_sub_le ((A1 c).mulVec (xLat c s (unitF53 v)) i)
        (B i ⟨0, by omega⟩ * s)
      rw [hY i v] at h ⊢
      have e : B i ⟨0, by omega⟩ * s + √(1 - s ^ 2) *
          ∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ * unitF53 v j - B i ⟨0, by omega⟩ * s =
          √(1 - s ^ 2) * ∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ * unitF53 v j := by ring
      rw [e] at h
      calc _ ≤ (√(1 - s ^ 2) * ∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ * unitF53 v j) ^ 2 :=
            sq_le_sq.mpr h
        _ = _ := by rw [mul_pow, Real.sq_sqrt hs1]
    have mq : Measurable (fun v => (∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ * unitF53 v j) ^ 2) :=
      (Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp measurable_unitF).const_mul
        _).pow_const 2
    have iq : Integrable (fun v => (∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ * unitF53 v j) ^ 2) ν := by
      refine Integrable.mono' (integrable_const (∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ ^ 2))
        mq.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := BstLean.Part130.abs_dot_le (fun j : Fin (n - 1) => B i ⟨j + 1, by omega⟩)
        (unitF53 v)
      have hu : normSq (unitF53 v) ≤ 1 := by
        have h1 := BstLean.Part162.radF_unitF_le v
        have h3 : normSq (unitF53 v) = radF53 (unitF53 v) ^ 2 := (BstLean.Part162.radF_sq _).symm
        rw [h3]; have := BstLean.Part162.radF_nonneg (unitF53 v); nlinarith
      have h4 : (∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ * unitF53 v j) ^ 2 ≤
          normSq (fun j : Fin (n - 1) => B i ⟨j + 1, by omega⟩) * normSq (unitF53 v) := by
        calc _ ≤ (√(normSq (fun j : Fin (n - 1) => B i ⟨j + 1, by omega⟩)) *
              √(normSq (unitF53 v))) ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
          _ = _ := by rw [mul_pow, Real.sq_sqrt (normSq_nonneg _), Real.sq_sqrt (normSq_nonneg _)]
      calc _ ≤ normSq (fun j : Fin (n - 1) => B i ⟨j + 1, by omega⟩) * normSq (unitF53 v) := h4
        _ ≤ normSq (fun j : Fin (n - 1) => B i ⟨j + 1, by omega⟩) * 1 :=
            mul_le_mul_of_nonneg_left hu (normSq_nonneg _)
        _ = _ := by unfold normSq; ring
    have hint := integral_mono
      (Integrable.mono' (iq.const_mul (1 - s ^ 2)) (((mrow i).sub measurable_const).pow_const
        2).aestronglyMeasurable (Filter.Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt v))
      (iq.const_mul (1 - s ^ 2)) hpt
    refine hint.trans ?_
    rw [integral_const_mul, dir_sq_mean hk, hnm]
    have htail : ∑ j : Fin (n - 1), B i ⟨j + 1, by omega⟩ ^ 2 ≤ ∑ k, B i k ^ 2 := by
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      subst hm
      rw [Fin.sum_univ_succ]
      have : 0 ≤ B i 0 ^ 2 := sq_nonneg _
      have e : ∑ j : Fin (m + 1 - 1), B i ⟨j + 1, by omega⟩ ^ 2 = ∑ j : Fin m, B i j.succ ^ 2 := rfl
      rw [e]; linarith
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htail hs1) hn1R.le
  -- sum over rows
  have hsum : ∑ i, e1Bar c s i - normSq (a1Bar c s) ≤
      (1 - s ^ 2) * (n * BstLean.Part152.opN (A1 c) ^ 2) / ((n : ℝ) - 1) := by
    have e : ∑ i, e1Bar c s i - normSq (a1Bar c s) = ∑ i, (e1Bar c s i - a1Bar c s i ^ 2) := by
      unfold normSq; rw [Finset.sum_sub_distrib]
    rw [e]
    calc ∑ i, (e1Bar c s i - a1Bar c s i ^ 2) ≤ ∑ i, (1 - s ^ 2) * (∑ k, B i k ^ 2) / ((n : ℝ) - 1) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = (1 - s ^ 2) * (∑ i, ∑ k, B i k ^ 2) / ((n : ℝ) - 1) := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (frob_AH_le c) hs1) hn1R.le
  unfold vsig2
  have hm : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  refine max_le (by positivity) (mul_le_mul_of_nonneg_left hsum hm)

/-- `σ₀² = t_A·n·O₁²/(n − 1)`, the upper bound of `ς²` on the good set. -/
noncomputable def sig0sq (n : ℕ) : ℝ := 2 / (mA n : ℝ) * (n * O1n n ^ 2 / ((n : ℝ) - 1))

lemma sig0sq_pos (hn : 2 ≤ n) : 0 < sig0sq n := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < (mA n : ℝ) := by unfold mA; push_cast; positivity
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have := O1n_pos (n := n) (by omega)
  unfold sig0sq; positivity

/-- **The upper `ς` bound at the nodes on the good set** (no new event). -/
theorem hvs_goodD (hn : 80000 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) : ∀ a ∈ KR c, vsig2 c (sgR c a) ≤ sig0sq n := by
  intro a ha
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := BstLean.Part164.window_goodA (by omega) passF passW measurable_passF
    measurable_passW _ c hc
  obtain ⟨hLH, hbulk, -⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH (gIdx_lt c hn1 (latC (paperDesignP n) c a))
  have hq := qB_pos hn
  have hs : sgR c a ^ 2 ≤ 1 := by have := hbulk _ hs1 hs2; unfold sgR; linarith
  have hop : BstLean.Part152.opN (A1 c) ≤ O1n n :=
    BstLean.Part164.eop_of_goodC16 (BstLean.Part164.goodC16_of_goodA (by omega) passF passW
      measurable_passF measurable_passW hc)
  have h0 := BstLean.Part152.opN_nonneg (A1 c)
  refine (vsig2_le (by omega) c hs).trans ?_
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hm : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  unfold sig0sq
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ h1.le) hm
  have hsq : BstLean.Part152.opN (A1 c) ^ 2 ≤ O1n n ^ 2 := pow_le_pow_left₀ h0 hop 2
  have hs0 : 0 ≤ sgR c a ^ 2 := sq_nonneg _
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (1 - sgR c a ^ 2) * (n * BstLean.Part152.opN (A1 c) ^ 2)
      ≤ 1 * (n * O1n n ^ 2) := by
        apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hsq hnn) (by positivity)
          (by norm_num)
    _ = n * O1n n ^ 2 := one_mul _

/-- **The moment inputs not yet proved**, after Part 169: the `L⁸` bounds `A_f`, `A_ω` of the
exact-rule errors, and `v_max`, `H_f`, `C_v`. -/
structure MomY (c : Ret n) (vmax Af Aw Hf Cv : ℝ) : Prop where
  hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax
  hXF : ∫ a in KR c, exF c a ^ 8 ∂muI n ≤ Af ^ 8
  hXW : ∫ a in KR c, exW c a ^ 8 ∂muI n ≤ Aw ^ 8
  hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2

/-- **The classifier theorem with the remaining moment inputs `MomY`** (every `n ≥ 80 000`).
Remaining: `MomY` on `goodD n D (E_A ∩ E_bias)`, the numerical condition
`P_B ≤ 0.004295²` at `a_f = aFn n A_f σ₀`, `a_ω = aWn n A_ω σ₀` with `σ₀ = √(sig0sq n)`, and
the charges `δ_A + δ_bias ≤ roomE`. -/
theorem classifier_paper_momY80k (hn : 80000 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ BstLean.Part167.roomE)
    {ε vmax Af Aw Hf Cv : ℝ} (hε1 : ε < 1) (hT : 0 < ε - vmax / dStar)
    (hAf : 0 < Af) (hAw : 0 < Aw) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax (aWn n Aw √(sig0sq n))
      (aFn n Af √(sig0sq n)) Hf Cv ≤ (4295 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomY c vmax Af Aw Hf Cv) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hσ : 0 < √(sig0sq n) := Real.sqrt_pos.mpr (sig0sq_pos (by omega))
  refine classifier_paper_momX80k hn t hEA hEb hA hb hroom hε1 hT hσ hAf hAw hHf hCv hnum
    fun c hc => ?_
  have hM' := hM c hc
  refine ⟨hM'.hVm, fun a ha => ?_, hM'.hXF, hM'.hXW, hM'.hf4, hM'.hf24, hM'.hV⟩
  rw [Real.sq_sqrt (sig0sq_pos (by omega)).le]
  exact hvs_goodD hn hc a ha

end BstLean.Part169
