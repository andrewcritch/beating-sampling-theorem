import BstLean.Part151SA
import BstLean.Part151TR2
import BstLean.Part151Struct

/-!
# Part 151: Lemma ST (b), (c) and equation (Tm)

Role: `delegations/statements/p151-spec.md`, items 1 and 4. Paper source:
`proofs/option-n/theorem5-04-standin-structure.tex`, Lemma ST (b), (c);
`proofs/option-n/theorem5-10-transport.tex`, equation (Tm).

* `lemmaST_c`: `V_Δ ≤ T_U² + (T_s + T_m)² + 2(T_s + T_m)·max(0, X_×)` (abstract vectors);
  `lemmaVA_b`: the corollary with numbers; `exists_dir`: the unit direction `w_×`.
* `cenB`, `cAv`, `sigP`, `xIn`, `a2v`, `lamX`, `sigX`, `Xm`, `Ym`, `P2`, `dM`, `dS`, `dU`, `Dc`:
  the centre `b`, `c_A`, `σ_p`, the stand-in input, `a₂(x)`, `λ(x)`, `σ(x)`, the coupled pair,
  `Δ_m`, `Δ_s`, `Δ_U`, the coupling cost `𝔇_c`.
* **`lemmaST_b`**: `Δ̂′ = Δ_s − Δ_U − Δ_m`.
* **`Dc_eq`**: `𝔇_c = |c_A|²·E(λ − 1)² + n·E(σ − σ_p)²`.
* **`lemmaTm`**: `Pr_{F₁,F₂}(t_F|Δ_m|² > (1 + δ)(1 + δ′)(2/n)𝔇_c) ≤ (432/m_F²)(1 + 63/m_F)(1/δ⁴
  + 1/δ′⁴)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (nrm nrm_sq nrm_nonneg)
open BstLean.Part134 (lam res sig measurable_lam measurable_sig normSq_ne_zero)
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint)
open BstLean.Part138 (cheapIn integral_cheapIn)
open BstLean.Part139 (gamK)
open BstLean.Part141 (cenA tauWA)
open BstLean.Part149 (thA tauOutOf lam_sq_le normSq_res_le stdGauss_normSq)
open BstLean.Part150 (CMap preH)

/-! ## Lemma ST (c), abstract -/

section abs

variable {ι : Type*} [Fintype ι]

lemma normSq_neg' (b : ι → ℝ) : normSq (-b) = normSq b := by
  unfold normSq; simp

lemma nrm_sub_le (a b : ι → ℝ) : nrm (a - b) ≤ nrm a + nrm b := by
  have h := BstLean.Part140.nrm_add_le' a (-b)
  have e : nrm (-b) = nrm b := by unfold nrm; rw [normSq_neg']
  rw [e, ← sub_eq_add_neg] at h
  exact h

/-- **Lemma ST (c)**: with `Δ = s − U − m`, `T_• = √(t·|•|²)`, `s − m = r·w`, `r = |s − m|`:
`t|Δ|² ≤ T_U² + (T_s + T_m)² + 2(T_s + T_m)·max(0, −√t⟨U, w⟩)`. -/
theorem lemmaST_c {t : ℝ} (ht : 0 ≤ t) (s U m w : ι → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hw : s - m = r • w) (hrn : r ^ 2 = normSq (s - m)) :
    t * normSq (s - U - m) ≤ t * normSq U + (√(t * normSq s) + √(t * normSq m)) ^ 2 +
      2 * (√(t * normSq s) + √(t * normSq m)) * max 0 (-(√t * (U ⬝ᵥ w))) := by
  have hs : √(t * normSq s) = √t * nrm s := Real.sqrt_mul ht _
  have hm : √(t * normSq m) = √t * nrm m := Real.sqrt_mul ht _
  have hrr : r = nrm (s - m) := by
    unfold nrm; rw [← hrn, Real.sqrt_sq hr]
  have hst0 : 0 ≤ √t := Real.sqrt_nonneg _
  set A : ℝ := √(t * normSq s) + √(t * normSq m) with hA
  set q : ℝ := √t * r with hq
  have hq0 : 0 ≤ q := mul_nonneg hst0 hr
  have hqA : q ≤ A := by
    rw [hA, hs, hm, hq, hrr, ← mul_add]
    exact mul_le_mul_of_nonneg_left (nrm_sub_le s m) hst0
  have e1 : normSq (s - U - m) = normSq (s - m) + normSq U - 2 * (U ⬝ᵥ (s - m)) := by
    simp only [normSq, dotProduct, Pi.sub_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : U ⬝ᵥ (s - m) = r * (U ⬝ᵥ w) := by
    rw [hw, dotProduct_smul, smul_eq_mul]
  have htt : √t * √t = t := Real.mul_self_sqrt ht
  set x : ℝ := -(√t * (U ⬝ᵥ w)) with hx
  set M : ℝ := max 0 x with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hxM : x ≤ M := le_max_right _ _
  have e3 : t * normSq (s - U - m) = q ^ 2 + t * normSq U + 2 * (q * x) := by
    rw [e1, e2, ← hrn, hq, hx]
    have : t * (r ^ 2 + normSq U - 2 * (r * (U ⬝ᵥ w))) =
        (√t * √t) * r ^ 2 + t * normSq U - 2 * ((√t * √t) * r * (U ⬝ᵥ w)) := by
      rw [htt]; ring
    rw [this]; ring
  rw [e3]
  have h1 : q ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hq0 hqA 2
  have h2 : q * x ≤ A * M :=
    (mul_le_mul_of_nonneg_left hxM hq0).trans (mul_le_mul_of_nonneg_right hqA hM0)
  linarith

/-- **Proposition VA (b), the algebra**: if `T_U ≤ a_U·u`, `T_s ≤ a_S·u`, `T_m ≤ a_M·u` and
`max(0, X_×) ≤ x·u`, then `t|Δ|² ≤ (a_U² + (a_S + a_M)² + 2(a_S + a_M)x)·u²`. -/
theorem lemmaVA_b {t : ℝ} (ht : 0 ≤ t) (s U m w : ι → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hw : s - m = r • w) (hrn : r ^ 2 = normSq (s - m)) {u aU aS aM x : ℝ} (hu : 0 ≤ u)
    (haS : 0 ≤ aS) (haM : 0 ≤ aM)
    (hU : √(t * normSq U) ≤ aU * u) (hS : √(t * normSq s) ≤ aS * u)
    (hM : √(t * normSq m) ≤ aM * u) (hX : max 0 (-(√t * (U ⬝ᵥ w))) ≤ x * u) :
    t * normSq (s - U - m) ≤ (aU ^ 2 + (aS + aM) ^ 2 + 2 * (aS + aM) * x) * u ^ 2 := by
  have h := lemmaST_c ht s U m w hr hw hrn
  have hU0 : 0 ≤ t * normSq U := mul_nonneg ht (normSq_nonneg _)
  have e : t * normSq U = √(t * normSq U) ^ 2 := (Real.sq_sqrt hU0).symm
  have h1 : t * normSq U ≤ (aU * u) ^ 2 := by
    rw [e]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hU 2
  set A : ℝ := √(t * normSq s) + √(t * normSq m) with hA
  have hA0 : 0 ≤ A := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hAle : A ≤ (aS + aM) * u := by rw [hA]; linarith
  have h2 : A ^ 2 ≤ ((aS + aM) * u) ^ 2 := pow_le_pow_left₀ hA0 hAle 2
  have hM0 : 0 ≤ max 0 (-(√t * (U ⬝ᵥ w))) := le_max_left _ _
  have h3 : A * max 0 (-(√t * (U ⬝ᵥ w))) ≤ ((aS + aM) * u) * (x * u) :=
    mul_le_mul hAle hX hM0 (by positivity)
  nlinarith

/-- The direction `w_×`: `s − m = r·w` with `r = |s − m|` and `|w| ≤ 1`. -/
lemma exists_dir (s m : ι → ℝ) :
    ∃ (r : ℝ) (w : ι → ℝ), 0 ≤ r ∧ normSq w ≤ 1 ∧ s - m = r • w ∧ r ^ 2 = normSq (s - m) := by
  by_cases h : normSq (s - m) = 0
  · refine ⟨0, 0, le_rfl, ?_, ?_, ?_⟩
    · simp [normSq]
    · rw [zero_smul]
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((s - m) i))).mp h j
        (Finset.mem_univ j)
      simpa using this
    · rw [h]; norm_num
  · have hpos : 0 < normSq (s - m) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h)
    have hr : 0 < nrm (s - m) := Real.sqrt_pos.mpr hpos
    refine ⟨nrm (s - m), (1 / nrm (s - m)) • (s - m), hr.le, ?_, ?_, nrm_sq _⟩
    · rw [normSq_smul, div_pow, one_pow, nrm_sq, one_div, inv_mul_cancel₀ h]
    · rw [smul_smul, mul_one_div_cancel hr.ne', one_smul]

end abs

/-! ## The objects of Lemma ST (b) -/

section conc

variable {n : ℕ}

/-- The centre `b`. -/
noncomputable def cenB (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    Fin (mA n) → ℝ := bh (W, thA A)

/-- `c_A = A₃ b`. -/
noncomputable def cAv (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    Fin n → ℝ := A.2.2.mulVec (cenB bh W A)

/-- `σ_p`. -/
noncomputable def sigP (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    ℝ := tauOutOf n (cenB bh W A)

/-- The stand-in input `x = sphPt(ĉ + τ₀ξ)`. -/
noncomputable def xIn (W : MlpParam (2 * n) (mW n) n) (ξ : Fin n → ℝ) : Fin n → ℝ :=
  sphPt (cenA W + tauWA W • ξ)

/-- `a₂(x)`. -/
noncomputable def a2v (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (ξ : Fin n → ℝ) : Fin (mA n) → ℝ := hid2 A.1 A.2.1 (xIn W ξ)

/-- `λ(x)`. -/
noncomputable def lamX (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (ξ : Fin n → ℝ) : ℝ := lam (cenB bh W A) (a2v W A ξ)

/-- `σ(x)`. -/
noncomputable def sigX (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (ξ : Fin n → ℝ) : ℝ := sig (2 / (mA n : ℝ)) (cenB bh W A) (a2v W A ξ)

/-- `λ(x)c_A + σ(x)η′`. -/
noncomputable def Xm (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (q : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  lamX bh W A q.1 • cAv bh W A + sigX bh W A q.1 • q.2

/-- `c_A + σ_pη′`. -/
noncomputable def Ym (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (q : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ := cAv bh W A + sigP bh W A • q.2

/-- The distribution of `(ξ, η′)`. -/
noncomputable abbrev P2 (n : ℕ) : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (stdGauss (Fin n)).prod (stdGauss (Fin n))

/-- `Δ_m`. -/
noncomputable def dM (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (θF : HidParam n (mF n)) : Fin (mF n) → ℝ := dPair (P2 n) (Xm bh W A) (Ym bh W A) θF

/-- `Δ_s`. -/
noncomputable def dS (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (θF : HidParam n (mF n)) (k : ℕ) (η : Fin k → Fin n → ℝ) : Fin (mF n) → ℝ :=
  dSamp θF (cAv bh W A) (sigP bh W A) k η

/-- `Δ_U`. -/
noncomputable def dU (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (θF : HidParam n (mF n)) : Fin (mF n) → ℝ := fun i =>
  ∫ ξ, hid2 θF.1 θF.2 (mlpEval A (xIn W ξ)) i ∂stdGauss (Fin n) -
    ∫ q, hid2 θF.1 θF.2 (Xm bh W A q) i ∂P2 n

/-- The coupling cost `𝔇_c = E|(λc_A + ση′) − (c_A + σ_pη′)|²`. -/
noncomputable def Dc (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    ℝ := ∫ q, normSq (Xm bh W A q - Ym bh W A q) ∂P2 n

variable (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)

lemma measurable_xIn : Measurable (xIn W) :=
  measurable_sphPt.comp (measurable_const.add (measurable_const_smul _))

lemma measurable_a2v : Measurable (a2v W A) := by
  have hc : Continuous (fun y : Fin n → ℝ => hid2 A.1 A.2.1 y) :=
    (continuous_hid2_joint (N := n) (m := mA n)).comp
      ((continuous_const (y := ((A.1, A.2.1) : HidParam n (mA n)))).prodMk continuous_id)
  exact hc.measurable.comp (measurable_xIn W)

lemma measurable_lamX : Measurable (lamX bh W A) :=
  (measurable_lam _).comp (measurable_a2v W A)

lemma measurable_sigX : Measurable (sigX bh W A) :=
  (measurable_sig _ _).comp (measurable_a2v W A)

lemma measurable_Xm : Measurable (Xm bh W A) := by
  unfold Xm
  exact (((measurable_lamX bh W A).comp measurable_fst).smul measurable_const).add
    (((measurable_sigX bh W A).comp measurable_fst).smul measurable_snd)

lemma measurable_Ym : Measurable (Ym bh W A) := by
  unfold Ym
  have h : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => sigP bh W A • q.2) :=
    (measurable_const_smul (sigP bh W A)).comp measurable_snd
  exact measurable_const.add h

lemma a2v_le (hn : 1 ≤ n) (ξ : Fin n → ℝ) :
    normSq (a2v W A ξ) ≤ frob A.2.1 * frob A.1 := by
  have h := normSq_hid2_le A.1 A.2.1 (xIn W ξ)
  unfold xIn at h
  rw [normSq_sphPt hn, mul_one] at h
  exact h

lemma lamX_sq_le (hn : 1 ≤ n) (hb : cenB bh W A ≠ 0) (ξ : Fin n → ℝ) :
    lamX bh W A ξ ^ 2 ≤ frob A.2.1 * frob A.1 / normSq (cenB bh W A) := by
  have hb0 : 0 < normSq (cenB bh W A) :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (normSq_ne_zero hb))
  exact (lam_sq_le hb _).trans (div_le_div_of_nonneg_right (a2v_le W A hn ξ) hb0.le)

lemma sigX_nonneg (ξ : Fin n → ℝ) : 0 ≤ sigX bh W A ξ :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma sigX_sq_le (hn : 1 ≤ n) (hb : cenB bh W A ≠ 0) (ξ : Fin n → ℝ) :
    sigX bh W A ξ ^ 2 ≤ 2 / (mA n : ℝ) * (frob A.2.1 * frob A.1) := by
  have hv : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  unfold sigX sig
  rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (normSq_nonneg _)]
  exact mul_le_mul_of_nonneg_left ((normSq_res_le hb _).trans (a2v_le W A hn ξ)) hv

lemma snd_normSq_int :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => normSq q.2) (P2 n) :=
  (stdGauss_normSq n).1.comp_snd _

lemma Xm_normSq_le (hn : 1 ≤ n) (hb : cenB bh W A ≠ 0) (q : (Fin n → ℝ) × (Fin n → ℝ)) :
    normSq (Xm bh W A q) ≤
      2 * (frob A.2.1 * frob A.1 / normSq (cenB bh W A) * normSq (cAv bh W A)) +
        2 * (2 / (mA n : ℝ) * (frob A.2.1 * frob A.1) * normSq q.2) := by
  unfold Xm
  refine (normSq_add_le _ _).trans ?_
  rw [normSq_smul, normSq_smul]
  have h1 := mul_le_mul_of_nonneg_right (lamX_sq_le bh W A hn hb q.1)
    (normSq_nonneg (cAv bh W A))
  have h2 := mul_le_mul_of_nonneg_right (sigX_sq_le bh W A hn hb q.1) (normSq_nonneg q.2)
  linarith

lemma Ym_normSq_le (q : (Fin n → ℝ) × (Fin n → ℝ)) :
    normSq (Ym bh W A q) ≤ 2 * normSq (cAv bh W A) + 2 * (sigP bh W A ^ 2 * normSq q.2) := by
  unfold Ym
  refine (normSq_add_le _ _).trans ?_
  rw [normSq_smul]

lemma XY_int (hn : 1 ≤ n) (hb : cenB bh W A ≠ 0) :
    Integrable (fun q => normSq (Xm bh W A q - Ym bh W A q)) (P2 n) := by
  have hI := snd_normSq_int (n := n)
  have hdom : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      2 * (2 * (frob A.2.1 * frob A.1 / normSq (cenB bh W A) * normSq (cAv bh W A)) +
        2 * (2 / (mA n : ℝ) * (frob A.2.1 * frob A.1) * normSq q.2)) +
      2 * (2 * normSq (cAv bh W A) + 2 * (sigP bh W A ^ 2 * normSq q.2))) (P2 n) :=
    (((integrable_const _).add ((hI.const_mul _).const_mul _)).const_mul _).add
      (((integrable_const _).add ((hI.const_mul _).const_mul _)).const_mul _)
  have hm : Measurable (fun q => normSq (Xm bh W A q - Ym bh W A q)) :=
    continuous_normSq.measurable.comp ((measurable_Xm bh W A).sub (measurable_Ym bh W A))
  refine hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)]
  have h := normSq_add_le (Xm bh W A q) (-(Ym bh W A q))
  rw [normSq_neg', ← sub_eq_add_neg] at h
  have h1 := Xm_normSq_le bh W A hn hb q
  have h2 := Ym_normSq_le bh W A q
  linarith

/-- **Lemma ST (b): `Δ̂′ = Δ_s − Δ_U − Δ_m`.** -/
theorem lemmaST_b (hn : 1 ≤ n) (hb : cenB bh W A ≠ 0) (θF : HidParam n (mF n)) (k : ℕ)
    (η : Fin k → Fin n → ℝ) :
    dHat bh k ((W, A, θF), η) = dS bh W A θF k η - dU bh W A θF - dM bh W A θF := by
  funext i
  have hXY := XY_int bh W A hn hb
  have hpair := hid2_pair_integrable (P2 n) (measurable_Xm bh W A) (measurable_Ym bh W A) hXY
    θF i
  have hYγ : Integrable (fun γ : Fin n → ℝ => zS θF (cAv bh W A) (sigP bh W A) γ i)
      (stdGauss (Fin n)) := (zS_coord_memLp θF _ _ i).integrable (by norm_num)
  have hY : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      hid2 θF.1 θF.2 (Ym bh W A q) i) (P2 n) := hYγ.comp_snd _
  have hX : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      hid2 θF.1 θF.2 (Xm bh W A q) i) (P2 n) := by
    refine (hpair.add hY).congr (Filter.Eventually.of_forall fun q => ?_)
    exact sub_add_cancel _ _
  have eY : ∫ q, hid2 θF.1 θF.2 (Ym bh W A q) i ∂P2 n =
      ∫ γ, zS θF (cAv bh W A) (sigP bh W A) γ i ∂stdGauss (Fin n) := by
    rw [integral_prod _ hY]
    have e : ∀ x : Fin n → ℝ, ∫ y, hid2 θF.1 θF.2 (Ym bh W A (x, y)) i ∂stdGauss (Fin n) =
        ∫ γ, zS θF (cAv bh W A) (sigP bh W A) γ i ∂stdGauss (Fin n) := fun _ => rfl
    simp_rw [e]
    simp
  have h4 : dM bh W A θF i = ∫ q, hid2 θF.1 θF.2 (Xm bh W A q) i ∂P2 n -
      ∫ γ, zS θF (cAv bh W A) (sigP bh W A) γ i ∂stdGauss (Fin n) := by
    rw [← eY, ← integral_sub hX hY]
    rfl
  have hφ : Measurable (fun x => hidF θF.1 θF.2 A x i) := (continuous_hidF _ _ _ i).measurable
  have h1 : dHat bh k ((W, A, θF), η) i =
      (k : ℝ)⁻¹ * ∑ j, zS θF (cAv bh W A) (sigP bh W A) (η j) i -
        ∫ ξ, hid2 θF.1 θF.2 (mlpEval A (xIn W ξ)) i ∂stdGauss (Fin n) := by
    unfold dHat
    simp only
    rw [integral_cheapIn _ _ hφ]
    rfl
  have h2 : dS bh W A θF k η i = (k : ℝ)⁻¹ * ∑ j, zS θF (cAv bh W A) (sigP bh W A) (η j) i -
      ∫ γ, zS θF (cAv bh W A) (sigP bh W A) γ i ∂stdGauss (Fin n) := rfl
  have h3 : dU bh W A θF i = ∫ ξ, hid2 θF.1 θF.2 (mlpEval A (xIn W ξ)) i ∂stdGauss (Fin n) -
      ∫ q, hid2 θF.1 θF.2 (Xm bh W A q) i ∂P2 n := rfl
  simp only [Pi.sub_apply]
  rw [h1, h2, h3, h4]
  ring

/-! ## The coupling cost and equation (Tm) -/

/-- **The coupling cost**: `𝔇_c = |c_A|²·E(λ − 1)² + n·E(σ − σ_p)²`. -/
theorem Dc_eq (hn : 1 ≤ n) (hb : cenB bh W A ≠ 0) :
    Dc bh W A = normSq (cAv bh W A) * ∫ ξ, (lamX bh W A ξ - 1) ^ 2 ∂stdGauss (Fin n) +
      n * ∫ ξ, (sigX bh W A ξ - sigP bh W A) ^ 2 ∂stdGauss (Fin n) := by
  have hXY := XY_int bh W A hn hb
  unfold Dc
  rw [integral_prod _ hXY]
  have e : ∀ ξ : Fin n → ℝ, ∫ γ, normSq (Xm bh W A (ξ, γ) - Ym bh W A (ξ, γ))
      ∂stdGauss (Fin n) = (lamX bh W A ξ - 1) ^ 2 * normSq (cAv bh W A) +
        n * (sigX bh W A ξ - sigP bh W A) ^ 2 := by
    intro ξ
    have e1 : ∀ γ : Fin n → ℝ, Xm bh W A (ξ, γ) - Ym bh W A (ξ, γ) =
        (lamX bh W A ξ - 1) • cAv bh W A + (sigX bh W A ξ - sigP bh W A) • γ := by
      intro γ
      unfold Xm Ym
      simp only [sub_smul, one_smul]
      abel
    simp_rw [e1]
    rw [shift_second, normSq_smul]
  simp_rw [e]
  -- integrability of the two bounded functions
  have i1 : Integrable (fun ξ => (lamX bh W A ξ - 1) ^ 2) (stdGauss (Fin n)) := by
    refine Integrable.of_bound
      (((measurable_lamX bh W A).sub measurable_const).pow_const 2).aestronglyMeasurable
      (2 * (frob A.2.1 * frob A.1 / normSq (cenB bh W A)) + 2)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := lamX_sq_le bh W A hn hb ξ
    nlinarith [sq_nonneg (lamX bh W A ξ + 1)]
  have i2 : Integrable (fun ξ => (sigX bh W A ξ - sigP bh W A) ^ 2) (stdGauss (Fin n)) := by
    refine Integrable.of_bound
      (((measurable_sigX bh W A).sub measurable_const).pow_const 2).aestronglyMeasurable
      (2 * (2 / (mA n : ℝ) * (frob A.2.1 * frob A.1)) + 2 * sigP bh W A ^ 2)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := sigX_sq_le bh W A hn hb ξ
    nlinarith [sq_nonneg (sigX bh W A ξ + sigP bh W A)]
  rw [integral_add (i1.mul_const _) (i2.const_mul _), integral_mul_const, integral_const_mul]
  ring

lemma mF_pos (hn : 1 ≤ n) : 1 ≤ mF n := by
  unfold mF
  have h : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  exact Nat.ceil_pos.mpr h

/-- **Equation (Tm) with its charge**: for `δ, δ′ > 0`:
`Pr_{F₁,F₂}(t_F|Δ_m|² > (1 + δ)(1 + δ′)·(2/n)·𝔇_c) ≤ (432/m_F²)(1 + 63/m_F)(1/δ⁴ + 1/δ′⁴)`. -/
theorem lemmaTm (hn : 1 ≤ n) (hb : cenB bh W A ≠ 0) {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') :
    (hidGauss n (mF n)).real
        {θF | (1 + δ) * (1 + δ') * (2 / (n : ℝ) * Dc bh W A) <
          2 / (mF n : ℝ) * normSq (dM bh W A θF)} ≤
      432 / (mF n : ℝ) ^ 2 * (1 + 63 / (mF n)) * (1 / δ ^ 4 + 1 / δ' ^ 4) :=
  lemmaTR (P2 n) hn (mF_pos hn) (measurable_Xm bh W A) (measurable_Ym bh W A)
    (XY_int bh W A hn hb) hδ hδ'

end conc

end BstLean.Part151
