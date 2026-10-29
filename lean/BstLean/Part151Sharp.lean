import BstLean.Part152GC
import BstLean.Part151U3
import BstLean.Part151SA

/-!
# Part 151: the concentration events of Lemma SA and Lemma U with the SHARP constant of (G1)

Role: `delegations/statements/p151-spec.md`, item 4 ("sharper constants"). `Part151SA`, `Part151U2`,
`Part151U3` use the Gaussian concentration of Part 148 (constant `π²/4`). Part 152
(`gaussConc_mat_upper_sharp`) has the sharp constant of the fact (G1) of the document. This file
restates the events with the charge `exp(−u²/(2ℓ²))`, and in the paper's form: with
`u = √(2L_c)·ℓ` the charge is `exp(−L_c)`.

NOTE: this file imports a file of Part 152 (`Part152GC`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (nrm nrm_sq nrm_nonneg)
open BstLean.Part133 (sq_integral_le)
open BstLean.Part134 (lam res sig measurable_lam measurable_sig measurable_res normSq_ne_zero
  cDist eDir measurable_mulVec_joint projPerp glue glue_res s1_disint measurable_glue
  measurable_mul_right res_self)
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint)
open BstLean.Part139 (gamK)
open BstLean.Part152 (gaussConc_mat_upper_sharp)
open BstLean.Part149 (thA tauOutOf outTrue outStand normSq_res_le lam_sq_le)
open BstLean.Part150 (CMap)

/-- `exp(−(√(2L)·ℓ)²/(2ℓ²)) = exp(−L)` for `ℓ > 0`, `L ≥ 0`. -/
lemma exp_paper {Lc ell : ℝ} (hL : 0 ≤ Lc) (hl : 0 < ell) :
    Real.exp (-(√(2 * Lc) * ell) ^ 2 / (2 * ell ^ 2)) = Real.exp (-Lc) := by
  congr 1
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-! ## The sampling term -/

section SA

variable {n m : ℕ}

/-- **Lemma SA, concentration, sharp constant**:
`Pr_η(T_s ≥ E_η T_s + u) ≤ exp(−u²/(2ℓ_s²))`, `ℓ_s = √(t_F)·L·|σ|/√k`. -/
theorem lemmaSA_conc_sharp (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ y y', normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ L ^ 2 * normSq (y - y'))
    {u : ℝ} (hu : 0 ≤ u) :
    (gamK k n).real {η | ∫ η, Ts θ c σ k η ∂gamK k n + u ≤ Ts θ c σ k η} ≤
      Real.exp (-u ^ 2 / (2 * (√(2 / (m : ℝ)) * L * |σ| / √(k : ℝ)) ^ 2)) := by
  have hℓ0 : 0 ≤ √(2 / (m : ℝ)) * L * |σ| / √(k : ℝ) := by positivity
  have h := gaussConc_mat_upper_sharp (m := k) (k := n)
    (g := fun M : Matrix (Fin k) (Fin n) ℝ => Ts θ c σ k M) hℓ0
    (fun M M' => lemmaSA_lip θ c σ hk hL0 hL M M') (v := 1) (by norm_num) hu
  rw [one_mul, ← gamK_eq_gaussMat] at h
  exact h

/-- **Lemma SA, concentration around the root of the second moment, sharp constant.** -/
theorem lemmaSA_conc'_sharp (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ y y', normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ L ^ 2 * normSq (y - y'))
    {u : ℝ} (hu : 0 ≤ u) :
    (gamK k n).real {η | √(2 / (m : ℝ) *
        ((∫ γ, normSq (zS θ c σ γ) ∂stdGauss (Fin n)) / k)) + u ≤ Ts θ c σ k η} ≤
      Real.exp (-u ^ 2 / (2 * (√(2 / (m : ℝ)) * L * |σ| / √(k : ℝ)) ^ 2)) := by
  refine le_trans (measureReal_mono ?_) (lemmaSA_conc_sharp θ c σ hk hL0 hL hu)
  intro η hη
  simp only [mem_ofPred_eq] at hη ⊢
  have := Ts_mean_le θ c σ hk
  linarith

/-- **The event `E_s` of the document**: with `ℓ_s = √(t_F)·L·|σ|/√k > 0` and `L_c ≥ 0`:
`Pr_η(T_s ≥ E_η T_s + √(2L_c)·ℓ_s) ≤ exp(−L_c)`. -/
theorem lemmaSA_Es (θ : HidParam n m) (c : Fin n → ℝ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ y y', normSq (hid2 θ.1 θ.2 y - hid2 θ.1 θ.2 y') ≤ L ^ 2 * normSq (y - y'))
    (hl : 0 < √(2 / (m : ℝ)) * L * |σ| / √(k : ℝ)) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gamK k n).real {η | ∫ η, Ts θ c σ k η ∂gamK k n +
        √(2 * Lc) * (√(2 / (m : ℝ)) * L * |σ| / √(k : ℝ)) ≤ Ts θ c σ k η} ≤ Real.exp (-Lc) := by
  have h := lemmaSA_conc_sharp θ c σ hk hL0 hL
    (u := √(2 * Lc) * (√(2 / (m : ℝ)) * L * |σ| / √(k : ℝ))) (by positivity)
  rwa [exp_paper hLc hl] at h

end SA

/-! ## The conditional tool -/

section cond

variable {n m : ℕ}

/-- **Conditional Gaussian concentration given `c = M b`, sharp constant.** -/
theorem condConc_sharp {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0)
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin m) ℝ → ℝ}
    (hg : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ => g p.1 p.2)) {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ (c : Fin n → ℝ) (M M' : Matrix (Fin n) (Fin m) ℝ),
      |g c (glue b c (M * projPerp b)) - g c (glue b c (M' * projPerp b))| ≤
        K * √(∑ i, ∑ j, (M i j - M' i j) ^ 2)) {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n m v).real
        {M | (∫ M', g (M.mulVec b) (glue b (M.mulVec b) (M' * projPerp b)) ∂gaussMat n m v) + u ≤
          g (M.mulVec b) M} ≤
      Real.exp (-u ^ 2 / (2 * (v * K ^ 2))) := by
  have hΦ : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) :=
    measurable_fst.prodMk ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  have hG : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      g p.1 (glue b p.1 (p.2 * projPerp b))) := hg.comp hΦ
  set mg : (Fin n → ℝ) → ℝ := fun c =>
    ∫ M', g c (glue b c (M' * projPerp b)) ∂gaussMat n m v with hmg
  have hmgm : Measurable mg :=
    (StronglyMeasurable.integral_prod_right'
      (f := fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
        g p.1 (glue b p.1 (p.2 * projPerp b))) hG.stronglyMeasurable).measurable
  set S : Set ((Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ) := {p | mg p.1 + u ≤ g p.1 p.2} with hS
  have mS : MeasurableSet S :=
    measurableSet_le ((hmgm.comp measurable_fst).add measurable_const) hg
  have hm1 : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) :=
    (measurable_mulVec_right b).prodMk measurable_id
  have e0 : {M : Matrix (Fin n) (Fin m) ℝ |
      (∫ M', g (M.mulVec b) (glue b (M.mulVec b) (M' * projPerp b)) ∂gaussMat n m v) + u ≤
        g (M.mulVec b) M} = (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) ⁻¹' S := rfl
  set E : ℝ := Real.exp (-u ^ 2 / (2 * (v * K ^ 2))) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hle : (gaussMat n m v) ((fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) ⁻¹' S) ≤
      ENNReal.ofReal E := by
    rw [← Measure.map_apply hm1 mS, s1_disint v hb, Measure.map_apply hΦ mS,
      Measure.prod_apply (hΦ mS)]
    calc ∫⁻ c, (gaussMat n m v) (Prod.mk c ⁻¹'
          ((fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
            (p.1, glue b p.1 (p.2 * projPerp b))) ⁻¹' S)) ∂cDist n v b
        ≤ ∫⁻ _c, ENNReal.ofReal E ∂cDist n v b := by
          refine lintegral_mono fun c => ?_
          have h := gaussConc_mat_upper_sharp (g := fun M' => g c (glue b c (M' * projPerp b)))
            hK0 (hK c) hv hu
          rw [measureReal_def] at h
          exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hE0).mpr h
      _ = ENNReal.ofReal E := by simp
  rw [e0, measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hE0 hle

end cond

/-! ## Lemma U (iii) -/

section U

variable {n : ℕ} (bh : CMap n) (W : MlpParam (2 * n) (mW n) n)
  (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

lemma exp_arg_sharp (n : ℕ) (hn : 1 ≤ n) (LF Mr u : ℝ) :
    Real.exp (-u ^ 2 / (2 *
        (2 / (mA n : ℝ) * (ellU n LF Mr / √(2 / (mA n : ℝ))) ^ 2))) =
      Real.exp (-u ^ 2 / (2 * ellU n LF Mr ^ 2)) := by
  have hmA : 0 < (mA n : ℝ) := by
    have : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have htA : 0 < 2 / (mA n : ℝ) := by positivity
  congr 3
  rw [div_pow, Real.sq_sqrt htA.le]
  field_simp

/-- **Lemma U (iii), the event `E_U`, sharp constant.** -/
theorem lemmaU_EU_sharp (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | (∫ M', TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) (A₃.mulVec (bh (W, (A₁, A₂))))
            (M' * projPerp (bh (W, (A₁, A₂))))) ∂gaussMat n (mA n) (2 / (mA n : ℝ))) + u ≤
          TU bh W A₁ A₂ θF A₃} ≤
      Real.exp (-u ^ 2 / (2 * ellU n LF Mr ^ 2)) := by
  have h := condConc_sharp (n := n) (m := mA n) (v := 2 / (mA n : ℝ)) (by positivity) hb
    (g := fun _ A₃ => TU bh W A₁ A₂ θF A₃)
    ((measurable_TU bh W A₁ A₂ hn hb θF).comp measurable_snd)
    (K := ellU n LF Mr / √(2 / (mA n : ℝ))) (by unfold ellU; positivity)
    (fun c M M' => TU_glue_lip bh W A₁ A₂ hn hb θF hMr0 hLF hMr c M M') hu
  rw [exp_arg_sharp n hn] at h
  exact h

/-- The event `E_×` with the conditional mean subtracted, sharp constant. -/
theorem lemmaU_Ecross_sub_sharp (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    {w : (Fin n → ℝ) → Fin (mF n) → ℝ} (hw : Measurable w) (hw1 : ∀ c, normSq (w c) ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | (∫ M', -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
            dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) (A₃.mulVec (bh (W, (A₁, A₂))))
              (M' * projPerp (bh (W, (A₁, A₂))))) θF i)
            ∂gaussMat n (mA n) (2 / (mA n : ℝ))) + u ≤
          -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
            dU bh W (A₁, A₂, A₃) θF i)} ≤
      Real.exp (-u ^ 2 / (2 * ellU n LF Mr ^ 2)) := by
  have hK0 : 0 ≤ ellU n LF Mr / √(2 / (mA n : ℝ)) := by unfold ellU; positivity
  have hgm : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin (mA n)) ℝ =>
      -(√(2 / (mF n : ℝ)) * ∑ i, w p.1 i * dU bh W (A₁, A₂, p.2) θF i)) := by
    refine (measurable_const.mul (Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_)).neg
    · exact (measurable_pi_apply i).comp (hw.comp measurable_fst)
    · exact (measurable_dU_A3 bh W A₁ A₂ hn hb θF i).comp measurable_snd
  have h := condConc_sharp (n := n) (m := mA n) (v := 2 / (mA n : ℝ)) (by positivity) hb
    (g := fun c A₃ => -(√(2 / (mF n : ℝ)) * ∑ i, w c i * dU bh W (A₁, A₂, A₃) θF i))
    hgm (K := ellU n LF Mr / √(2 / (mA n : ℝ))) hK0
    (fun c M M' => by
      have h1 := cross_glue_lip bh W A₁ A₂ hn hb θF hMr0 hLF hMr c M M' (w c)
      have hsw : √(normSq (w c)) ≤ 1 := by
        have h2 := Real.sqrt_le_sqrt (hw1 c)
        rwa [Real.sqrt_one] at h2
      have e : -(√(2 / (mF n : ℝ)) * ∑ i, w c i *
            dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M * projPerp (bh (W, (A₁, A₂))))) θF i) -
          -(√(2 / (mF n : ℝ)) * ∑ i, w c i *
            dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF i) =
          -(√(2 / (mF n : ℝ)) * ∑ i, w c i *
            (dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M * projPerp (bh (W, (A₁, A₂))))) θF i -
              dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂)))))
                θF i)) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      rw [e, abs_neg]
      refine h1.trans ?_
      have hs0 := Real.sqrt_nonneg (∑ i, ∑ j, (M i j - M' i j) ^ 2)
      have : √(normSq (w c)) * (ellU n LF Mr / √(2 / (mA n : ℝ))) ≤
          1 * (ellU n LF Mr / √(2 / (mA n : ℝ))) := mul_le_mul_of_nonneg_right hsw hK0
      rw [one_mul] at this
      exact mul_le_mul_of_nonneg_right this hs0) hu
  rw [exp_arg_sharp n hn] at h
  exact h

/-- **Lemma U (iii), the event `E_×`, sharp constant.** -/
theorem lemmaU_Ecross_sharp (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    {w : (Fin n → ℝ) → Fin (mF n) → ℝ} (hw : Measurable w) (hw1 : ∀ c, normSq (w c) ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | u ≤ -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
            dU bh W (A₁, A₂, A₃) θF i)} ≤
      Real.exp (-u ^ 2 / (2 * ellU n LF Mr ^ 2)) := by
  have h := lemmaU_Ecross_sub_sharp bh W A₁ A₂ hn hb θF hMr0 hLF hMr hw hw1 hu
  have hz : ∀ c : Fin n → ℝ, ∫ M', -(√(2 / (mF n : ℝ)) * ∑ i, w c i *
      dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF i)
      ∂gaussMat n (mA n) (2 / (mA n : ℝ)) = 0 := by
    intro c
    rw [integral_neg, integral_const_mul, integral_finsetSum _ fun i _ =>
      ((dU_condMean bh W A₁ A₂ hn hb θF i c).1).const_mul _]
    simp_rw [integral_const_mul, (dU_condMean bh W A₁ A₂ hn hb θF _ c).2]
    simp
  simp_rw [hz, zero_add] at h
  exact h

/-- **Lemma U (iii), the two events together, sharp constant.** -/
theorem lemmaU_events_sharp (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    {w : (Fin n → ℝ) → Fin (mF n) → ℝ} (hw : Measurable w) (hw1 : ∀ c, normSq (w c) ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | ¬ (TU bh W A₁ A₂ θF A₃ <
              √(TUsqCond bh W A₁ A₂ θF (A₃.mulVec (bh (W, (A₁, A₂))))) + u ∧
            -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
              dU bh W (A₁, A₂, A₃) θF i) < u)} ≤
      2 * Real.exp (-u ^ 2 / (2 * ellU n LF Mr ^ 2)) := by
  have h1 := lemmaU_EU_sharp bh W A₁ A₂ hn hb θF hMr0 hLF hMr hu
  have h2 := lemmaU_Ecross_sharp bh W A₁ A₂ hn hb θF hMr0 hLF hMr hw hw1 hu
  set S1 : Set (Matrix (Fin n) (Fin (mA n)) ℝ) := {A₃ |
    (∫ M', TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) (A₃.mulVec (bh (W, (A₁, A₂))))
      (M' * projPerp (bh (W, (A₁, A₂))))) ∂gaussMat n (mA n) (2 / (mA n : ℝ))) + u ≤
      TU bh W A₁ A₂ θF A₃} with hS1
  set S2 : Set (Matrix (Fin n) (Fin (mA n)) ℝ) := {A₃ |
    u ≤ -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
      dU bh W (A₁, A₂, A₃) θF i)} with hS2
  have hun := measureReal_union_le (μ := gaussMat n (mA n) (2 / (mA n : ℝ))) S1 S2
  refine (measureReal_mono (s₂ := S1 ∪ S2) ?_ (measure_ne_top _ _)).trans (by linarith)
  intro A₃ hA
  simp only [mem_ofPred_eq, not_and_or, not_lt] at hA
  rcases hA with h | h
  · refine Or.inl ?_
    have := TU_condMean_le bh W A₁ A₂ hn hb θF (A₃.mulVec (bh (W, (A₁, A₂))))
    show _ + u ≤ _
    linarith
  · exact Or.inr h

/-- **The event `E_U` of the document**: for `ℓ_U > 0`, `L_c ≥ 0`:
`Pr(T_U ≥ E[T_U | c_A] + √(2L_c)·ℓ_U) ≤ exp(−L_c)`. -/
theorem lemmaU_EUc (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2) (hl : 0 < ellU n LF Mr) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | (∫ M', TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) (A₃.mulVec (bh (W, (A₁, A₂))))
            (M' * projPerp (bh (W, (A₁, A₂))))) ∂gaussMat n (mA n) (2 / (mA n : ℝ))) +
            √(2 * Lc) * ellU n LF Mr ≤ TU bh W A₁ A₂ θF A₃} ≤ Real.exp (-Lc) := by
  have h := lemmaU_EU_sharp bh W A₁ A₂ hn hb θF hMr0 hLF hMr
    (u := √(2 * Lc) * ellU n LF Mr) (by positivity)
  rwa [exp_paper hLc hl] at h

/-- **The event `E_×` of the document**: for `ℓ_U > 0`, `L_c ≥ 0`:
`Pr(X_× ≥ √(2L_c)·ℓ_U) ≤ exp(−L_c)`, `X_× = −√t_F·⟨w_×, Δ_U⟩`. -/
theorem lemmaU_Ecrossc (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    {w : (Fin n → ℝ) → Fin (mF n) → ℝ} (hw : Measurable w) (hw1 : ∀ c, normSq (w c) ≤ 1)
    (hl : 0 < ellU n LF Mr) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | √(2 * Lc) * ellU n LF Mr ≤
          -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
            dU bh W (A₁, A₂, A₃) θF i)} ≤ Real.exp (-Lc) := by
  have h := lemmaU_Ecross_sharp bh W A₁ A₂ hn hb θF hMr0 hLF hMr hw hw1
    (u := √(2 * Lc) * ellU n LF Mr) (by positivity)
  rwa [exp_paper hLc hl] at h

end U

end BstLean.Part151
