import BstLean.Part160MFAll

/-!
# Part 160 (file `MFB1`): tools for change (B) (the improved mean of `‖H‖²_HS`)

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-05-centre.tex`, Lemma `t7:p05:HS`.

The first part of this file is a COPY of the auxiliary section of `Part154L1c.lean` (its lemmas
are private there): the row distribution, the factor `p = Φ(⟨a, c⟩/(τ|a|))` (`pR`), the
reflection, the second pair mean, the covariance `rowC` of two rows. New:

* `PhiG_tail_prod`: `Φ(t)(1 − Φ(t)) ≥ (π/2)φ(t)² = e^{−t²}/4`. (The paper uses the sharper
  `(2Φ(t) − 1)² ≤ 1 − e^{−2t²/π}`; the exponent here is `t²` in the place of `2t²/π`.)
* `keyK`: for a fixed vector `b`: `E_a[⟨b, a⟩² p(1 − p)] ≥
  (1/4)(2/n)·[(|b|² − ⟨b, ĉ⟩²)·J − √3·e^{−6}·|b|²]`, `J = (1 + 2|c|²/(τ²S₀))^{−1/2}`,
  for every `0 < S₀ ≤ n − 2√(12n)`.
-/

namespace BstLean.Part160.MFB

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part154 BstLean.Part160
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

section aux

open BstLean.Part153 (dt sP wE sum_sub_sq sP_nonneg measurable_wE wE_moment_le invBd exists_unit
  integrable_of_bdd wE_pos wE_le rowLaw rowLaw_four rowV rowV_nonneg rowV_le vS nrm_nonneg nrm_sq
  psiS_one psiS_neg hasDerivAt_psiG hasDerivAt_PhiG PhiG_pos PhiG_le_one)
open BstLean.Part131 (stdGauss_decomp projMat projMat_mulVec projMat_dot)
open BstLean.Part29 (gaussMom gaussMom_eq)

/-! ## The kernel `E[(z·u)⁴/|z|²]` -/

lemma kernel_ptw {x s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) :
    x ^ 4 / (x ^ 2 + s) ≤ x ^ 4 * (s + ε)⁻¹ + ε := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hx4 : 0 ≤ x ^ 4 := by positivity
  have hpos : 0 < s + ε := by linarith
  rcases le_or_gt ε (x ^ 2) with h | h
  · have h1 : x ^ 4 / (x ^ 2 + s) ≤ x ^ 4 / (s + ε) :=
      div_le_div_of_nonneg_left hx4 hpos (by linarith)
    rw [← div_eq_mul_inv]
    linarith
  · have h1 : x ^ 4 / (x ^ 2 + s) ≤ x ^ 2 := by
      rcases eq_or_lt_of_le (add_nonneg hx2 hs) with h0 | h0
      · rw [← h0, div_zero]; exact hx2
      · rw [div_le_iff₀ h0]
        nlinarith [mul_nonneg hx2 hs]
    have h2 : 0 ≤ x ^ 4 * (s + ε)⁻¹ := mul_nonneg hx4 (inv_nonneg.2 hpos.le)
    linarith

lemma meas_dot_L1c {n : ℕ} (b : Fin n → ℝ) : Measurable (fun a : Fin n → ℝ => a ⬝ᵥ b) := by
  unfold dotProduct; fun_prop

lemma meas_dot'_L1c {n : ℕ} (b : Fin n → ℝ) :
    Measurable (fun a : Fin n → ℝ => b ⬝ᵥ a) := by
  unfold dotProduct; fun_prop

lemma gaussMom_four : gaussMom 4 = 3 := by
  have : Even 4 := by decide
  simp [gaussMom, this, Nat.doubleFactorial]

lemma gaussMom_two : gaussMom 2 = 1 := by
  simp [gaussMom, Nat.doubleFactorial]

lemma kernel_unit {m : ℕ} (hm : 2 < m) {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) :
    Integrable (fun z : Fin (m + 1) → ℝ => (z ⬝ᵥ u) ^ 4 / normSq z) (stdGauss (Fin (m + 1))) ∧
    ∫ z, (z ⬝ᵥ u) ^ 4 / normSq z ∂stdGauss (Fin (m + 1)) ≤ 3 / ((m : ℝ) - 2) := by
  have he : u ⬝ᵥ u = 1 := by
    simp only [dotProduct]
    rw [← hu]
    exact Finset.sum_congr rfl fun i _ => (sq (u i)).symm
  have hφm : Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) => p.1 • u + projMat u *ᵥ p.2) := by
    have e : (fun p : ℝ × (Fin (m + 1) → ℝ) => p.1 • u + projMat u *ᵥ p.2) =
        fun p => p.1 • u + (p.2 - (u ⬝ᵥ p.2) • u) := by
      funext p; rw [projMat_mulVec]
    rw [e]
    exact (measurable_fst.smul_const u).add
      (measurable_snd.sub (((meas_dot'_L1c u).comp measurable_snd).smul_const u))
  have hT : Measurable (fun z : Fin (m + 1) → ℝ => (z ⬝ᵥ u) ^ 4 / normSq z) :=
    ((meas_dot_L1c u).pow_const 4).div continuous_normSq.measurable
  have hcomp : ∀ p : ℝ × (Fin (m + 1) → ℝ),
      ((p.1 • u + projMat u *ᵥ p.2) ⬝ᵥ u) ^ 4 / normSq (p.1 • u + projMat u *ᵥ p.2) =
        p.1 ^ 4 / (p.1 ^ 2 + sP u p.2) := by
    rintro ⟨x, h⟩
    have e1 : (x • u + projMat u *ᵥ h) ⬝ᵥ u = x := by
      rw [add_dotProduct, smul_dotProduct, he, projMat_dot he]
      simp
    have e2 : normSq (x • u + projMat u *ᵥ h) = x ^ 2 + sP u h := by
      have e : normSq (x • u + projMat u *ᵥ h) = ∑ i, (h i - (dt u h - x) * u i) ^ 2 := by
        unfold normSq
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [projMat_mulVec]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        have : u ⬝ᵥ h = dt u h := rfl
        rw [this]
        ring
      rw [e, sum_sub_sq, hu]
      unfold sP
      ring
    simp only [e1, e2]
  have hdec := stdGauss_decomp he
  have hSle : ∀ p : ℝ × (Fin (m + 1) → ℝ), p.1 ^ 4 / (p.1 ^ 2 + sP u p.2) ≤ p.1 ^ 2 := by
    intro p
    have hx2 : 0 ≤ p.1 ^ 2 := sq_nonneg _
    have hs := sP_nonneg hu p.2
    rcases eq_or_lt_of_le (add_nonneg hx2 hs) with h0 | h0
    · rw [← h0, div_zero]; exact hx2
    · rw [div_le_iff₀ h0]
      nlinarith [mul_nonneg hx2 hs]
  have hS0 : ∀ p : ℝ × (Fin (m + 1) → ℝ), 0 ≤ p.1 ^ 4 / (p.1 ^ 2 + sP u p.2) := fun p =>
    div_nonneg (by positivity) (add_nonneg (sq_nonneg _) (sP_nonneg hu p.2))
  have hSm : Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) => p.1 ^ 4 / (p.1 ^ 2 + sP u p.2)) :=
    (measurable_fst.pow_const 4).div
      ((measurable_fst.pow_const 2).add ((BstLean.Part153.measurable_sP u).comp measurable_snd))
  have ix2 : Integrable (fun p : ℝ × (Fin (m + 1) → ℝ) => p.1 ^ 2 * (1 : ℝ))
      ((gaussianReal 0 1).prod (stdGauss (Fin (m + 1)))) :=
    (integrable_pow_gauss 2).mul_prod (integrable_const (1 : ℝ))
  have iS : Integrable (fun p : ℝ × (Fin (m + 1) → ℝ) => p.1 ^ 4 / (p.1 ^ 2 + sP u p.2))
      ((gaussianReal 0 1).prod (stdGauss (Fin (m + 1)))) := by
    refine Integrable.mono' ix2 hSm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 p), mul_one]
    exact hSle p
  have iT : Integrable (fun z : Fin (m + 1) → ℝ => (z ⬝ᵥ u) ^ 4 / normSq z)
      (((gaussianReal 0 1).prod (stdGauss (Fin (m + 1)))).map
        (fun p => p.1 • u + projMat u *ᵥ p.2)) :=
    (integrable_map_measure hT.aestronglyMeasurable hφm.aemeasurable).mpr
      (iS.congr (ae_of_all _ fun p => (hcomp p).symm))
  rw [hdec] at iT
  refine ⟨iT, ?_⟩
  have eT : ∫ z, (z ⬝ᵥ u) ^ 4 / normSq z ∂stdGauss (Fin (m + 1)) =
      ∫ p : ℝ × (Fin (m + 1) → ℝ), p.1 ^ 4 / (p.1 ^ 2 + sP u p.2)
        ∂((gaussianReal 0 1).prod (stdGauss (Fin (m + 1)))) := by
    have h := integral_map (μ := (gaussianReal 0 1).prod (stdGauss (Fin (m + 1))))
      hφm.aemeasurable hT.aestronglyMeasurable
    rw [hdec] at h
    rw [h]
    exact integral_congr_ae (ae_of_all _ hcomp)
  rw [eT]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have iW : Integrable (wE u ε) (stdGauss (Fin (m + 1))) :=
    integrable_of_bdd (measurable_wE u ε) (C := ε⁻¹) fun ζ => by
      rw [abs_of_pos (wE_pos hu hε ζ)]; exact wE_le hu hε ζ
  have iB : Integrable (fun p : ℝ × (Fin (m + 1) → ℝ) => p.1 ^ 4 * wE u ε p.2)
      ((gaussianReal 0 1).prod (stdGauss (Fin (m + 1)))) :=
    (integrable_pow_gauss 4).mul_prod iW
  have h1 : ∫ p : ℝ × (Fin (m + 1) → ℝ), p.1 ^ 4 / (p.1 ^ 2 + sP u p.2)
        ∂((gaussianReal 0 1).prod (stdGauss (Fin (m + 1)))) ≤
      ∫ p : ℝ × (Fin (m + 1) → ℝ), (p.1 ^ 4 * wE u ε p.2 + ε)
        ∂((gaussianReal 0 1).prod (stdGauss (Fin (m + 1)))) :=
    integral_mono iS (iB.add (integrable_const ε)) fun p => kernel_ptw (sP_nonneg hu p.2) hε
  rw [integral_add iB (integrable_const ε),
    integral_prod_mul (fun x : ℝ => x ^ 4) (wE u ε), gaussMom_eq, gaussMom_four] at h1
  have h2 := wE_moment_le hu hε 1 (by omega)
  simp only [pow_one, invBd, Finset.prod_range_one, Nat.cast_zero, zero_add, mul_one] at h2
  have hm2 : (0 : ℝ) < (m : ℝ) - 2 := by
    have : (2 : ℝ) < m := by exact_mod_cast hm
    linarith
  have h3 : 3 * ∫ ζ, wE u ε ζ ∂stdGauss (Fin (m + 1)) ≤ 3 / ((m : ℝ) - 2) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  linarith

lemma kernel_vec {n : ℕ} (hn : 4 ≤ n) (v : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => (z ⬝ᵥ v) ^ 4 / normSq z) (stdGauss (Fin n)) ∧
    ∫ z, (z ⬝ᵥ v) ^ 4 / normSq z ∂stdGauss (Fin n) ≤ 3 / ((n : ℝ) - 3) * normSq v ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨u, a, hu, rfl⟩ := exists_unit v
  obtain ⟨hi, hb⟩ := kernel_unit (by omega) hu
  have e : ∀ z : Fin (m + 1) → ℝ, (z ⬝ᵥ (a • u)) ^ 4 / normSq z =
      a ^ 4 * ((z ⬝ᵥ u) ^ 4 / normSq z) := by
    intro z
    rw [dotProduct_smul, smul_eq_mul]
    ring
  simp_rw [e]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, normSq_smul]
  have h1 : normSq u = 1 := hu
  have h2 : ((m + 1 : ℕ) : ℝ) - 3 = (m : ℝ) - 2 := by push_cast; ring
  rw [h1, h2]
  calc a ^ 4 * ∫ z, (z ⬝ᵥ u) ^ 4 / normSq z ∂stdGauss (Fin (m + 1))
      ≤ a ^ 4 * (3 / ((m : ℝ) - 2)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 3 / ((m : ℝ) - 2) * (a ^ 2 * 1) ^ 2 := by ring

/-! ## The distribution of one row -/

lemma rl_sm (n : ℕ) : Measurable (fun ξ : Fin n → ℝ => √(2 / (n : ℝ)) • ξ) :=
  measurable_const_smul _

lemma rl_int {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    ∫ a, F a ∂rowLaw n = ∫ z, F (√(2 / (n : ℝ)) • z) ∂stdGauss (Fin n) := by
  unfold rowLaw
  exact integral_map (rl_sm n).aemeasurable hF.aestronglyMeasurable

lemma rl_itg {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    Integrable F (rowLaw n) ↔
      Integrable (fun z : Fin n → ℝ => F (√(2 / (n : ℝ)) • z)) (stdGauss (Fin n)) := by
  unfold rowLaw
  exact integrable_map_measure hF.aestronglyMeasurable (rl_sm n).aemeasurable

lemma rl_neg (n : ℕ) : (rowLaw n).map (fun a : Fin n → ℝ => -a) = rowLaw n := by
  unfold rowLaw
  rw [Measure.map_map measurable_neg (rl_sm n)]
  have e : (fun a : Fin n → ℝ => -a) ∘ (fun ξ : Fin n → ℝ => √(2 / (n : ℝ)) • ξ) =
      (fun ξ : Fin n → ℝ => √(2 / (n : ℝ)) • ξ) ∘ (fun z : Fin n → ℝ => -z) := by
    funext ξ; simp
  rw [e, ← Measure.map_map (rl_sm n) measurable_neg, BstLean.Part135.stdGauss_neg]

lemma rl_normSq {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun a : Fin n → ℝ => normSq a) (rowLaw n) ∧ ∫ a, normSq a ∂rowLaw n = 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i0, e0⟩ := BstLean.Part149.stdGauss_normSq n
  have hF : Measurable (fun a : Fin n → ℝ => normSq a) := continuous_normSq.measurable
  have e : ∀ z : Fin n → ℝ, normSq (√(2 / (n : ℝ)) • z) = 2 / (n : ℝ) * normSq z := by
    intro z; rw [normSq_smul, Real.sq_sqrt (by positivity)]
  constructor
  · refine (rl_itg hF).mpr ?_
    simp_rw [e]
    exact i0.const_mul _
  · rw [rl_int hF]
    simp_rw [e]
    rw [integral_const_mul, e0]
    field_simp

lemma rl_dot2 {n : ℕ} (hn : 1 ≤ n) (b : Fin n → ℝ) :
    Integrable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2) (rowLaw n) ∧
    ∫ a, (b ⬝ᵥ a) ^ 2 ∂rowLaw n = 2 / (n : ℝ) * normSq b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hF : Measurable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2) := (meas_dot'_L1c b).pow_const 2
  have e : ∀ z : Fin n → ℝ, (b ⬝ᵥ (√(2 / (n : ℝ)) • z)) ^ 2 = 2 / (n : ℝ) * (z ⬝ᵥ b) ^ 2 := by
    intro z
    rw [dotProduct_smul, smul_eq_mul, mul_pow, Real.sq_sqrt (by positivity), dotProduct_comm]
  have msq : Measurable (fun t : ℝ => t ^ 2) := measurable_id.pow_const 2
  have i1 : Integrable (fun z : Fin n → ℝ => (z ⬝ᵥ b) ^ 2) (stdGauss (Fin n)) := by
    refine gauss_lin_integrable b msq ?_
    simp_rw [mul_pow]
    exact (integrable_pow_gauss 2).const_mul _
  have e1 : ∫ z : Fin n → ℝ, (z ⬝ᵥ b) ^ 2 ∂stdGauss (Fin n) = normSq b := by
    have h := gauss_lin_integral b msq
    simp only [mul_pow] at h
    rw [integral_const_mul, gaussMom_eq, gaussMom_two, mul_one,
      Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] at h
    exact h
  constructor
  · refine (rl_itg hF).mpr ?_
    simp_rw [e]
    exact i1.const_mul _
  · rw [rl_int hF]
    simp_rw [e]
    rw [integral_const_mul, e1]

/-! ## The factor `p = Φ(μ/|g|)` and the reflection `a ↦ −a` -/

lemma PhiG_neg_L1c (v : ℝ) : PhiG (-v) = 1 - PhiG v := by
  have h1 : (fun x : ℝ => psiG (-x)) = fun x => psiG x - x := by
    funext x; rw [← psiS_one, ← psiS_one]; exact psiS_neg 1 x
  have d1 : HasDerivAt (fun x : ℝ => psiG (-x)) (PhiG (-v) * -1) v :=
    (hasDerivAt_psiG (-v)).comp v (hasDerivAt_neg v)
  have d2 : HasDerivAt (fun x : ℝ => psiG x - x) (PhiG v - 1) v :=
    (hasDerivAt_psiG v).sub (hasDerivAt_id v)
  rw [h1] at d1
  have := d1.unique d2
  linarith

lemma continuous_PhiG_L1c : Continuous PhiG :=
  continuous_iff_continuousAt.2 fun v => (hasDerivAt_PhiG v).continuousAt

/-- `p(a) = Φ(⟨a, c⟩/(τ|a|))`. -/
noncomputable def pR {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) : ℝ :=
  PhiG (a ⬝ᵥ c / nrm (τ • a))

lemma meas_nrm_smul {n : ℕ} (τ : ℝ) : Measurable (fun a : Fin n → ℝ => nrm (τ • a)) :=
  (continuous_normSq.measurable.comp (measurable_const_smul τ)).sqrt

lemma meas_pR {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Measurable (pR c τ) :=
  continuous_PhiG_L1c.measurable.comp ((meas_dot_L1c c).div (meas_nrm_smul τ))

lemma pR_nonneg {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) : 0 ≤ pR c τ a :=
  (PhiG_pos _).le

lemma pR_le_one {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) : pR c τ a ≤ 1 :=
  PhiG_le_one _

lemma pR_neg {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) :
    pR c τ (-a) = 1 - pR c τ a := by
  unfold pR
  have e1 : nrm (τ • -a) = nrm (τ • a) := by
    unfold nrm normSq; simp
  rw [neg_dotProduct, e1, neg_div, PhiG_neg_L1c]

/-- The reflection `a ↦ −a`: `E[G(a)p(a)²] ≤ ½·E G(a)` for `G ≥ 0` even. -/
lemma refl_le {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) {G : (Fin n → ℝ) → ℝ} (hG : Measurable G)
    (h0 : ∀ a, 0 ≤ G a) (hev : ∀ a, G (-a) = G a) (hi : Integrable G (rowLaw n)) :
    Integrable (fun a => G a * pR c τ a ^ 2) (rowLaw n) ∧
    ∫ a, G a * pR c τ a ^ 2 ∂rowLaw n ≤ 1 / 2 * ∫ a, G a ∂rowLaw n := by
  have hp := meas_pR c τ
  have hm : Measurable (fun a => G a * pR c τ a ^ 2) := hG.mul (hp.pow_const 2)
  have hm2 : Measurable (fun a => G a * (1 - pR c τ a) ^ 2) :=
    hG.mul ((measurable_const.sub hp).pow_const 2)
  have i1 : Integrable (fun a => G a * pR c τ a ^ 2) (rowLaw n) := by
    refine Integrable.mono' hi hm.aestronglyMeasurable (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 a) (sq_nonneg _))]
    exact mul_le_of_le_one_right (h0 a) (pow_le_one₀ (pR_nonneg c τ a) (pR_le_one c τ a))
  have i2 : Integrable (fun a => G a * (1 - pR c τ a) ^ 2) (rowLaw n) := by
    refine Integrable.mono' hi hm2.aestronglyMeasurable (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 a) (sq_nonneg _))]
    exact mul_le_of_le_one_right (h0 a)
      (pow_le_one₀ (sub_nonneg.2 (pR_le_one c τ a)) (by linarith [pR_nonneg c τ a]))
  refine ⟨i1, ?_⟩
  have e1 : ∫ a, G a * pR c τ a ^ 2 ∂rowLaw n = ∫ a, G a * (1 - pR c τ a) ^ 2 ∂rowLaw n := by
    have h := integral_map (μ := rowLaw n) (measurable_neg : Measurable (fun a : Fin n → ℝ => -a)).aemeasurable
      hm.aestronglyMeasurable
    rw [rl_neg] at h
    rw [h]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [hev, pR_neg]
  have h2 : ∫ a, (G a * pR c τ a ^ 2 + G a * (1 - pR c τ a) ^ 2) ∂rowLaw n ≤
      ∫ a, G a ∂rowLaw n := by
    refine integral_mono (i1.add i2) hi fun a => ?_
    have hp0 := pR_nonneg c τ a
    have hp1 := pR_le_one c τ a
    show G a * pR c τ a ^ 2 + G a * (1 - pR c τ a) ^ 2 ≤ G a
    nlinarith [mul_nonneg (h0 a) (mul_nonneg hp0 (sub_nonneg.2 hp1))]
  rw [integral_add i1 i2, ← e1] at h2
  linarith

/-! ## The first mean -/

lemma dot_sq_le_L1c {n : ℕ} (a a' : Fin n → ℝ) : (a ⬝ᵥ a') ^ 2 ≤ normSq a * normSq a' :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a a'

lemma meas_dot2_L1c {n : ℕ} :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 ⬝ᵥ q.2) := by
  unfold dotProduct; fun_prop

lemma itg_nn {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => normSq q.1 * normSq q.2)
      ((rowLaw n).prod (rowLaw n)) :=
  (rl_normSq hn).1.mul_prod (rl_normSq hn).1

lemma mean1 {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2) ((rowLaw n).prod (rowLaw n)) ∧
    ∫ q : (Fin n → ℝ) × (Fin n → ℝ), (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2
      ∂((rowLaw n).prod (rowLaw n)) ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2) :=
    ((meas_dot2_L1c.pow_const 2).mul (((meas_pR c τ).comp measurable_fst).pow_const 2)).mul
      (((meas_pR c τ).comp measurable_snd).pow_const 2)
  have h0 : ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
      0 ≤ (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2 := fun q => by positivity
  have hle : ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
      (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2 ≤ normSq q.1 * normSq q.2 := by
    intro q
    have h1 := dot_sq_le_L1c q.1 q.2
    have p1 : pR c τ q.1 ^ 2 ≤ 1 := pow_le_one₀ (pR_nonneg c τ _) (pR_le_one c τ _)
    have p2 : pR c τ q.2 ^ 2 ≤ 1 := pow_le_one₀ (pR_nonneg c τ _) (pR_le_one c τ _)
    have a1 : (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 ≤ (q.1 ⬝ᵥ q.2) ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg _) p1
    have a2 : (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2 ≤
        (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 :=
      mul_le_of_le_one_right (by positivity) p2
    linarith
  have hI : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2) ((rowLaw n).prod (rowLaw n)) := by
    refine Integrable.mono' (itg_nn hn) hm.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 q)]
    exact hle q
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  obtain ⟨iN, eN⟩ := rl_normSq hn
  obtain ⟨iR, hR⟩ := refl_le c τ (continuous_normSq.measurable) normSq_nonneg
    BstLean.Part135.normSq_neg iN
  rw [eN] at hR
  have inner : ∀ a : Fin n → ℝ,
      ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 ∂rowLaw n ≤
        1 / (n : ℝ) * (normSq a * pR c τ a ^ 2) := by
    intro a
    obtain ⟨iD, eD⟩ := rl_dot2 hn a
    obtain ⟨-, hD⟩ := refl_le c τ ((meas_dot'_L1c a).pow_const 2) (fun a' => sq_nonneg _)
      (fun a' => by rw [dotProduct_neg, neg_sq]) iD
    rw [eD] at hD
    have e : ∀ a' : Fin n → ℝ, (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 =
        pR c τ a ^ 2 * ((a ⬝ᵥ a') ^ 2 * pR c τ a' ^ 2) := fun a' => by ring
    simp_rw [e]
    rw [integral_const_mul]
    calc pR c τ a ^ 2 * ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a' ^ 2 ∂rowLaw n
        ≤ pR c τ a ^ 2 * (1 / 2 * (2 / (n : ℝ) * normSq a)) :=
          mul_le_mul_of_nonneg_left hD (sq_nonneg _)
      _ = 1 / (n : ℝ) * (normSq a * pR c τ a ^ 2) := by ring
  calc ∫ a, ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 ∂rowLaw n ∂rowLaw n
      ≤ ∫ a, 1 / (n : ℝ) * (normSq a * pR c τ a ^ 2) ∂rowLaw n :=
        integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun a' => h0 (a, a'))
          (iR.const_mul _) (ae_of_all _ inner)
    _ = 1 / (n : ℝ) * ∫ a, normSq a * pR c τ a ^ 2 ∂rowLaw n := integral_const_mul _ _
    _ ≤ 1 / (n : ℝ) * (1 / 2 * 2) := mul_le_mul_of_nonneg_left hR (by positivity)
    _ = 1 / (n : ℝ) := by ring

/-! ## The second mean -/

/-- `⟨a, a′⟩⁴/(|a|²|a′|²)`. -/
noncomputable def Qf {n : ℕ} (q : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (q.1 ⬝ᵥ q.2) ^ 4 / (normSq q.1 * normSq q.2)

lemma meas_Qf {n : ℕ} : Measurable (Qf (n := n)) :=
  (meas_dot2_L1c.pow_const 4).div ((continuous_normSq.measurable.comp measurable_fst).mul
    (continuous_normSq.measurable.comp measurable_snd))

lemma Qf_nonneg {n : ℕ} (q : (Fin n → ℝ) × (Fin n → ℝ)) : 0 ≤ Qf q :=
  div_nonneg (by positivity) (mul_nonneg (normSq_nonneg _) (normSq_nonneg _))

lemma Qf_le {n : ℕ} (q : (Fin n → ℝ) × (Fin n → ℝ)) : Qf q ≤ normSq q.1 * normSq q.2 := by
  have h1 := dot_sq_le_L1c q.1 q.2
  have hN := mul_nonneg (normSq_nonneg q.1) (normSq_nonneg q.2)
  unfold Qf
  rcases eq_or_lt_of_le hN with h0 | h0
  · rw [← h0, div_zero]
  · rw [div_le_iff₀ h0]
    have : (q.1 ⬝ᵥ q.2) ^ 4 = ((q.1 ⬝ᵥ q.2) ^ 2) ^ 2 := by ring
    rw [this, ← sq]
    exact pow_le_pow_left₀ (sq_nonneg _) h1 2

lemma mean2 {n : ℕ} (hn : 4 ≤ n) :
    Integrable (Qf (n := n)) ((rowLaw n).prod (rowLaw n)) ∧
    ∫ q, Qf q ∂((rowLaw n).prod (rowLaw n)) ≤ 12 / ((n : ℝ) * ((n : ℝ) - 3)) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hI : Integrable (Qf (n := n)) ((rowLaw n).prod (rowLaw n)) := by
    refine Integrable.mono' (itg_nn hn1) meas_Qf.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Qf_nonneg q)]
    exact Qf_le q
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  obtain ⟨iN, eN⟩ := rl_normSq hn1
  have inner : ∀ a : Fin n → ℝ,
      ∫ a', Qf (a, a') ∂rowLaw n ≤ 2 / (n : ℝ) * (3 / ((n : ℝ) - 3)) * normSq a := by
    intro a
    obtain ⟨iT, hT⟩ := kernel_vec hn a
    have hF : Measurable (fun a' : Fin n → ℝ => Qf (a, a')) :=
      meas_Qf.comp (measurable_const.prodMk measurable_id)
    rw [rl_int hF]
    have ht : (2 / (n : ℝ)) ≠ 0 := by positivity
    have e : ∀ z : Fin n → ℝ, Qf (a, √(2 / (n : ℝ)) • z) =
        2 / (n : ℝ) / normSq a * ((z ⬝ᵥ a) ^ 4 / normSq z) := by
      intro z
      unfold Qf
      simp only
      rw [dotProduct_smul, smul_eq_mul, normSq_smul, Real.sq_sqrt (by positivity),
        dotProduct_comm a z, div_mul_div_comm]
      have e4 : (√(2 / (n : ℝ)) * (z ⬝ᵥ a)) ^ 4 =
          2 / (n : ℝ) * (2 / (n : ℝ) * (z ⬝ᵥ a) ^ 4) := by
        have h4 : √(2 / (n : ℝ)) ^ 4 = 2 / (n : ℝ) * (2 / (n : ℝ)) := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
          ring
        rw [mul_pow, h4]
        ring
      rw [e4, show normSq a * (2 / (n : ℝ) * normSq z) = 2 / (n : ℝ) * (normSq a * normSq z) by
        ring, mul_div_mul_left _ _ ht]
    simp_rw [e]
    rw [integral_const_mul]
    rcases eq_or_lt_of_le (normSq_nonneg a) with h0 | h0
    · rw [← h0]; simp
    · calc 2 / (n : ℝ) / normSq a * ∫ z, (z ⬝ᵥ a) ^ 4 / normSq z ∂stdGauss (Fin n)
          ≤ 2 / (n : ℝ) / normSq a * (3 / ((n : ℝ) - 3) * normSq a ^ 2) :=
            mul_le_mul_of_nonneg_left hT (by positivity)
        _ = 2 / (n : ℝ) * (3 / ((n : ℝ) - 3)) * normSq a := by
            field_simp
  calc ∫ a, ∫ a', Qf (a, a') ∂rowLaw n ∂rowLaw n
      ≤ ∫ a, 2 / (n : ℝ) * (3 / ((n : ℝ) - 3)) * normSq a ∂rowLaw n :=
        integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun a' => Qf_nonneg _)
          (iN.const_mul _) (ae_of_all _ inner)
    _ = 2 / (n : ℝ) * (3 / ((n : ℝ) - 3)) * 2 := by rw [integral_const_mul, eN]
    _ = 12 / ((n : ℝ) * ((n : ℝ) - 3)) := by
        rw [div_mul_div_comm, div_mul_eq_mul_div]
        norm_num

/-! ## The covariance of two rows -/

/-- `C(a, a′) = Cov_ξ(relu⟨a, y⟩, relu⟨a′, y⟩)`, `y = c + τξ`. -/
noncomputable def rowC {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a a' : Fin n → ℝ) : ℝ :=
  ∫ z, relu (a ⬝ᵥ c + z ⬝ᵥ (τ • a)) * relu (a' ⬝ᵥ c + z ⬝ᵥ (τ • a')) ∂stdGauss (Fin n) -
    psiS (nrm (τ • a)) (a ⬝ᵥ c) * psiS (nrm (τ • a')) (a' ⬝ᵥ c)

lemma lin_facts {n : ℕ} (g : Fin n → ℝ) (x : ℝ) :
    Integrable (fun z : Fin n → ℝ => relu (x + z ⬝ᵥ g)) (stdGauss (Fin n)) ∧
    Integrable (fun z : Fin n → ℝ => relu (x + z ⬝ᵥ g) ^ 2) (stdGauss (Fin n)) ∧
    ∫ z, relu (x + z ⬝ᵥ g) ∂stdGauss (Fin n) = psiS (nrm g) x ∧
    ∫ z, relu (x + z ⬝ᵥ g) ^ 2 ∂stdGauss (Fin n) =
      ∫ t, relu (x + nrm g * t) ^ 2 ∂gaussianReal 0 1 := by
  have m1 : Measurable (fun t : ℝ => relu (x + t)) :=
    measurable_relu.comp (measurable_const.add measurable_id)
  have m2 : Measurable (fun t : ℝ => relu (x + t) ^ 2) := m1.pow_const 2
  exact ⟨gauss_lin_integrable g m1 (BstLean.Part137.integrable_relu_shift x _),
    gauss_lin_integrable g m2 (BstLean.Part137.integrable_relu_shift_sq x _),
    gauss_lin_integral g m1, gauss_lin_integral g m2⟩

lemma meas_rowC {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => rowC c τ q.1 q.2) := by
  have hc : Continuous (fun w : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      relu (w.1.1 ⬝ᵥ c + w.2 ⬝ᵥ (τ • w.1.1)) * relu (w.1.2 ⬝ᵥ c + w.2 ⬝ᵥ (τ • w.1.2))) := by
    refine (continuous_relu.comp ?_).mul (continuous_relu.comp ?_)
    · simp only [dotProduct, Pi.smul_apply, smul_eq_mul]; fun_prop
    · simp only [dotProduct, Pi.smul_apply, smul_eq_mul]; fun_prop
  have h1 := hc.measurable.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))
  have h2 : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      psiS (nrm (τ • q.1)) (q.1 ⬝ᵥ c)) :=
    BstLean.Part137.measurable_psiS.comp
      (((meas_nrm_smul τ).comp measurable_fst).prodMk ((meas_dot_L1c c).comp measurable_fst))
  have h3 : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      psiS (nrm (τ • q.2)) (q.2 ⬝ᵥ c)) :=
    BstLean.Part137.measurable_psiS.comp
      (((meas_nrm_smul τ).comp measurable_snd).prodMk ((meas_dot_L1c c).comp measurable_snd))
  exact h1.measurable.sub (h2.mul h3)

lemma cov_scale_L1c {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : Integrable (fun ω => X ω * Y ω) μ) (r : ℝ) :
    ∫ ω, (r * X ω - r * ∫ ω', X ω' ∂μ) * (r * Y ω - r * ∫ ω', Y ω' ∂μ) ∂μ =
      r * r * (∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ) := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = ∫ ω, X ω ∂μ := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ∫ ω, Y ω ∂μ := ⟨_, rfl⟩
  rw [← hp, ← hq]
  have e : ∀ ω, (r * X ω - r * p) * (r * Y ω - r * q) =
      r * r * (X ω * Y ω) - r * r * q * X ω - r * r * p * Y ω + r * r * p * q := fun ω => by ring
  simp_rw [e]
  have hA : Integrable (fun ω => r * r * (X ω * Y ω)) μ := hXY.const_mul _
  have hB : Integrable (fun ω => r * r * q * X ω) μ := hX.const_mul _
  have hC : Integrable (fun ω => r * r * p * Y ω) μ := hY.const_mul _
  have hAB : Integrable (fun ω => r * r * (X ω * Y ω) - r * r * q * X ω) μ := hA.sub hB
  have hABC : Integrable (fun ω => r * r * (X ω * Y ω) - r * r * q * X ω - r * r * p * Y ω) μ :=
    hAB.sub hC
  rw [integral_add hABC (integrable_const _), integral_sub hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul, ← hp, ← hq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

lemma fA_apply {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (ξ : Fin n → ℝ) (i : Fin m) :
    fA A₁ c τ ξ i =
      √(2 / (m : ℝ)) * relu (rowOf i A₁ ⬝ᵥ c + ξ ⬝ᵥ (τ • rowOf i A₁)) := by
  unfold fA reluV
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 2
  simp only [mulVec, dotProduct, rowOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma covF_eq {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (i j : Fin m) :
    covF (stdGauss (Fin n)) (fA A₁ c τ) i j =
      2 / (m : ℝ) * rowC c τ (rowOf i A₁) (rowOf j A₁) := by
  have hrr : √(2 / (m : ℝ)) * √(2 / (m : ℝ)) = 2 / (m : ℝ) := Real.mul_self_sqrt (by positivity)
  obtain ⟨i1, i1s, e1, -⟩ := lin_facts (τ • rowOf i A₁) (rowOf i A₁ ⬝ᵥ c)
  obtain ⟨i2, i2s, e2, -⟩ := lin_facts (τ • rowOf j A₁) (rowOf j A₁ ⬝ᵥ c)
  have mX : ∀ k : Fin m, Measurable (fun z : Fin n → ℝ =>
      relu (rowOf k A₁ ⬝ᵥ c + z ⬝ᵥ (τ • rowOf k A₁))) := fun k =>
    measurable_relu.comp (measurable_const.add (meas_dot_L1c _))
  have i12 : Integrable (fun z : Fin n → ℝ =>
      relu (rowOf i A₁ ⬝ᵥ c + z ⬝ᵥ (τ • rowOf i A₁)) *
        relu (rowOf j A₁ ⬝ᵥ c + z ⬝ᵥ (τ • rowOf j A₁))) (stdGauss (Fin n)) :=
    MemLp.integrable_mul ((memLp_two_iff_integrable_sq (mX i).aestronglyMeasurable).mpr i1s)
      ((memLp_two_iff_integrable_sq (mX j).aestronglyMeasurable).mpr i2s)
  have fb : ∀ k : Fin m, fbar (stdGauss (Fin n)) (fA A₁ c τ) k =
      √(2 / (m : ℝ)) * psiS (nrm (τ • rowOf k A₁)) (rowOf k A₁ ⬝ᵥ c) := by
    intro k
    unfold fbar
    simp_rw [fA_apply]
    rw [integral_const_mul, (lin_facts _ _).2.2.1]
  unfold covF
  rw [fb i, fb j]
  simp_rw [fA_apply]
  rw [← e1, ← e2, cov_scale_L1c i1 i2 i12, hrr, e1, e2]
  rfl

lemma nrm_smul_L1c {n : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (a : Fin n → ℝ) :
    nrm (τ • a) = τ * √(∑ j, a j ^ 2) := by
  unfold nrm
  rw [normSq_smul, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ]
  rfl

lemma rowC_self {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (a : Fin n → ℝ) :
    rowC c τ a a = rowV c τ a := by
  obtain ⟨-, -, -, e2⟩ := lin_facts (τ • a) (a ⬝ᵥ c)
  unfold rowC rowV vS
  simp_rw [← sq]
  rw [e2, nrm_smul_L1c hτ]
  rfl

lemma rowC_sq_le {n : ℕ} {K : ℝ} (hK0 : 0 ≤ K) (hK : PRvecAbs K) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {κ : ℝ} (hκ : 0 < κ) (a a' : Fin n → ℝ) :
    rowC c τ a a' ^ 2 ≤ (1 + κ) * (τ ^ 4 * ((a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2)) +
      (1 + 1 / κ) * (K ^ 2 * (τ ^ 4 * Qf (a, a'))) := by
  have h := hK n (τ • a) (τ • a') (a ⬝ᵥ c) (a' ⬝ᵥ c)
  have ed : (τ • a) ⬝ᵥ (τ • a') = τ ^ 2 * (a ⬝ᵥ a') := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  rw [ed] at h
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = τ ^ 2 * (a ⬝ᵥ a') * pR c τ a * pR c τ a' := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = K * (τ ^ 2 * (a ⬝ᵥ a')) ^ 2 / (nrm (τ • a) * nrm (τ • a')) :=
    ⟨_, rfl⟩
  have h' : |rowC c τ a a' - x| ≤ y := by rw [hx, hy]; exact h
  have hy0 : 0 ≤ y := by
    rw [hy]
    exact div_nonneg (mul_nonneg hK0 (sq_nonneg _)) (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
  have hy2 : y ^ 2 = K ^ 2 * (τ ^ 4 * Qf (a, a')) := by
    rw [hy, div_pow, mul_pow, mul_pow (nrm (τ • a)), nrm_sq, nrm_sq, normSq_smul, normSq_smul]
    unfold Qf
    simp only
    rw [show ((τ ^ 2 * (a ⬝ᵥ a')) ^ 2) ^ 2 = τ ^ 4 * (τ ^ 4 * (a ⬝ᵥ a') ^ 4) by ring,
      show τ ^ 2 * normSq a * (τ ^ 2 * normSq a') = τ ^ 4 * (normSq a * normSq a') by ring,
      mul_div_assoc, mul_div_mul_left _ _ (pow_ne_zero 4 hτ.ne'), mul_div_assoc]
  have hr : |rowC c τ a a'| ≤ |x| + y := by
    have := abs_sub_abs_le_abs_sub (rowC c τ a a') x
    linarith
  have hsq : rowC c τ a a' ^ 2 ≤ (|x| + y) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  have hmix : 2 * (|x| * y) ≤ κ * x ^ 2 + 1 / κ * y ^ 2 := by
    have h1 := sq_nonneg (κ * |x| - y)
    have h2 : κ * |x| ^ 2 + 1 / κ * y ^ 2 - 2 * (|x| * y) = (κ * |x| - y) ^ 2 / κ := by
      field_simp
      ring
    have h3 : 0 ≤ (κ * |x| - y) ^ 2 / κ := div_nonneg h1 hκ.le
    rw [sq_abs] at h2
    linarith
  have hx2 : x ^ 2 = τ ^ 4 * ((a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2) := by rw [hx]; ring
  rw [← hx2, ← hy2]
  have h5 : (|x| + y) ^ 2 = x ^ 2 + 2 * (|x| * y) + y ^ 2 := by rw [add_sq, sq_abs]; ring
  linarith

/-! ## Two rows of a Gaussian matrix -/

lemma pair_map {n m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    (gaussMat m n (2 / (n : ℝ))).map (fun M => (rowOf i M, rowOf j M)) =
      (rowLaw n).prod (rowLaw n) := by
  have hrows : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => fun i => rowOf i M) :=
    measurable_pi_iff.mpr fun i => measurable_rowOf i
  have hmap : (gaussMat m n (2 / (n : ℝ))).map (fun M i => rowOf i M) =
      Measure.pi fun _ : Fin m => rowLaw n := BstLean.Part148.gaussMat_rows_map m n _
  have hind := iIndepFun_pi (X := fun _ : Fin m => (id : (Fin n → ℝ) → (Fin n → ℝ)))
    (μ := fun _ : Fin m => rowLaw n) (fun _ => aemeasurable_id)
  have h2 := hind.indepFun hij
  have h3 := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).mp h2
  have ei := (measurePreserving_eval (fun _ : Fin m => rowLaw n) i).map_eq
  have ej := (measurePreserving_eval (fun _ : Fin m => rowLaw n) j).map_eq
  have hpe : Measurable (fun ω : Fin m → Fin n → ℝ => (ω i, ω j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have h4 : (Measure.pi fun _ : Fin m => rowLaw n).map
      (fun ω : Fin m → Fin n → ℝ => (ω i, ω j)) = (rowLaw n).prod (rowLaw n) :=
    h3.trans (congrArg₂ Measure.prod ei ej)
  have e : (fun M : Matrix (Fin m) (Fin n) ℝ => (rowOf i M, rowOf j M)) =
      (fun ω : Fin m → Fin n → ℝ => (ω i, ω j)) ∘ (fun M i => rowOf i M) := rfl
  rw [e, ← Measure.map_map hpe hrows, hmap, h4]

lemma int_offd_mat {n m : ℕ} {i j : Fin m} (hij : i ≠ j)
    {G : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hG : Measurable G)
    (hI : Integrable G ((rowLaw n).prod (rowLaw n))) :
    Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => G (rowOf i A₁, rowOf j A₁))
      (gaussMat m n (2 / (n : ℝ))) ∧
    ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, G (rowOf i A₁, rowOf j A₁) ∂gaussMat m n (2 / (n : ℝ)) =
      ∫ q, G q ∂((rowLaw n).prod (rowLaw n)) := by
  have hp : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (rowOf i M, rowOf j M)) :=
    (measurable_rowOf i).prodMk (measurable_rowOf j)
  rw [← pair_map hij] at hI ⊢
  exact ⟨(integrable_map_measure hG.aestronglyMeasurable hp.aemeasurable).mp hI,
    (integral_map hp.aemeasurable hG.aestronglyMeasurable).symm⟩

lemma int_diag_mat {n m : ℕ} (i : Fin m) {G : (Fin n → ℝ) → ℝ} (hG : Measurable G)
    (hI : Integrable G (rowLaw n)) :
    Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => G (rowOf i A₁))
      (gaussMat m n (2 / (n : ℝ))) ∧
    ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, G (rowOf i A₁) ∂gaussMat m n (2 / (n : ℝ)) =
      ∫ a, G a ∂rowLaw n := by
  have hmap : (gaussMat m n (2 / (n : ℝ))).map (rowOf i) = rowLaw n := gaussMat_row _ i
  rw [← hmap] at hI ⊢
  exact ⟨(integrable_map_measure hG.aestronglyMeasurable (measurable_rowOf i).aemeasurable).mp hI,
    (integral_map (measurable_rowOf i).aemeasurable hG.aestronglyMeasurable).symm⟩

/-! ## The two bounds -/

lemma opt_L1c {E A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
    (h : ∀ κ : ℝ, 0 < κ → E ≤ A * ((1 + κ) + (1 + 1 / κ) * s ^ 2)) : E ≤ A * (1 + s) ^ 2 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA1 : 0 < A + 1 := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (A + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos hε hA1
  have h1 := h (s + δ) (by linarith)
  have h2 : s ^ 2 / (s + δ) ≤ s := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : A * δ ≤ ε := by
    rw [hδ, ← mul_div_assoc, div_le_iff₀ hA1]; nlinarith
  have h4 : (1 + (s + δ)) + (1 + 1 / (s + δ)) * s ^ 2 ≤ (1 + s) ^ 2 + δ := by
    have : (1 + 1 / (s + δ)) * s ^ 2 = s ^ 2 + s ^ 2 / (s + δ) := by ring
    rw [this]; nlinarith
  calc E ≤ A * ((1 + (s + δ)) + (1 + 1 / (s + δ)) * s ^ 2) := h1
    _ ≤ A * ((1 + s) ^ 2 + δ) := mul_le_mul_of_nonneg_left h4 hA
    _ = A * (1 + s) ^ 2 + A * δ := by ring
    _ ≤ A * (1 + s) ^ 2 + ε := by linarith

lemma diagL {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun a : Fin n → ℝ => rowC c τ a a ^ 2) (rowLaw n) ∧
    ∫ a, rowC c τ a a ^ 2 ∂rowLaw n ≤ τ ^ 4 * (4 * (1 + 2 / (n : ℝ))) := by
  obtain ⟨i4, e4⟩ := rowLaw_four hn
  have hle : ∀ a : Fin n → ℝ, rowC c τ a a ^ 2 ≤ τ ^ 4 * normSq a ^ 2 := fun a => by
    rw [rowC_self c hτ a]
    calc rowV c τ a ^ 2 ≤ (τ ^ 2 * normSq a) ^ 2 :=
          pow_le_pow_left₀ (rowV_nonneg c τ a) (rowV_le c τ a) 2
      _ = τ ^ 4 * normSq a ^ 2 := by ring
  have hm : Measurable (fun a : Fin n → ℝ => rowC c τ a a ^ 2) :=
    ((meas_rowC c τ).comp (measurable_id.prodMk measurable_id)).pow_const 2
  have iC : Integrable (fun a : Fin n → ℝ => rowC c τ a a ^ 2) (rowLaw n) := by
    refine Integrable.mono' (i4.const_mul (τ ^ 4)) hm.aestronglyMeasurable
      (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle a
  refine ⟨iC, ?_⟩
  have := integral_mono iC (i4.const_mul (τ ^ 4)) hle
  rwa [integral_const_mul, e4] at this


/-! ## New for change (B) -/

open Filter Topology in
/-- `Φ(t)(1 − Φ(t)) ≥ (π/2)·φ(t)²` for `t ≥ 0`. -/
lemma PhiG_tail_prod_nonneg {y : ℝ} (hy : 0 ≤ y) :
    π / 2 * (phiG y * phiG y) ≤ PhiG y * (1 - PhiG y) := by
  have hπ := Real.pi_pos
  obtain ⟨N, hN⟩ : ∃ N : ℝ → ℝ, N = fun t => PhiG t * (1 - PhiG t) - π / 2 * (phiG t * phiG t) :=
    ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ → ℝ, M = fun t => π * t * phiG t - (2 * PhiG t - 1) := ⟨_, rfl⟩
  have dN : ∀ t, HasDerivAt N (phiG t * M t) t := by
    intro t
    have hφ := BstLean.Part153.hasDerivAt_phiG t
    have hΦ := hasDerivAt_PhiG t
    have h := (hΦ.mul (hΦ.const_sub 1)).sub ((hφ.mul hφ).const_mul (π / 2))
    rw [hN]
    refine HasDerivAt.congr_deriv h ?_
    rw [hM]; ring
  have dM : ∀ t, HasDerivAt M (phiG t * (π - 2 - π * t ^ 2)) t := by
    intro t
    have hφ := BstLean.Part153.hasDerivAt_phiG t
    have hΦ := hasDerivAt_PhiG t
    have h := (((hasDerivAt_id t).const_mul π).mul hφ).sub ((hΦ.const_mul 2).sub_const 1)
    rw [hM]
    refine HasDerivAt.congr_deriv h ?_
    simp only [id]; ring
  have hN0 : N 0 = 0 := by
    rw [hN]
    have h0 : phiG 0 = (√(2 * π))⁻¹ := by unfold phiG; norm_num
    have h1 : phiG 0 * phiG 0 = (2 * π)⁻¹ := by
      rw [h0, ← mul_inv, Real.mul_self_sqrt (by positivity)]
    simp only
    rw [PhiG_zero, h1]
    field_simp
    ring
  have hM0 : M 0 = 0 := by rw [hM]; simp only; rw [PhiG_zero]; ring
  have hNlim : Tendsto N atTop (𝓝 0) := by
    have h := (tendsto_PhiG.mul tendsto_tail).sub ((tendsto_phiG.mul tendsto_phiG).const_mul (π / 2))
    rw [show (1 * 0 - π / 2 * (0 * 0) : ℝ) = 0 by ring] at h
    rw [hN]; exact h
  have key : 0 ≤ N y := by
    by_contra hcon
    rw [not_le] at hcon
    have hy0 : 0 < y := by
      rcases hy.eq_or_lt with e | e
      · rw [← e, hN0] at hcon; exact absurd hcon (lt_irrefl _)
      · exact e
    obtain ⟨v, hv, hv'⟩ := exists_deriv_neg dN hy0 (by rw [hN0]; exact hcon)
    obtain ⟨z, hz, hz'⟩ := exists_deriv_pos_after dN hNlim hcon
    have hMv : M v < 0 := by
      by_contra h; rw [not_lt] at h
      have := mul_nonneg (BstLean.Part153.phiG_pos v).le h; linarith
    have hMz : 0 < M z := by
      by_contra h; rw [not_lt] at h
      have := mul_nonpos_of_nonneg_of_nonpos (BstLean.Part153.phiG_pos z).le h; linarith
    obtain ⟨s, hs, hs'⟩ := exists_deriv_neg dM hv.1 (by rw [hM0]; exact hMv)
    obtain ⟨r, hr, hr'⟩ := exists_deriv_pos dM (hv.2.trans hz) (hMv.trans hMz)
    have q1 : π - 2 - π * s ^ 2 < 0 := by
      by_contra h; rw [not_lt] at h
      have := mul_nonneg (BstLean.Part153.phiG_pos s).le h; linarith
    have q2 : 0 < π - 2 - π * r ^ 2 := by
      by_contra h; rw [not_lt] at h
      have := mul_nonpos_of_nonneg_of_nonpos (BstLean.Part153.phiG_pos r).le h; linarith
    have hsr : s < r := hs.2.trans hr.1
    have : s ^ 2 < r ^ 2 := pow_lt_pow_left₀ hsr hs.1.le (by norm_num)
    nlinarith
  rw [hN] at key
  simp only at key
  linarith

/-- `Φ(t)(1 − Φ(t)) ≥ (π/2)·φ(t)²`, every real `t`. -/
lemma PhiG_tail_prod (t : ℝ) : π / 2 * (phiG t * phiG t) ≤ PhiG t * (1 - PhiG t) := by
  rcases le_total 0 t with h | h
  · exact PhiG_tail_prod_nonneg h
  · have := PhiG_tail_prod_nonneg (y := -t) (by linarith)
    rw [BstLean.Part153.phiG_neg, PhiG_neg_L1c] at this
    linarith

/-- `p(1 − p) ≥ e^{−t²}/4`, `p = Φ(t)`. -/
lemma PhiG_var_ge (t : ℝ) : 1 / 4 * rexp (-(t ^ 2)) ≤ PhiG t * (1 - PhiG t) := by
  refine le_trans (le_of_eq ?_) (PhiG_tail_prod t)
  have hπ := Real.pi_pos
  unfold phiG
  have e1 : rexp (-(t ^ 2 / 2)) * rexp (-(t ^ 2 / 2)) = rexp (-(t ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  calc 1 / 4 * rexp (-(t ^ 2)) = π / 2 * ((2 * π)⁻¹ * rexp (-(t ^ 2))) := by
        field_simp; ring
    _ = _ := by rw [← e1, ← e2]; ring

/-- The second moment and the fourth moment of a linear form of a standard Gaussian vector. -/
lemma lin_moments {n : ℕ} (w : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => z ⬝ᵥ w) (stdGauss (Fin n)) ∧
    ∫ z : Fin n → ℝ, z ⬝ᵥ w ∂stdGauss (Fin n) = 0 ∧
    Integrable (fun z : Fin n → ℝ => (z ⬝ᵥ w) ^ 2) (stdGauss (Fin n)) ∧
    ∫ z : Fin n → ℝ, (z ⬝ᵥ w) ^ 2 ∂stdGauss (Fin n) = normSq w ∧
    Integrable (fun z : Fin n → ℝ => (z ⬝ᵥ w) ^ 4) (stdGauss (Fin n)) ∧
    ∫ z : Fin n → ℝ, (z ⬝ᵥ w) ^ 4 ∂stdGauss (Fin n) = 3 * normSq w ^ 2 := by
  have hS : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : √(∑ j, w j ^ 2) ^ 2 = normSq w := Real.sq_sqrt hS
  have m1 : Measurable (fun t : ℝ => t) := measurable_id
  have m2 : Measurable (fun t : ℝ => t ^ 2) := measurable_id.pow_const 2
  have m4 : Measurable (fun t : ℝ => t ^ 4) := measurable_id.pow_const 4
  have i1 : Integrable (fun z : ℝ => √(∑ j, w j ^ 2) * z) (gaussianReal 0 1) := by
    have := (integrable_pow_gauss 1).const_mul (√(∑ j, w j ^ 2))
    simpa using this
  have i2 : Integrable (fun z : ℝ => (√(∑ j, w j ^ 2) * z) ^ 2) (gaussianReal 0 1) := by
    simp_rw [mul_pow]; exact (integrable_pow_gauss 2).const_mul _
  have i4 : Integrable (fun z : ℝ => (√(∑ j, w j ^ 2) * z) ^ 4) (gaussianReal 0 1) := by
    simp_rw [mul_pow]; exact (integrable_pow_gauss 4).const_mul _
  refine ⟨gauss_lin_integrable w m1 i1, ?_, gauss_lin_integrable w m2 i2, ?_,
    gauss_lin_integrable w m4 i4, ?_⟩
  · rw [gauss_lin_integral w m1, integral_const_mul, integral_id_gaussianReal, mul_zero]
  · have h := gauss_lin_integral w m2
    simp only [mul_pow] at h
    rw [integral_const_mul, gaussMom_eq, gaussMom_two, mul_one, hsq] at h
    exact h
  · have h := gauss_lin_integral w m4
    simp only [mul_pow] at h
    rw [integral_const_mul, gaussMom_eq, gaussMom_four] at h
    rw [h]
    have : √(∑ j, w j ^ 2) ^ 4 = normSq w ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
    rw [this]; ring

/-- The Gaussian integral with the factor `exp(−ν⟨z, c⟩²)`: a lower bound. -/
lemma gauss_weighted_lower {n : ℕ} (c : Fin n → ℝ) (hc : 0 < normSq c) (b : Fin n → ℝ) {ν : ℝ}
    (hν : 0 ≤ ν) :
    (normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) * (√(1 + 2 * (ν * normSq c)))⁻¹ ≤
      ∫ z : Fin n → ℝ, (z ⬝ᵥ b) ^ 2 * rexp (-(ν * (z ⬝ᵥ c) ^ 2)) ∂stdGauss (Fin n) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = nrm c := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hc
  have hr2 : r ^ 2 = normSq c := by rw [hr]; exact nrm_sq c
  obtain ⟨e, he⟩ : ∃ e : Fin n → ℝ, e = r⁻¹ • c := ⟨_, rfl⟩
  have hcc : c ⬝ᵥ c = normSq c := by
    unfold normSq dotProduct; exact Finset.sum_congr rfl fun i _ => by ring
  have hee : e ⬝ᵥ e = 1 := by
    rw [he, smul_dotProduct, dotProduct_smul, hcc, ← hr2]
    simp only [smul_eq_mul]; field_simp
  have hec : e ⬝ᵥ c = r := by
    rw [he, smul_dotProduct, hcc, ← hr2]; simp only [smul_eq_mul]; field_simp
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = e ⬝ᵥ b := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℝ, w = b - β • e := ⟨_, rfl⟩
  have hwn : normSq w = normSq b - (b ⬝ᵥ c) ^ 2 / normSq c := by
    have hbb : b ⬝ᵥ b = normSq b := by
      unfold normSq dotProduct; exact Finset.sum_congr rfl fun i _ => by ring
    have hww : w ⬝ᵥ w = normSq w := by
      unfold normSq dotProduct; exact Finset.sum_congr rfl fun i _ => by ring
    have hβc : b ⬝ᵥ c = β * r := by
      rw [hβ, he, smul_dotProduct, dotProduct_comm c b]
      simp only [smul_eq_mul]; field_simp
    rw [← hww, hw, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_dotProduct, dotProduct_smul, hee, hbb, dotProduct_comm b e, ← hβ,
      hβc, ← hr2]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [← hwn]
  -- the integrand
  obtain ⟨H, hH⟩ : ∃ H : (Fin n → ℝ) → ℝ,
      H = fun z => (z ⬝ᵥ b) ^ 2 * rexp (-(ν * (z ⬝ᵥ c) ^ 2)) := ⟨_, rfl⟩
  have hdm : ∀ u : Fin n → ℝ, Measurable (fun z : Fin n → ℝ => z ⬝ᵥ u) := fun u => by
    unfold dotProduct; fun_prop
  have hHm : Measurable H := by
    rw [hH]
    exact ((hdm b).pow_const 2).mul
      (Real.measurable_exp.comp ((((hdm c).pow_const 2).const_mul ν).neg))
  obtain ⟨-, -, ib2, -, -, -⟩ := lin_moments b
  have hHi : Integrable H (stdGauss (Fin n)) := by
    refine Integrable.mono' ib2 hHm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [hH, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by have := mul_nonneg hν (sq_nonneg (z ⬝ᵥ c)); linarith)
  have hφm : Measurable (fun p : ℝ × (Fin n → ℝ) => p.1 • e + projMat e *ᵥ p.2) :=
    BstLean.Part154.meas_phi e
  have hd := stdGauss_decomp hee
  have hHi' : Integrable H (((gaussianReal 0 1).prod (stdGauss (Fin n))).map
      (fun p => p.1 • e + projMat e *ᵥ p.2)) := by rw [hd]; exact hHi
  have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => H (p.1 • e + projMat e *ᵥ p.2))
      ((gaussianReal 0 1).prod (stdGauss (Fin n))) :=
    (integrable_map_measure hHm.aestronglyMeasurable hφm.aemeasurable).mp hHi'
  have hsplit : ∫ z, H z ∂stdGauss (Fin n) =
      ∫ ζ, (∫ z', H (ζ • e + projMat e *ᵥ z') ∂stdGauss (Fin n)) ∂gaussianReal 0 1 := by
    calc ∫ z, H z ∂stdGauss (Fin n)
        = ∫ z, H z ∂(((gaussianReal 0 1).prod (stdGauss (Fin n))).map
            (fun p => p.1 • e + projMat e *ᵥ p.2)) := by rw [hd]
      _ = ∫ p : ℝ × (Fin n → ℝ), H (p.1 • e + projMat e *ᵥ p.2)
            ∂((gaussianReal 0 1).prod (stdGauss (Fin n))) :=
          integral_map hφm.aemeasurable hHm.aestronglyMeasurable
      _ = _ := integral_prod _ hprod
  -- the inner integral
  obtain ⟨iw1, ew1, iw2, ew2, -, -⟩ := lin_moments w
  have hinner : ∀ ζ : ℝ, ∫ z', H (ζ • e + projMat e *ᵥ z') ∂stdGauss (Fin n) =
      rexp (-(ν * normSq c * ζ ^ 2)) * (ζ ^ 2 * β ^ 2 + normSq w) := by
    intro ζ
    have e1 : ∀ z' : Fin n → ℝ, (ζ • e + projMat e *ᵥ z') ⬝ᵥ c = ζ * r := by
      intro z'
      have h0 : (projMat e *ᵥ z') ⬝ᵥ c = 0 := by
        have h1 := projMat_dot hee z'
        have : c = r • e := by rw [he, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
        rw [this, dotProduct_smul, h1]; simp
      rw [add_dotProduct, smul_dotProduct, hec, h0]; simp
    have e2 : ∀ z' : Fin n → ℝ, (ζ • e + projMat e *ᵥ z') ⬝ᵥ b = ζ * β + z' ⬝ᵥ w := by
      intro z'
      rw [add_dotProduct, smul_dotProduct, ← hβ, projMat_mulVec, sub_dotProduct, smul_dotProduct,
        ← hβ, hw, dotProduct_sub, dotProduct_smul, dotProduct_comm z' e]
      simp only [smul_eq_mul]; ring
    rw [hH]
    simp only [e1, e2]
    have e3 : ∀ z' : Fin n → ℝ, (ζ * β + z' ⬝ᵥ w) ^ 2 * rexp (-(ν * (ζ * r) ^ 2)) =
        rexp (-(ν * normSq c * ζ ^ 2)) *
          ((ζ * β) ^ 2 + 2 * (ζ * β) * (z' ⬝ᵥ w) + (z' ⬝ᵥ w) ^ 2) := by
      intro z'
      have : ν * (ζ * r) ^ 2 = ν * normSq c * ζ ^ 2 := by rw [mul_pow, hr2]; ring
      rw [this]; ring
    simp_rw [e3]
    rw [integral_const_mul]
    have hA : ∫ z' : Fin n → ℝ, ((ζ * β) ^ 2 + 2 * (ζ * β) * (z' ⬝ᵥ w) + (z' ⬝ᵥ w) ^ 2)
        ∂stdGauss (Fin n) = ∫ z' : Fin n → ℝ, ((ζ * β) ^ 2 + 2 * (ζ * β) * (z' ⬝ᵥ w))
          ∂stdGauss (Fin n) + ∫ z' : Fin n → ℝ, (z' ⬝ᵥ w) ^ 2 ∂stdGauss (Fin n) :=
      integral_add ((integrable_const _).add (iw1.const_mul _)) iw2
    have hB : ∫ z' : Fin n → ℝ, ((ζ * β) ^ 2 + 2 * (ζ * β) * (z' ⬝ᵥ w)) ∂stdGauss (Fin n) =
        ∫ _z' : Fin n → ℝ, (ζ * β) ^ 2 ∂stdGauss (Fin n) +
          ∫ z' : Fin n → ℝ, 2 * (ζ * β) * (z' ⬝ᵥ w) ∂stdGauss (Fin n) :=
      integral_add (integrable_const _) (iw1.const_mul _)
    rw [hA, hB, integral_const_mul, ew1, ew2, integral_const, probReal_univ, one_smul]
    ring
  rw [← hH, hsplit]
  simp_rw [hinner]
  have hκ : 0 ≤ ν * normSq c := mul_nonneg hν hc.le
  have hg := gauss_exp_sq hκ
  have i0 : Integrable (fun ζ : ℝ => rexp (-(ν * normSq c * ζ ^ 2))) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (Real.measurable_exp.comp ((measurable_id.pow_const 2).const_mul _).neg).aestronglyMeasurable
      (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by have := mul_nonneg hκ (sq_nonneg ζ); linarith)
  have i1 : Integrable (fun ζ : ℝ => rexp (-(ν * normSq c * ζ ^ 2)) * (ζ ^ 2 * β ^ 2 + normSq w))
      (gaussianReal 0 1) := by
    have hdom : Integrable (fun ζ : ℝ => ζ ^ 2 * β ^ 2 + normSq w) (gaussianReal 0 1) :=
      ((integrable_pow_gauss 2).mul_const _).add (integrable_const _)
    refine Integrable.mono' hdom
      ((Real.measurable_exp.comp ((measurable_id.pow_const 2).const_mul _).neg).mul
        (((measurable_id.pow_const 2).mul_const _).add_const _)).aestronglyMeasurable
      (ae_of_all _ fun ζ => ?_)
    have h0 : 0 ≤ ζ ^ 2 * β ^ 2 + normSq w := add_nonneg (by positivity) (normSq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h0)]
    refine mul_le_of_le_one_left h0 ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by have := mul_nonneg hκ (sq_nonneg ζ); linarith)
  have hmono : ∫ ζ : ℝ, rexp (-(ν * normSq c * ζ ^ 2)) * normSq w ∂gaussianReal 0 1 ≤
      ∫ ζ : ℝ, rexp (-(ν * normSq c * ζ ^ 2)) * (ζ ^ 2 * β ^ 2 + normSq w) ∂gaussianReal 0 1 :=
    integral_mono (i0.mul_const _) i1 fun ζ =>
      mul_le_mul_of_nonneg_left (by have : 0 ≤ ζ ^ 2 * β ^ 2 := by positivity
                                    linarith) (Real.exp_pos _).le
  rw [integral_mul_const, hg] at hmono
  rw [mul_comm]
  exact hmono

/-- **The key lower bound**: for a fixed vector `b` and `0 < S₀ ≤ n − 2√(12n)`:
`E_a[⟨b, a⟩² p(1 − p)] ≥ (1/4)(2/n)·[(|b|² − ⟨b, c⟩²/|c|²)·J − √3·e^{−6}·|b|²]`,
`J = (1 + 2|c|²/(τ²S₀))^{−1/2}`. -/
lemma keyK {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    (b : Fin n → ℝ) {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) :
    Integrable (fun a => (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a))) (rowLaw n) ∧
    1 / 4 * (2 / (n : ℝ)) * ((normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹ - √3 * rexp (-6) * normSq b) ≤
      ∫ a, (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ, s0 = 2 / (n : ℝ) * S0 := ⟨_, rfl⟩
  have hs0p : 0 < s0 := by rw [hs0]; positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = 1 / (τ ^ 2 * s0) := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  obtain ⟨iD, eD⟩ := rl_dot2 hn b
  have hpm := meas_pR c τ
  have hGm : Measurable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2) := (meas_dot'_L1c b).pow_const 2
  have hBad : MeasurableSet {a : Fin n → ℝ | normSq a < s0} :=
    measurableSet_lt continuous_normSq.measurable measurable_const
  obtain ⟨ind, hind⟩ : ∃ ind : (Fin n → ℝ) → ℝ,
      ind = Set.indicator {a : Fin n → ℝ | normSq a < s0} (fun _ => (1 : ℝ)) := ⟨_, rfl⟩
  have hindm : Measurable ind := by rw [hind]; exact measurable_const.indicator hBad
  have hind01 : ∀ a, ind a = 0 ∨ ind a = 1 := by
    intro a; rw [hind]; by_cases h : a ∈ {a : Fin n → ℝ | normSq a < s0}
    · right; exact Set.indicator_of_mem h _
    · left; exact Set.indicator_of_notMem h _
  -- the pointwise bound
  have hpt : ∀ a : Fin n → ℝ, 1 / 4 * ((b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) -
      (b ⬝ᵥ a) ^ 2 * ind a) ≤ (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a)) := by
    intro a
    have h1 := PhiG_var_ge (a ⬝ᵥ c / nrm (τ • a))
    have hG : 0 ≤ (b ⬝ᵥ a) ^ 2 := sq_nonneg _
    have h2 : rexp (-(μ * (a ⬝ᵥ c) ^ 2)) - ind a ≤ rexp (-((a ⬝ᵥ c / nrm (τ • a)) ^ 2)) := by
      by_cases hb : a ∈ {a : Fin n → ℝ | normSq a < s0}
      · have : ind a = 1 := by rw [hind]; exact Set.indicator_of_mem hb _
        rw [this]
        have h3 : rexp (-(μ * (a ⬝ᵥ c) ^ 2)) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by have := mul_nonneg hμ0.le (sq_nonneg (a ⬝ᵥ c)); linarith)
        have := Real.exp_pos (-((a ⬝ᵥ c / nrm (τ • a)) ^ 2))
        linarith
      · have h0 : ind a = 0 := by rw [hind]; exact Set.indicator_of_notMem hb _
        rw [h0, sub_zero]
        have hA : s0 ≤ normSq a := not_lt.mp hb
        refine Real.exp_le_exp.mpr (neg_le_neg ?_)
        rw [div_pow, nrm_sq, normSq_smul, hμ]
        have hden : 0 < τ ^ 2 * normSq a := by
          have := lt_of_lt_of_le hs0p hA
          positivity
        rw [div_le_iff₀ hden]
        have e : 1 / (τ ^ 2 * s0) * (a ⬝ᵥ c) ^ 2 * (τ ^ 2 * normSq a) =
            (a ⬝ᵥ c) ^ 2 * (normSq a / s0) := by field_simp
        rw [e]
        have : 1 ≤ normSq a / s0 := by rw [le_div_iff₀ hs0p]; linarith
        nlinarith [sq_nonneg (a ⬝ᵥ c)]
    unfold pR
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (by linarith : rexp
      (-((a ⬝ᵥ c / nrm (τ • a)) ^ 2)) ≤ 4 * (PhiG (a ⬝ᵥ c / nrm (τ • a)) *
        (1 - PhiG (a ⬝ᵥ c / nrm (τ • a)))))) hG
    nlinarith
  -- integrability
  have hF1m : Measurable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2))) :=
    hGm.mul (Real.measurable_exp.comp ((((meas_dot_L1c c).pow_const 2).const_mul μ).neg))
  have iF1 : Integrable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)))
      (rowLaw n) := by
    refine Integrable.mono' iD hF1m.aestronglyMeasurable (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by have := mul_nonneg hμ0.le (sq_nonneg (a ⬝ᵥ c)); linarith)
  have iF2 : Integrable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2 * ind a) (rowLaw n) := by
    refine Integrable.mono' iD (hGm.mul hindm).aestronglyMeasurable (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rcases hind01 a with h | h <;> rw [h] <;> norm_num
  have iT : Integrable (fun a => (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a))) (rowLaw n) := by
    refine Integrable.mono' iD (hGm.mul (hpm.mul (measurable_const.sub hpm))).aestronglyMeasurable
      (ae_of_all _ fun a => ?_)
    have hp0 := pR_nonneg c τ a
    have hp1 := pR_le_one c τ a
    have hq : 0 ≤ pR c τ a * (1 - pR c τ a) := mul_nonneg hp0 (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hq)]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    nlinarith
  refine ⟨iT, ?_⟩
  -- the main integral
  have hI1 : 2 / (n : ℝ) * ((normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) *
      (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹) ≤
      ∫ a, (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) ∂rowLaw n := by
    rw [rl_int hF1m]
    have e : ∀ z : Fin n → ℝ, (b ⬝ᵥ (√(2 / (n : ℝ)) • z)) ^ 2 *
        rexp (-(μ * ((√(2 / (n : ℝ)) • z) ⬝ᵥ c) ^ 2)) =
        2 / (n : ℝ) * ((z ⬝ᵥ b) ^ 2 * rexp (-(μ * (2 / (n : ℝ)) * (z ⬝ᵥ c) ^ 2))) := by
      intro z
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, mul_pow, mul_pow,
        Real.sq_sqrt (by positivity), dotProduct_comm b z]
      have : μ * (2 / (n : ℝ) * (z ⬝ᵥ c) ^ 2) = μ * (2 / (n : ℝ)) * (z ⬝ᵥ c) ^ 2 := by ring
      rw [this]; ring
    simp_rw [e]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := gauss_weighted_lower c hc b (ν := μ * (2 / (n : ℝ))) (by positivity)
    have e2 : μ * (2 / (n : ℝ)) * normSq c = normSq c / (τ ^ 2 * S0) := by
      rw [hμ, hs0]; field_simp
    rw [e2] at h
    exact h
  -- the bad set
  have hI2 : ∫ a, (b ⬝ᵥ a) ^ 2 * ind a ∂rowLaw n ≤ √3 * rexp (-6) * (2 / (n : ℝ) * normSq b) := by
    have hU2 : Integrable (fun a : Fin n → ℝ => ((b ⬝ᵥ a) ^ 2) ^ 2) (rowLaw n) ∧
        ∫ a : Fin n → ℝ, ((b ⬝ᵥ a) ^ 2) ^ 2 ∂rowLaw n = 3 * (2 / (n : ℝ) * normSq b) ^ 2 := by
      have hm4 : Measurable (fun a : Fin n → ℝ => ((b ⬝ᵥ a) ^ 2) ^ 2) := hGm.pow_const 2
      obtain ⟨-, -, -, -, i4, e4⟩ := lin_moments b
      have e : ∀ z : Fin n → ℝ, ((b ⬝ᵥ (√(2 / (n : ℝ)) • z)) ^ 2) ^ 2 =
          (2 / (n : ℝ)) ^ 2 * (z ⬝ᵥ b) ^ 4 := by
        intro z
        rw [dotProduct_smul, smul_eq_mul, mul_pow, Real.sq_sqrt (by positivity),
          dotProduct_comm b z]
        ring
      constructor
      · refine (rl_itg hm4).mpr ?_
        simp_rw [e]; exact i4.const_mul _
      · rw [rl_int hm4]
        simp_rw [e]
        rw [integral_const_mul, e4]; ring
    have hV2 : Integrable (fun a : Fin n → ℝ => ind a ^ 2) (rowLaw n) :=
      Integrable.mono' (integrable_const (1 : ℝ)) (hindm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun a => by rcases hind01 a with h | h <;> rw [h] <;> norm_num)
    obtain ⟨-, hCS⟩ := BstLean.Part132.integral_mul_le_sqrt hGm hindm hU2.1 hV2
    have hle : ∫ a, (b ⬝ᵥ a) ^ 2 * ind a ∂rowLaw n ≤
        ∫ a, |(b ⬝ᵥ a) ^ 2| * |ind a| ∂rowLaw n :=
      integral_mono_of_nonneg (ae_of_all _ fun a => mul_nonneg (sq_nonneg _)
        (by rcases hind01 a with h | h <;> rw [h] <;> norm_num))
        ((iF2.abs).congr (ae_of_all _ fun a => by simp [abs_mul]))
        (ae_of_all _ fun a => by
          show (b ⬝ᵥ a) ^ 2 * ind a ≤ |(b ⬝ᵥ a) ^ 2| * |ind a|
          rw [← abs_mul]; exact le_abs_self _)
    -- the probability of the bad set
    have hV : ∫ a, ind a ^ 2 ∂rowLaw n ≤ rexp (-12) := by
      have e1 : (fun a : Fin n → ℝ => ind a ^ 2) = ind := by
        funext a; rcases hind01 a with h | h <;> rw [h] <;> norm_num
      rw [e1, hind, integral_indicator_const _ hBad, smul_eq_mul, mul_one]
      unfold rowLaw
      rw [map_measureReal_apply (rl_sm n) hBad]
      refine (measureReal_mono ?_).trans (BstLean.Part152.chiSq_lower_LM (ι := Fin n)
        (x := 12) (by norm_num))
      intro z hz
      have hz' : normSq (√(2 / (n : ℝ)) • z) < s0 := hz
      rw [normSq_smul, Real.sq_sqrt (by positivity), hs0] at hz'
      have h3 : normSq z < S0 := lt_of_mul_lt_mul_left hz' (by positivity)
      show ∑ i, z i ^ 2 ≤ (Fintype.card (Fin n) : ℝ) - 2 * √((Fintype.card (Fin n) : ℝ) * 12)
      rw [Fintype.card_fin]
      exact (le_of_lt h3).trans hS
    have h6 : √(rexp (-12)) = rexp (-6) := by
      rw [show (-12 : ℝ) = -6 + -6 by norm_num, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
    have hsU : √(∫ a : Fin n → ℝ, ((b ⬝ᵥ a) ^ 2) ^ 2 ∂rowLaw n) =
        √3 * (2 / (n : ℝ) * normSq b) := by
      rw [hU2.2, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by have := normSq_nonneg b; positivity)]
    calc ∫ a, (b ⬝ᵥ a) ^ 2 * ind a ∂rowLaw n
        ≤ √(∫ a : Fin n → ℝ, ((b ⬝ᵥ a) ^ 2) ^ 2 ∂rowLaw n) * √(∫ a, ind a ^ 2 ∂rowLaw n) :=
          hle.trans hCS
      _ ≤ √3 * (2 / (n : ℝ) * normSq b) * rexp (-6) := by
          rw [hsU, ← h6]
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hV)
            (by have := normSq_nonneg b; positivity)
      _ = _ := by ring
  have hfin0 := integral_mono ((iF1.sub iF2).const_mul (1 / 4)) iT hpt
  have hc1 : ∫ a, 1 / 4 * ((b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) -
      (b ⬝ᵥ a) ^ 2 * ind a) ∂rowLaw n =
      1 / 4 * (∫ a, (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) ∂rowLaw n -
        ∫ a, (b ⬝ᵥ a) ^ 2 * ind a ∂rowLaw n) := by
    rw [integral_const_mul]
    congr 1
    exact integral_sub iF1 iF2
  have hfin : 1 / 4 * (∫ a, (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) ∂rowLaw n -
        ∫ a, (b ⬝ᵥ a) ^ 2 * ind a ∂rowLaw n) ≤
      ∫ a, (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    rw [← hc1]; exact hfin0
  refine le_trans ?_ hfin
  have : 1 / 4 * (2 / (n : ℝ)) * ((normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹ - √3 * rexp (-6) * normSq b) =
      1 / 4 * (2 / (n : ℝ) * ((normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹) - √3 * rexp (-6) * (2 / (n : ℝ) * normSq b)) := by
    ring
  rw [this]
  linarith

end aux

end BstLean.Part160.MFB

open BstLean.Part160.MFB in
#print axioms PhiG_tail_prod
open BstLean.Part160.MFB in
#print axioms keyK
