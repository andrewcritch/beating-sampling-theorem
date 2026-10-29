import BstLean.Part154App

/-!
# Part 154: Lemma L1 (c): `E‖H‖²_HS ≤ 4·c_HS·τ⁴/n`

Paper source: `proofs/option-n/theorem5-06-centre.tex`, Lemma L1 (c), with the constant `K` of
Lemma PR (i) as a parameter (`cHSK n K`).

Route. `H_{ii′} = t·C(a_i, a_{i′})`, `C = rowC` a function of two rows. For `i ≠ i′` the two rows
are independent with the distribution `rowLaw n`; Lemma PR (i) gives
`C² ≤ (1+ϰ)τ⁴⟨a,a′⟩²p²p′² + (1+1/ϰ)K²τ⁴⟨a,a′⟩⁴/(|a|²|a′|²)`.
* first mean (`mean1`): the reflection `a ↦ −a` gives `E[⟨a,a′⟩²p²p′²] ≤ 1/n`;
* second mean (`mean2`): `E[⟨a,a′⟩⁴/(|a|²|a′|²)] ≤ 12/(n(n−3))`, from `stdGauss_decomp` and the
  inverse moment `wE_moment_le` of Part 153 (`kernel_unit`, `kernel_vec`);
* diagonal: `C(a,a) = Var relu(μ + sZ) ≤ τ²|a|²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

/-- The constant of Lemma L1 (c) with the constant `K` of Lemma PR (i):
`(1 + K√(12/(n − 4)))² + 4(1 + 2/n)/n`. -/
noncomputable def cHSK (n : ℕ) (K : ℝ) : ℝ :=
  (1 + K * √(12 / ((n : ℝ) - 4))) ^ 2 + 4 * (1 + 2 / (n : ℝ)) / n

section aux

open BstLean.Part153 (dt sP wE sum_sub_sq sP_nonneg measurable_wE wE_moment_le invBd exists_unit
  integrable_of_bdd wE_pos wE_le rowLaw rowLaw_four rowV rowV_nonneg rowV_le vS nrm_nonneg nrm_sq
  psiS_one psiS_neg hasDerivAt_psiG hasDerivAt_PhiG PhiG_pos PhiG_le_one)
open BstLean.Part131 (stdGauss_decomp projMat projMat_mulVec projMat_dot)
open BstLean.Part29 (gaussMom gaussMom_eq)

/-! ## The kernel `E[(z·u)⁴/|z|²]` -/

private lemma kernel_ptw {x s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) :
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

private lemma meas_dot_L1c {n : ℕ} (b : Fin n → ℝ) : Measurable (fun a : Fin n → ℝ => a ⬝ᵥ b) := by
  unfold dotProduct; fun_prop

private lemma meas_dot'_L1c {n : ℕ} (b : Fin n → ℝ) :
    Measurable (fun a : Fin n → ℝ => b ⬝ᵥ a) := by
  unfold dotProduct; fun_prop

private lemma gaussMom_four : gaussMom 4 = 3 := by
  have : Even 4 := by decide
  simp [gaussMom, this, Nat.doubleFactorial]

private lemma gaussMom_two : gaussMom 2 = 1 := by
  simp [gaussMom, Nat.doubleFactorial]

private lemma kernel_unit {m : ℕ} (hm : 2 < m) {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) :
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

private lemma kernel_vec {n : ℕ} (hn : 4 ≤ n) (v : Fin n → ℝ) :
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

private lemma rl_sm (n : ℕ) : Measurable (fun ξ : Fin n → ℝ => √(2 / (n : ℝ)) • ξ) :=
  measurable_const_smul _

private lemma rl_int {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    ∫ a, F a ∂rowLaw n = ∫ z, F (√(2 / (n : ℝ)) • z) ∂stdGauss (Fin n) := by
  unfold rowLaw
  exact integral_map (rl_sm n).aemeasurable hF.aestronglyMeasurable

private lemma rl_itg {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    Integrable F (rowLaw n) ↔
      Integrable (fun z : Fin n → ℝ => F (√(2 / (n : ℝ)) • z)) (stdGauss (Fin n)) := by
  unfold rowLaw
  exact integrable_map_measure hF.aestronglyMeasurable (rl_sm n).aemeasurable

private lemma rl_neg (n : ℕ) : (rowLaw n).map (fun a : Fin n → ℝ => -a) = rowLaw n := by
  unfold rowLaw
  rw [Measure.map_map measurable_neg (rl_sm n)]
  have e : (fun a : Fin n → ℝ => -a) ∘ (fun ξ : Fin n → ℝ => √(2 / (n : ℝ)) • ξ) =
      (fun ξ : Fin n → ℝ => √(2 / (n : ℝ)) • ξ) ∘ (fun z : Fin n → ℝ => -z) := by
    funext ξ; simp
  rw [e, ← Measure.map_map (rl_sm n) measurable_neg, BstLean.Part135.stdGauss_neg]

private lemma rl_normSq {n : ℕ} (hn : 1 ≤ n) :
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

private lemma rl_dot2 {n : ℕ} (hn : 1 ≤ n) (b : Fin n → ℝ) :
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

private lemma PhiG_neg_L1c (v : ℝ) : PhiG (-v) = 1 - PhiG v := by
  have h1 : (fun x : ℝ => psiG (-x)) = fun x => psiG x - x := by
    funext x; rw [← psiS_one, ← psiS_one]; exact psiS_neg 1 x
  have d1 : HasDerivAt (fun x : ℝ => psiG (-x)) (PhiG (-v) * -1) v :=
    (hasDerivAt_psiG (-v)).comp v (hasDerivAt_neg v)
  have d2 : HasDerivAt (fun x : ℝ => psiG x - x) (PhiG v - 1) v :=
    (hasDerivAt_psiG v).sub (hasDerivAt_id v)
  rw [h1] at d1
  have := d1.unique d2
  linarith

private lemma continuous_PhiG_L1c : Continuous PhiG :=
  continuous_iff_continuousAt.2 fun v => (hasDerivAt_PhiG v).continuousAt

/-- `p(a) = Φ(⟨a, c⟩/(τ|a|))`. -/
private noncomputable def pR {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) : ℝ :=
  PhiG (a ⬝ᵥ c / nrm (τ • a))

private lemma meas_nrm_smul {n : ℕ} (τ : ℝ) : Measurable (fun a : Fin n → ℝ => nrm (τ • a)) :=
  (continuous_normSq.measurable.comp (measurable_const_smul τ)).sqrt

private lemma meas_pR {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Measurable (pR c τ) :=
  continuous_PhiG_L1c.measurable.comp ((meas_dot_L1c c).div (meas_nrm_smul τ))

private lemma pR_nonneg {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) : 0 ≤ pR c τ a :=
  (PhiG_pos _).le

private lemma pR_le_one {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) : pR c τ a ≤ 1 :=
  PhiG_le_one _

private lemma pR_neg {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : Fin n → ℝ) :
    pR c τ (-a) = 1 - pR c τ a := by
  unfold pR
  have e1 : nrm (τ • -a) = nrm (τ • a) := by
    unfold nrm normSq; simp
  rw [neg_dotProduct, e1, neg_div, PhiG_neg_L1c]

/-- The reflection `a ↦ −a`: `E[G(a)p(a)²] ≤ ½·E G(a)` for `G ≥ 0` even. -/
private lemma refl_le {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) {G : (Fin n → ℝ) → ℝ} (hG : Measurable G)
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

private lemma dot_sq_le_L1c {n : ℕ} (a a' : Fin n → ℝ) : (a ⬝ᵥ a') ^ 2 ≤ normSq a * normSq a' :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a a'

private lemma meas_dot2_L1c {n : ℕ} :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 ⬝ᵥ q.2) := by
  unfold dotProduct; fun_prop

private lemma itg_nn {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => normSq q.1 * normSq q.2)
      ((rowLaw n).prod (rowLaw n)) :=
  (rl_normSq hn).1.mul_prod (rl_normSq hn).1

private lemma mean1 {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
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
private noncomputable def Qf {n : ℕ} (q : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (q.1 ⬝ᵥ q.2) ^ 4 / (normSq q.1 * normSq q.2)

private lemma meas_Qf {n : ℕ} : Measurable (Qf (n := n)) :=
  (meas_dot2_L1c.pow_const 4).div ((continuous_normSq.measurable.comp measurable_fst).mul
    (continuous_normSq.measurable.comp measurable_snd))

private lemma Qf_nonneg {n : ℕ} (q : (Fin n → ℝ) × (Fin n → ℝ)) : 0 ≤ Qf q :=
  div_nonneg (by positivity) (mul_nonneg (normSq_nonneg _) (normSq_nonneg _))

private lemma Qf_le {n : ℕ} (q : (Fin n → ℝ) × (Fin n → ℝ)) : Qf q ≤ normSq q.1 * normSq q.2 := by
  have h1 := dot_sq_le_L1c q.1 q.2
  have hN := mul_nonneg (normSq_nonneg q.1) (normSq_nonneg q.2)
  unfold Qf
  rcases eq_or_lt_of_le hN with h0 | h0
  · rw [← h0, div_zero]
  · rw [div_le_iff₀ h0]
    have : (q.1 ⬝ᵥ q.2) ^ 4 = ((q.1 ⬝ᵥ q.2) ^ 2) ^ 2 := by ring
    rw [this, ← sq]
    exact pow_le_pow_left₀ (sq_nonneg _) h1 2

private lemma mean2 {n : ℕ} (hn : 4 ≤ n) :
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
private noncomputable def rowC {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a a' : Fin n → ℝ) : ℝ :=
  ∫ z, relu (a ⬝ᵥ c + z ⬝ᵥ (τ • a)) * relu (a' ⬝ᵥ c + z ⬝ᵥ (τ • a')) ∂stdGauss (Fin n) -
    psiS (nrm (τ • a)) (a ⬝ᵥ c) * psiS (nrm (τ • a')) (a' ⬝ᵥ c)

private lemma lin_facts {n : ℕ} (g : Fin n → ℝ) (x : ℝ) :
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

private lemma meas_rowC {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
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

private lemma cov_scale_L1c {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
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

private lemma fA_apply {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (ξ : Fin n → ℝ) (i : Fin m) :
    fA A₁ c τ ξ i =
      √(2 / (m : ℝ)) * relu (rowOf i A₁ ⬝ᵥ c + ξ ⬝ᵥ (τ • rowOf i A₁)) := by
  unfold fA reluV
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 2
  simp only [mulVec, dotProduct, rowOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma covF_eq {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
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

private lemma nrm_smul_L1c {n : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (a : Fin n → ℝ) :
    nrm (τ • a) = τ * √(∑ j, a j ^ 2) := by
  unfold nrm
  rw [normSq_smul, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ]
  rfl

private lemma rowC_self {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (a : Fin n → ℝ) :
    rowC c τ a a = rowV c τ a := by
  obtain ⟨-, -, -, e2⟩ := lin_facts (τ • a) (a ⬝ᵥ c)
  unfold rowC rowV vS
  simp_rw [← sq]
  rw [e2, nrm_smul_L1c hτ]
  rfl

private lemma rowC_sq_le {n : ℕ} {K : ℝ} (hK0 : 0 ≤ K) (hK : PRvecAbs K) (c : Fin n → ℝ) {τ : ℝ}
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

private lemma pair_map {n m : ℕ} {i j : Fin m} (hij : i ≠ j) :
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

private lemma int_offd_mat {n m : ℕ} {i j : Fin m} (hij : i ≠ j)
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

private lemma int_diag_mat {n m : ℕ} (i : Fin m) {G : (Fin n → ℝ) → ℝ} (hG : Measurable G)
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

private lemma opt_L1c {E A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
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

private lemma offd {n : ℕ} (hn : 8 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : PRvecAbs K) :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => rowC c τ q.1 q.2 ^ 2)
      ((rowLaw n).prod (rowLaw n)) ∧
    ∫ q : (Fin n → ℝ) × (Fin n → ℝ), rowC c τ q.1 q.2 ^ 2 ∂((rowLaw n).prod (rowLaw n)) ≤
      τ ^ 4 / (n : ℝ) * (1 + K * √(12 / ((n : ℝ) - 4))) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn4 : (0 : ℝ) < (n : ℝ) - 4 := by
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨i1, e1⟩ := mean1 hn1 c τ
  obtain ⟨i2, e2⟩ := mean2 (n := n) (by omega)
  have hm := (meas_rowC c τ).pow_const 2
  have ptw : ∀ κ : ℝ, 0 < κ → ∀ q : (Fin n → ℝ) × (Fin n → ℝ), rowC c τ q.1 q.2 ^ 2 ≤
      (1 + κ) * (τ ^ 4 * ((q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2)) +
        (1 + 1 / κ) * (K ^ 2 * (τ ^ 4 * Qf q)) :=
    fun κ hκ q => rowC_sq_le hK0 hK c hτ hκ q.1 q.2
  have iA : ∀ κ : ℝ, Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (1 + κ) * (τ ^ 4 * ((q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2)))
      ((rowLaw n).prod (rowLaw n)) := fun κ => (i1.const_mul _).const_mul _
  have iB : ∀ κ : ℝ, Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (1 + 1 / κ) * (K ^ 2 * (τ ^ 4 * Qf q))) ((rowLaw n).prod (rowLaw n)) := fun κ =>
    ((i2.const_mul _).const_mul _).const_mul _
  have iC : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => rowC c τ q.1 q.2 ^ 2)
      ((rowLaw n).prod (rowLaw n)) := by
    refine Integrable.mono' ((iA 1).add (iB 1)) hm.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact ptw 1 one_pos q
  refine ⟨iC, opt_L1c (by positivity) (mul_nonneg hK0 (Real.sqrt_nonneg _)) fun κ hκ => ?_⟩
  have iAB : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (1 + κ) * (τ ^ 4 * ((q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2)) +
        (1 + 1 / κ) * (K ^ 2 * (τ ^ 4 * Qf q))) ((rowLaw n).prod (rowLaw n)) := (iA κ).add (iB κ)
  have h := integral_mono iC iAB (ptw κ hκ)
  rw [integral_add (iA κ) (iB κ), integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul] at h
  have hs2 : (K * √(12 / ((n : ℝ) - 4))) ^ 2 = K ^ 2 * (12 / ((n : ℝ) - 4)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have e2' : ∫ q, Qf q ∂((rowLaw n).prod (rowLaw n)) ≤ 1 / (n : ℝ) * (12 / ((n : ℝ) - 4)) := by
    refine e2.trans ?_
    rw [div_mul_div_comm, one_mul]
    exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hnR hn4) (by nlinarith)
  have hκi : 0 < 1 / κ := one_div_pos.2 hκ
  have a1 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ τ ^ 4)) (by linarith : 0 ≤ 1 + κ)
  have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left e2' (by positivity : (0 : ℝ) ≤ τ ^ 4)) (sq_nonneg K))
    (by linarith : 0 ≤ 1 + 1 / κ)
  rw [hs2]
  have e : τ ^ 4 / (n : ℝ) * (1 + κ + (1 + 1 / κ) * (K ^ 2 * (12 / ((n : ℝ) - 4)))) =
      (1 + κ) * (τ ^ 4 * (1 / (n : ℝ))) +
        (1 + 1 / κ) * (K ^ 2 * (τ ^ 4 * (1 / (n : ℝ) * (12 / ((n : ℝ) - 4))))) := by ring
  rw [e]
  linarith

private lemma diagL {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
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

end aux

theorem measurable_hsH {n m : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => hsH A₁ c τ) := by
  unfold hsH hsF
  simp_rw [covF_eq]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (((meas_rowC c τ).comp ((measurable_rowOf i).prodMk (measurable_rowOf j))).const_mul _).pow_const 2

theorem hsH_nonneg {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    0 ≤ hsH A₁ c τ := by
  unfold hsH hsF
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- **Lemma L1 (c).** -/
theorem hsH_mean {n : ℕ} (hn : 8 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : PRvecAbs K) :
    Integrable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => hsH A₁ c τ)
      (gaussMat (mA n) n (2 / (n : ℝ))) ∧
    ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      4 * cHSK n K * τ ^ 4 / n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨iO, eO⟩ := offd hn c hτ hK0 hK
  obtain ⟨iD, eD⟩ := diagL hn1 c hτ.le
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 / ((mA n : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = τ ^ 4 / (n : ℝ) * (1 + K * √(12 / ((n : ℝ) - 4))) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Dg, hDg⟩ : ∃ Dg : ℝ, Dg = τ ^ 4 * (4 * (1 + 2 / (n : ℝ))) := ⟨_, rfl⟩
  rw [← hP] at eO
  rw [← hDg] at eD
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hD0 : 0 ≤ Dg := by rw [hDg]; positivity
  have mO : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (t * rowC c τ q.1 q.2) ^ 2) :=
    ((meas_rowC c τ).const_mul t).pow_const 2
  have mD : Measurable (fun a : Fin n → ℝ => (t * rowC c τ a a) ^ 2) :=
    (((meas_rowC c τ).comp (measurable_id.prodMk measurable_id)).const_mul t).pow_const 2
  have iO' : Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (t * rowC c τ q.1 q.2) ^ 2)
      ((BstLean.Part153.rowLaw n).prod (BstLean.Part153.rowLaw n)) := by
    simp_rw [mul_pow]; exact iO.const_mul _
  have iD' : Integrable (fun a : Fin n → ℝ => (t * rowC c τ a a) ^ 2) (BstLean.Part153.rowLaw n) := by
    simp_rw [mul_pow]; exact iD.const_mul _
  have key : ∀ i j : Fin (mA n),
      Integrable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        (t * rowC c τ (rowOf i A₁) (rowOf j A₁)) ^ 2) (gaussMat (mA n) n (2 / (n : ℝ))) ∧
      ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, (t * rowC c τ (rowOf i A₁) (rowOf j A₁)) ^ 2
        ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ t ^ 2 * (P + if i = j then Dg else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      obtain ⟨h1, h2⟩ := int_diag_mat (m := mA n) i mD iD'
      refine ⟨h1, ?_⟩
      rw [h2]
      simp only [↓reduceIte]
      simp_rw [mul_pow]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg t)
    · obtain ⟨h1, h2⟩ := int_offd_mat (m := mA n) hij mO iO'
      refine ⟨h1, ?_⟩
      rw [h2]
      simp only [hij, ↓reduceIte]
      simp_rw [mul_pow]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg t)
  have hsum : ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A₁ c τ =
      ∑ i, ∑ j, (t * rowC c τ (rowOf i A₁) (rowOf j A₁)) ^ 2 := by
    intro A₁
    unfold hsH hsF
    simp_rw [covF_eq, ht]
  simp_rw [hsum]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (key i j).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (key i j).1]
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  calc ∑ i, ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
        ∑ j, (t * rowC c τ (rowOf i A₁) (rowOf j A₁)) ^ 2 ∂gaussMat (mA n) n (2 / (n : ℝ))
      = ∑ i, ∑ j, ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
          (t * rowC c τ (rowOf i A₁) (rowOf j A₁)) ^ 2 ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => (key i j).1
    _ ≤ ∑ i : Fin (mA n), ∑ j : Fin (mA n), t ^ 2 * (P + if i = j then Dg else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (key i j).2
    _ = t ^ 2 * (((mA n : ℕ) : ℝ) ^ 2 * P + ((mA n : ℕ) : ℝ) * Dg) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
    _ = 4 * cHSK n K * τ ^ 4 / n := by
        rw [ht, hmR, hP, hDg]
        unfold cHSK
        field_simp
        ring

end BstLean.Part154
