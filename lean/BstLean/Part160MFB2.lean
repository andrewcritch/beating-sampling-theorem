import BstLean.Part160MFB1

/-!
# Part 160 (file `MFB2`): the improved mean of `‖H‖²_HS` (change (B))

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-05-centre.tex`, Lemma `t7:p05:HS`.

* `JB n c τ S₀ = (1 + 2|c|²/(τ²S₀))^{−1/2}`, `epsB = √3·e^{−6}`.
* `M1B = (1 − J/2 + ε/2)(1 − J(n − 1)/(2n) + ε/2) + J/(2n)`: the first pair mean in units `1/n`
  (Part 154: `1`; the paper: `q′² + 1/n`).
* `mean1B`: `E[⟨a, a′⟩² p² p′²] ≤ M1B/n`.
* `cHSB n K M₁ = (√M₁ + K√(12/(n − 4)))² + 4(1 + 2/n)/n`; `hsH_mean_B`.
-/

namespace BstLean.Part160.MFB

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part154 BstLean.Part160
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)
open BstLean.Part153 (rowLaw rowLaw_four rowV rowV_nonneg rowV_le vS nrm_nonneg nrm_sq)

/-- `J = (1 + 2|c|²/(τ²S₀))^{−1/2}`. -/
noncomputable def JB {n : ℕ} (c : Fin n → ℝ) (τ S0 : ℝ) : ℝ :=
  (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹

/-- `ε = √3·e^{−6}`. -/
noncomputable def epsB : ℝ := √3 * rexp (-6)

/-- The first pair mean in units `1/n`. -/
noncomputable def M1B (n : ℕ) (c : Fin n → ℝ) (τ S0 : ℝ) : ℝ :=
  (1 - JB c τ S0 / 2 + epsB / 2) * (1 - JB c τ S0 * (((n : ℝ) - 1) / (2 * n)) + epsB / 2) +
    JB c τ S0 / (2 * n)

/-- The constant of Lemma L1 (c) with the first pair mean `M₁`. -/
noncomputable def cHSB (n : ℕ) (K M1 : ℝ) : ℝ :=
  (√M1 + K * √(12 / ((n : ℝ) - 4))) ^ 2 + 4 * (1 + 2 / (n : ℝ)) / n

lemma epsB_pos : 0 < epsB := by unfold epsB; positivity

lemma JB_bounds {n : ℕ} (c : Fin n → ℝ) {τ S0 : ℝ} (hτ : 0 < τ) (hS0 : 0 < S0) :
    0 < JB c τ S0 ∧ JB c τ S0 ≤ 1 := by
  have h0 : 0 ≤ normSq c / (τ ^ 2 * S0) := div_nonneg (normSq_nonneg c) (by positivity)
  have h1 : (1 : ℝ) ≤ √(1 + 2 * (normSq c / (τ ^ 2 * S0))) :=
    Real.one_le_sqrt.mpr (by linarith)
  unfold JB
  exact ⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ h1⟩

lemma M1B_pos {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (_hc : 0 < normSq c) {τ S0 : ℝ} (hτ : 0 < τ)
    (hS0 : 0 < S0) : 0 < M1B n c τ S0 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hJ0, hJ1⟩ := JB_bounds c hτ hS0
  have he := epsB_pos
  have h1 : 0 ≤ 1 - JB c τ S0 / 2 + epsB / 2 := by linarith
  have hq : ((n : ℝ) - 1) / (2 * n) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hq0 : 0 ≤ ((n : ℝ) - 1) / (2 * n) := div_nonneg (by linarith) (by positivity)
  have h2 : 0 ≤ 1 - JB c τ S0 * (((n : ℝ) - 1) / (2 * n)) + epsB / 2 := by
    have : JB c τ S0 * (((n : ℝ) - 1) / (2 * n)) ≤ 1 * (1 / 2) := mul_le_mul hJ1 hq hq0 (by norm_num)
    linarith
  have h3 : 0 < JB c τ S0 / (2 * n) := by positivity
  unfold M1B
  have := mul_nonneg h1 h2
  linarith

/-- The optimisation over the Young parameter, with a first constant `M`. -/
lemma optM {E A M s : ℝ} (hA : 0 ≤ A) (hM : 0 < M) (hs : 0 ≤ s)
    (h : ∀ κ : ℝ, 0 < κ → E ≤ A * ((1 + κ) * M + (1 + 1 / κ) * s ^ 2)) :
    E ≤ A * (√M + s) ^ 2 := by
  have hsM : 0 < √M := Real.sqrt_pos.mpr hM
  have hM2 : √M ^ 2 = M := Real.sq_sqrt hM.le
  have h2 := opt_L1c (E := E) (A := A * M) (s := s / √M) (mul_nonneg hA hM.le)
    (div_nonneg hs hsM.le) (fun κ hκ => by
      have := h κ hκ
      have e : A * M * ((1 + κ) + (1 + 1 / κ) * (s / √M) ^ 2) =
          A * ((1 + κ) * M + (1 + 1 / κ) * s ^ 2) := by
        rw [div_pow, hM2]; field_simp
      rw [e]; exact this)
  have e2 : A * M * (1 + s / √M) ^ 2 = A * (√M + s) ^ 2 := by
    have : (1 + s / √M) ^ 2 = (√M + s) ^ 2 / M := by
      rw [← hM2, ← div_pow, hM2]; congr 1; field_simp
    rw [this]; field_simp
  rw [e2] at h2
  exact h2

/-- The reflection identity: `E[G p²] = ½·E G − E[G p(1 − p)]` for an even `G ≥ 0`. -/
lemma refl_eq {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) {G : (Fin n → ℝ) → ℝ} (hG : Measurable G)
    (h0 : ∀ a, 0 ≤ G a) (hev : ∀ a, G (-a) = G a) (hi : Integrable G (rowLaw n)) :
    Integrable (fun a => G a * pR c τ a ^ 2) (rowLaw n) ∧
    Integrable (fun a => G a * (pR c τ a * (1 - pR c τ a))) (rowLaw n) ∧
    ∫ a, G a * pR c τ a ^ 2 ∂rowLaw n =
      1 / 2 * ∫ a, G a ∂rowLaw n - ∫ a, G a * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
  have hp := meas_pR c τ
  have hm : Measurable (fun a => G a * pR c τ a ^ 2) := hG.mul (hp.pow_const 2)
  have hm2 : Measurable (fun a => G a * (1 - pR c τ a) ^ 2) :=
    hG.mul ((measurable_const.sub hp).pow_const 2)
  have hm3 : Measurable (fun a => G a * (pR c τ a * (1 - pR c τ a))) :=
    hG.mul (hp.mul (measurable_const.sub hp))
  have i1 : Integrable (fun a => G a * pR c τ a ^ 2) (rowLaw n) := (refl_le c τ hG h0 hev hi).1
  have i2 : Integrable (fun a => G a * (1 - pR c τ a) ^ 2) (rowLaw n) := by
    refine Integrable.mono' hi hm2.aestronglyMeasurable (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 a) (sq_nonneg _))]
    exact mul_le_of_le_one_right (h0 a)
      (pow_le_one₀ (sub_nonneg.2 (pR_le_one c τ a)) (by linarith [pR_nonneg c τ a]))
  have i3 : Integrable (fun a => G a * (pR c τ a * (1 - pR c τ a))) (rowLaw n) := by
    refine Integrable.mono' hi hm3.aestronglyMeasurable (ae_of_all _ fun a => ?_)
    have hp0 := pR_nonneg c τ a
    have hp1 := pR_le_one c τ a
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 a) (mul_nonneg hp0 (by linarith)))]
    refine mul_le_of_le_one_right (h0 a) ?_
    nlinarith
  refine ⟨i1, i3, ?_⟩
  have e1 : ∫ a, G a * pR c τ a ^ 2 ∂rowLaw n = ∫ a, G a * (1 - pR c τ a) ^ 2 ∂rowLaw n := by
    have h := integral_map (μ := rowLaw n)
      (measurable_neg : Measurable (fun a : Fin n → ℝ => -a)).aemeasurable hm.aestronglyMeasurable
    rw [rl_neg] at h
    rw [h]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [hev, pR_neg]
  have hsum : ∫ a, G a ∂rowLaw n = ∫ a, G a * pR c τ a ^ 2 ∂rowLaw n +
      ∫ a, G a * (1 - pR c τ a) ^ 2 ∂rowLaw n +
      2 * ∫ a, G a * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    have hA : ∫ a, (G a * pR c τ a ^ 2 + G a * (1 - pR c τ a) ^ 2 +
        2 * (G a * (pR c τ a * (1 - pR c τ a)))) ∂rowLaw n =
        ∫ a, (G a * pR c τ a ^ 2 + G a * (1 - pR c τ a) ^ 2) ∂rowLaw n +
        ∫ a, 2 * (G a * (pR c τ a * (1 - pR c τ a))) ∂rowLaw n :=
      integral_add (i1.add i2) (i3.const_mul 2)
    have hB : ∫ a, (G a * pR c τ a ^ 2 + G a * (1 - pR c τ a) ^ 2) ∂rowLaw n =
        ∫ a, G a * pR c τ a ^ 2 ∂rowLaw n + ∫ a, G a * (1 - pR c τ a) ^ 2 ∂rowLaw n :=
      integral_add i1 i2
    have hC : ∫ a, G a ∂rowLaw n = ∫ a, (G a * pR c τ a ^ 2 + G a * (1 - pR c τ a) ^ 2 +
        2 * (G a * (pR c τ a * (1 - pR c τ a)))) ∂rowLaw n :=
      integral_congr_ae (ae_of_all _ fun a => by ring)
    rw [hC, hA, hB, integral_const_mul]
  rw [← e1] at hsum
  linarith

/-- The inner mean for a fixed row `a`. -/
lemma innerB {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) (a : Fin n → ℝ) :
    ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a' ^ 2 ∂rowLaw n ≤
      1 / (n : ℝ) * ((1 - JB c τ S0 / 2 + epsB / 2) * normSq a +
        JB c τ S0 / 2 * ((a ⬝ᵥ c) ^ 2 / normSq c)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨iD, eD⟩ := rl_dot2 hn a
  obtain ⟨-, -, hR⟩ := refl_eq c τ ((meas_dot'_L1c a).pow_const 2) (fun a' => sq_nonneg _)
    (fun a' => by rw [dotProduct_neg, neg_sq]) iD
  obtain ⟨-, hK⟩ := keyK hn c hc hτ a hS0 hS
  rw [hR, eD]
  unfold JB epsB
  have e : 1 / 4 * (2 / (n : ℝ)) * ((normSq a - (a ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹ - √3 * rexp (-6) * normSq a) =
      1 / (n : ℝ) * (1 / 2 * ((normSq a - (a ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹ - √3 * rexp (-6) * normSq a)) := by ring
  rw [e] at hK
  have e2 : 1 / 2 * (2 / (n : ℝ) * normSq a) = 1 / (n : ℝ) * normSq a := by ring
  rw [e2]
  have e3 : 1 / (n : ℝ) * ((1 - (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹ / 2 +
        √3 * rexp (-6) / 2) * normSq a +
        (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹ / 2 * ((a ⬝ᵥ c) ^ 2 / normSq c)) =
      1 / (n : ℝ) * normSq a - 1 / (n : ℝ) * (1 / 2 * ((normSq a - (a ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * (normSq c / (τ ^ 2 * S0))))⁻¹ - √3 * rexp (-6) * normSq a)) := by ring
  rw [e3]
  linarith

/-- `E[|a|² p²] ≤ 1 − J(n − 1)/(2n) + ε/2`. -/
lemma normB {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) :
    Integrable (fun a => normSq a * pR c τ a ^ 2) (rowLaw n) ∧
    ∫ a, normSq a * pR c τ a ^ 2 ∂rowLaw n ≤
      1 - JB c τ S0 * (((n : ℝ) - 1) / (2 * n)) + epsB / 2 := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨iN, eN⟩ := rl_normSq hn
  obtain ⟨i1, i3, hR⟩ := refl_eq c τ (continuous_normSq.measurable) normSq_nonneg
    BstLean.Part135.normSq_neg iN
  refine ⟨i1, ?_⟩
  rw [hR, eN]
  -- `|a|² = Σ_k ⟨e_k, a⟩²`
  have hcoord : ∀ a : Fin n → ℝ, normSq a * (pR c τ a * (1 - pR c τ a)) =
      ∑ k : Fin n, ((Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ a) ^ 2 *
        (pR c τ a * (1 - pR c τ a)) := by
    intro a
    rw [← Finset.sum_mul]
    congr 1
    unfold normSq
    exact Finset.sum_congr rfl fun k _ => by rw [single_dotProduct, one_mul]
  have hk : ∀ k : Fin n, Integrable (fun a => ((Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ a) ^ 2 *
      (pR c τ a * (1 - pR c τ a))) (rowLaw n) ∧
      1 / 4 * (2 / (n : ℝ)) * ((1 - c k ^ 2 / normSq c) * JB c τ S0 - epsB) ≤
        ∫ a, ((Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ a) ^ 2 *
          (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    intro k
    obtain ⟨hi, hb⟩ := keyK hn c hc hτ (Pi.single k (1 : ℝ)) hS0 hS
    refine ⟨hi, ?_⟩
    have e1 : normSq (Pi.single k (1 : ℝ) : Fin n → ℝ) = 1 := by
      unfold normSq
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun h => absurd (Finset.mem_univ k) h)]
      simp
    have e2 : (Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ c = c k := by
      rw [single_dotProduct, one_mul]
    rw [e1, e2] at hb
    unfold JB epsB
    linarith
  have hsumI : ∫ a, normSq a * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n =
      ∑ k : Fin n, ∫ a, ((Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ a) ^ 2 *
        (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    simp_rw [hcoord]
    exact integral_finsetSum _ fun k _ => (hk k).1
  have hlow : 1 / 4 * (2 / (n : ℝ)) * (((n : ℝ) - 1) * JB c τ S0 - n * epsB) ≤
      ∫ a, normSq a * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    rw [hsumI]
    have h1 := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => (hk k).2)
    refine le_trans (le_of_eq ?_) h1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
      ← Finset.sum_div]
    have hcs : ∑ k : Fin n, c k ^ 2 = normSq c := rfl
    rw [hcs, div_self hc.ne']
    simp
  have e : 1 / 4 * (2 / (n : ℝ)) * (((n : ℝ) - 1) * JB c τ S0 - n * epsB) =
      JB c τ S0 * (((n : ℝ) - 1) / (2 * n)) - epsB / 2 := by
    field_simp; ring
  rw [e] at hlow
  linarith

/-- **The first pair mean with the reflection gain on both rows**:
`E[⟨a, a′⟩² p² p′²] ≤ M1B/n`. -/
lemma mean1B {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2) ((rowLaw n).prod (rowLaw n)) ∧
    ∫ q : (Fin n → ℝ) × (Fin n → ℝ), (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2
      ∂((rowLaw n).prod (rowLaw n)) ≤ 1 / (n : ℝ) * M1B n c τ S0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hI, -⟩ := mean1 hn c τ
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  obtain ⟨hJ0, hJ1⟩ := JB_bounds c hτ hS0
  have he := epsB_pos
  obtain ⟨iR, hR⟩ := normB hn c hc hτ hS0 hS
  obtain ⟨iC, eC⟩ := rl_dot2 hn c
  obtain ⟨iA, hA⟩ := refl_le c τ ((meas_dot'_L1c c).pow_const 2) (fun a => sq_nonneg _)
    (fun a => by rw [dotProduct_neg, neg_sq]) iC
  rw [eC] at hA
  have h0 : ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
      0 ≤ (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2 := fun q => by positivity
  have inner : ∀ a : Fin n → ℝ,
      ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 ∂rowLaw n ≤
        1 / (n : ℝ) * ((1 - JB c τ S0 / 2 + epsB / 2) * (normSq a * pR c τ a ^ 2) +
          JB c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2)) := by
    intro a
    have hin := innerB hn c hc hτ hS0 hS a
    have e : ∀ a' : Fin n → ℝ, (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 =
        pR c τ a ^ 2 * ((a ⬝ᵥ a') ^ 2 * pR c τ a' ^ 2) := fun a' => by ring
    simp_rw [e]
    rw [integral_const_mul]
    have := mul_le_mul_of_nonneg_left hin (sq_nonneg (pR c τ a))
    refine this.trans (le_of_eq ?_)
    rw [dotProduct_comm c a]
    field_simp
  have iB : Integrable (fun a : Fin n → ℝ =>
      1 / (n : ℝ) * ((1 - JB c τ S0 / 2 + epsB / 2) * (normSq a * pR c τ a ^ 2) +
        JB c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2))) (rowLaw n) :=
    ((iR.const_mul _).add (iA.const_mul _)).const_mul _
  have hmain := integral_mono_of_nonneg
    (f := fun a : Fin n → ℝ => ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 ∂rowLaw n)
    (ae_of_all _ fun a => integral_nonneg fun a' => h0 (a, a')) iB (ae_of_all _ inner)
  refine hmain.trans ?_
  have hsplit : ∫ a : Fin n → ℝ,
      1 / (n : ℝ) * ((1 - JB c τ S0 / 2 + epsB / 2) * (normSq a * pR c τ a ^ 2) +
        JB c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2)) ∂rowLaw n =
      1 / (n : ℝ) * ((1 - JB c τ S0 / 2 + epsB / 2) * ∫ a, normSq a * pR c τ a ^ 2 ∂rowLaw n +
        JB c τ S0 / 2 / normSq c * ∫ a, (c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2 ∂rowLaw n) := by
    rw [integral_const_mul]
    congr 1
    have hA2 : ∫ a : Fin n → ℝ, ((1 - JB c τ S0 / 2 + epsB / 2) * (normSq a * pR c τ a ^ 2) +
        JB c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2)) ∂rowLaw n =
        ∫ a : Fin n → ℝ, (1 - JB c τ S0 / 2 + epsB / 2) * (normSq a * pR c τ a ^ 2) ∂rowLaw n +
        ∫ a : Fin n → ℝ, JB c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2) ∂rowLaw n :=
      integral_add (iR.const_mul _) (iA.const_mul _)
    rw [hA2, integral_const_mul, integral_const_mul]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hc1 : 0 ≤ 1 - JB c τ S0 / 2 + epsB / 2 := by linarith
  have t1 := mul_le_mul_of_nonneg_left hR hc1
  have hc2 : 0 ≤ JB c τ S0 / 2 / normSq c := by positivity
  have t2 := mul_le_mul_of_nonneg_left hA hc2
  have e2 : JB c τ S0 / 2 / normSq c * (1 / 2 * (2 / (n : ℝ) * normSq c)) =
      JB c τ S0 / (2 * n) := by field_simp
  rw [e2] at t2
  unfold M1B
  linarith

lemma offdB {n : ℕ} (hn : 8 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : PRvecAbs K) :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => rowC c τ q.1 q.2 ^ 2)
      ((rowLaw n).prod (rowLaw n)) ∧
    ∫ q : (Fin n → ℝ) × (Fin n → ℝ), rowC c τ q.1 q.2 ^ 2 ∂((rowLaw n).prod (rowLaw n)) ≤
      τ ^ 4 / (n : ℝ) * (√(M1B n c τ S0) + K * √(12 / ((n : ℝ) - 4))) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn4 : (0 : ℝ) < (n : ℝ) - 4 := by
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨i1, e1⟩ := mean1B hn1 c hc hτ hS0 hS
  have hM0 := M1B_pos hn1 c hc hτ hS0
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
  refine ⟨iC, optM (by positivity) hM0 (mul_nonneg hK0 (Real.sqrt_nonneg _)) fun κ hκ => ?_⟩
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
  have e : τ ^ 4 / (n : ℝ) * ((1 + κ) * M1B n c τ S0 +
        (1 + 1 / κ) * (K ^ 2 * (12 / ((n : ℝ) - 4)))) =
      (1 + κ) * (τ ^ 4 * (1 / (n : ℝ) * M1B n c τ S0)) +
        (1 + 1 / κ) * (K ^ 2 * (τ ^ 4 * (1 / (n : ℝ) * (12 / ((n : ℝ) - 4))))) := by ring
  rw [e]
  linarith

/-- **Lemma L1 (c) with the improved first pair mean** (change (B), Lemma `t7:p05:HS`):
`E_{A₁}‖H‖²_HS ≤ 4·cHSB·τ⁴/n`, `cHSB = (√M₁ + K√(12/(n − 4)))² + 4(1 + 2/n)/n`. -/
theorem hsH_mean_B {n : ℕ} (hn : 8 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : PRvecAbs K) :
    Integrable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => hsH A₁ c τ)
      (gaussMat (mA n) n (2 / (n : ℝ))) ∧
    ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      4 * cHSB n K (M1B n c τ S0) * τ ^ 4 / n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨iO, eO⟩ := offdB hn c hc hτ hS0 hS hK0 hK
  obtain ⟨iD, eD⟩ := diagL hn1 c hτ.le
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 / ((mA n : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = τ ^ 4 / (n : ℝ) * (√(M1B n c τ S0) + K * √(12 / ((n : ℝ) - 4))) ^ 2 :=
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
    _ = 4 * cHSB n K (M1B n c τ S0) * τ ^ 4 / n := by
        rw [ht, hmR, hP, hDg]
        unfold cHSB
        field_simp
        ring

end BstLean.Part160.MFB

open BstLean.Part160.MFB in
#print axioms mean1B
open BstLean.Part160.MFB in
#print axioms hsH_mean_B
