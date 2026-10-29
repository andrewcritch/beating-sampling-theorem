import BstLean.Part154App

/-!
# Part 154: Lemma MA (ii) and the events `E_D`, `E_Π`, `E_Pb` of `A₂` (for a fixed `A₁`)
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)
open BstLean.Part153 (nrm_nonneg nrm_sq relu_sub_sq abs_dot_le_nrm nrm_add_le abs_nrm_sub_le
  nrm_smul nrm_mulVec_le continuous_h1 integrable_h1_sq GamS_nonneg h1n memLp_h1n GamS_eq_gO
  GamBar_le Pb_lip conc_upper_strict conc_lower_strict conc_abs_strict measurable_GamS
  measurable_Pb_joint measurable_int_Pb)

variable {n m : ℕ}

private lemma abs_relu_sub_le_Lip (a b : ℝ) : |relu a - relu b| ≤ |a - b| :=
  sq_le_sq.mp (relu_sub_sq a b)

private lemma prob_stdGauss_Lip (n : ℕ) : IsProbabilityMeasure (stdGauss (Fin n)) := by
  unfold stdGauss; infer_instance

private lemma hid2_sub_le_Lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ)
    (y : Fin n → ℝ) (j : Fin m) :
    |hid2 A₁ A₂ y j - hid2 A₁ A₂' y j| ≤
      nrm (fun k => A₂ j k - A₂' j k) * nrm (reluV (A₁ *ᵥ y)) := by
  have h := abs_relu_sub_le_Lip ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) ((A₂' *ᵥ reluV (A₁ *ᵥ y)) j)
  have e : (A₂ *ᵥ reluV (A₁ *ᵥ y)) j - (A₂' *ᵥ reluV (A₁ *ᵥ y)) j =
      (fun k => A₂ j k - A₂' j k) ⬝ᵥ reluV (A₁ *ᵥ y) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e] at h
  exact h.trans (abs_dot_le_nrm _ _)

private lemma integrable_h1n_Lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (h1n A₁ c τ) (stdGauss (Fin n)) := by
  have := prob_stdGauss_Lip n
  exact (memLp_h1n A₁ c τ).integrable one_le_two

private lemma integrable_hid2_Lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (j : Fin m) :
    Integrable (fun ξ => hid2 A₁ A₂ (c + τ • ξ) j) (stdGauss (Fin n)) := by
  have hc : Continuous (fun ξ : Fin n → ℝ => reluV (A₂ *ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) j) :=
    (continuous_apply j).comp (continuous_reluV.comp
      (Continuous.matrix_mulVec continuous_const (continuous_h1 A₁ c τ)))
  refine Integrable.mono' ((integrable_h1n_Lip A₁ c τ).const_mul (nrm (fun k => A₂ j k)))
    hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  have h := abs_relu_sub_le_Lip ((A₂ *ᵥ reluV (A₁ *ᵥ (c + τ • ξ))) j) 0
  have h0 : relu 0 = 0 := by simp [relu]
  rw [h0, sub_zero, sub_zero] at h
  exact h.trans (abs_dot_le_nrm _ _)

private lemma int_h1n_sq_le_Lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    (∫ ξ, h1n A₁ c τ ξ ∂stdGauss (Fin n)) ^ 2 ≤
      ∫ ξ, normSq (reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n) := by
  have := prob_stdGauss_Lip n
  have hi1 := integrable_h1n_Lip A₁ c τ
  have hi2 := integrable_h1_sq A₁ c τ
  obtain ⟨e, he⟩ : ∃ e, e = ∫ ξ, h1n A₁ c τ ξ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← he]
  have h0 : 0 ≤ ∫ ξ, (h1n A₁ c τ ξ - e) ^ 2 ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => sq_nonneg _
  have e1 : ∀ ξ, (h1n A₁ c τ ξ - e) ^ 2 =
      normSq (reluV (A₁ *ᵥ (c + τ • ξ))) - 2 * e * h1n A₁ c τ ξ + e ^ 2 := fun ξ => by
    rw [sub_sq]
    unfold h1n
    rw [nrm_sq]
    ring
  simp_rw [e1] at h0
  have ea := integral_add (μ := stdGauss (Fin n))
    (f := fun ξ => normSq (reluV (A₁ *ᵥ (c + τ • ξ))) - 2 * e * h1n A₁ c τ ξ)
    (g := fun _ => e ^ 2) (hi2.sub (hi1.const_mul _)) (integrable_const _)
  have eb := integral_sub (μ := stdGauss (Fin n))
    (f := fun ξ => normSq (reluV (A₁ *ᵥ (c + τ • ξ))))
    (g := fun ξ => 2 * e * h1n A₁ c τ ξ) hi2 (hi1.const_mul _)
  rw [ea, eb, integral_const_mul, ← he] at h0
  simp at h0
  nlinarith [h0]

theorem hbar2_lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ) :
    √(2 / (m : ℝ)) * nrm (hbar2 A₁ A₂ c τ - hbar2 A₁ A₂' c τ) ≤
      √(GamS A₁ c τ) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by

  obtain ⟨E, hE⟩ : ∃ E, E = ∫ ξ, h1n A₁ c τ ξ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  have hcoord : ∀ j, (hbar2 A₁ A₂ c τ j - hbar2 A₁ A₂' c τ j) ^ 2 ≤
      normSq (fun k => A₂ j k - A₂' j k) * E ^ 2 := by
    intro j
    have e1 : hbar2 A₁ A₂ c τ j - hbar2 A₁ A₂' c τ j =
        ∫ ξ, (hid2 A₁ A₂ (c + τ • ξ) j - hid2 A₁ A₂' (c + τ • ξ) j) ∂stdGauss (Fin n) :=
      (integral_sub (integrable_hid2_Lip A₁ A₂ c τ j) (integrable_hid2_Lip A₁ A₂' c τ j)).symm
    have h2 : |∫ ξ, (hid2 A₁ A₂ (c + τ • ξ) j - hid2 A₁ A₂' (c + τ • ξ) j) ∂stdGauss (Fin n)| ≤
        nrm (fun k => A₂ j k - A₂' j k) * E := by
      refine abs_integral_le_integral_abs.trans ?_
      rw [hE, ← integral_const_mul]
      exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => abs_nonneg _)
        ((integrable_h1n_Lip A₁ c τ).const_mul _)
        (Filter.Eventually.of_forall fun ξ => hid2_sub_le_Lip A₁ A₂ A₂' _ j)
    rw [e1, ← nrm_sq, ← mul_pow]
    exact sq_le_sq.mpr (h2.trans (le_abs_self _))
  have hsum : normSq (hbar2 A₁ A₂ c τ - hbar2 A₁ A₂' c τ) ≤
      (∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) * E ^ 2 := by
    unfold normSq
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hcoord j
  have hE2 := int_h1n_sq_le_Lip A₁ c τ
  rw [← hE] at hE2
  have hF0 : 0 ≤ ∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have key : 2 / (m : ℝ) * normSq (hbar2 A₁ A₂ c τ - hbar2 A₁ A₂' c τ) ≤
      GamS A₁ c τ * ∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2 := by
    unfold GamS
    calc 2 / (m : ℝ) * normSq (hbar2 A₁ A₂ c τ - hbar2 A₁ A₂' c τ)
        ≤ 2 / (m : ℝ) * ((∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) * E ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 2 / (m : ℝ) * ((∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) *
            ∫ ξ, normSq (reluV (A₁ *ᵥ (c + τ • ξ))) ∂stdGauss (Fin n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE2 hF0) (by positivity)
      _ = _ := by ring
  calc √(2 / (m : ℝ)) * nrm (hbar2 A₁ A₂ c τ - hbar2 A₁ A₂' c τ)
      = √(2 / (m : ℝ) * normSq (hbar2 A₁ A₂ c τ - hbar2 A₁ A₂' c τ)) := by
        unfold nrm
        rw [Real.sqrt_mul (by positivity)]
    _ ≤ √(GamS A₁ c τ * ∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := Real.sqrt_le_sqrt key
    _ = _ := Real.sqrt_mul (GamS_nonneg _ _ _) _

private lemma sqrt_hO_le_Lip (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) : √(2 / (m : ℝ)) * nrm (hO A₁ c τ) ≤ √(GamS A₁ c τ) := by
  have e : √(2 / (m : ℝ)) * nrm (hO A₁ c τ) = √(2 / (m : ℝ) * normSq (hO A₁ c τ)) := by
    unfold nrm
    rw [Real.sqrt_mul (by positivity)]
  rw [e, GamS_eq_gO hm]
  exact Real.sqrt_le_sqrt (GamBar_le A₁ c τ)

private lemma nrm_sub_le_Lip {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    nrm (u - v) ≤ nrm u + nrm v := by
  have h := nrm_add_le u ((-1 : ℝ) • v)
  rw [nrm_smul] at h
  have e : u + (-1 : ℝ) • v = u - v := by
    ext i
    simp [sub_eq_add_neg]
  rw [e] at h
  simpa using h

theorem bO_lip (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ) :
    √(2 / (m : ℝ)) * nrm (bO A₁ A₂ c τ - bO A₁ A₂' c τ) ≤
      √(GamS A₁ c τ) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by

  have h2 : nrm (bO A₁ A₂ c τ - bO A₁ A₂' c τ) ≤ nrm ((A₂ - A₂') *ᵥ hO A₁ c τ) := by
    unfold nrm
    refine Real.sqrt_le_sqrt ?_
    unfold normSq
    refine Finset.sum_le_sum fun j _ => ?_
    have := BstLean.Part141.psiS_lip_x (sO A₁ c τ) ((A₂ *ᵥ hO A₁ c τ) j) ((A₂' *ᵥ hO A₁ c τ) j)
    rw [Matrix.sub_mulVec]
    simp only [Pi.sub_apply, bO]
    exact sq_le_sq.mpr this
  have h3 := nrm_mulVec_le (A₂ - A₂') (hO A₁ c τ)
  have h4 := opN_le_frob (A₂ - A₂')
  simp only [Matrix.sub_apply] at h4
  have h5 := sqrt_hO_le_Lip hm A₁ c τ
  have hF := Real.sqrt_nonneg (∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2)
  calc √(2 / (m : ℝ)) * nrm (bO A₁ A₂ c τ - bO A₁ A₂' c τ)
      ≤ √(2 / (m : ℝ)) * (√(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) * nrm (hO A₁ c τ)) :=
        mul_le_mul_of_nonneg_left (h2.trans (h3.trans
          (mul_le_mul_of_nonneg_right h4 (nrm_nonneg _)))) (Real.sqrt_nonneg _)
    _ = (√(2 / (m : ℝ)) * nrm (hO A₁ c τ)) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h5 hF

/-- **Lemma MA (ii)**: `|𝐝|` is Lipschitz in `A₂` with the constant `2√Γ`. -/
theorem dC_lip (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ) :
    |dC A₁ A₂ c τ - dC A₁ A₂' c τ| ≤
      2 * √(GamS A₁ c τ) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by

  unfold dC
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := abs_nrm_sub_le (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ) (hbar2 A₁ A₂' c τ - bO A₁ A₂' c τ)
  have e : hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ - (hbar2 A₁ A₂' c τ - bO A₁ A₂' c τ) =
      (hbar2 A₁ A₂ c τ - hbar2 A₁ A₂' c τ) - (bO A₁ A₂ c τ - bO A₁ A₂' c τ) := by abel
  rw [e] at h1
  have h2 := nrm_sub_le_Lip (hbar2 A₁ A₂ c τ - hbar2 A₁ A₂' c τ) (bO A₁ A₂ c τ - bO A₁ A₂' c τ)
  have h3 := hbar2_lip A₁ c τ A₂ A₂'
  have h4 := bO_lip hm A₁ c τ A₂ A₂'
  have h5 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.sqrt_nonneg (2 / (m : ℝ)))
  rw [mul_add] at h5
  linarith

theorem Ph_lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ) :
    |Ph A₁ A₂ c τ - Ph A₁ A₂' c τ| ≤
      √(GamS A₁ c τ) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by

  unfold Ph
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := abs_nrm_sub_le (hbar2 A₁ A₂ c τ) (hbar2 A₁ A₂' c τ)
  exact (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)).trans (hbar2_lip A₁ c τ A₂ A₂')

/-- `Δ_𝖯 = 𝖯_h − 𝖯_b`. -/
noncomputable def DelP (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ := Ph A₁ A₂ c τ - Pb A₁ c τ A₂

/-- The complement of `E_D`. -/
def BadD (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A₂ | ∫ A₂, dC A₁ A₂ c τ ∂gaussMat m m (2 / (m : ℝ)) +
      √(2 * Lc * (2 / (m : ℝ))) * (2 * √(GamS A₁ c τ)) < dC A₁ A₂ c τ}

/-- The complement of `E_Π`. -/
def BadPi (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A₂ | √(2 * Lc * (2 / (m : ℝ))) * (2 * √(GamS A₁ c τ)) <
    |DelP A₁ A₂ c τ - ∫ A₂, DelP A₁ A₂ c τ ∂gaussMat m m (2 / (m : ℝ))|}

/-- The complement of `E_Pb`. -/
def BadPb (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A₂ | Pb A₁ c τ A₂ < ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat m m (2 / (m : ℝ)) -
      √(2 * Lc * (2 / (m : ℝ))) * √(GamS A₁ c τ)}

private lemma Pb_lip_Lip (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ) :
    |Pb A₁ c τ A₂ - Pb A₁ c τ A₂'| ≤
      √(GamS A₁ c τ) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) :=
  (Pb_lip A₁ c τ A₂ A₂').trans
    (mul_le_mul_of_nonneg_right (sqrt_hO_le_Lip hm A₁ c τ) (Real.sqrt_nonneg _))

private lemma DelP_lip_Lip (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ) :
    |DelP A₁ A₂ c τ - DelP A₁ A₂' c τ| ≤
      2 * √(GamS A₁ c τ) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by
  have h1 := abs_le.mp (Ph_lip A₁ c τ A₂ A₂')
  have h2 := abs_le.mp (Pb_lip_Lip hm A₁ c τ A₂ A₂')
  unfold DelP
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Variance and integrability of a Lipschitz function of a Gaussian matrix. -/
private lemma var_gen_Lip {p q : ℕ} {g : Matrix (Fin p) (Fin q) ℝ → ℝ} {L v : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin p) (Fin q) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2)) (hv : 0 ≤ v) :
    Integrable g (gaussMat p q v) ∧ Integrable (fun M => g M ^ 2) (gaussMat p q v) ∧
    ∫ M, g M ^ 2 ∂gaussMat p q v - (∫ M, g M ∂gaussMat p q v) ^ 2 ≤ v * L ^ 2 := by
  obtain ⟨hvi, hvb⟩ := gaussVar_mat_le_sharp hL0 hL hv
  have hgc := BstLean.Part148.matLip_continuous hL
  obtain ⟨e, he⟩ : ∃ e, e = ∫ M, g M ∂gaussMat p q v := ⟨_, rfl⟩
  rw [← he] at hvi hvb ⊢
  have hgi : Integrable g (gaussMat p q v) := by
    refine Integrable.mono' (hvi.add (integrable_const (1 + |e|))) hgc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun M => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |g M| ≤ |g M - e| + |e| := by
      have := abs_add_le (g M - e) e
      simpa using this
    have h2 : |g M - e| ≤ (g M - e) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|g M - e| - 1), sq_abs (g M - e), abs_nonneg (g M - e)]
    simp only [Pi.add_apply]
    linarith
  have hg2 : Integrable (fun M => g M ^ 2) (gaussMat p q v) := by
    have e2 : (fun M => g M ^ 2) = fun M => (g M - e) ^ 2 + (2 * e * g M - e ^ 2) := by
      funext M
      ring
    rw [e2]
    exact hvi.add ((hgi.const_mul _).sub (integrable_const _))
  refine ⟨hgi, hg2, ?_⟩
  have e1 : ∀ M, (g M - e) ^ 2 = g M ^ 2 - 2 * e * g M + e ^ 2 := fun M => by ring
  simp_rw [e1] at hvb
  have ea := integral_add (μ := gaussMat p q v)
    (f := fun M => g M ^ 2 - 2 * e * g M) (g := fun _ => e ^ 2)
    (hg2.sub (hgi.const_mul _)) (integrable_const _)
  have eb := integral_sub (μ := gaussMat p q v)
    (f := fun M => g M ^ 2) (g := fun M => 2 * e * g M) hg2 (hgi.const_mul _)
  rw [ea, eb, integral_const_mul, ← he] at hvb
  simp at hvb
  nlinarith [hvb]

theorem ED_prob (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ}
    (hLc : 0 ≤ Lc) : (gaussMat m m (2 / (m : ℝ))).real (BadD A₁ c τ Lc) ≤ rexp (-Lc) := by

  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  exact conc_upper_strict (g := fun A₂ => dC A₁ A₂ c τ) (by positivity) (dC_lip hm A₁ c τ) hv hLc

theorem EPi_prob (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ}
    (hLc : 0 ≤ Lc) : (gaussMat m m (2 / (m : ℝ))).real (BadPi A₁ c τ Lc) ≤ 2 * rexp (-Lc) := by

  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  exact conc_abs_strict (g := fun A₂ => DelP A₁ A₂ c τ) (by positivity)
    (DelP_lip_Lip hm A₁ c τ) hv hLc

theorem EPb_prob (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ}
    (hLc : 0 ≤ Lc) : (gaussMat m m (2 / (m : ℝ))).real (BadPb A₁ c τ Lc) ≤ rexp (-Lc) := by

  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  exact conc_lower_strict (g := fun A₂ => Pb A₁ c τ A₂) (Real.sqrt_nonneg _)
    (Pb_lip_Lip hm A₁ c τ) hv hLc

/-- The variances: `Var 𝖯_h ≤ t·Γ`, `Var 𝖯_b ≤ t·Γ` (and the integrability of the squares). -/
theorem Ph_var (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun A₂ => Ph A₁ A₂ c τ) (gaussMat m m (2 / (m : ℝ))) ∧
    Integrable (fun A₂ => Ph A₁ A₂ c τ ^ 2) (gaussMat m m (2 / (m : ℝ))) ∧
    ∫ A₂, Ph A₁ A₂ c τ ^ 2 ∂gaussMat m m (2 / (m : ℝ)) -
        (∫ A₂, Ph A₁ A₂ c τ ∂gaussMat m m (2 / (m : ℝ))) ^ 2 ≤ 2 / (m : ℝ) * GamS A₁ c τ := by

  have h := var_gen_Lip (g := fun A₂ => Ph A₁ A₂ c τ) (v := 2 / (m : ℝ)) (Real.sqrt_nonneg _)
    (Ph_lip A₁ c τ) (by positivity)
  rw [Real.sq_sqrt (GamS_nonneg _ _ _)] at h
  exact h

theorem Pb_var (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun A₂ => Pb A₁ c τ A₂) (gaussMat m m (2 / (m : ℝ))) ∧
    Integrable (fun A₂ => Pb A₁ c τ A₂ ^ 2) (gaussMat m m (2 / (m : ℝ))) ∧
    ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat m m (2 / (m : ℝ)) -
        (∫ A₂, Pb A₁ c τ A₂ ∂gaussMat m m (2 / (m : ℝ))) ^ 2 ≤ 2 / (m : ℝ) * GamS A₁ c τ := by

  have h := var_gen_Lip (g := fun A₂ => Pb A₁ c τ A₂) (v := 2 / (m : ℝ)) (Real.sqrt_nonneg _)
    (Pb_lip_Lip hm A₁ c τ) (by positivity)
  rw [Real.sq_sqrt (GamS_nonneg _ _ _)] at h
  exact h

theorem dC_integrable (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun A₂ => dC A₁ A₂ c τ) (gaussMat m m (2 / (m : ℝ))) ∧
    Integrable (fun A₂ => dC A₁ A₂ c τ ^ 2) (gaussMat m m (2 / (m : ℝ))) := by

  have h := var_gen_Lip (g := fun A₂ => dC A₁ A₂ c τ) (v := 2 / (m : ℝ))
    (L := 2 * √(GamS A₁ c τ)) (by positivity) (dC_lip hm A₁ c τ) (by positivity)
  exact ⟨h.1, h.2.1⟩

private lemma measurable_hbar2_joint_Lip (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      hbar2 θ.1 θ.2 c τ) := by
  refine measurable_pi_iff.mpr fun j => ?_
  have hc1 : Continuous (fun q : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) => q.1 *ᵥ q.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  have hc2 : Continuous (fun q : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => q.1 *ᵥ q.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  have hy : Continuous (fun q : (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      (Fin n → ℝ) => c + τ • q.2) := continuous_const.add (continuous_snd.const_smul τ)
  have h1 : Continuous (fun q : (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      (Fin n → ℝ) => reluV (q.1.1 *ᵥ (c + τ • q.2))) :=
    continuous_reluV.comp (hc1.comp ((continuous_fst.comp continuous_fst).prodMk hy))
  have h2 : Continuous (fun q : (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      (Fin n → ℝ) => hid2 q.1.1 q.1.2 (c + τ • q.2) j) :=
    (continuous_apply j).comp (continuous_reluV.comp
      (hc2.comp ((continuous_snd.comp continuous_fst).prodMk h1)))
  exact (h2.measurable.stronglyMeasurable.integral_prod_right'
    (ν := stdGauss (Fin n))).measurable

private lemma measurable_bO_joint_Lip (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      bO θ.1 θ.2 c τ) := by
  have hf : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      (((c, τ), θ) : ((Fin n → ℝ) × ℝ) × BstLean.Part136.HidParam n m)) :=
    measurable_const.prodMk measurable_id
  have h := (measurable_bO (n := n) (m := m)).comp hf
  exact h

private lemma measurable_dC_joint_Lip (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      dC θ.1 θ.2 c τ) := by
  have h1 : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      √(normSq (hbar2 θ.1 θ.2 c τ - bO θ.1 θ.2 c τ))) :=
    (continuous_normSq.measurable.comp
      ((measurable_hbar2_joint_Lip c τ).sub (measurable_bO_joint_Lip c τ))).sqrt
  exact h1.const_mul _

private lemma measurable_Ph_joint_Lip (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      Ph θ.1 θ.2 c τ) := by
  have h1 : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      √(normSq (hbar2 θ.1 θ.2 c τ))) :=
    (continuous_normSq.measurable.comp (measurable_hbar2_joint_Lip c τ)).sqrt
  exact h1.const_mul _

private lemma measurable_DelP_joint_Lip (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      DelP θ.1 θ.2 c τ) :=
  (measurable_Ph_joint_Lip c τ).sub (measurable_Pb_joint c τ)

private lemma measurable_int_dC_Lip (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      ∫ A₂, dC A₁ A₂ c τ ∂gaussMat m m (2 / (m : ℝ))) :=
  ((measurable_dC_joint_Lip (m := m) c τ).stronglyMeasurable.integral_prod_right'
    (ν := gaussMat m m (2 / (m : ℝ)))).measurable

private lemma measurable_int_DelP_Lip (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      ∫ A₂, DelP A₁ A₂ c τ ∂gaussMat m m (2 / (m : ℝ))) :=
  ((measurable_DelP_joint_Lip (m := m) c τ).stronglyMeasurable.integral_prod_right'
    (ν := gaussMat m m (2 / (m : ℝ)))).measurable

/-- Joint measurability, for the union bound over `(A₁, A₂)`. -/
theorem measurableSet_BadD_joint (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    MeasurableSet {θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ |
      θ.2 ∈ BadD θ.1 c τ Lc} := by

  exact measurableSet_lt (((measurable_int_dC_Lip (m := m) c τ).comp measurable_fst).add
    (((((measurable_GamS c τ).comp measurable_fst).sqrt).const_mul 2).const_mul _))
    (measurable_dC_joint_Lip c τ)

theorem measurableSet_BadPi_joint (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    MeasurableSet {θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ |
      θ.2 ∈ BadPi θ.1 c τ Lc} := by

  exact measurableSet_lt
    (((((measurable_GamS c τ).comp measurable_fst).sqrt).const_mul 2).const_mul _)
    (continuous_abs.measurable.comp ((measurable_DelP_joint_Lip c τ).sub
      ((measurable_int_DelP_Lip (m := m) c τ).comp measurable_fst)))

theorem measurableSet_BadPb_joint (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    MeasurableSet {θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ |
      θ.2 ∈ BadPb θ.1 c τ Lc} := by

  exact measurableSet_lt (measurable_Pb_joint c τ)
    (((measurable_int_Pb c τ).comp measurable_fst).sub
      ((((measurable_GamS c τ).comp measurable_fst).sqrt).const_mul _))

end BstLean.Part154
