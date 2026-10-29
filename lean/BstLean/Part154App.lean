import BstLean.Part154Defs
import BstLean.Part153All
import BstLean.Part150P45b

/-!
# Part 154: the mean-field lemma applied to the first layer of `A`: definitions and the bridge
Do not use `sorry`, `native_decide` or `axiom`.

`A₁ : m × n`, `c = ĉ`, `τ = τ₀`, `t = 2/m`, `y = c + τ•ξ`, `ξ ∼ stdGauss (Fin n)`.
`fA ξ = √t·relu(A₁ y)` is the map `f` of Lemma MF; `hsH = ‖H‖²_HS`;
`hbar2 = h̄₂ = E_ξ relu(A₂ relu(A₁ y))`; `dC = |𝐝| = √t·|h̄₂ − b′°|`; `Ph = 𝖯_h = √t·|h̄₂|`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

noncomputable section

variable {n m : ℕ}

/-- `f(ξ) = √t·relu(A₁(c + τξ))`. -/
def fA (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : Fin m → ℝ :=
  √(2 / (m : ℝ)) • reluV (A₁ *ᵥ (c + τ • ξ))

/-- `‖H‖²_HS`, `H = t·Cov_ξ(h₁(y))`. -/
def hsH (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  hsF (stdGauss (Fin n)) (fA A₁ c τ)

/-- `h̄₂ = E_ξ h₂(y)` (not normalized). -/
def hbar2 (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) : Fin m → ℝ :=
  fun j => ∫ ξ, hid2 A₁ A₂ (c + τ • ξ) j ∂stdGauss (Fin n)

/-- `|𝐝| = √t·|h̄₂ − b′°|`. -/
def dC (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) : ℝ :=
  √(2 / (m : ℝ)) * nrm (hbar2 A₁ A₂ c τ - bO A₁ A₂ c τ)

/-- `𝖯_h = √t·|h̄₂|`. -/
def Ph (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) : ℝ :=
  √(2 / (m : ℝ)) * nrm (hbar2 A₁ A₂ c τ)

/-- `π̄(ϱ) = exp(−(√(1 − 2ϱ) − 1/√2)²/(2ϱ))`. -/
def piBar (ϱ : ℝ) : ℝ := rexp (-((√(1 - 2 * ϱ) - 1 / √2) ^ 2 / (2 * ϱ)))

/-- Lemma PR (i) in absolute-value form for two linear forms of one standard Gaussian vector. -/
def PRvecAbs (K : ℝ) : Prop :=
  ∀ (m : ℕ) (g g' : Fin m → ℝ) (a a' : ℝ),
    |∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) -
        psiS (nrm g) a * psiS (nrm g') a' -
        (g ⬝ᵥ g') * PhiG (a / nrm g) * PhiG (a' / nrm g')| ≤
      K * (g ⬝ᵥ g') ^ 2 / (nrm g * nrm g')

private lemma psiG_posApp (v : ℝ) : 0 < psiG v := by
  have hm : StrictMono psiG := strictMono_of_deriv_pos fun x => by
    rw [(BstLean.Part153.hasDerivAt_psiG x).deriv]; exact BstLean.Part153.PhiG_pos x
  exact lt_of_le_of_lt (BstLean.Part153.psiG_nonneg (v - 1)) (hm (by linarith))

private lemma normSq_sqrt_smulApp {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 ≤ t) (v : ι → ℝ) :
    normSq (√t • v) = t * normSq v := by
  rw [normSq_smul, Real.sq_sqrt ht]

private lemma t_posApp {m : ℕ} (hm : 1 ≤ m) : (0 : ℝ) < 2 / (m : ℝ) := by
  have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

private lemma dot_cancelApp {m : ℕ} (hm : 1 ≤ m) (r v : Fin m → ℝ) :
    ((√(2 / (m : ℝ)))⁻¹ • r) ⬝ᵥ (√(2 / (m : ℝ)) • v) = r ⬝ᵥ v := by
  have hs : √(2 / (m : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (t_posApp hm)).ne'
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hs, one_mul]

private lemma rows_auxApp {m : ℕ} {v : ℝ} (hv : 0 < v) {G : (Fin m → ℝ) → ℝ}
    (hG : Integrable G (stdGauss (Fin m))) :
    Integrable (fun A₂ : Matrix (Fin m) (Fin m) ℝ => ∑ j, G ((√v)⁻¹ • rowOf j A₂))
      (gaussMat m m v) ∧
    ∫ A₂ : Matrix (Fin m) (Fin m) ℝ, ∑ j, G ((√v)⁻¹ • rowOf j A₂) ∂gaussMat m m v =
      (m : ℝ) * ∫ z, G z ∂stdGauss (Fin m) := by
  have hs : √v ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hφ : ∀ j : Fin m, Measurable
      (fun A₂ : Matrix (Fin m) (Fin m) ℝ => (√v)⁻¹ • rowOf j A₂) := fun j =>
    (measurable_const_smul _).comp (measurable_rowOf j)
  have hmap : ∀ j : Fin m, (gaussMat m m v).map
      (fun A₂ : Matrix (Fin m) (Fin m) ℝ => (√v)⁻¹ • rowOf j A₂) = stdGauss (Fin m) := by
    intro j
    have h1 : (gaussMat m m v).map (fun A₂ : Matrix (Fin m) (Fin m) ℝ => (√v)⁻¹ • rowOf j A₂) =
        ((gaussMat m m v).map (rowOf j)).map (fun x : Fin m → ℝ => (√v)⁻¹ • x) :=
      (Measure.map_map (measurable_const_smul _) (measurable_rowOf j)).symm
    rw [h1, gaussMat_row, Measure.map_map (measurable_const_smul _) (measurable_const_smul _)]
    have e : ((fun x : Fin m → ℝ => (√v)⁻¹ • x) ∘ fun ξ : Fin m → ℝ => √v • ξ) = id := by
      funext ξ
      simp [smul_smul, inv_mul_cancel₀ hs]
    rw [e, Measure.map_id]
  have hint : ∀ j : Fin m, Integrable
      (fun A₂ : Matrix (Fin m) (Fin m) ℝ => G ((√v)⁻¹ • rowOf j A₂)) (gaussMat m m v) := by
    intro j
    have hG' : Integrable G ((gaussMat m m v).map
        (fun A₂ : Matrix (Fin m) (Fin m) ℝ => (√v)⁻¹ • rowOf j A₂)) := by rw [hmap]; exact hG
    exact hG'.comp_measurable (hφ j)
  have hval : ∀ j : Fin m, ∫ A₂ : Matrix (Fin m) (Fin m) ℝ, G ((√v)⁻¹ • rowOf j A₂)
      ∂gaussMat m m v = ∫ z, G z ∂stdGauss (Fin m) := by
    intro j
    have hG' : AEStronglyMeasurable G ((gaussMat m m v).map
        (fun A₂ : Matrix (Fin m) (Fin m) ℝ => (√v)⁻¹ • rowOf j A₂)) := by
      rw [hmap]; exact hG.aestronglyMeasurable
    rw [← integral_map (hφ j).aemeasurable hG', hmap]
  refine ⟨integrable_finsetSum _ fun j _ => hint j, ?_⟩
  rw [integral_finsetSum _ fun j _ => hint j]
  simp_rw [hval]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem measurable_fA (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fA A₁ c τ) := by
  show Measurable (fun ξ : Fin n → ℝ => √(2 / (m : ℝ)) • reluV (A₁ *ᵥ (c + τ • ξ)))
  exact Measurable.const_smul (BstLean.Part153.continuous_h1 A₁ c τ).measurable (√(2 / (m : ℝ)))

/-- `|f(ξ)|² ≤ t·opN(A₁)²·|c + τξ|²`, and the fourth moment is finite. -/
theorem integrable_fA4 (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun ξ => normSq (fA A₁ c τ ξ) ^ 2) (stdGauss (Fin n)) := by
  have hnr : ∀ ξ : Fin n → ℝ, normSq (c + τ • ξ) ≤ 2 * normSq c + 2 * τ ^ 2 * normSq ξ := by
    intro ξ
    unfold normSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [sq_nonneg (c i - τ * ξ i)]
  have hdom : Integrable (fun ξ : Fin n → ℝ => (2 / (m : ℝ)) ^ 2 * (opN A₁ ^ 2) ^ 2 *
      (8 * normSq c ^ 2 + 8 * τ ^ 4 * nrm ξ ^ (2 * 2))) (stdGauss (Fin n)) :=
    ((integrable_const _).add
      ((BstLean.Part153.nrm_moment n (P := 2) (by norm_num)).1.const_mul _)).const_mul _
  have hc0 : Continuous (fun ξ : Fin n → ℝ => √(2 / (m : ℝ)) • reluV (A₁ *ᵥ (c + τ • ξ))) :=
    Continuous.const_smul (BstLean.Part153.continuous_h1 A₁ c τ) (√(2 / (m : ℝ)))
  have hc : Continuous (fun ξ : Fin n → ℝ => normSq (fA A₁ c τ ξ) ^ 2) :=
    (continuous_normSq.comp hc0).pow 2
  refine Integrable.mono' hdom hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have e1 : normSq (fA A₁ c τ ξ) = 2 / (m : ℝ) * normSq (reluV (A₁ *ᵥ (c + τ • ξ))) :=
    normSq_sqrt_smulApp (by positivity) _
  have h1 : normSq (reluV (A₁ *ᵥ (c + τ • ξ))) ≤ opN A₁ ^ 2 * normSq (c + τ • ξ) :=
    (BstLean.Part153.normSq_reluV_le _).trans (BstLean.Part153.normSq_mulVec_le _ _)
  have e2 : nrm ξ ^ (2 * 2) = normSq ξ ^ 2 := by rw [pow_mul, BstLean.Part153.nrm_sq]
  rw [e1, e2]
  have hX := normSq_nonneg (reluV (A₁ *ᵥ (c + τ • ξ)))
  have hP := normSq_nonneg c
  have hQ := normSq_nonneg ξ
  have hO : 0 ≤ opN A₁ ^ 2 := sq_nonneg _
  have h2 : normSq (reluV (A₁ *ᵥ (c + τ • ξ))) ≤
      opN A₁ ^ 2 * (2 * normSq c + 2 * τ ^ 2 * normSq ξ) :=
    h1.trans (mul_le_mul_of_nonneg_left (hnr ξ) hO)
  have h3 : normSq (reluV (A₁ *ᵥ (c + τ • ξ))) ^ 2 ≤
      (opN A₁ ^ 2 * (2 * normSq c + 2 * τ ^ 2 * normSq ξ)) ^ 2 := pow_le_pow_left₀ hX h2 2
  have h4 : (opN A₁ ^ 2 * (2 * normSq c + 2 * τ ^ 2 * normSq ξ)) ^ 2 ≤
      (opN A₁ ^ 2) ^ 2 * (8 * normSq c ^ 2 + 8 * τ ^ 4 * normSq ξ ^ 2) := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [sq_nonneg (2 * normSq c - 2 * τ ^ 2 * normSq ξ)]
  calc (2 / (m : ℝ) * normSq (reluV (A₁ *ᵥ (c + τ • ξ)))) ^ 2
      = (2 / (m : ℝ)) ^ 2 * normSq (reluV (A₁ *ᵥ (c + τ • ξ))) ^ 2 := by ring
    _ ≤ (2 / (m : ℝ)) ^ 2 * ((opN A₁ ^ 2) ^ 2 * (8 * normSq c ^ 2 + 8 * τ ^ 4 * normSq ξ ^ 2)) :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (sq_nonneg _)
    _ = (2 / (m : ℝ)) ^ 2 * (opN A₁ ^ 2) ^ 2 * (8 * normSq c ^ 2 + 8 * τ ^ 4 * normSq ξ ^ 2) := by
        ring

theorem fbar_fA (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    fbar (stdGauss (Fin n)) (fA A₁ c τ) = √(2 / (m : ℝ)) • hO A₁ c τ := by
  funext i
  show ∫ ξ : Fin n → ℝ, (√(2 / (m : ℝ)) • reluV (A₁ *ᵥ (c + τ • ξ))) i ∂stdGauss (Fin n) =
    (√(2 / (m : ℝ)) • hO A₁ c τ) i
  simp only [Pi.smul_apply, smul_eq_mul, reluV]
  rw [integral_const_mul, (hO_eq_gauss A₁ c τ i).2]

theorem GamF_fA (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    GamF (stdGauss (Fin n)) (fA A₁ c τ) = gO A₁ c τ := by
  rw [← BstLean.Part153.GamS_eq_gO hm]
  unfold GamF BstLean.Part153.GamS
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
    normSq_sqrt_smulApp (by positivity) _)

theorem GamBarF_fA (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    GamBarF (stdGauss (Fin n)) (fA A₁ c τ) = 2 / (m : ℝ) * normSq (hO A₁ c τ) := by
  unfold GamBarF
  rw [fbar_fA]
  exact normSq_sqrt_smulApp (by positivity) _

theorem sF2_fA (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    sF2 (stdGauss (Fin n)) (fA A₁ c τ) = sO2 A₁ c τ := by
  unfold sF2
  rw [GamF_fA hm, GamBarF_fA]
  rfl

theorem sF_fA (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    sF (stdGauss (Fin n)) (fA A₁ c τ) = sO A₁ c τ := by
  unfold sF sO
  rw [sF2_fA hm]

/-- (M1) for `fA`, from Lemma L1 (a) (`covH_le` of Part 153). -/
theorem M1_fA (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (w : Fin m → ℝ) :
    ∫ ξ, (w ⬝ᵥ fA A₁ c τ ξ - w ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ^ 2 ∂stdGauss (Fin n) ≤
      2 / (m : ℝ) * τ ^ 2 * opN A₁ ^ 2 * normSq w := by
  have hmean : ∫ ξ' : Fin n → ℝ, w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ')) ∂stdGauss (Fin n) =
      w ⬝ᵥ hO A₁ c τ := by
    simp only [dotProduct, reluV]
    rw [integral_finsetSum _ fun i _ => (hO_eq_gauss A₁ c τ i).1.const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, (hO_eq_gauss A₁ c τ i).2]
  have h := (BstLean.Part153.covH_le A₁ c τ w).2
  rw [hmean] at h
  rw [fbar_fA]
  have e : ∀ ξ : Fin n → ℝ, (w ⬝ᵥ fA A₁ c τ ξ - w ⬝ᵥ (√(2 / (m : ℝ)) • hO A₁ c τ)) ^ 2 =
      2 / (m : ℝ) * (w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ)) - w ⬝ᵥ hO A₁ c τ) ^ 2 := by
    intro ξ
    unfold fA
    rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_sub, mul_pow,
      Real.sq_sqrt (by positivity)]
  simp_rw [e]
  rw [integral_const_mul]
  calc 2 / (m : ℝ) * ∫ ξ : Fin n → ℝ, (w ⬝ᵥ reluV (A₁ *ᵥ (c + τ • ξ)) - w ⬝ᵥ hO A₁ c τ) ^ 2
        ∂stdGauss (Fin n)
      ≤ 2 / (m : ℝ) * (τ ^ 2 * opN A₁ ^ 2 * normSq w) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 / (m : ℝ) * τ ^ 2 * opN A₁ ^ 2 * normSq w := by ring

theorem XF_row (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (j : Fin m) :
    XF (stdGauss (Fin n)) (fA A₁ c τ) ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) =
      hbar2 A₁ A₂ c τ j ∧
    ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ) =
      (A₂ *ᵥ hO A₁ c τ) j := by
  constructor
  · unfold XF hbar2
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show relu (((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) ⬝ᵥ
      (√(2 / (m : ℝ)) • reluV (A₁ *ᵥ (c + τ • ξ)))) = _
    rw [dot_cancelApp hm]
    rfl
  · rw [fbar_fA, dot_cancelApp hm]
    rfl

/-- Row `j` of `Z₂ = A₂/√t` is the vector `z` of Lemma MF: `𝖣(z) = (h̄₂)_j − b′°_j`. -/
theorem DF_row (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (j : Fin m) :
    DF (stdGauss (Fin n)) (fA A₁ c τ) ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) =
      hbar2 A₁ A₂ c τ j - bO A₁ A₂ c τ j := by
  unfold DF
  rw [(XF_row hm A₁ A₂ c τ j).1, (XF_row hm A₁ A₂ c τ j).2, sF_fA hm]
  rfl

/-- The rows of `A₂ ∼ gaussMat m m (2/m)`, divided by `√t`, are standard Gaussian vectors:
`E_{A₂}[t·Σ_j G(row_j/√t)] = 2·E_z G(z)`. -/
theorem rows_mean (hm : 1 ≤ m) {G : (Fin m → ℝ) → ℝ} (hG : Integrable G (stdGauss (Fin m))) :
    Integrable (fun A₂ : Matrix (Fin m) (Fin m) ℝ =>
      2 / (m : ℝ) * ∑ j, G ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k)) (gaussMat m m (2 / (m : ℝ))) ∧
    ∫ A₂ : Matrix (Fin m) (Fin m) ℝ,
        2 / (m : ℝ) * ∑ j, G ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) ∂gaussMat m m (2 / (m : ℝ)) =
      2 * ∫ z, G z ∂stdGauss (Fin m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨h1, h2⟩ := rows_auxApp (t_posApp hm) hG
  have h1' : Integrable (fun A₂ : Matrix (Fin m) (Fin m) ℝ =>
      ∑ j, G ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k)) (gaussMat m m (2 / (m : ℝ))) := h1
  have h2' : ∫ A₂ : Matrix (Fin m) (Fin m) ℝ,
      ∑ j, G ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) ∂gaussMat m m (2 / (m : ℝ)) =
      (m : ℝ) * ∫ z, G z ∂stdGauss (Fin m) := h2
  refine ⟨h1'.const_mul _, ?_⟩
  rw [integral_const_mul, h2']
  field_simp

/-- `|𝐝|² = t·Σ_j 𝖣(row_j/√t)²`. -/
theorem dC_sq (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    dC A₁ A₂ c τ ^ 2 = 2 / (m : ℝ) *
      ∑ j, DF (stdGauss (Fin n)) (fA A₁ c τ) ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) ^ 2 := by
  unfold dC
  rw [mul_pow, Real.sq_sqrt (by positivity), BstLean.Part153.nrm_sq]
  simp_rw [DF_row hm]
  rfl

theorem Ph_sq (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    Ph A₁ A₂ c τ ^ 2 = 2 / (m : ℝ) *
      ∑ j, XF (stdGauss (Fin n)) (fA A₁ c τ) ((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) ^ 2 := by
  unfold Ph
  rw [mul_pow, Real.sq_sqrt (by positivity), BstLean.Part153.nrm_sq]
  simp_rw [fun j => (XF_row hm A₁ A₂ c τ j).1]
  rfl

theorem Pb_sq' (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    Pb A₁ c τ A₂ ^ 2 = 2 / (m : ℝ) *
      ∑ j, psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
        (((√(2 / (m : ℝ)))⁻¹ • fun k => A₂ j k) ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ^ 2 := by
  rw [BstLean.Part153.Pb_sq, sF_fA hm]
  simp_rw [fun j => (XF_row hm A₁ A₂ c τ j).2]
  rfl

/-- `h̄₁ ≠ 0` if `s_h² > 0` (then `A₁` has a nonzero row and `τ ≠ 0`). -/
theorem hO_pos_of_sO2 (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hs : 0 < sO2 A₁ c τ) : 0 < normSq (hO A₁ c τ) := by
  rw [BstLean.Part153.sO2_rows] at hs
  have hsum : 0 < ∑ i, BstLean.Part153.rowV c τ (rowOf i A₁) :=
    (mul_pos_iff_of_pos_left (t_posApp hm)).mp hs
  have hex : ∃ i, 0 < BstLean.Part153.rowV c τ (rowOf i A₁) := by
    by_contra h
    push Not at h
    exact absurd hsum (not_lt.mpr (Finset.sum_nonpos fun i _ => h i))
  obtain ⟨i, hi⟩ := hex
  have hle : BstLean.Part153.rowV c τ (rowOf i A₁) ≤ sRow A₁ τ i ^ 2 :=
    BstLean.Part153.vS_le _ _
  have hsr : 0 < sRow A₁ τ i := by
    have h0 : 0 ≤ sRow A₁ τ i := mul_nonneg hτ.le (Real.sqrt_nonneg _)
    rcases h0.eq_or_lt with h | h
    · rw [← h] at hle
      norm_num at hle
      linarith
    · exact h
  have hpos : 0 < hO A₁ c τ i := by
    show 0 < psiS (sRow A₁ τ i) (mRow A₁ c i)
    rw [BstLean.Part153.psiS_scale hsr, BstLean.Part153.psiS_one]
    exact mul_pos hsr (psiG_posApp _)
  calc (0 : ℝ) < hO A₁ c τ i ^ 2 := by positivity
    _ ≤ normSq (hO A₁ c τ) :=
        Finset.single_le_sum (f := fun i => hO A₁ c τ i ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)

end

end BstLean.Part154
