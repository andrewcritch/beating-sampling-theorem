import BstLean.Part153Op
import BstLean.Part153Conc
import BstLean.Part150CDefs
import BstLean.Part141Atom
import BstLean.Part130Row
import BstLean.Part130Kappa
import BstLean.Part133L2

/-!
# Part 153: the energy of the oracle centre (Lemma EN (ii), (iii); Lemma PR (ii))

Paper source: `proofs/option-n/theorem5-06-centre.tex`, Lemma EN parts (ii) and (iii), and
Lemma PR (ii) (the chord of `κ`).

Notation. `A₁ : m × n`, `c`, `τ` are fixed; `A₂` is an `m × m` Gaussian matrix with entry variance
`t = 2/m`. `Γ = gO A₁ c τ`, `Γ̄ = t·|h̄₁|² = t·normSq (hO A₁ c τ)`, `s_h² = sO2 A₁ c τ = Γ − Γ̄`.

* `Pb A₁ c τ A₂ = √t·|b′°|` (`b′° = bO A₁ A₂ c τ`): the paper's `𝖯_b`.
* `Pb_lip`: `A₂ ↦ 𝖯_b` is Lipschitz with constant `√t·|h̄₁|` for the Frobenius norm.
* `GamBar_le`: `Γ̄ ≤ Γ`; `sO2_nonneg`.
* `Ebe_prob`: `Pr(𝖯_b > E 𝖯_b + √(2·L_c·t·Γ)) ≤ exp(−L_c)`.
* `psi_sq_row`: `2·E ψ_s(σZ)² = (σ² + s²)·κ(σ²/(σ² + s²))`.
* `rb_eq`: `E 𝖯_b² = Γ·κ(Γ̄/Γ)`; `rb_bounds`: `Γ/π ≤ E 𝖯_b² ≤ Γ − (1 − 1/π)·s_h²`.
* `eb_le`: Lemma EN (iii) (deterministic, `m = n²`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part137 BstLean.Part150 BstLean.Part152

noncomputable section

variable {n m : ℕ}

/-- `𝖯_b = √t·|b′°|`, `t = 2/m`. -/
def Pb (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  √(2 / (m : ℝ)) * nrm (bO A₁ A₂ c τ)

lemma Pb_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ Pb A₁ c τ A₂ :=
  mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)

lemma Pb_sq (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) :
    Pb A₁ c τ A₂ ^ 2 = 2 / (m : ℝ) * normSq (bO A₁ A₂ c τ) := by
  unfold Pb
  rw [mul_pow, Real.sq_sqrt (by positivity), nrm_sq]

/-- **Lemma EN (ii), the Lipschitz constant**: `A₂ ↦ 𝖯_b` is Lipschitz with constant
`√t·|h̄₁|` for the Frobenius norm. -/
theorem Pb_lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (A₂ A₂' : Matrix (Fin m) (Fin m) ℝ) :
    |Pb A₁ c τ A₂ - Pb A₁ c τ A₂'| ≤
      (√(2 / (m : ℝ)) * nrm (hO A₁ c τ)) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := by
  unfold Pb
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have h1 := abs_nrm_sub_le (bO A₁ A₂ c τ) (bO A₁ A₂' c τ)
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
  calc |nrm (bO A₁ A₂ c τ) - nrm (bO A₁ A₂' c τ)|
      ≤ opN (A₂ - A₂') * nrm (hO A₁ c τ) := h1.trans (h2.trans h3)
    _ ≤ √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) * nrm (hO A₁ c τ) :=
        mul_le_mul_of_nonneg_right h4 (nrm_nonneg _)
    _ = nrm (hO A₁ c τ) * √(∑ i, ∑ j, (A₂ i j - A₂' i j) ^ 2) := mul_comm _ _

/-- `Γ̄ ≤ Γ`. -/
theorem GamBar_le (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    2 / (m : ℝ) * normSq (hO A₁ c τ) ≤ gO A₁ c τ := by
  unfold gO normSq
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  exact psiS_sq_le _ _

theorem sO2_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    0 ≤ sO2 A₁ c τ := by
  have h := GamBar_le A₁ c τ
  unfold normSq at h
  unfold sO2
  linarith

lemma GamBar_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    0 ≤ 2 / (m : ℝ) * normSq (hO A₁ c τ) :=
  mul_nonneg (by positivity) (normSq_nonneg _)

lemma gO_nonneg' (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    0 ≤ gO A₁ c τ := (GamBar_nonneg A₁ c τ).trans (GamBar_le A₁ c τ)

/-- **Lemma EN (ii), the event `E_be`**: `Pr(𝖯_b > E 𝖯_b + √(2·L_c·t·Γ)) ≤ exp(−L_c)`. -/
theorem Ebe_prob (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat m m (2 / (m : ℝ))).real
        {A₂ | ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat m m (2 / (m : ℝ)) +
          √(2 * Lc * (2 / (m : ℝ)) * gO A₁ c τ) < Pb A₁ c τ A₂} ≤ Real.exp (-Lc) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hL0 : 0 ≤ √(2 / (m : ℝ)) * nrm (hO A₁ c τ) :=
    mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)
  have h := conc_upper_strict (g := Pb A₁ c τ) hL0 (Pb_lip A₁ c τ) hv hLc
  refine le_trans (measureReal_mono (fun M hM => ?_)) h
  simp only [Set.mem_ofPred_eq] at hM ⊢
  refine lt_of_le_of_lt ?_ hM
  have e : √(2 / (m : ℝ)) * nrm (hO A₁ c τ) = √(2 / (m : ℝ) * normSq (hO A₁ c τ)) := by
    unfold nrm
    rw [Real.sqrt_mul hv.le]
  rw [e, ← Real.sqrt_mul (by positivity)]
  gcongr
  exact GamBar_le A₁ c τ

/-! ## The second moment of `ψ_s` of a Gaussian number -/

lemma inner2 (a s : ℝ) :
    ∫ η : Fin 2 → ℝ, relu (a + s * η 0) * relu (a + s * η 1) ∂stdGauss (Fin 2) =
      psiS s a * psiS s a := by
  let G : ℝ × ℝ → ℝ := fun p => relu (a + s * p.1) * relu (a + s * p.2)
  have h := (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' G
  have e : ∫ η : Fin 2 → ℝ, relu (a + s * η 0) * relu (a + s * η 1) ∂stdGauss (Fin 2) =
      ∫ p, G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    rw [← h]
    rfl
  rw [e]
  exact integral_prod_mul (fun z => relu (a + s * z)) (fun z => relu (a + s * z))

/-- `2·E ψ_s(σZ)² = (σ² + s²)·κ(σ²/(σ² + s²))`: the two-point formula for the pair
`(σZ₀ + sZ₁, σZ₀ + sZ₂)`. -/
theorem psi_sq_row (σ s : ℝ) :
    2 * ∫ z, psiS s (σ * z) ^ 2 ∂gaussianReal 0 1 =
      (σ ^ 2 + s ^ 2) * kappa (σ ^ 2 / (σ ^ 2 + s ^ 2)) := by
  let h : Fin 3 → ℝ := ![σ, s, 0]
  let h' : Fin 3 → ℝ := ![σ, 0, s]
  have hr := row_formula_std h h'
  have n1 : normSq h = σ ^ 2 + s ^ 2 := by simp [normSq, Fin.sum_univ_three, h]
  have n2 : normSq h' = σ ^ 2 + s ^ 2 := by simp [normSq, Fin.sum_univ_three, h']
  have d : ∑ j, h j * h' j = σ ^ 2 := by
    simp [Fin.sum_univ_three, h, h']
    ring
  rw [n1, n2, d, Real.mul_self_sqrt (by positivity)] at hr
  rw [← hr]
  congr 1
  let G : ℝ × (Fin 2 → ℝ) → ℝ :=
    fun p => relu (σ * p.1 + s * p.2 0) * relu (σ * p.1 + s * p.2 1)
  have e1 : ∀ ξ : Fin 3 → ℝ, relu (∑ j, ξ j * h j) * relu (∑ j, ξ j * h' j) =
      G (ξ 0, fun j => ξ j.succ) := by
    intro ξ
    have a1 : ∑ j, ξ j * h j = σ * ξ 0 + s * ξ 1 := by
      simp [Fin.sum_univ_three, h]
      ring
    have a2 : ∑ j, ξ j * h' j = σ * ξ 0 + s * ξ 2 := by
      simp [Fin.sum_univ_three, h']
      ring
    rw [a1, a2]
    rfl
  have hi3 : Integrable (fun ξ : Fin 3 → ℝ => G (ξ 0, fun j => ξ j.succ)) (stdGauss (Fin 3)) := by
    have := (rowPair137 (v := 1) zero_le_one h h').1
    simp only [Real.sqrt_one, one_smul] at this
    simp_rw [e1] at this
    exact this
  have hG : Integrable G ((gaussianReal 0 1).prod (stdGauss (Fin 2))) :=
    (aug_integrable G).mp hi3
  simp_rw [e1]
  rw [aug_integral G, integral_prod _ hG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [G]
  rw [inner2, sq]

lemma integrable_psi_sq (σ s : ℝ) :
    Integrable (fun z : ℝ => psiS s (σ * z) ^ 2) (gaussianReal 0 1) := by
  have hd : Integrable (fun z : ℝ => 2 * σ ^ 2 * z ^ 2 + 2 * psiS s 0 ^ 2) (gaussianReal 0 1) :=
    ((integrable_pow_gauss 2).const_mul _).add (integrable_const _)
  have hm : Measurable (fun z : ℝ => psiS s (σ * z) ^ 2) :=
    (measurable_psiS.comp
      (measurable_const.prodMk (measurable_const.mul measurable_id))).pow_const 2
  refine Integrable.mono' hd hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hl := BstLean.Part141.psiS_lip_x s (σ * z) 0
  rw [sub_zero] at hl
  have h2 : (psiS s (σ * z) - psiS s 0) ^ 2 ≤ (σ * z) ^ 2 := sq_le_sq.mpr hl
  nlinarith [sq_nonneg (psiS s (σ * z) - 2 * psiS s 0)]

/-! ## The conditional mean of the energy -/

/-- **`𝗋_b² = E[𝖯_b² | A₁] = Γ·κ(Γ̄/Γ)`.** -/
theorem rb_eq (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun A₂ => Pb A₁ c τ A₂ ^ 2) (gaussMat m m (2 / (m : ℝ))) ∧
    ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat m m (2 / (m : ℝ)) =
      gO A₁ c τ * kappa (2 / (m : ℝ) * normSq (hO A₁ c τ) / gO A₁ c τ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set v : ℝ := 2 / (m : ℝ) with hv
  have hv0 : 0 ≤ v := by positivity
  set hb := hO A₁ c τ with hhb
  set s := sO A₁ c τ with hs
  set σ : ℝ := √v * √(normSq hb) with hσ
  let g : (Fin m → ℝ) → ℝ := fun y => ∑ j, psiS s (y j) ^ 2
  have hg : Measurable g := Finset.measurable_sum _ fun j _ =>
    (measurable_psiS.comp (measurable_const.prodMk (measurable_pi_apply j))).pow_const 2
  have eP : ∀ A₂ : Matrix (Fin m) (Fin m) ℝ, Pb A₁ c τ A₂ ^ 2 = v * g (A₂.mulVec hb) := by
    intro A₂
    rw [Pb_sq]
    rfl
  have eg : ∀ ξ : Fin m → ℝ, g ((√v * √(normSq hb)) • ξ) = ∑ j, psiS s (σ * ξ j) ^ 2 := by
    intro ξ
    rfl
  have hf := integrable_psi_sq σ s
  have hi : Integrable (fun ξ : Fin m → ℝ => g ((√v * √(normSq hb)) • ξ)) (stdGauss (Fin m)) := by
    simp_rw [eg]
    unfold stdGauss
    exact pi_sum_integrable hf
  have hσ2 : σ ^ 2 = v * normSq hb := by
    rw [hσ, mul_pow, Real.sq_sqrt hv0, Real.sq_sqrt (normSq_nonneg _)]
  have hs2 : s ^ 2 = sO2 A₁ c τ := by
    rw [hs]
    unfold sO
    exact Real.sq_sqrt (sO2_nonneg A₁ c τ)
  have hsum : σ ^ 2 + s ^ 2 = gO A₁ c τ := by
    rw [hσ2, hs2]
    unfold sO2 normSq
    ring
  refine ⟨?_, ?_⟩
  · simp_rw [eP]
    exact (layer_transfer_integrable v hb hg hi).const_mul v
  · simp_rw [eP]
    rw [integral_const_mul, layer_transfer v hb hg]
    simp_rw [eg]
    have hp := pi_sum (ι := Fin m) (μ := gaussianReal 0 1) hf
    unfold stdGauss
    rw [hp, Fintype.card_fin]
    have hk := psi_sq_row σ s
    rw [hsum, hσ2] at hk
    rw [← hk, hv]
    field_simp

/-- **Lemma EN (ii), the mean of the energy** (with Lemma PR (ii), the chord of `κ`):
`Γ/π ≤ 𝗋_b² ≤ Γ − (1 − 1/π)·s_h²`. -/
theorem rb_bounds (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun A₂ => Pb A₁ c τ A₂ ^ 2) (gaussMat m m (2 / (m : ℝ))) ∧
    gO A₁ c τ / π ≤ ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat m m (2 / (m : ℝ)) ∧
    ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat m m (2 / (m : ℝ)) ≤
      gO A₁ c τ - (1 - 1 / π) * sO2 A₁ c τ := by
  obtain ⟨hi, he⟩ := rb_eq hm A₁ c τ
  refine ⟨hi, ?_⟩
  rw [he]
  have hGb0 := GamBar_nonneg A₁ c τ
  have hGb := GamBar_le A₁ c τ
  have hs : sO2 A₁ c τ = gO A₁ c τ - 2 / (m : ℝ) * normSq (hO A₁ c τ) := rfl
  rw [hs]
  set Γ := gO A₁ c τ
  set Gb := 2 / (m : ℝ) * normSq (hO A₁ c τ)
  have hp := Real.pi_pos
  rcases hGb0.trans hGb |>.eq_or_lt with h0 | hpos
  · have hG : Gb = 0 := le_antisymm (by rw [h0]; exact hGb) hGb0
    rw [← h0, hG]
    simp
  · set r := Gb / Γ with hr
    have hr0 : 0 ≤ r := div_nonneg hGb0 hpos.le
    have hr1 : r ≤ 1 := (div_le_one hpos).mpr hGb
    have hΓr : Γ * r = Gb := by rw [hr]; field_simp
    have k0 : 1 / π ≤ kappa r := by
      have := kappa_monotoneOn (a := 0) (b := r) ⟨by norm_num, by norm_num⟩
        ⟨by linarith, hr1⟩ hr0
      rwa [kappa_zero] at this
    have k1 : kappa r ≤ (1 - r) * (1 / π) + r := by
      have h1r : 0 ≤ 1 - r := by linarith
      have := kappa_convexOn.2 (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨by norm_num, by norm_num⟩)
        (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨by norm_num, by norm_num⟩) h1r hr0 (by ring)
      simpa [kappa_zero, kappa_one] using this
    constructor
    · calc Γ / π = Γ * (1 / π) := by ring
        _ ≤ Γ * kappa r := mul_le_mul_of_nonneg_left k0 hpos.le
    · calc Γ * kappa r ≤ Γ * ((1 - r) * (1 / π) + r) := mul_le_mul_of_nonneg_left k1 hpos.le
        _ = Γ - (1 - 1 / π) * (Γ - Gb) := by rw [← hΓr]; ring

/-! ## Lemma EN (iii) -/

/-- **Lemma EN (iii)** (deterministic; `m = n²`): on `E_e` (`hE`), `E_sc` (`hsc`), `E_be` (`hbe`),
with `θ_in ≥ θ_lo` (`hθ`): `e_b° = t|b′°|²/(γρ²) ≤ 1 + 2δ − (1 − 1/π)·(c_s/2)·θ_lo`. -/
theorem eb_le {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) {Lc δ cs θlo : ℝ}
    (hρ : 0 < normSq c + (n : ℝ) * τ ^ 2) (hLc : 0 ≤ Lc)
    (hE : |gO A₁ c τ - 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)| ≤
      δ * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)))
    (hcs : 0 ≤ cs) (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hθ : θlo ≤ (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))
    (hbe : Pb A₁ c τ A₂ ≤ ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
      √(2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * gO A₁ c τ))
    (hnum : (1 + δ) * (4 * √Lc / (n : ℝ) + 4 * Lc / (n : ℝ) ^ 2) ≤ δ) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤
      1 + 2 * δ - (1 - 1 / π) * (cs / 2) * θlo := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ hn
  have hcast : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨hi, hlo, hup⟩ := rb_bounds hmA A₁ c τ
  rw [← Pb_sq]
  have hP0 := Pb_nonneg A₁ c τ A₂
  have hΓ0 := gO_nonneg' A₁ c τ
  have hs0 := sO2_nonneg A₁ c τ
  have hI0 : 0 ≤ ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) :=
    integral_nonneg fun A₂ => Pb_nonneg A₁ c τ A₂
  have hJ := BstLean.Part133.sq_integral_le hi
  have hp := Real.pi_pos
  have hpi : 0 ≤ 1 - 1 / π := by
    have : 1 / π ≤ 1 := by rw [div_le_one hp]; linarith [Real.pi_gt_three]
    linarith
  set P := Pb A₁ c τ A₂
  set I := ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))
  set R2 := ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))
  set Γ := gO A₁ c τ
  set S := sO2 A₁ c τ
  set G0 := 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) with hG0
  have hG0pos : 0 < G0 := by positivity
  have hR2Γ : R2 ≤ Γ := by nlinarith
  have hIΓ : I ≤ √Γ := Real.le_sqrt_of_sq_le (hJ.trans hR2Γ)
  have hsΓ : √Γ ^ 2 = Γ := Real.sq_sqrt hΓ0
  have hsL : √Lc ^ 2 = Lc := Real.sq_sqrt hLc
  have hD : √(2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * Γ) = √Γ * (2 * √Lc / (n : ℝ)) := by
    have e : 2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * Γ = (√Γ * (2 * √Lc / (n : ℝ))) ^ 2 := by
      rw [hcast, mul_pow, div_pow, mul_pow, hsΓ, hsL]
      field_simp
    rw [e]
    exact Real.sqrt_sq (by positivity)
  rw [hD] at hbe
  set q := 4 * √Lc / (n : ℝ) + 4 * Lc / (n : ℝ) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hPsq : P ^ 2 ≤ R2 + Γ * q := by
    have h1 : P ^ 2 ≤ (I + √Γ * (2 * √Lc / (n : ℝ))) ^ 2 := pow_le_pow_left₀ hP0 hbe 2
    have hw : 0 ≤ 2 * √Lc / (n : ℝ) := by positivity
    have h2 : I * (√Γ * (2 * √Lc / (n : ℝ))) ≤ √Γ * (√Γ * (2 * √Lc / (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hIΓ (mul_nonneg (Real.sqrt_nonneg _) hw)
    have h3 : √Γ * (√Γ * (2 * √Lc / (n : ℝ))) = Γ * (2 * √Lc / (n : ℝ)) := by
      rw [← mul_assoc, ← sq, hsΓ]
    have h4 : (√Γ * (2 * √Lc / (n : ℝ))) ^ 2 = Γ * (4 * Lc / (n : ℝ) ^ 2) := by
      rw [mul_pow, div_pow, mul_pow, hsΓ, hsL]
      ring
    have h5 : Γ * q = 2 * (Γ * (2 * √Lc / (n : ℝ))) + Γ * (4 * Lc / (n : ℝ) ^ 2) := by
      rw [hq]; ring
    nlinarith
  have hΓle : Γ ≤ (1 + δ) * G0 := by
    have := (abs_le.mp hE).2
    linarith
  have hΓq : Γ * q ≤ δ * G0 := by
    calc Γ * q ≤ (1 + δ) * G0 * q := mul_le_mul_of_nonneg_right hΓle hq0
      _ = G0 * ((1 + δ) * q) := by ring
      _ ≤ G0 * δ := mul_le_mul_of_nonneg_left hnum hG0pos.le
      _ = δ * G0 := mul_comm _ _
  have hτ : θlo / 2 * G0 ≤ τ ^ 2 := by
    have h1 : θlo * (normSq c + (n : ℝ) * τ ^ 2) ≤ (n : ℝ) * τ ^ 2 := (le_div_iff₀ hρ).mp hθ
    have h2 : θlo / 2 * G0 = θlo * (normSq c + (n : ℝ) * τ ^ 2) / (n : ℝ) := by
      rw [hG0]; field_simp
    rw [h2, div_le_iff₀ hnR]
    linarith
  have hS : cs * (θlo / 2 * G0) ≤ S := (mul_le_mul_of_nonneg_left hτ hcs).trans hsc
  have hS' : (1 - 1 / π) * (cs * (θlo / 2 * G0)) ≤ (1 - 1 / π) * S :=
    mul_le_mul_of_nonneg_left hS hpi
  rw [div_le_iff₀ hG0pos]
  calc P ^ 2 ≤ R2 + Γ * q := hPsq
    _ ≤ Γ - (1 - 1 / π) * S + δ * G0 := by linarith
    _ ≤ (1 + δ) * G0 - (1 - 1 / π) * (cs * (θlo / 2 * G0)) + δ * G0 := by linarith
    _ = (1 + 2 * δ - (1 - 1 / π) * (cs / 2) * θlo) * G0 := by ring

end

end BstLean.Part153

#print axioms BstLean.Part153.Pb_lip
#print axioms BstLean.Part153.GamBar_le
#print axioms BstLean.Part153.sO2_nonneg
#print axioms BstLean.Part153.Ebe_prob
#print axioms BstLean.Part153.psi_sq_row
#print axioms BstLean.Part153.rb_eq
#print axioms BstLean.Part153.rb_bounds
#print axioms BstLean.Part153.eb_le
