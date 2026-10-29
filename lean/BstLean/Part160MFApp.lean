import BstLean.Part160MFInt

/-!
# Part 160 (file `MFApp`): the integrated mean-field lemma for the first layer of `A`

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-05-centre.tex`, Lemma `t7:p05:MA` (the mean bound `E|𝐝|² ≤ U_ρ²·ξ_c′`).

* `piG a u v = exp(−(√(1 − u) − 1/a)²/(2v))`: the tail mass of a Lipschitz function.
* `lip_lower_tail`: for a nonnegative `L`-Lipschitz `g` of a standard Gaussian vector with
  `S(1 − u) ≤ (E g)²`, `L² ≤ vS`, `1/a ≤ √(1 − u)`: `Pr(g² < S/a²) ≤ piG a u v`.
* `sig_lip`, `fA_lip`: `ς` and `|f|` are `ℓ`-Lipschitz for `f = fA A₁ c τ`.
* `xiCI`: the constant `ξ_c′` of Lean.
* `MA_i_int`: `E_{A₂}|𝐝|² ≤ U_ρ²·ξ_c′(θ_in)`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part154
open BstLean.Part137 (psiS)
open BstLean.Part148 (EuLip)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

/-- `exp(−(√(1 − u) − 1/a)²/(2v))`. -/
noncomputable def piG (a u v : ℝ) : ℝ := rexp (-((√(1 - u) - 1 / a) ^ 2 / (2 * v)))

lemma piG_nonneg (a u v : ℝ) : 0 ≤ piG a u v := (Real.exp_pos _).le

/-- **The lower tail of a nonnegative Lipschitz function of a Gaussian vector.** -/
theorem lip_lower_tail {ι : Type} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 < L) (hL : EuLip g L) (hg : ∀ x, 0 ≤ g x) {S u v a : ℝ} (hS : 0 < S) (ha : 0 < a)
    (hv : 0 < v) (hu : u ≤ 1) (hE : S * (1 - u) ≤ (∫ x, g x ∂stdGauss ι) ^ 2)
    (hLv : L ^ 2 ≤ v * S) (hgap : 1 / a ≤ √(1 - u)) :
    (stdGauss ι).real {x | g x ^ 2 < S / a ^ 2} ≤ piG a u v := by
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ∫ x, g x ∂stdGauss ι := ⟨_, rfl⟩
  rw [← he] at hE
  have he0 : 0 ≤ e := by rw [he]; exact integral_nonneg hg
  have hsS : 0 < √S := Real.sqrt_pos.mpr hS
  have hsS2 : √S ^ 2 = S := Real.sq_sqrt hS.le
  have hr2 : √(1 - u) ^ 2 = 1 - u := Real.sq_sqrt (by linarith)
  have hMe : √S * √(1 - u) ≤ e := by
    by_contra hc
    rw [not_le] at hc
    have := pow_lt_pow_left₀ hc he0 (two_ne_zero)
    rw [mul_pow, hsS2, hr2] at this
    linarith
  obtain ⟨t0, ht0⟩ : ∃ t0 : ℝ, t0 = √S * (√(1 - u) - 1 / a) := ⟨_, rfl⟩
  have ht00 : 0 ≤ t0 := by rw [ht0]; exact mul_nonneg hsS.le (by linarith)
  have hsub : {x | g x ^ 2 < S / a ^ 2} ⊆ {x | g x ≤ ∫ y, g y ∂stdGauss ι - t0} := by
    intro x hx
    have hx' : g x ^ 2 < S / a ^ 2 := hx
    show g x ≤ ∫ y, g y ∂stdGauss ι - t0
    rw [← he]
    have h1 : g x < √S / a := by
      by_contra hc
      rw [not_lt] at hc
      have := pow_le_pow_left₀ (by positivity) hc 2
      rw [div_pow, hsS2] at this
      linarith
    have e4 : e - t0 = e - √S * √(1 - u) + √S / a := by rw [ht0]; ring
    rw [e4]
    linarith
  refine (measureReal_mono hsub).trans ((BstLean.Part152.gaussConc_lower_sharp hL0.le hL ht00).trans ?_)
  unfold piG
  refine Real.exp_le_exp.mpr ?_
  rw [ht0, mul_pow, hsS2]
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (√(1 - u) - 1 / a) ^ 2 := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hL2 : 0 < L ^ 2 := by positivity
  have key : q / (2 * v) ≤ S * q / (2 * L ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hLv)]
  have e5 : -(S * q) / (2 * L ^ 2) = -(S * q / (2 * L ^ 2)) := by ring
  rw [e5]
  linarith

variable {n m : ℕ}

lemma le_of_sq_le_A {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  rw [not_le] at hc
  nlinarith [mul_pos (sub_pos.2 hc) (by linarith : 0 < a + b)]

/-- `|f|` is `ℓ`-Lipschitz, `f = fA A₁ c τ`, if `√t·|τ|·opN(A₁) ≤ ℓ`. -/
theorem fA_lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ ℓ : ℝ}
    (hℓ0 : √(2 / (m : ℝ)) * (|τ| * opN A₁) ≤ ℓ) :
    EuLip (fun ξ => nrm (fA A₁ c τ ξ)) ℓ := by
  intro ξ ξ'
  have e1 : fA A₁ c τ ξ - fA A₁ c τ ξ' =
      √(2 / (m : ℝ)) • (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ'))) := by
    simp only [fA]
    rw [smul_sub]
  have e2 : A₁ *ᵥ (c + τ • ξ) - A₁ *ᵥ (c + τ • ξ') = A₁ *ᵥ (τ • (ξ - ξ')) := by
    rw [← Matrix.mulVec_sub]
    congr 1
    rw [smul_sub]
    abel
  have e3 : √(∑ i, (ξ i - ξ' i) ^ 2) = nrm (ξ - ξ') := rfl
  rw [e3]
  calc |nrm (fA A₁ c τ ξ) - nrm (fA A₁ c τ ξ')|
      ≤ nrm (fA A₁ c τ ξ - fA A₁ c τ ξ') := BstLean.Part153.abs_nrm_sub_le _ _
    _ = √(2 / (m : ℝ)) * nrm (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ'))) := by
        rw [e1, BstLean.Part153.nrm_smul, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ √(2 / (m : ℝ)) * nrm (A₁ *ᵥ (c + τ • ξ) - A₁ *ᵥ (c + τ • ξ')) :=
        mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_reluV_sub_le _ _) (Real.sqrt_nonneg _)
    _ = √(2 / (m : ℝ)) * nrm (A₁ *ᵥ (τ • (ξ - ξ'))) := by rw [e2]
    _ ≤ √(2 / (m : ℝ)) * (opN A₁ * nrm (τ • (ξ - ξ'))) :=
        mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_mulVec_le _ _) (Real.sqrt_nonneg _)
    _ = √(2 / (m : ℝ)) * (|τ| * opN A₁) * nrm (ξ - ξ') := by
        rw [BstLean.Part153.nrm_smul]; ring
    _ ≤ ℓ * nrm (ξ - ξ') := mul_le_mul_of_nonneg_right hℓ0 (BstLean.Part153.nrm_nonneg _)

lemma proj_contr_A (b u : Fin m → ℝ) (γ : ℝ) (hγ : γ * normSq b = u ⬝ᵥ b) :
    normSq (u - γ • b) ≤ normSq u := by
  have e : u - γ • b = u + (-γ) • b := by rw [neg_smul, sub_eq_add_neg]
  rw [e, normSq_add', dotProduct_smul, smul_eq_mul, normSq_smul, ← hγ]
  nlinarith [mul_nonneg (sq_nonneg γ) (normSq_nonneg b)]

/-- `ς = |Π f|` is `ℓ`-Lipschitz, `f = fA A₁ c τ`. -/
theorem sig_lip (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ ℓ : ℝ}
    (hG : 0 < GamBarF (stdGauss (Fin n)) (fA A₁ c τ))
    (hℓ0 : √(2 / (m : ℝ)) * (|τ| * opN A₁) ≤ ℓ) :
    EuLip (fun ξ => nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ)) ℓ := by
  intro ξ ξ'
  set fb := fbar (stdGauss (Fin n)) (fA A₁ c τ) with hfb
  set G := GamBarF (stdGauss (Fin n)) (fA A₁ c τ) with hGd
  have hNb : normSq fb = G := rfl
  have e0 : gF (stdGauss (Fin n)) (fA A₁ c τ) ξ - gF (stdGauss (Fin n)) (fA A₁ c τ) ξ' =
      (fA A₁ c τ ξ - fA A₁ c τ ξ') -
        (betaF (stdGauss (Fin n)) (fA A₁ c τ) ξ - betaF (stdGauss (Fin n)) (fA A₁ c τ) ξ') •
          fb := by
    simp only [gF]
    rw [sub_smul]
    abel
  have hγ : (betaF (stdGauss (Fin n)) (fA A₁ c τ) ξ -
      betaF (stdGauss (Fin n)) (fA A₁ c τ) ξ') * normSq fb =
      (fA A₁ c τ ξ - fA A₁ c τ ξ') ⬝ᵥ fb := by
    rw [hNb, sub_dotProduct]
    simp only [betaF]
    rw [← hfb, ← hGd]
    field_simp
  have h1 : nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ - gF (stdGauss (Fin n)) (fA A₁ c τ) ξ') ≤
      nrm (fA A₁ c τ ξ - fA A₁ c τ ξ') := by
    rw [e0]
    exact Real.sqrt_le_sqrt (proj_contr_A _ _ _ hγ)
  have h2 := fA_lip A₁ c hℓ0
  -- the same chain as `fA_lip`, from the difference
  have e1 : fA A₁ c τ ξ - fA A₁ c τ ξ' =
      √(2 / (m : ℝ)) • (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ'))) := by
    simp only [fA]
    rw [smul_sub]
  have e2 : A₁ *ᵥ (c + τ • ξ) - A₁ *ᵥ (c + τ • ξ') = A₁ *ᵥ (τ • (ξ - ξ')) := by
    rw [← Matrix.mulVec_sub]
    congr 1
    rw [smul_sub]
    abel
  have e3 : √(∑ i, (ξ i - ξ' i) ^ 2) = nrm (ξ - ξ') := rfl
  rw [e3]
  calc |nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) - nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ')|
      ≤ nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ - gF (stdGauss (Fin n)) (fA A₁ c τ) ξ') :=
        BstLean.Part153.abs_nrm_sub_le _ _
    _ ≤ nrm (fA A₁ c τ ξ - fA A₁ c τ ξ') := h1
    _ = √(2 / (m : ℝ)) * nrm (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ'))) := by
        rw [e1, BstLean.Part153.nrm_smul, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ √(2 / (m : ℝ)) * nrm (A₁ *ᵥ (c + τ • ξ) - A₁ *ᵥ (c + τ • ξ')) :=
        mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_reluV_sub_le _ _) (Real.sqrt_nonneg _)
    _ = √(2 / (m : ℝ)) * nrm (A₁ *ᵥ (τ • (ξ - ξ'))) := by rw [e2]
    _ ≤ √(2 / (m : ℝ)) * (opN A₁ * nrm (τ • (ξ - ξ'))) :=
        mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_mulVec_le _ _) (Real.sqrt_nonneg _)
    _ = √(2 / (m : ℝ)) * (|τ| * opN A₁) * nrm (ξ - ξ') := by
        rw [BstLean.Part153.nrm_smul]; ring
    _ ≤ ℓ * nrm (ξ - ξ') := mul_le_mul_of_nonneg_right hℓ0 (BstLean.Part153.nrm_nonneg _)

/-- **The two tail masses for `f = fA A₁ c τ`** under `MFHyp`: for `ℓ² ≤ v₁·s²`,
`1/a₁ ≤ √(1 − 2v₁)` and `ℓ² ≤ v₃·Γ`, `1/a₃ ≤ √(1 − v₃)`. -/
theorem tails_fA (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ ℓ πg : ℝ}
    (H : MFHyp (stdGauss (Fin n)) (fA A₁ c τ) ℓ πg)
    (hℓ0 : √(2 / (m : ℝ)) * (|τ| * opN A₁) ≤ ℓ) {a1 a3 v1 v3 : ℝ} (ha1 : 0 < a1) (ha3 : 0 < a3)
    (hv1 : 0 < v1) (hv3 : 0 < v3) (hv1' : 2 * v1 ≤ 1) (hv3' : v3 ≤ 1)
    (h1 : ℓ ^ 2 ≤ v1 * sF2 (stdGauss (Fin n)) (fA A₁ c τ))
    (h3 : ℓ ^ 2 ≤ v3 * GamF (stdGauss (Fin n)) (fA A₁ c τ))
    (hg1 : 1 / a1 ≤ √(1 - 2 * v1)) (hg3 : 1 / a3 ≤ √(1 - v3)) :
    (stdGauss (Fin n)).real {ω | sig2F (stdGauss (Fin n)) (fA A₁ c τ) ω <
        sF2 (stdGauss (Fin n)) (fA A₁ c τ) / a1 ^ 2} ≤ piG a1 (2 * v1) v1 ∧
    (stdGauss (Fin n)).real {ω | normSq (fA A₁ c τ ω) <
        GamF (stdGauss (Fin n)) (fA A₁ c τ) / a3 ^ 2} ≤ piG a3 v3 v3 := by
  have hμ : IsProbabilityMeasure (stdGauss (Fin n)) := inferInstance
  have hℓ := H.hℓ
  have hs := H.hs
  have hΓ := GamF_pos H
  obtain ⟨_, _, _, hd0, hd1⟩ := H.F1
  obtain ⟨hsi, hsv⟩ := H.F2
  obtain ⟨hςi', _, _⟩ := H.sig_int
  have hLς := sig_lip A₁ c H.hbar hℓ0
  have hLf := fA_lip A₁ c hℓ0
  have hς2 : ∀ ξ, nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) ^ 2 =
      sig2F (stdGauss (Fin n)) (fA A₁ c τ) ξ := fun ξ => BstLean.Part153.nrm_sq _
  have hf2 : ∀ ξ, nrm (fA A₁ c τ ξ) ^ 2 = normSq (fA A₁ c τ ξ) :=
    fun ξ => BstLean.Part153.nrm_sq _
  constructor
  · -- `ς`
    have hςi : Integrable (fun ξ => nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ))
        (stdGauss (Fin n)) := hςi'
    obtain ⟨hvi, hvar⟩ := BstLean.Part152.gaussVar_le_sharp hℓ.le hLς
    set e := ∫ ξ, nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) ∂stdGauss (Fin n) with he
    set E2 := ∫ ω, sig2F (stdGauss (Fin n)) (fA A₁ c τ) ω ∂stdGauss (Fin n) with hE2
    have hvar_eq : ∫ ξ, (nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) - e) ^ 2 ∂stdGauss (Fin n) =
        E2 - e ^ 2 := by
      have ex : ∀ ξ, (nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) - e) ^ 2 =
          sig2F (stdGauss (Fin n)) (fA A₁ c τ) ξ -
            2 * e * nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) + e ^ 2 := fun ξ => by
        rw [← hς2]; ring
      simp only [ex]
      have hA : Integrable (fun ξ => sig2F (stdGauss (Fin n)) (fA A₁ c τ) ξ -
          2 * e * nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ)) (stdGauss (Fin n)) :=
        hsi.sub (hςi.const_mul _)
      rw [integral_add hA (integrable_const _),
        integral_sub hsi (hςi.const_mul _), integral_const_mul, integral_const]
      simp only [probReal_univ, one_smul]
      rw [← he, ← hE2]
      ring
    rw [hvar_eq] at hvar
    have hE : sF2 (stdGauss (Fin n)) (fA A₁ c τ) * (1 - 2 * v1) ≤ e ^ 2 := by nlinarith
    have key := lip_lower_tail hℓ hLς (fun ξ => BstLean.Part153.nrm_nonneg _) hs ha1 hv1
      hv1' hE h1 hg1
    simp only [hς2] at key
    exact key
  · -- `|f|`
    have hfi2 : Integrable (fun ξ => normSq (fA A₁ c τ ξ)) (stdGauss (Fin n)) := H.int_sq
    have hfi : Integrable (fun ξ => nrm (fA A₁ c τ ξ)) (stdGauss (Fin n)) :=
      (BstLean.Part152.gaussConc_mgf_sharp hℓ.le hLf 0).1
    obtain ⟨hvi, hvar⟩ := BstLean.Part152.gaussVar_le_sharp hℓ.le hLf
    set e := ∫ ξ, nrm (fA A₁ c τ ξ) ∂stdGauss (Fin n) with he
    have hΓe : GamF (stdGauss (Fin n)) (fA A₁ c τ) =
        ∫ ξ, normSq (fA A₁ c τ ξ) ∂stdGauss (Fin n) := rfl
    have hvar_eq : ∫ ξ, (nrm (fA A₁ c τ ξ) - e) ^ 2 ∂stdGauss (Fin n) =
        GamF (stdGauss (Fin n)) (fA A₁ c τ) - e ^ 2 := by
      have ex : ∀ ξ, (nrm (fA A₁ c τ ξ) - e) ^ 2 =
          normSq (fA A₁ c τ ξ) - 2 * e * nrm (fA A₁ c τ ξ) + e ^ 2 := fun ξ => by
        rw [← hf2]; ring
      simp only [ex]
      have hA : Integrable (fun ξ => normSq (fA A₁ c τ ξ) - 2 * e * nrm (fA A₁ c τ ξ))
          (stdGauss (Fin n)) := hfi2.sub (hfi.const_mul _)
      rw [integral_add hA (integrable_const _),
        integral_sub hfi2 (hfi.const_mul _), integral_const_mul, integral_const]
      simp only [probReal_univ, one_smul]
      rw [← he, ← hΓe]
      ring
    rw [hvar_eq] at hvar
    have hE : GamF (stdGauss (Fin n)) (fA A₁ c τ) * (1 - v3) ≤ e ^ 2 := by nlinarith
    have key := lip_lower_tail hℓ hLf (fun ξ => BstLean.Part153.nrm_nonneg _) hΓ ha3 hv3
      hv3' hE h3 hg3
    simp only [hf2] at key
    exact key


/-! ## The mean bound for the oracle centre -/

/-- `r̄_Γ = 2w_n/((1 − δ_e)n)`, an upper bound of `ℓ²/Γ`. -/
noncomputable def rG (n : ℕ) (δe : ℝ) : ℝ := 2 * wn n / ((1 - δe) * n)

/-- **`ξ_c′(θ)` of Lean**: the integrated remainder
`4K₀c_H h_H a₁a₃ θ^{3/2}/√(2c_s(1 − δ_e))`, the two tails, and the linear and bias terms of
`xiC` of Part 154 (unchanged). -/
noncomputable def xiCI (n : ℕ) (cs cH hH a1 a3 δe θ : ℝ) : ℝ :=
  4 * K0 * cH * hH * (a1 * a3) * (θ * √θ) / √(2 * cs * (1 - δe)) +
    8 * K0 * wn n * n * (piG a1 (2 * rhoBar n cs) (rhoBar n cs) / a1 +
      piG a3 (rG n δe) (rG n δe) / a3) +
    4 * wn n * ((2 * θ * rhoBar n cs +
      4 * (√2 - 1) ^ 2 * rhoBar n cs * n * nuR (rhoBar n cs)) / π +
        θ * piBar (rhoBar n cs)) +
    bN n cs θ

lemma rhoBar_posI {n : ℕ} (hn : 1 ≤ n) {cs : ℝ} (hcs : 0 < cs) : 0 < rhoBar n cs := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < wn n := by unfold BstLean.Part153.wn; positivity
  unfold rhoBar
  positivity

lemma Uθ_I {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * thetaC c τ = 2 * τ ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ := rhoC_posP hn c hτ
  unfold thetaC
  field_simp

/-- The common setup of `MA_i` and `MA_cross`. -/
theorem setupMA_I {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {cs : ℝ} (hcs : 0 < cs) (hϱ : rhoBar n cs < 1 / 4)
    (hop : 2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2 ≤ 4 * wn n / n)
    (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ) :
    ∃ ℓ ϱ : ℝ, ℓ ^ 2 = 4 * wn n * τ ^ 2 / n ∧ ϱ = ℓ ^ 2 / sO2 A₁ c τ ∧ 0 < ϱ ∧
      ϱ ≤ rhoBar n cs ∧
      MFHyp (stdGauss (Fin n)) (fA A₁ c τ) ℓ (piBar (rhoBar n cs)) ∧
      2 * (sO2 A₁ c τ * QB ϱ (piBar (rhoBar n cs))) ≤
        rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * bN n cs (thetaC c τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < wn n := by unfold BstLean.Part153.wn; positivity
  have hm := BstLean.Part153.one_le_mA hn
  have hmR : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  have hcτ : 0 < cs * τ ^ 2 := by positivity
  have hs : 0 < sO2 A₁ c τ := hcτ.trans_le hsc
  have hℓ0 : 0 < 4 * wn n * τ ^ 2 / n := by positivity
  have hℓ2 : √(4 * wn n * τ ^ 2 / n) ^ 2 = 4 * wn n * τ ^ 2 / n := Real.sq_sqrt hℓ0.le
  have hϱb := rhoBar_posI hn hcs
  have hle : √(4 * wn n * τ ^ 2 / n) ^ 2 / sO2 A₁ c τ ≤ rhoBar n cs := by
    rw [hℓ2]
    have h1 : 4 * wn n * τ ^ 2 / n / sO2 A₁ c τ ≤ 4 * wn n * τ ^ 2 / n / (cs * τ ^ 2) :=
      div_le_div_of_nonneg_left hℓ0.le hcτ hsc
    have h2 : 4 * wn n * τ ^ 2 / n / (cs * τ ^ 2) = rhoBar n cs := by
      unfold rhoBar
      field_simp
    linarith
  have hpos : 0 < √(4 * wn n * τ ^ 2 / n) ^ 2 / sO2 A₁ c τ := by rw [hℓ2]; positivity
  refine ⟨√(4 * wn n * τ ^ 2 / n), _, hℓ2, rfl, hpos, hle, ?_, ?_⟩
  · refine MFHyp_fA hm A₁ c hτ (Real.sqrt_pos.mpr hℓ0) ?_ hs (hle.trans_lt hϱ)
      (piBar_mono hpos hle hϱ) (piBar_le_one hϱb)
    rw [hℓ2]
    have := mul_le_mul_of_nonneg_left hop (sq_nonneg τ)
    calc 2 / ((mA n : ℕ) : ℝ) * τ ^ 2 * opN A₁ ^ 2
        = τ ^ 2 * (2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2) := by ring
      _ ≤ τ ^ 2 * (4 * wn n / n) := this
      _ = 4 * wn n * τ ^ 2 / n := by ring
  · obtain ⟨ϱ, hϱd⟩ : ∃ ϱ, ϱ = √(4 * wn n * τ ^ 2 / n) ^ 2 / sO2 A₁ c τ := ⟨_, rfl⟩
    rw [← hϱd] at hle hpos ⊢
    have hsϱ : sO2 A₁ c τ * ϱ = 4 * wn n * τ ^ 2 / n := by
      rw [hϱd, hℓ2]
      field_simp
    have hQ := QB_div_mono hpos hle (piBar_nonneg (rhoBar n cs))
    have h1 := mul_le_mul_of_nonneg_left hQ hs.le
    have hU := Uθ_I hn c hτ
    have e1 : sO2 A₁ c τ * (ϱ / rhoBar n cs * QB (rhoBar n cs) (piBar (rhoBar n cs))) =
        sO2 A₁ c τ * ϱ * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs := by ring
    have e2 : rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * bN n cs (thetaC c τ) =
        rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * thetaC c τ *
          (4 * wn n * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs) := by
      unfold bN
      ring
    rw [e2, hU]
    rw [e1, hsϱ] at h1
    have e3 : 2 * τ ^ 2 / (n : ℝ) *
        (4 * wn n * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs) =
        2 * (4 * wn n * τ ^ 2 / n * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs) := by
      ring
    rw [e3]
    linarith

lemma nuR_monoI {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : nuR x ≤ nuR y := by
  unfold nuR
  nlinarith [pow_le_pow_left₀ hx hxy 2]

/-- The algebra of the integrated remainder term. -/
lemma term1_alg {R N θ τ cs δe cH hH a1 a3 s2 G hs' : ℝ} (hR0 : 0 < R) (hnR : 0 < N)
    (hτ : 0 < τ) (hcs : 0 < cs) (hδ1 : δe < 1) (ha1 : 0 < a1) (ha3 : 0 < a3)
    (hU : R * (2 / N / N) * θ = 2 * τ ^ 2 / N) (hsc : cs * τ ^ 2 ≤ s2) (hs : 0 < s2)
    (hΓlo : (1 - δe) * (2 / N) * R ≤ G) (hhs0 : 0 ≤ hs')
    (hHS : hs' ≤ 4 * cH * τ ^ 4 * hH / N) :
    2 * (K0 * (hs' / √(s2 / a1 ^ 2 * (G / a3 ^ 2)))) ≤
      R * (2 / N / N) * (4 * K0 * cH * hH * (a1 * a3) * (θ * √θ) / √(2 * cs * (1 - δe))) := by
  have hK0 : 0 ≤ K0 := K0_pos.le
  have hδ1' : 0 < 1 - δe := by linarith
  obtain ⟨s0, hs0d⟩ : ∃ s0 : ℝ, s0 = √(2 * cs * (1 - δe)) := ⟨_, rfl⟩
  rw [← hs0d]
  have hs0 : 0 < s0 := by rw [hs0d]; exact Real.sqrt_pos.mpr (by positivity)
  have hs02 : s0 ^ 2 = 2 * cs * (1 - δe) := by rw [hs0d]; exact Real.sq_sqrt (by positivity)
  obtain ⟨q, hqd⟩ : ∃ q : ℝ, q = √(R / N) := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqd]; exact Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = R / N := by rw [hqd]; exact Real.sq_sqrt (by positivity)
  have hRq : R = q ^ 2 * N := by rw [hq2]; field_simp
  have hτq : τ ^ 2 = θ * q ^ 2 := by
    rw [hq2]
    field_simp at hU ⊢
    linarith
  have hθq : θ = (τ / q) ^ 2 := by
    rw [div_pow, hτq]; field_simp
  have hsθ : √θ = τ / q := by
    rw [hθq]; exact Real.sqrt_sq (by positivity)
  obtain ⟨D0, hD0d⟩ : ∃ D0 : ℝ, D0 = τ * s0 * q / (a1 * a3) := ⟨_, rfl⟩
  have hD0 : 0 < D0 := by rw [hD0d]; positivity
  have hDle : D0 ≤ √(s2 / a1 ^ 2 * (G / a3 ^ 2)) := by
    refine Real.le_sqrt_of_sq_le ?_
    have e : D0 ^ 2 = (cs * τ ^ 2) * ((1 - δe) * (2 / N) * R) / (a1 ^ 2 * a3 ^ 2) := by
      rw [hD0d, div_pow, mul_pow, mul_pow, mul_pow, hs02, hq2]
      field_simp
    have e' : s2 / a1 ^ 2 * (G / a3 ^ 2) = s2 * G / (a1 ^ 2 * a3 ^ 2) := by
      field_simp
    rw [e, e']
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul hsc hΓlo (by positivity) hs.le
  have h1 : hs' / √(s2 / a1 ^ 2 * (G / a3 ^ 2)) ≤ hs' / D0 :=
    div_le_div_of_nonneg_left hhs0 hD0 hDle
  have h2 : hs' / D0 ≤ (4 * cH * τ ^ 4 * hH / N) / D0 :=
    div_le_div_of_nonneg_right hHS hD0.le
  have h3 : R * (2 / N / N) * (4 * K0 * cH * hH * (a1 * a3) * (θ * √θ) / s0) =
      2 * (K0 * ((4 * cH * τ ^ 4 * hH / N) / D0)) := by
    rw [hsθ, hθq, hRq, hD0d]
    field_simp
  rw [h3]
  have := mul_le_mul_of_nonneg_left (h1.trans h2) hK0
  linarith

/-- The algebra of the two tail terms. -/
lemma term2_alg {R N w s2 G a1 a3 p1 p3 : ℝ} (hs : 0 < s2) (hsG : s2 ≤ G)
    (hΓ : G ≤ 4 * w / N * R) (hnR : 0 < N) (ha1 : 0 < a1) (ha3 : 0 < a3) (hp10 : 0 ≤ p1)
    (hp30 : 0 ≤ p3) :
    2 * (K0 * (2 * √s2 * (√(s2 / a1 ^ 2) * p1 + √(G / a3 ^ 2) * p3))) ≤
      R * (2 / N / N) * (8 * K0 * w * N * (p1 / a1 + p3 / a3)) := by
  have hK0 : 0 ≤ K0 := K0_pos.le
  have hG0 : 0 < G := lt_of_lt_of_le hs hsG
  obtain ⟨Gu, hGu⟩ : ∃ Gu : ℝ, Gu = 4 * w / N * R := ⟨_, rfl⟩
  rw [← hGu] at hΓ
  have hsΓ' : s2 ≤ Gu := hsG.trans hΓ
  have hGu0 : 0 ≤ Gu := hG0.le.trans hΓ
  have hr1 : √(s2 / a1 ^ 2) = √s2 / a1 := by
    rw [Real.sqrt_div hs.le, Real.sqrt_sq ha1.le]
  have hr3 : √(G / a3 ^ 2) = √G / a3 := by
    rw [Real.sqrt_div hG0.le, Real.sqrt_sq ha3.le]
  have hss : √s2 * √s2 ≤ Gu := by
    rw [Real.mul_self_sqrt hs.le]; exact hsΓ'
  have hsG' : √s2 * √G ≤ Gu := by
    rw [← Real.sqrt_mul hs.le]
    refine Real.sqrt_le_iff.mpr ⟨hGu0, ?_⟩
    rw [sq]
    exact mul_le_mul hsΓ' hΓ hG0.le hGu0
  rw [hr1, hr3]
  have h1 : √s2 * (√s2 / a1 * p1 + √G / a3 * p3) ≤ Gu * (p1 / a1 + p3 / a3) := by
    have e : √s2 * (√s2 / a1 * p1 + √G / a3 * p3) =
        (√s2 * √s2) * (p1 / a1) + (√s2 * √G) * (p3 / a3) := by ring
    rw [e, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hss (by positivity))
      (mul_le_mul_of_nonneg_right hsG' (by positivity))
  have h2 : R * (2 / N / N) * (8 * K0 * w * N * (p1 / a1 + p3 / a3)) =
      4 * K0 * (Gu * (p1 / a1 + p3 / a3)) := by
    rw [hGu]; field_simp; ring
  rw [h2]
  have := mul_le_mul_of_nonneg_left h1 hK0
  linarith

/-- **Lemma MA (i) with the integrated remainder** (Lemma `t7:p05:MA`, first conclusion). Fix
`A₁` with the conclusions of `E_op`, `E_sc`, `E_H`, and with `Γ ≥ (1 − δ_e)γ_Aρ²`; integrate
`A₂`: `E|𝐝|² ≤ U_ρ²·ξ_c′(θ_in)`, `U_ρ² = ρ²γ_A/n`. -/
theorem MA_i_int {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {cs cH hH a1 a3 δe : ℝ} (hcs : 0 < cs)
    (hϱ : rhoBar n cs < 1 / 4)
    (hop : 2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2 ≤ 4 * wn n / n)
    (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hHS : hsH A₁ c τ ≤ 4 * cH * τ ^ 4 * hH / n)
    (hδ1 : δe < 1)
    (hΓlo : (1 - δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 ≤ gO A₁ c τ)
    (ha1 : 0 < a1) (ha3 : 0 < a3) (hg1 : 1 / a1 ≤ √(1 - 2 * rhoBar n cs))
    (hrG : rG n δe ≤ 1) (hg3 : 1 / a3 ≤ √(1 - rG n δe)) :
    Integrable (fun A₂ => dC A₁ A₂ c τ ^ 2)
      (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) ∧
    ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * xiCI n cs cH hH a1 a3 δe (thetaC c τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < wn n := by unfold BstLean.Part153.wn; positivity
  have hm := BstLean.Part153.one_le_mA hn
  have hmR : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  have hcτ : 0 < cs * τ ^ 2 := by positivity
  have hs : 0 < sO2 A₁ c τ := hcτ.trans_le hsc
  have hK0 : 0 ≤ K0 := K0_pos.le
  have hρ := rhoC_posP hn c hτ
  have hρ2 := rhoC_sqP c τ
  obtain ⟨hθ0, hθ1⟩ := thetaC_bounds hn c hτ
  have hϱb := rhoBar_posI hn hcs
  have hπ0 := piBar_nonneg (rhoBar n cs)
  have hU := Uθ_I hn c hτ
  obtain ⟨ℓ, ϱ, hℓ2, hϱd, hpos, hle, H, hB⟩ := setupMA_I hn A₁ c hτ hcs hϱ hop hsc
  have hI := H.DF_sq_int
  -- `√t·|τ|·opN(A₁) ≤ ℓ`
  have hℓpos : 0 < ℓ := H.hℓ
  have hℓ0 : √(2 / ((mA n : ℕ) : ℝ)) * (|τ| * opN A₁) ≤ ℓ := by
    refine le_of_sq_le_A hℓpos.le ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs, hℓ2]
    have := mul_le_mul_of_nonneg_left hop (sq_nonneg τ)
    calc 2 / ((mA n : ℕ) : ℝ) * (τ ^ 2 * opN A₁ ^ 2)
        = τ ^ 2 * (2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2) := by ring
      _ ≤ τ ^ 2 * (4 * wn n / n) := this
      _ = 4 * wn n * τ ^ 2 / n := by ring
  have hsFe : sF (stdGauss (Fin n)) (fA A₁ c τ) = √(sO2 A₁ c τ) := by
    unfold sF; rw [sF2_fA hm]
  have hrb4 : 2 * rhoBar n cs ≤ 1 := by linarith
  have hτR : τ ^ 2 ≤ rhoC c τ ^ 2 / n := by
    rw [le_div_iff₀ hnR, hρ2]
    nlinarith [normSq_nonneg c]
  have hrG0 : 0 < rG n δe := by unfold rG; positivity
  have hv1 : ℓ ^ 2 ≤ rhoBar n cs * sF2 (stdGauss (Fin n)) (fA A₁ c τ) := by
    rw [sF2_fA hm]
    have e : ℓ ^ 2 = ϱ * sO2 A₁ c τ := by rw [hϱd, div_mul_cancel₀ _ hs.ne']
    rw [e]
    exact mul_le_mul_of_nonneg_right hle hs.le
  have hv3 : ℓ ^ 2 ≤ rG n δe * GamF (stdGauss (Fin n)) (fA A₁ c τ) := by
    rw [GamF_fA hm, hℓ2]
    have h1 : rG n δe * ((1 - δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2) ≤ rG n δe * gO A₁ c τ :=
      mul_le_mul_of_nonneg_left hΓlo hrG0.le
    have h2 : rG n δe * ((1 - δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2) =
        4 * wn n * (rhoC c τ ^ 2 / n) / n := by
      unfold rG
      have : (1 - δe) ≠ 0 := by linarith
      field_simp
      norm_num
    have h3 : 4 * wn n * τ ^ 2 / n ≤ 4 * wn n * (rhoC c τ ^ 2 / n) / n := by
      have := mul_le_mul_of_nonneg_left hτR (by positivity : (0 : ℝ) ≤ 4 * wn n)
      exact div_le_div_of_nonneg_right this hnR.le
    linarith
  obtain ⟨ht1, ht3⟩ := tails_fA A₁ c H hℓ0 ha1 ha3 hϱb hrG0 hrb4 hrG hv1 hv3 hg1 hg3
  have hle2 := lemmaMF_int H (kap := a1 ^ 2) (kap3 := a3 ^ 2) (by positivity) (by positivity)
    ht1 ht3
  obtain ⟨p1, hp1⟩ : ∃ p1, p1 = piG a1 (2 * rhoBar n cs) (rhoBar n cs) := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ p3, p3 = piG a3 (rG n δe) (rG n δe) := ⟨_, rfl⟩
  have hp10 : 0 ≤ p1 := by rw [hp1]; exact piG_nonneg _ _ _
  have hp30 : 0 ≤ p3 := by rw [hp3]; exact piG_nonneg _ _ _
  rw [← hp1, ← hp3, hsFe, GamF_fA hm] at hle2
  have hrm := rows_mean hm hI
  have e : (fun A₂ => dC A₁ A₂ c τ ^ 2) = fun A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      2 / ((mA n : ℕ) : ℝ) * ∑ j, DF (stdGauss (Fin n)) (fA A₁ c τ)
        ((√(2 / ((mA n : ℕ) : ℝ)))⁻¹ • fun k => A₂ j k) ^ 2 :=
    funext fun A₂ => dC_sq hm A₁ A₂ c τ
  rw [e]
  refine ⟨hrm.1, ?_⟩
  rw [hrm.2]
  rw [sF2_fA hm, ← hϱd] at hle2
  have hhs : hsF (stdGauss (Fin n)) (fA A₁ c τ) = hsH A₁ c τ := rfl
  rw [hhs] at hle2
  -- the quantities
  obtain ⟨Gb, hGb⟩ : ∃ Gb, Gb = GamBarF (stdGauss (Fin n)) (fA A₁ c τ) := ⟨_, rfl⟩
  rw [← hGb] at hle2
  have hGb0 : 0 ≤ Gb := by rw [hGb]; exact normSq_nonneg _
  have hΓ : gO A₁ c τ ≤ 4 * wn n / n * rhoC c τ ^ 2 := by
    rw [← BstLean.Part153.GamS_eq_gO hm, hρ2]
    exact (BstLean.Part153.GamS_le A₁ c τ).trans (mul_le_mul_of_nonneg_right hop
      (add_nonneg (normSq_nonneg _) (by positivity)))
  have hGbΓ : Gb ≤ gO A₁ c τ := by
    have h1 : sF2 (stdGauss (Fin n)) (fA A₁ c τ) =
        GamF (stdGauss (Fin n)) (fA A₁ c τ) - GamBarF (stdGauss (Fin n)) (fA A₁ c τ) := rfl
    rw [sF2_fA hm, GamF_fA hm, ← hGb] at h1
    linarith
  have hsΓ : sO2 A₁ c τ ≤ gO A₁ c τ := by
    have h1 : 0 ≤ 2 / ((mA n : ℕ) : ℝ) * ∑ i, hO A₁ c τ i ^ 2 :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    unfold sO2
    linarith
  have hhs0 : 0 ≤ hsH A₁ c τ := by
    rw [← hhs]
    unfold hsF
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨R, hR⟩ : ∃ R, R = rhoC c τ ^ 2 := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = thetaC c τ := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = sO2 A₁ c τ := ⟨_, rfl⟩
  obtain ⟨hs', hhs'⟩ : ∃ hs', hs' = hsH A₁ c τ := ⟨_, rfl⟩
  obtain ⟨pb, hpb⟩ : ∃ pb, pb = piBar (rhoBar n cs) := ⟨_, rfl⟩
  obtain ⟨rb, hrb⟩ : ∃ rb, rb = rhoBar n cs := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, w = wn n := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) := ⟨_, rfl⟩
  have hrbe : rb = 4 * w / (cs * N) := by rw [hrb, hwd, hN]; rfl
  rw [← hR, ← hθ] at hU hB ⊢
  rw [← hs2] at hle2 hB hsc hs hsΓ
  rw [← hhs'] at hle2 hHS hhs0
  rw [← hpb] at hle2 hB hπ0
  rw [← hrb] at hle hϱb
  rw [← hR] at hΓ
  rw [← hwd] at hℓ2 hΓ hw
  rw [← hN] at hℓ2 hΓ hU hB hnR hHS ⊢
  rw [← hR, ← hN] at hΓlo
  have hR0 : 0 < R := by rw [hR]; positivity
  have hΓ' := hGbΓ.trans hΓ
  have hsΓ' := hsΓ.trans hΓ
  obtain ⟨G, hG⟩ : ∃ G, G = gO A₁ c τ := ⟨_, rfl⟩
  rw [← hG] at hle2 hΓ hsΓ hΓlo hGbΓ
  have e1 := term1_alg (cH := cH) (hH := hH) hR0 hnR hτ hcs hδ1 ha1 ha3 hU hsc hs hΓlo hhs0 hHS
  have e2 := term2_alg (R := R) hs hsΓ hΓ hnR ha1 ha3 hp10 hp30
  -- term 3
  have hν := nuR_monoI hpos.le hle
  have hν0 : 0 ≤ nuR ϱ := by unfold nuR; positivity
  have hG0 : 0 ≤ Gb / s2 := div_nonneg hGb0 hs.le
  have hb : ℓ ^ 2 * (Gb / s2) ≤ R * (2 / N / N) * (2 * w * rb * N) := by
    have h1 : Gb / s2 ≤ (4 * w / N * R) / (cs * τ ^ 2) :=
      div_le_div₀ (hGb0.trans hΓ') hΓ' hcτ hsc
    have h2 : ℓ ^ 2 * (Gb / s2) ≤ ℓ ^ 2 * ((4 * w / N * R) / (cs * τ ^ 2)) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg ℓ)
    have h3 : ℓ ^ 2 * ((4 * w / N * R) / (cs * τ ^ 2)) = R * (2 / N / N) * (2 * w * rb * N) := by
      rw [hℓ2, hrbe]
      field_simp
      ring
    linarith
  have hb0 : 0 ≤ R * (2 / N / N) * (2 * w * rb * N) := by positivity
  have hbν : ℓ ^ 2 * (Gb / s2) * nuR ϱ ≤ R * (2 / N / N) * (2 * w * rb * N) * nuR rb :=
    mul_le_mul hb hν hν0 hb0
  have hℓU : 2 * ℓ ^ 2 = R * (2 / N / N) * θ * (4 * w) := by
    rw [hU, hℓ2]
    ring
  have hℓ0 : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have hc0 : 0 ≤ 4 * (√2 - 1) ^ 2 := by positivity
  have hπp : 0 < π := Real.pi_pos
  have e3 : 2 * (ℓ ^ 2 * (1 / π * (2 * ϱ + 4 * (√2 - 1) ^ 2 * (Gb / s2) * nuR ϱ) + pb)) ≤
      R * (2 / N / N) * (4 * w * ((2 * θ * rb + 4 * (√2 - 1) ^ 2 * rb * N * nuR rb) / π +
        θ * pb)) := by
    have h1 : 2 * ℓ ^ 2 * ϱ ≤ 2 * ℓ ^ 2 * rb := mul_le_mul_of_nonneg_left hle (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hbν hc0
    have h3 : 2 * (ℓ ^ 2 * (1 / π * (2 * ϱ + 4 * (√2 - 1) ^ 2 * (Gb / s2) * nuR ϱ) + pb)) =
        (1 / π) * (2 * (2 * ℓ ^ 2 * ϱ) +
          2 * (4 * (√2 - 1) ^ 2 * (ℓ ^ 2 * (Gb / s2) * nuR ϱ))) + 2 * ℓ ^ 2 * pb := by ring
    have h4 : R * (2 / N / N) * (4 * w * ((2 * θ * rb + 4 * (√2 - 1) ^ 2 * rb * N * nuR rb) / π +
        θ * pb)) =
        (1 / π) * (2 * (R * (2 / N / N) * θ * (4 * w) * rb) +
          2 * (4 * (√2 - 1) ^ 2 * (R * (2 / N / N) * (2 * w * rb * N) * nuR rb))) +
          R * (2 / N / N) * θ * (4 * w) * pb := by ring
    rw [h3, h4, ← hℓU]
    have h5 : 2 * (2 * ℓ ^ 2 * ϱ) + 2 * (4 * (√2 - 1) ^ 2 * (ℓ ^ 2 * (Gb / s2) * nuR ϱ)) ≤
        2 * (2 * ℓ ^ 2 * rb) +
          2 * (4 * (√2 - 1) ^ 2 * (R * (2 / N / N) * (2 * w * rb * N) * nuR rb)) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 1 / π by positivity)
    linarith
  have e5 : R * (2 / N / N) * xiCI n cs cH hH a1 a3 δe θ =
      R * (2 / N / N) * (4 * K0 * cH * hH * (a1 * a3) * (θ * √θ) / √(2 * cs * (1 - δe))) +
      R * (2 / N / N) * (8 * K0 * w * N * (p1 / a1 + p3 / a3)) +
      R * (2 / N / N) * (4 * w * ((2 * θ * rb + 4 * (√2 - 1) ^ 2 * rb * N * nuR rb) / π +
        θ * pb)) + R * (2 / N / N) * bN n cs θ := by
    unfold xiCI
    rw [← hp1, ← hp3, ← hpb, ← hrb, ← hwd, ← hN]
    ring
  rw [e5]
  linarith only [hle2, e1, e2, e3, hB]

end BstLean.Part160

open BstLean.Part160 in
#print axioms lip_lower_tail
open BstLean.Part160 in
#print axioms tails_fA
open BstLean.Part160 in
#print axioms MA_i_int
