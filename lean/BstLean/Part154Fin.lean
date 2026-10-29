import BstLean.Part154App

/-!
# Part 154: the event `E_χ`, Proposition FC on the events, and Lemma TF (vector form)
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

/-- `δ_χ = 2√L_c/n + 2L_c/n²`. -/
noncomputable def deltaChi (n : ℕ) (Lc : ℝ) : ℝ := 2 * √Lc / n + 2 * Lc / (n : ℝ) ^ 2

/-- The complement of `E_χ`: `|A₂e|² > t|e|²·m(1 + δ_χ)`, `e = ĥ₁ − h̄₁` (`J` atoms). -/
def BadChi (n J : ℕ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {A₂ | 2 / ((mA n : ℕ) : ℝ) * normSq (hT J A₁ c τ - hO A₁ c τ) * ((mA n : ℕ) : ℝ) *
      (1 + deltaChi n Lc) < normSq (A₂ *ᵥ (hT J A₁ c τ - hO A₁ c τ))}

theorem EChi_prob {n : ℕ} (hn : 1 ≤ n) (J : ℕ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))).real (BadChi n J A₁ c τ Lc) ≤ rexp (-Lc) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (((mA n : ℕ) : ℝ)) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set e := hT J A₁ c τ - hO A₁ c τ with he
  set v : ℝ := 2 / ((mA n : ℕ) : ℝ) with hv
  have hv0 : 0 ≤ v := by rw [hv, hmR]; positivity
  have hS : MeasurableSet {y : Fin (mA n) → ℝ |
      v * normSq e * ((mA n : ℕ) : ℝ) * (1 + deltaChi n Lc) < normSq y} :=
    measurableSet_lt measurable_const measurable_normSq
  have hmeas : Measurable (fun M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ => M *ᵥ e) :=
    BstLean.Part149.measurable_mulVec_joint.comp (measurable_id.prodMk measurable_const)
  have hsm : Measurable (fun ξ : Fin (mA n) → ℝ => (√v * √(normSq e)) • ξ) :=
    measurable_const_smul _
  have hpre : BadChi n J A₁ c τ Lc = (fun M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ => M *ᵥ e) ⁻¹'
      {y | v * normSq e * ((mA n : ℕ) : ℝ) * (1 + deltaChi n Lc) < normSq y} := rfl
  rw [hpre, ← map_measureReal_apply hmeas hS, gaussMat_mulVec, map_measureReal_apply hsm hS]
  have hq0 : 0 ≤ v * normSq e := mul_nonneg hv0 (normSq_nonneg e)
  have hns : ∀ ξ : Fin (mA n) → ℝ, normSq ((√v * √(normSq e)) • ξ) =
      v * normSq e * ∑ i, ξ i ^ 2 := by
    intro ξ
    rw [normSq_smul, mul_pow, Real.sq_sqrt hv0, Real.sq_sqrt (normSq_nonneg e)]
    rfl
  have hsqrt : √(((mA n : ℕ) : ℝ) * Lc) = (n : ℝ) * √Lc := by
    rw [hmR, Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  have hsub : (fun ξ : Fin (mA n) → ℝ => (√v * √(normSq e)) • ξ) ⁻¹'
      {y | v * normSq e * ((mA n : ℕ) : ℝ) * (1 + deltaChi n Lc) < normSq y} ⊆
      {ξ : Fin (mA n) → ℝ | (Fintype.card (Fin (mA n)) : ℝ) +
        2 * √((Fintype.card (Fin (mA n)) : ℝ) * Lc) + 2 * Lc ≤ ∑ i, ξ i ^ 2} := by
    intro ξ hξ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hξ ⊢
    rw [hns] at hξ
    rw [Fintype.card_fin, hsqrt]
    have hpos : 0 < v * normSq e := by
      rcases hq0.eq_or_lt with h0 | h0
      · rw [← h0] at hξ; simp at hξ
      · exact h0
    have h1 : ((mA n : ℕ) : ℝ) * (1 + deltaChi n Lc) < ∑ i, ξ i ^ 2 := by
      have : v * normSq e * (((mA n : ℕ) : ℝ) * (1 + deltaChi n Lc)) <
          v * normSq e * ∑ i, ξ i ^ 2 := by linarith only [hξ]
      exact lt_of_mul_lt_mul_left this hpos.le
    have h2 : ((mA n : ℕ) : ℝ) * (1 + deltaChi n Lc) =
        ((mA n : ℕ) : ℝ) + 2 * ((n : ℝ) * √Lc) + 2 * Lc := by
      rw [hmR]; unfold deltaChi; field_simp; ring
    linarith only [h1, h2]
  exact (measureReal_mono hsub).trans (chiSq_upper_LM hLc)

theorem measurableSet_BadChi_joint {n : ℕ} (hn : 1 ≤ n) (J : ℕ) (c : Fin n → ℝ) (τ : ℝ)
    (Lc : ℝ) :
    MeasurableSet {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      θ.2 ∈ BadChi n J θ.1 c τ Lc} := by
  have hmap : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      ((((c, τ), θ) : ((Fin n → ℝ) × ℝ) × BstLean.Part136.HidParam n (mA n)))) :=
    measurable_const.prodMk measurable_id
  have h1 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      hT J θ.1 c τ - hO θ.1 c τ) :=
    ((measurable_hT (n := n) (m := mA n) J).comp hmap).sub
      ((measurable_hO (n := n) (m := mA n)).comp hmap)
  have h2 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      θ.2 *ᵥ (hT J θ.1 c τ - hO θ.1 c τ)) :=
    BstLean.Part149.measurable_mulVec_joint.comp (measurable_snd.prodMk h1)
  exact measurableSet_lt
    ((((measurable_normSq.comp h1).const_mul _).mul_const _).mul_const _)
    (measurable_normSq.comp h2)

/-- **Proposition FC (iii) on the events** `E_op ∩ E_sc ∩ E_e ∩ E_χ`:
`√t·|b′ − b′°|/ρ ≤ ϵ_J·√(γ_A/n)`. -/
theorem FC_iii {n : ℕ} (hn : 1 ≤ n) {J : ℕ} (hJ : 1 ≤ J) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ cs δe Lc : ℝ} (hτ : 0 < τ)
    (hcs : 0 < cs) (hδe : 0 ≤ δe) (hLc : 0 ≤ Lc) (hop : A₁ ∈ Eop n)
    (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hEe : gO A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2)
    (hχ : A₂ ∉ BadChi n J A₁ c τ Lc) :
    √(2 / ((mA n : ℕ) : ℝ)) * nrm (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ ≤
      epsJ n J J (wn n) cs δe (deltaChi n Lc) * √(2 / (n : ℝ) / n) := by
  have hw : 0 < wn n := by unfold BstLean.Part153.wn; positivity
  have hδχ : 0 ≤ deltaChi n Lc := by unfold deltaChi; positivity
  have hE : normSq (A₂ *ᵥ (hT J A₁ c τ - hO A₁ c τ)) ≤
      2 / ((mA n : ℕ) : ℝ) * normSq (hT J A₁ c τ - hO A₁ c τ) * ((mA n : ℕ) : ℝ) *
        (1 + deltaChi n Lc) := not_lt.mp hχ
  exact p45_iii hn (BstLean.Part130.one_le_mA hn) hJ hJ A₁ A₂ c hτ hw hcs hδe hδχ
    (BstLean.Part153.fro_le_Eop hn hop) hsc hEe hE

/-- **Lemma TF (a), (b), (c) for vectors.** `a = ā₂`, `bo = b°`, `b` the centre of the
program, `s = √t_A`, `X = √(γ_A/n)`, `x1 = √ξ°_hp`, `x2 = √ξ°_∥`, `pl = p_low`,
`eo = √e°_{b,max}`, `ε = ϵ_J`, `rn = √n`. -/
theorem TF_vec {k : ℕ} (a bo b : Fin k → ℝ) {s X x1 x2 pl eo ε rn : ℝ} (hs : 0 ≤ s)
    (hX : 0 < X) (hrn : 0 < rn) (hpl : 0 < pl) (hε : 0 ≤ ε) (hx1 : 0 ≤ x1)
    (h1 : s * nrm (a - bo) ≤ X * x1)
    (h2 : |(s • (a - bo)) ⬝ᵥ ((nrm bo)⁻¹ • bo)| ≤ X * x2)
    (h3 : X * rn * pl ≤ s * nrm bo) (h3' : s * nrm bo ≤ X * rn * eo)
    (h4 : s * nrm (b - bo) ≤ X * ε) (hεpl : ε / rn < pl) :
    s * nrm (a - b) ≤ X * (x1 + ε) ∧
    |(s • (a - b)) ⬝ᵥ ((nrm b)⁻¹ • b)| ≤ X * (x2 + ε * (1 + 2 * x1 / (pl * rn))) ∧
    X * rn * (pl - ε / rn) ≤ s * nrm b ∧ s * nrm b ≤ X * rn * (eo + ε / rn) ∧ 0 < nrm b := by
  have hD : nrm (bo - b) = nrm (b - bo) := by
    have e : bo - b = (-1 : ℝ) • (b - bo) := by ext i; simp
    rw [e, BstLean.Part153.nrm_smul]; simp
  have hB0 := BstLean.Part153.nrm_nonneg b
  have hBo0 := BstLean.Part153.nrm_nonneg bo
  have hD0 := BstLean.Part153.nrm_nonneg (b - bo)
  have hA0 := BstLean.Part153.nrm_nonneg (a - bo)
  have hXε : X * ε = X * rn * (ε / rn) := by field_simp
  -- (a)
  have ha : s * nrm (a - b) ≤ X * (x1 + ε) := by
    have e : a - b = (a - bo) + (bo - b) := by abel
    have h := BstLean.Part153.nrm_add_le (a - bo) (bo - b)
    rw [← e, hD] at h
    have := mul_le_mul_of_nonneg_left h hs
    linarith only [this, h1, h4]
  -- (c)
  have habs := abs_le.mp (BstLean.Part153.abs_nrm_sub_le b bo)
  have hc1 : X * rn * (pl - ε / rn) ≤ s * nrm b := by
    have := mul_le_mul_of_nonneg_left (show nrm bo - nrm (b - bo) ≤ nrm b by linarith only [habs.1]) hs
    linarith only [this, h3, h4, hXε]
  have hc2 : s * nrm b ≤ X * rn * (eo + ε / rn) := by
    have := mul_le_mul_of_nonneg_left (show nrm b ≤ nrm bo + nrm (b - bo) by linarith only [habs.2]) hs
    linarith only [this, h3', h4, hXε]
  have hsB : 0 < s * nrm b :=
    lt_of_lt_of_le (mul_pos (mul_pos hX hrn) (sub_pos.mpr hεpl)) hc1
  have hsBo : 0 < s * nrm bo := lt_of_lt_of_le (mul_pos (mul_pos hX hrn) hpl) h3
  have hs' : 0 < s := by
    rcases hs.eq_or_lt with h | h
    · rw [← h] at hsB; simp at hsB
    · exact h
  have hB : 0 < nrm b := (pos_iff_pos_of_mul_pos hsB).mp hs'
  have hBo : 0 < nrm bo := (pos_iff_pos_of_mul_pos hsBo).mp hs'
  refine ⟨ha, ?_, hc1, hc2, hB⟩
  -- (b)
  have hdec : (s • (a - b)) ⬝ᵥ ((nrm b)⁻¹ • b) =
      (s • (a - bo)) ⬝ᵥ ((nrm bo)⁻¹ • bo) +
      (s • (a - bo)) ⬝ᵥ ((nrm b)⁻¹ • b - (nrm bo)⁻¹ • bo) +
      (s • (bo - b)) ⬝ᵥ ((nrm b)⁻¹ • b) := by
    have e : s • (a - b) = s • (a - bo) + s • (bo - b) := by
      rw [← smul_add]; congr 1; abel
    rw [e, add_dotProduct, dotProduct_sub]; ring
  have hunit : nrm ((nrm b)⁻¹ • b) = 1 := by
    rw [BstLean.Part153.nrm_smul, abs_of_pos (inv_pos.mpr hB), inv_mul_cancel₀ hB.ne']
  have ht3 : |(s • (bo - b)) ⬝ᵥ ((nrm b)⁻¹ • b)| ≤ X * ε := by
    have h := BstLean.Part153.abs_dot_le_nrm (s • (bo - b)) ((nrm b)⁻¹ • b)
    rw [hunit, BstLean.Part153.nrm_smul, abs_of_pos hs', hD, mul_one] at h
    exact h.trans h4
  have hdiff : nrm ((nrm b)⁻¹ • b - (nrm bo)⁻¹ • bo) ≤ 2 * ε / (pl * rn) := by
    have e : (nrm b)⁻¹ • b - (nrm bo)⁻¹ • bo =
        (nrm bo)⁻¹ • (b - bo) + ((nrm b)⁻¹ - (nrm bo)⁻¹) • b := by
      ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h := BstLean.Part153.nrm_add_le ((nrm bo)⁻¹ • (b - bo)) (((nrm b)⁻¹ - (nrm bo)⁻¹) • b)
    rw [← e, BstLean.Part153.nrm_smul, BstLean.Part153.nrm_smul,
      abs_of_pos (inv_pos.mpr hBo)] at h
    have e2 : |(nrm b)⁻¹ - (nrm bo)⁻¹| * nrm b = |nrm bo - nrm b| / nrm bo := by
      have : (nrm b)⁻¹ - (nrm bo)⁻¹ = (nrm bo - nrm b) / (nrm b * nrm bo) := by
        field_simp
      rw [this, abs_div, abs_of_pos (mul_pos hB hBo)]
      field_simp
    rw [e2] at h
    have h5 : |nrm bo - nrm b| ≤ nrm (b - bo) := by
      rw [abs_sub_comm]; exact BstLean.Part153.abs_nrm_sub_le b bo
    have h6 : nrm ((nrm b)⁻¹ • b - (nrm bo)⁻¹ • bo) ≤ 2 * nrm (b - bo) / nrm bo := by
      have : |nrm bo - nrm b| / nrm bo ≤ nrm (b - bo) / nrm bo :=
        div_le_div_of_nonneg_right h5 hBo.le
      calc nrm ((nrm b)⁻¹ • b - (nrm bo)⁻¹ • bo)
          ≤ (nrm bo)⁻¹ * nrm (b - bo) + nrm (b - bo) / nrm bo := by linarith only [h, this]
        _ = 2 * nrm (b - bo) / nrm bo := by field_simp; ring
    refine h6.trans ?_
    rw [div_le_div_iff₀ hBo (mul_pos hpl hrn)]
    have hk : s * X * (nrm (b - bo) * (pl * rn)) ≤ s * X * (ε * nrm bo) := by
      have k1 : s * nrm (b - bo) * (X * rn * pl) ≤ X * ε * (X * rn * pl) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      have k2 : X * ε * (X * rn * pl) ≤ X * ε * (s * nrm bo) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      nlinarith only [k1, k2]
    have := le_of_mul_le_mul_left hk (mul_pos hs' hX)
    linarith only [this]
  have ht2 : |(s • (a - bo)) ⬝ᵥ ((nrm b)⁻¹ • b - (nrm bo)⁻¹ • bo)| ≤
      X * x1 * (2 * ε / (pl * rn)) := by
    have h := BstLean.Part153.abs_dot_le_nrm (s • (a - bo)) ((nrm b)⁻¹ • b - (nrm bo)⁻¹ • bo)
    rw [BstLean.Part153.nrm_smul, abs_of_pos hs'] at h
    exact h.trans (mul_le_mul h1 hdiff (BstLean.Part153.nrm_nonneg _) (by positivity))
  rw [hdec]
  have e : X * (x2 + ε * (1 + 2 * x1 / (pl * rn))) =
      X * x2 + X * x1 * (2 * ε / (pl * rn)) + X * ε := by ring
  rw [e]
  exact (abs_add_three _ _ _).trans (add_le_add (add_le_add h2 ht2) ht3)

end BstLean.Part154
