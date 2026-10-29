import BstLean.Part211Energy

/-! Original energy and finite-rule events for the computed binomial centre. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (hO gO bO bT rhoC thetaC epsJ sO2)
open BstLean.Part153 (nrm Pb Eop GamS BadE BadBe)
open BstLean.Part154 (BadChi BadPb)
open BstLean.Part206

noncomputable def gMinus (n : ℕ) : ℝ := (√(1 - 2 / (n : ℝ) ^ 2) - 2 * √12 / n) ^ 2
noncomputable def gPlus (n : ℕ) : ℝ := (1 + 2 * √12 / (n : ℝ)) ^ 2

theorem energy_on_source {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A ∉ BadE n c τ)
    (hGuard : 2 * √12 / (n : ℝ) ≤ √(1 - 2 / (n : ℝ) ^ 2)) :
    (2 / n * rhoC c τ ^ 2) * gMinus n ≤ gO A c τ ∧
      gO A c τ ≤ (2 / n * rhoC c τ ^ 2) * gPlus n := by
  have h := BstLean.Part153.Ee_bounds hn c τ (by norm_num : (0 : ℝ) ≤ 12) (not_lt.mp hA)
  have hm := one_le_mA (by omega : 1 ≤ n)
  rw [BstLean.Part153.GamS_eq_gO hm] at h
  rw [BstLean.Part150.rhoC_sqP]
  exact ⟨by simpa only [gMinus, mul_comm] using h.2 hGuard,
    by simpa only [gPlus, mul_comm] using h.1⟩

/-- FC supplies the finite-rule error in the normalization used by both energy formulas. -/
theorem finite_energy_on_source {n J : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    {τ cs δe : ℝ} (hτ : 0 < τ) (hcs : 0 < cs) (hδe : 0 ≤ δe)
    (hop : A ∈ Eop n) (hsc : cs * τ ^ 2 ≤ sO2 A c τ)
    (hEe : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2)
    (hχ : M ∉ BadChi n J A c τ 12) :
    √(2 / (mA n : ℝ)) / √(2 / n * rhoC c τ ^ 2) *
      nrm (bT J J A M c τ - bO A M c τ) ≤
        epsJ n J J (BstLean.Part153.wn n) cs δe (BstLean.Part154.deltaChi n 12) / √(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have hγ : 0 < 2 / (n : ℝ) := by positivity
  have h := BstLean.Part154.FC_iii hn hJ A M c hτ hcs hδe (by norm_num) hop hsc hEe hχ
  have hd := div_le_div_of_nonneg_right h (sqrt_nonneg (2 / (n : ℝ)))
  have he : √(2 / n * rhoC c τ ^ 2) = √(2 / (n : ℝ)) * rhoC c τ := by
    rw [sqrt_mul hγ.le, sqrt_sq hρ.le]
  rw [sqrt_div hγ.le] at hd
  rw [he]
  convert hd using 1 <;> field_simp

/-- The original lower norm event has the same deviation as the upper norm event. -/
theorem lower_second_on_source {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (hM : M ∉ BadPb A c τ 12) :
    (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) -
      √(24 * (2 / (mA n : ℝ)) * gO A c τ) ≤ Pb A c τ M := by
  simp only [BadPb, mem_setOf_eq, not_lt] at hM
  have h := hM
  change _ - √(2 * 12 * (2 / (mA n : ℝ))) * √(GamS A c τ) ≤ _ at h
  rw [BstLean.Part153.GamS_eq_gO (one_le_mA hn), ← sqrt_mul (by positivity)] at h
  simpa only [show (2 : ℝ) * 12 = 24 by norm_num] using h

theorem upper_second_on_source {n : ℕ}
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (hM : M ∉ BadBe n c τ A) :
    Pb A c τ M ≤ (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) +
      √(24 * (2 / (mA n : ℝ)) * gO A c τ) := by
  simpa only [BadBe, mem_setOf_eq, not_lt, show (2 : ℝ) * 12 = 24 by norm_num] using hM

def FirstEnergyBad (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  ((Eop n)ᶜ ∪ {A | sO2 A c τ < BstLean.Part154.csC * τ ^ 2}) ∪ BadE n c τ ∪
    ((FirstUpper n c τ)ᶜ ∪ (FirstLower n c τ)ᶜ)

def SecondEnergyBad (n J : ℕ) (c : Fin n → ℝ) (τ : ℝ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  (BadBe n c τ A ∪ BadPb A c τ 12) ∪ BadChi n J A c τ 12

def EnergySource (n J : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {p | p.1 ∉ FirstEnergyBad n c τ ∧ p.2 ∉ SecondEnergyBad n J c τ p.1}

theorem first_energy_bad_charge {n : ℕ} (hn : 4096 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (FirstEnergyBad n c τ) ≤
      exp (-(n : ℝ) / 2) + 3445 / (n : ℝ) ^ 2 + 4 * exp (-12) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let μ := gaussMat (mA n) n (2 / (n : ℝ))
  let S := {A : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A c τ < BstLean.Part154.csC * τ ^ 2}
  have h1 := measureReal_union_le (μ := μ) (Eop n)ᶜ S
  have h2 := measureReal_union_le (μ := μ) ((Eop n)ᶜ ∪ S) (BadE n c τ)
  have h3 := measureReal_union_le (μ := μ) (FirstUpper n c τ)ᶜ (FirstLower n c τ)ᶜ
  have h4 := measureReal_union_le (μ := μ) (((Eop n)ᶜ ∪ S) ∪ BadE n c τ)
    ((FirstUpper n c τ)ᶜ ∪ (FirstLower n c τ)ᶜ)
  have hop := BstLean.Part153.Eop_prob hn1
  have hsc := BstLean.Part153.Esc_prob hn c hτ
  have he := BstLean.Part153.Ee_prob (m := mA n) c τ
    (show 0 < 2 / (n : ℝ) by positivity) (Lc := 12) (by norm_num)
  obtain ⟨hU, hL⟩ := first_source_charges hn1 c hτ
  change μ.real (FirstEnergyBad n c τ) ≤ _
  change μ.real (Eop n)ᶜ ≤ _ at hop
  change μ.real S ≤ _ at hsc
  change μ.real (BadE n c τ) ≤ _ at he
  change μ.real (FirstUpper n c τ)ᶜ ≤ _ at hU
  change μ.real (FirstLower n c τ)ᶜ ≤ _ at hL
  change μ.real ((((Eop n)ᶜ ∪ S) ∪ BadE n c τ) ∪
    ((FirstUpper n c τ)ᶜ ∪ (FirstLower n c τ)ᶜ)) ≤ _
  linarith

theorem second_energy_bad_charge {n : ℕ} (hn : 1 ≤ n) (J : ℕ) (c : Fin n → ℝ) (τ : ℝ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))).real (SecondEnergyBad n J c τ A) ≤
      3 * exp (-12) := by
  let μ := gaussMat (mA n) (mA n) (2 / (mA n : ℝ))
  have h1 := measureReal_union_le (μ := μ) (BadBe n c τ A) (BadPb A c τ 12)
  have h2 := measureReal_union_le (μ := μ) (BadBe n c τ A ∪ BadPb A c τ 12)
    (BadChi n J A c τ 12)
  have hb := BstLean.Part153.Ebe_prob (one_le_mA hn) A c τ (Lc := 12) (by norm_num)
  have hp := BstLean.Part154.EPb_prob (one_le_mA hn) A c τ (Lc := 12) (by norm_num)
  have hc := BstLean.Part154.EChi_prob hn J A c τ (Lc := 12) (by norm_num)
  change μ.real (BadBe n c τ A) ≤ _ at hb
  change μ.real (BadPb A c τ 12) ≤ _ at hp
  change μ.real (BadChi n J A c τ 12) ≤ _ at hc
  change μ.real ((BadBe n c τ A ∪ BadPb A c τ 12) ∪ BadChi n J A c τ 12) ≤ _
  linarith

lemma measurable_second_energy_bad {n : ℕ} (hn : 1 ≤ n) (J : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    MeasurableSet {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ | p.2 ∈ SecondEnergyBad n J c τ p.1} := by
  have hb : MeasurableSet {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ | p.2 ∈ BadBe n c τ p.1} :=
    measurableSet_lt
      (((BstLean.Part153.measurable_int_Pb c τ).comp measurable_fst).add
        ((((BstLean.Part153.measurable_gO_A1 (one_le_mA hn) c τ).comp measurable_fst).const_mul _).sqrt))
      (BstLean.Part153.measurable_Pb_joint c τ)
  exact (hb.union (BstLean.Part154.measurableSet_BadPb_joint (one_le_mA hn) c τ 12)).union
    (BstLean.Part154.measurableSet_BadChi_joint hn J c τ 12)

/-- The full energy source intersection has the paper's seven concentration payments. -/
theorem energy_source_charge {n : ℕ} (hn : 4096 ≤ n) (J : ℕ) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    (BstLean.Part153.nuA n).real (EnergySource n J c τ)ᶜ ≤
      exp (-(n : ℝ) / 2) + 3445 / (n : ℝ) ^ 2 + 7 * exp (-12) := by
  have hn1 : 1 ≤ n := by omega
  let B1 := {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ | p.1 ∈ FirstEnergyBad n c τ}
  let B2 := {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ | p.2 ∈ SecondEnergyBad n J c τ p.1}
  have he : (EnergySource n J c τ)ᶜ = B1 ∪ B2 := by
    ext p
    simp only [EnergySource, B1, B2, mem_compl_iff, mem_setOf_eq, mem_union, not_and_or, not_not]
  have h1 : (BstLean.Part153.nuA n).real B1 ≤
      exp (-(n : ℝ) / 2) + 3445 / (n : ℝ) ^ 2 + 4 * exp (-12) := by
    rw [BstLean.Part153.prod_real_fst]
    exact first_energy_bad_charge hn c hτ
  have h2 : (BstLean.Part153.nuA n).real B2 ≤ 3 * exp (-12) :=
    BstLean.Part153.prod_real_le_of_fibre (measurable_second_energy_bad hn1 J c τ)
      (by positivity) (fun A => second_energy_bad_charge hn1 J c τ A)
  rw [he]
  have h := measureReal_union_le (μ := BstLean.Part153.nuA n) B1 B2
  linarith

lemma csC_positive : 0 < BstLean.Part154.csC := by
  have hp : 1 / π < 1 := by rw [div_lt_one pi_pos]; linarith [pi_gt_three]
  unfold BstLean.Part154.csC
  exact mul_pos (by norm_num) (by linarith)

noncomputable def finiteEnergy (n J : ℕ) (δe : ℝ) : ℝ :=
  epsJ n J J (BstLean.Part153.wn n) BstLean.Part154.csC δe (BstLean.Part154.deltaChi n 12)

lemma finiteEnergy_nonneg (n J : ℕ) {δe : ℝ} (hδe : 0 ≤ δe) : 0 ≤ finiteEnergy n J δe := by
  have ha := BstLean.Part150.alphaJ_nonneg J
  have hb := BstLean.Part150.betaJ_nonneg J
  have hc := csC_positive
  unfold finiteEnergy epsJ BstLean.Part154.deltaChi BstLean.Part153.wn
  positivity

/-- The exact binomial centre has both energy bounds on the complete source intersection.
All remaining guards concern explicit scalar formulas. -/
theorem computed_energy_on_source {n J : ℕ} (hn : 2 ≤ n) (hJ : 1 ≤ J)
    (c : Fin n → ℝ) {τ δe q : ℝ} (hτ : 0 < τ) (hδe : 0 ≤ δe)
    (hq : q ∈ Icc (-1) 1) (hcap : 1 - thetaC c τ ≤ q)
    (hGroot : 2 * √12 / (n : ℝ) < √(1 - 2 / (n : ℝ) ^ 2))
    (hGupper : gPlus n ≤ 1 + δe)
    (hDomain : energyRatio n (gMinus n) q ≤ 1)
    (hRoot : 0 ≤ meanLowerRoot n (thetaC c τ))
    (hBracket : 0 ≤ kappa (meanLowerRoot n (thetaC c τ) ^ 2 / gPlus n) - 2 / (n : ℝ) ^ 2)
    (hGuard : 0 ≤ √(gMinus n * (kappa (meanLowerRoot n (thetaC c τ) ^ 2 / gPlus n) -
      2 / (n : ℝ) ^ 2)) - 2 * √(12 * gPlus n) / n - finiteEnergy n J δe / √(n : ℝ))
    {A : Matrix (Fin (mA n)) (Fin n) ℝ}
    {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hSource : (A, M) ∈ EnergySource n J c τ) :
    energyLower n (gMinus n) (gPlus n) (finiteEnergy n J δe) (thetaC c τ) ≤
        (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) / (2 / n * rhoC c τ ^ 2) ∧
      (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) / (2 / n * rhoC c τ ^ 2) ≤
        energyUpper n (gMinus n) (gPlus n) (finiteEnergy n J δe) q := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn1 c hτ
  have hg : 0 < gMinus n := sq_pos_of_pos (sub_pos.mpr hGroot)
  have hu : 0 < gPlus n := by unfold gPlus; positivity
  have hA : A ∈ Eop n ∧ BstLean.Part154.csC * τ ^ 2 ≤ sO2 A c τ ∧
      A ∉ BadE n c τ ∧ A ∈ FirstUpper n c τ ∧ A ∈ FirstLower n c τ := by
    have h := hSource.1
    simpa only [FirstEnergyBad, mem_union, mem_compl_iff, mem_setOf_eq,
      not_or, not_not, not_lt, and_assoc] using h
  have hM : M ∉ BadBe n c τ A ∧ M ∉ BadPb A c τ 12 ∧ M ∉ BadChi n J A c τ 12 := by
    have h := hSource.2
    simpa only [SecondEnergyBad, mem_union, not_or, and_assoc] using h
  obtain ⟨hLo, hHi⟩ := energy_on_source hn c τ hA.2.2.1 hGroot.le
  have hEe : gO A c τ ≤ (1 + δe) * (2 / n) * rhoC c τ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hGupper
      (show 0 ≤ (2 / n * rhoC c τ ^ 2) by positivity)
    nlinarith only [hHi, h]
  have hFin := finite_energy_on_source hn1 hJ A M c hτ csC_positive hδe hA.1 hA.2.1 hEe hM.2.2
  refine ⟨lower_energy_from_first_source hn1 A c hτ M (bT J J A M c τ) hg hu
      hLo hHi hA.2.2.2.2 hRoot hBracket (lower_second_on_source hn1 A c τ hM.2.1) hFin hGuard,
    TL_from_first_source hn1 A c hτ M (bT J J A M c τ) hg hu.le
      (finiteEnergy_nonneg n J hδe) hq hcap hLo hHi hDomain hA.2.2.2.1
      (upper_second_on_source A c τ hM.1) hFin⟩

theorem computed_hidden_normalization {n J : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (2 / (mA n : ℝ)) * normSq ((rhoC c τ)⁻¹ • bT J J A M c τ) / (2 / (n : ℝ)) =
      (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) / (2 / n * rhoC c τ ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  rw [normSq_smul]
  field_simp

/-- An upper hidden energy below one removes the clipping in the retained noise. -/
theorem retained_noise_energy {n J : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) {τ E : ℝ} (hτ : 0 < τ) (hE : E ≤ 1)
    (hEnergy : (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) /
      (2 / n * rhoC c τ ^ 2) ≤ E) :
    BstLean.Part150.sigT J J A M c τ ^ 2 =
      (2 / n) * (1 - (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) /
        (2 / n * rhoC c τ ^ 2)) ∧
    (2 / n) * (1 - E) ≤ BstLean.Part150.sigT J J A M c τ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hρ := BstLean.Part150.rhoC_posP hn c hτ
  have hγ : 0 < 2 / (n : ℝ) := by positivity
  have he : 2 / (n : ℝ) - (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) / rhoC c τ ^ 2 =
      (2 / n) * (1 - (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) /
        (2 / n * rhoC c τ ^ 2)) := by field_simp
  have h0 : 0 ≤ (2 / n) * (1 - (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) /
      (2 / n * rhoC c τ ^ 2)) := mul_nonneg hγ.le (by linarith)
  have hs : BstLean.Part150.sigT J J A M c τ ^ 2 =
      (2 / n) * (1 - (2 / (mA n : ℝ)) * normSq (bT J J A M c τ) /
        (2 / n * rhoC c τ ^ 2)) := by
    unfold BstLean.Part150.sigT
    rw [he, max_eq_right h0, sq_sqrt h0]
  refine ⟨hs, ?_⟩
  rw [hs]
  exact mul_le_mul_of_nonneg_left (by linarith) hγ.le

#print axioms retained_noise_energy
#print axioms finite_energy_on_source
#print axioms energy_source_charge
#print axioms computed_energy_on_source
#print axioms computed_hidden_normalization
end BstLean.Part211
