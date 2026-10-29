import BstLean.Part206Energy

/-! TL formulas at a fixed retained noise fraction. The moment bounds for the
first-layer mean remain explicit premises. The mean-threshold event is preserved. -/
namespace BstLean.Part206
open MeasureTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (gO hO bO)
open BstLean.Part153 (nrm Pb)

noncomputable def meanRoot (n : ℕ) (q : ℝ) : ℝ :=
  √(kappa q + 5 / (n : ℝ)) + 2 * √12 / (n : ℝ)

noncomputable def energyRatio (n : ℕ) (gLower q : ℝ) : ℝ :=
  meanRoot n q ^ 2 / gLower

noncomputable def energyUpper (n : ℕ) (gLower gUpper finite q : ℝ) : ℝ :=
  (√(gUpper * kappa (energyRatio n gLower q)) +
    2 * √(12 * gUpper) / (n : ℝ) + finite / √(n : ℝ)) ^ 2

noncomputable def meanLowerRoot (n : ℕ) (θ : ℝ) : ℝ :=
  √(kappa (1 - θ) - 8 * θ / (n : ℝ) - 2 / (n : ℝ) ^ 2) - 2 * √12 / (n : ℝ)

/-- The original lower mean-threshold event gives the retained-noise lower mean energy. -/
theorem first_mean_lower_threshold {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {V : Ω → ℝ} {n : ℕ} {θ : ℝ}
    (hV : ∀ x, 0 ≤ V x)
    (hMoment : kappa (1 - θ) - 8 * θ / (n : ℝ) ≤ ∫ x, V x ^ 2 ∂μ)
    (hVar : (∫ x, V x ^ 2 ∂μ) - (∫ x, V x ∂μ) ^ 2 ≤ 2 / (n : ℝ) ^ 2)
    {x : Ω} (hEvent : (∫ x, V x ∂μ) - 2 * √12 / (n : ℝ) ≤ V x)
    (hGuard : 0 ≤ meanLowerRoot n θ) : meanLowerRoot n θ ^ 2 ≤ V x ^ 2 := by
  have hmean0 : 0 ≤ ∫ x, V x ∂μ := integral_nonneg hV
  have hs : kappa (1 - θ) - 8 * θ / (n : ℝ) - 2 / (n : ℝ) ^ 2 ≤
      (∫ x, V x ∂μ) ^ 2 := by linarith
  have hroot := (sqrt_le_sqrt hs).trans_eq (sqrt_sq hmean0)
  have hLower : meanLowerRoot n θ ≤ V x := by unfold meanLowerRoot; linarith
  exact pow_le_pow_left₀ hGuard hLower 2

/-- The local first-layer bound follows from the original mean-threshold event. -/
theorem first_mean_threshold {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {V : Ω → ℝ} {n : ℕ} (hn : 1 ≤ n)
    {q : ℝ} (hq : q ∈ Icc (-1) 1) (hi : Integrable V μ)
    (hi2 : Integrable (fun x => V x ^ 2) μ)
    (hMoment : (∫ x, V x ^ 2 ∂μ) ≤ kappa q + 5 / (n : ℝ))
    {x : Ω} (hV : 0 ≤ V x)
    (hEvent : V x ≤ (∫ x, V x ∂μ) + 2 * √12 / (n : ℝ)) :
    V x ^ 2 ≤ meanRoot n q ^ 2 := by
  have hk := (kappa_mem hq.1 hq.2).1
  have hb : 0 ≤ kappa q + 5 / (n : ℝ) := by positivity
  have hj := (mean_sq_le_second hi hi2).trans hMoment
  have hm : (∫ x, V x ∂μ) ≤ √(kappa q + 5 / (n : ℝ)) := by
    nlinarith [sqrt_nonneg (kappa q + 5 / (n : ℝ)), sq_sqrt hb]
  apply pow_le_pow_left₀ hV
  unfold meanRoot
  linarith

theorem meanRoot_mono {n : ℕ} {q Q : ℝ}
    (hq : q ∈ Icc (-1) 1) (hQ : Q ∈ Icc (-1) 1) (h : q ≤ Q) :
    meanRoot n q ≤ meanRoot n Q := by
  unfold meanRoot
  exact add_le_add (sqrt_le_sqrt (add_le_add
    (kappa_monotoneOn hq hQ h) le_rfl)) le_rfl

theorem energyRatio_mono {n : ℕ} (hn : 1 ≤ n) {gLower q Q : ℝ}
    (hg : 0 < gLower) (hq : q ∈ Icc (-1) 1) (hQ : Q ∈ Icc (-1) 1)
    (h : q ≤ Q) : energyRatio n gLower q ≤ energyRatio n gLower Q := by
  unfold energyRatio
  apply div_le_div_of_nonneg_right _ hg.le
  apply pow_le_pow_left₀ _ (meanRoot_mono hq hQ h)
  unfold meanRoot
  positivity

/-- TL is nonincreasing in the noise fraction on the checked kernel domain. -/
theorem TL_mono {n : ℕ} (hn : 1 ≤ n) {gLower gUpper finite q Q : ℝ}
    (hg : 0 < gLower) (hu : 0 ≤ gUpper) (hf : 0 ≤ finite)
    (hq : q ∈ Icc (-1) 1) (hQ : Q ∈ Icc (-1) 1) (h : q ≤ Q)
    (hDomain : energyRatio n gLower Q ≤ 1) :
    energyUpper n gLower gUpper finite q ≤ energyUpper n gLower gUpper finite Q := by
  have hr := energyRatio_mono hn hg hq hQ h
  have hr0 : 0 ≤ energyRatio n gLower q := by unfold energyRatio; positivity
  have hR0 : 0 ≤ energyRatio n gLower Q := by unfold energyRatio; positivity
  have hk := kappa_monotoneOn ⟨by linarith, hr.trans hDomain⟩
    ⟨by linarith, hDomain⟩ hr
  unfold energyUpper
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add (add_le_add
    (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hk hu)) le_rfl) le_rfl

/-- A noise cell uses its lower endpoint and the retained signal cap together. -/
theorem TL_cell {n : ℕ} (hn : 1 ≤ n) {gLower gUpper finite θ θlo qWorld : ℝ}
    (hg : 0 < gLower) (hu : 0 ≤ gUpper) (hf : 0 ≤ finite)
    (hθ : θ ∈ Icc 0 1) (hlo : θlo ∈ Icc 0 1) (hcell : θlo ≤ θ)
    (hw : qWorld ∈ Icc 0 1) (hWorld : 1 - θ ≤ qWorld)
    (hDomain : energyRatio n gLower qWorld ≤ 1) :
    energyUpper n gLower gUpper finite (1 - θ) ≤
      energyUpper n gLower gUpper finite (min (1 - θlo) qWorld) ∧
    energyUpper n gLower gUpper finite (min (1 - θlo) qWorld) ≤
      energyUpper n gLower gUpper finite qWorld := by
  have hq : 1 - θ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hQ : min (1 - θlo) qWorld ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · exact le_min (by linarith [hlo.2]) (by linarith [hw.1])
    · exact (min_le_right _ _).trans hw.2
  have hw' : qWorld ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hw.1], hw.2⟩
  have hcap := energyRatio_mono hn hg hQ hw' (min_le_right _ _)
  exact ⟨TL_mono hn hg hu hf hq hQ (le_min (by linarith) hWorld)
    (hcap.trans hDomain), TL_mono hn hg hu hf hQ hw' (min_le_right _ _) hDomain⟩

/-- TL for the actual second-layer centre, from retained energy and mean premises. -/
theorem TL_actual {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ)
    {scale gLower gUpper finite q : ℝ} (hs : 0 < scale) (hg : 0 < gLower)
    (hu : 0 ≤ gUpper) (hf : 0 ≤ finite)
    (hLower : scale * gLower ≤ gO A c τ)
    (hUpper : gO A c τ ≤ scale * gUpper)
    (hMean : 2 / (m : ℝ) * normSq (hO A c τ) ≤ scale * meanRoot n q ^ 2)
    (hDomain : energyRatio n gLower q ≤ 1)
    (hEvent : Pb A c τ M ≤ (∫ M, Pb A c τ M ∂gaussMat m m (2 / (m : ℝ))) +
      √scale * (2 * √(12 * gUpper) / (n : ℝ)))
    (hFinite : √(2 / (m : ℝ)) / √scale * nrm (b - bO A M c τ) ≤ finite / √(n : ℝ)) :
    (2 / (m : ℝ)) * normSq b / scale ≤ energyUpper n gLower gUpper finite q := by
  have hG : 0 < gO A c τ := (mul_pos hs hg).trans_le hLower
  have hr : (2 / (m : ℝ) * normSq (hO A c τ)) / gO A c τ ≤
      energyRatio n gLower q := by
    unfold energyRatio
    apply (div_le_div_iff₀ hG hg).mpr
    have h1 := mul_le_mul_of_nonneg_right hMean hg.le
    have h2 := mul_le_mul_of_nonneg_right hLower (sq_nonneg (meanRoot n q))
    nlinarith
  have hO := oracle_energy_upper hm A c τ M hG hs.le hUpper hr hDomain hEvent
  have hratio0 : 0 ≤ energyRatio n gLower q := by unfold energyRatio; positivity
  have hk0 := (kappa_mem (by linarith : -1 ≤ energyRatio n gLower q) hDomain).1
  rw [mul_assoc, sqrt_mul hs.le] at hO
  have he : (√(2 / (m : ℝ)) / √scale) * nrm (bO A M c τ) = Pb A c τ M / √scale := by
    unfold Pb
    ring
  have ho : √(2 / (m : ℝ)) / √scale * nrm (bO A M c τ) ≤
      √(gUpper * kappa (energyRatio n gLower q)) + 2 * √(12 * gUpper) / (n : ℝ) := by
    rw [he, div_le_iff₀ (sqrt_pos.mpr hs)]
    nlinarith only [hO]
  have ha := BstLean.Part153.abs_nrm_sub_le b (bO A M c τ)
  have hab := mul_le_mul_of_nonneg_left (abs_le.mp ha).2
    (show 0 ≤ √(2 / (m : ℝ)) / √scale by positivity)
  have hb : √(2 / (m : ℝ)) / √scale * nrm b ≤
      √(gUpper * kappa (energyRatio n gLower q)) +
      2 * √(12 * gUpper) / (n : ℝ) + finite / √(n : ℝ) := by linarith
  have hb2 := pow_le_pow_left₀ (mul_nonneg
    (div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (BstLean.Part153.nrm_nonneg b)) hb 2
  simpa only [mul_pow, div_pow, sq_sqrt (by positivity : 0 ≤ (2 : ℝ) / m),
    sq_sqrt hs.le, BstLean.Part153.nrm_sq, energyUpper, div_mul_eq_mul_div] using hb2

/-- The original upper mean-threshold event has its original conditional charge. -/
theorem TL_source_charge {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))).real
      {M | (∫ M, Pb A c τ M ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) +
        √(24 * (2 / (mA n : ℝ)) * gO A c τ) < Pb A c τ M} ≤ exp (-12) := by
  simpa only [show (2 : ℝ) * 12 = 24 by norm_num] using
    BstLean.Part153.Ebe_prob (one_le_mA hn) A c τ (Lc := 12) (by norm_num)

theorem TL_source_deviation {n : ℕ} (hn : 1 ≤ n)
    {G scale gUpper : ℝ} (hG : 0 ≤ G) (hs : 0 ≤ scale) (hu : 0 ≤ gUpper)
    (hUpper : G ≤ scale * gUpper) :
    √(24 * (2 / (mA n : ℝ)) * G) ≤
      √scale * (2 * √(12 * gUpper) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hsq := mul_le_mul_of_nonneg_left hUpper
    (show 0 ≤ 24 * (2 / (n : ℝ) ^ 2) by positivity)
  rw [hm]
  have he : (√scale * (2 * √(12 * gUpper) / (n : ℝ))) ^ 2 =
      24 * (2 / (n : ℝ) ^ 2) * (scale * gUpper) := by
    rw [mul_pow, div_pow, mul_pow, sq_sqrt hs, sq_sqrt (by positivity : 0 ≤ 12 * gUpper)]
    ring
  have hroot : √(24 * (2 / (n : ℝ) ^ 2) * G) ^ 2 =
      24 * (2 / (n : ℝ) ^ 2) * G := sq_sqrt (by positivity)
  have hnn : 0 ≤ √scale * (2 * √(12 * gUpper) / (n : ℝ)) := by positivity
  nlinarith only [hsq, he, hroot, hnn, sqrt_nonneg (24 * (2 / (n : ℝ) ^ 2) * G)]

/-- TL uses the source event and adds no new second-layer concentration event. -/
theorem TL_on_source_event {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (b : Fin (mA n) → ℝ)
    {scale gLower gUpper finite q : ℝ} (hs : 0 < scale) (hg : 0 < gLower)
    (hu : 0 ≤ gUpper) (hf : 0 ≤ finite)
    (hLower : scale * gLower ≤ gO A c τ)
    (hUpper : gO A c τ ≤ scale * gUpper)
    (hMean : 2 / (mA n : ℝ) * normSq (hO A c τ) ≤ scale * meanRoot n q ^ 2)
    (hDomain : energyRatio n gLower q ≤ 1)
    (hEvent : Pb A c τ M ≤ (∫ M, Pb A c τ M
      ∂gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) +
        √(24 * (2 / (mA n : ℝ)) * gO A c τ))
    (hFinite : √(2 / (mA n : ℝ)) / √scale * nrm (b - bO A M c τ) ≤ finite / √(n : ℝ)) :
    (2 / (mA n : ℝ)) * normSq b / scale ≤ energyUpper n gLower gUpper finite q := by
  have hDev := TL_source_deviation hn (BstLean.Part153.gO_nonneg' A c τ)
    hs.le hu hUpper
  exact TL_actual hn (one_le_mA hn) A c τ M b hs hg hu hf hLower hUpper hMean
    hDomain (hEvent.trans (add_le_add le_rfl hDev)) hFinite

#print axioms first_mean_threshold
#print axioms first_mean_lower_threshold
#print axioms meanRoot_mono
#print axioms energyRatio_mono
#print axioms TL_mono
#print axioms TL_cell
#print axioms TL_actual
#print axioms TL_source_charge
#print axioms TL_source_deviation
#print axioms TL_on_source_event
end BstLean.Part206
