import BstLean.Part291ConditionalSplit

/-! Actual high conditional moments, extracted from the proved FL argument.
The latitude moment is an explicit input on the original product measure. -/
namespace BstLean.BlueprintLow
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162

theorem paper_high_conditional_moments {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    {wl ws σl η CA : ℝ} (hwl : 0 ≤ wl) (hws : 0 < ws) (hσl : 0 < σl)
    (h0 : 0 < η) (h1 : η < 1) (hCA : normSq c.2.1.2 ≤ CA) :
    let d := dPaper D c wl ws σl η h0 h1
    (∀ k : ℕ, k ≠ 0 → ∀ τ : ℝ, 0 < τ →
      (∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ (2 * k)
        ∂stdGauss (Fin (n - 1)) ∂muI n) ≤ τ ^ (2 * k) →
      (∫ a in keptIx D c d, condMom d (epsF D c d) (2 * k) a ∂muI n) ≤
        (cEw ws σl * ((iotaP η (2 * k) + c2η η + c3η η ws σl) * τ)) ^ (2 * k)) ∧
    (∀ k : ℕ, k ≠ 0 → ∀ τ : ℝ, 0 < τ →
      (∫ a, ∫ v, |lA D c a v - lbar D c a| ^ (2 * k)
        ∂stdGauss (Fin (n - 1)) ∂muI n) ≤ τ ^ (2 * k) →
      (∫ a in keptIx D c d, condMom d (delF D c d) (2 * k) a ∂muI n) ≤
        (√CA / σl * ((iotaP η (2 * k) + c2η η) * τ)) ^ (2 * k)) := by
  dsimp only
  set ν := stdGauss (Fin (n - 1)) with hν
  set d := dPaper D c wl ws σl η h0 h1 with hd
  set K := keptIx D c d with hK
  have mK : MeasurableSet K := measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hCA0 : 0 ≤ CA := (normSq_nonneg _).trans hCA
  set L := √CA * (2 * wl) / σl with hL
  have hL0 : 0 ≤ L := by positivity
  have hε0 : 0 ≤ eps0 ws σl := by
    unfold eps0; have : 0 ≤ 2 * ws / σl := by positivity
    nlinarith
  have mS : ∀ a, Measurable (fun v => sgA D c a v) := fun a => measurable_sgA_left D c a
  have mLa : ∀ a, Measurable (fun v => lA D c a v) := fun a => measurable_lA_left D c a
  have bS : ∀ a v, |sgA D c a v| ≤ lipSig D c := abs_sgA_le hn D c
  have bLa : ∀ a v, |lA D c a v| ≤ lipLam D c := abs_lA_le hn D c
  -- window
  have hwin : ∀ a ∈ K, σl ^ 2 ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ eps0 ws σl ∧ |lA D c a v - d.lam0 a| ≤ 2 * wl ∧
      normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ L ^ 2 := by
    intro a ha
    obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
    obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, -, -⟩ :=
      idx_scale (measurableSet_slice d a) hm (mS a) (bS a) hws.le hσl hGψ
    have hS0 : σl ^ 2 ≤ d.S0 a := by rw [hS]; exact (pow_le_pow_left₀ hσl.le hlo 2).trans s1
    have hφw := idx_phi_window (measurableSet_slice d a) hm (mLa a) (bLa a) hGφ
    refine ⟨hS0, fun v hv => ⟨?_, ?_, ?_⟩⟩
    · rw [sA_eq, hS]
      obtain ⟨x1, x2⟩ := hG' v hv
      exact idx_eps_window hσl hws.le hlo hhi s1 s2 x1 x2
    · rw [hl]; exact hφw v hv
    · have hδ := hφw v hv
      rw [← hl] at hδ
      have h2 : (lA D c a v - d.lam0 a) ^ 2 ≤ (2 * wl) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
      have h3 : normSq c.2.1.2 / d.S0 a ≤ CA / σl ^ 2 :=
        div_le_div₀ hCA0 hCA (by positivity) hS0
      calc normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤ CA / σl ^ 2 * (2 * wl) ^ 2 :=
            mul_le_mul h3 h2 (sq_nonneg _) (by positivity)
        _ = L ^ 2 := by rw [hL, div_pow, mul_pow (√CA), Real.sq_sqrt hCA0]; ring
  -- the fields as functions of `(a, v)` and their bounds
  have hvE : ∀ a v, v ∉ slice d a → epsF D c d a v = 0 := fun a v hv => by
    simp only [epsF, eG, Set.indicator_of_notMem hv]
  have hvD : ∀ a v, v ∉ slice d a → delF D c d a v = 0 := fun a v hv => by
    simp only [delF, dG, Set.indicator_of_notMem hv, mul_zero]
  have mE := measurable_epsF D c d
  have mD := measurable_delF D c d
  have hKβ : ∀ a ∈ K, removed ν d.good a < 1 := fun a ha => lt_of_le_of_lt ha.2 d.eta_lt
  have hbE : ∀ a ∈ K, ∀ v, |epsF D c d a v| ≤ eps0 ws σl := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [epsF, eG, Set.indicator_of_mem hv]; exact ((hwin a ha).2 v hv).1
    · rw [hvE a v hv, abs_zero]; exact hε0
  have hbD : ∀ a ∈ K, ∀ v, |delF D c d a v| ≤ L := fun a ha v => by
    by_cases hv : v ∈ slice d a
    · simp only [delF, dG, Set.indicator_of_mem hv]
      have h := ((hwin a ha).2 v hv).2.2
      have hS : 0 < d.S0 a := lt_of_lt_of_le (by positivity) (hwin a ha).1
      have h2 : √(normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2) ≤ √(L ^ 2) :=
        Real.sqrt_le_sqrt h
      rwa [Real.sqrt_mul (div_nonneg (normSq_nonneg _) hS.le), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq hL0, ← abs_of_nonneg (Real.sqrt_nonneg (normSq c.2.1.2 / d.S0 a)),
        ← abs_mul] at h2
    · rw [hvD a v hv, abs_zero]; exact hL0
  -- the latitude moments as functions of `a`
  have hgb : ∀ a, |gbar D c a| ≤ lipSig D c := fun a => by
    unfold gbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |sgA D c a v| ∂ν ≤ ∫ _v, lipSig D c ∂ν :=
          integral_mono (intB (mS a).abs (M := lipSig D c) fun v => by rw [abs_abs]; exact bS a v)
            (integrable_const _) (bS a)
      _ = lipSig D c := by simp
  have hlb : ∀ a, |lbar D c a| ≤ lipLam D c := fun a => by
    unfold lbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |lA D c a v| ∂ν ≤ ∫ _v, lipLam D c ∂ν :=
          integral_mono (intB (mLa a).abs (M := lipLam D c) fun v => by rw [abs_abs]; exact bLa a v)
            (integrable_const _) (bLa a)
      _ = lipLam D c := by simp
  set Ks := 2 * lipSig D c with hKs
  set Kl := 2 * lipLam D c with hKl
  have hKs0 : 0 ≤ Ks := by have := lipSig_nonneg D c; positivity
  have hKl0 : 0 ≤ Kl := by have := lipLam_nonneg D c; positivity
  have bYs : ∀ a v, |sgA D c a v - gbar D c a| ≤ Ks := fun a v =>
    (abs_sub _ _).trans (by linarith [bS a v, hgb a])
  have bYl : ∀ a v, |lA D c a v - lbar D c a| ≤ Kl := fun a v =>
    (abs_sub _ _).trans (by linarith [bLa a v, hlb a])
  have mYs : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => sgA D c p.1 p.2 - gbar D c p.1) :=
    (measurable_sgA D c).sub ((measurable_gbar D c).comp measurable_fst)
  have mYl : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => lA D c p.1 p.2 - lbar D c p.1) :=
    (measurable_lA D c).sub ((measurable_lbar D c).comp measurable_fst)
  have mInt : ∀ {F : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable F →
      Measurable (fun a => ∫ v, F (a, v) ∂ν) := fun hF =>
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have mVs : Measurable (fun a => ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν) := mInt (mYs.pow_const 2)
  have mVl : Measurable (fun a => ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν) := mInt (mYl.pow_const 2)
  have mMs : ∀ p : ℕ, Measurable (fun a => ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν) := fun p =>
    mInt (mYs.abs.pow_const p)
  have mMl : ∀ p : ℕ, Measurable (fun a => ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν) := fun p =>
    mInt (mYl.abs.pow_const p)
  have bInt : ∀ {f : (Fin (n - 1) → ℝ) → ℝ} {M : ℝ}, Measurable f → (∀ v, 0 ≤ f v) →
      (∀ v, f v ≤ M) → 0 ≤ ∫ v, f v ∂ν ∧ ∫ v, f v ∂ν ≤ M := fun {f} {M} hf h0 hM => by
    refine ⟨integral_nonneg h0, ?_⟩
    calc ∫ v, f v ∂ν ≤ ∫ _v, M ∂ν :=
          integral_mono (intB hf (M := M) fun v => by rw [abs_of_nonneg (h0 v)]; exact hM v)
            (integrable_const _) hM
      _ = M := by simp
  have bVs : ∀ a, 0 ≤ ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν ∧
      ∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν ≤ Ks ^ 2 := fun a =>
    bInt (((mS a).sub_const _).pow_const 2) (fun v => sq_nonneg _)
      (fun v => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bYs a v) 2)
  have bVl : ∀ a, 0 ≤ ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν ∧
      ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν ≤ Kl ^ 2 := fun a =>
    bInt (((mLa a).sub_const _).pow_const 2) (fun v => sq_nonneg _)
      (fun v => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bYl a v) 2)
  have bMs : ∀ p : ℕ, ∀ a, 0 ≤ ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν ∧
      ∫ v, |sgA D c a v - gbar D c a| ^ p ∂ν ≤ Ks ^ p := fun p a =>
    bInt (((mS a).sub_const _).abs.pow_const p) (fun v => pow_nonneg (abs_nonneg _) _)
      (fun v => pow_le_pow_left₀ (abs_nonneg _) (bYs a v) p)
  have bMl : ∀ p : ℕ, ∀ a, 0 ≤ ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν ∧
      ∫ v, |lA D c a v - lbar D c a| ^ p ∂ν ≤ Kl ^ p := fun p a =>
    bInt (((mLa a).sub_const _).abs.pow_const p) (fun v => pow_nonneg (abs_nonneg _) _)
      (fun v => pow_le_pow_left₀ (abs_nonneg _) (bYl a v) p)
  have hηm : ∀ a ∈ K, (ν.real (slice d a))⁻¹ ≤ (1 - η)⁻¹ := fun a ha =>
    inv_anti₀ (by linarith) (kept_facts hn D c h0 h1 ha).2.1
  have hc2 : 0 < c2η η := Real.sqrt_pos.mpr (div_pos h0 (by linarith))
  have hc3 : 0 < c3η η ws σl := by
    unfold c3η; have := Real.sqrt_pos.mpr (show (0:ℝ) < 1 - η by linarith); positivity
  have hcE : 0 ≤ cEw ws σl := by unfold cEw; positivity
  have hcV : 0 ≤ cVw ws σl := by unfold cVw; positivity
  -- the square-root of the variance and Jensen
  have msd : ∀ (F : Ix n → (Fin (n - 1) → ℝ) → ℝ),
      Measurable (fun a => ∫ v, F a v ^ 2 ∂ν) → Measurable (fun a => √(∫ v, F a v ^ 2 ∂ν)) :=
    fun F h => h.sqrt
  have sd_pow : ∀ {x : ℝ}, 0 ≤ x → ∀ k : ℕ, √x ^ (2 * k) = x ^ k := fun {x} hx k => by
    rw [pow_mul, Real.sq_sqrt hx]
  -- (Ie_k)
  have Ie : ∀ k : ℕ, k ≠ 0 → ∀ τ : ℝ, 0 < τ →
      ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ (2 * k) ∂ν ∂muI n ≤ τ ^ (2 * k) →
      ∫ a in K, condMom d (epsF D c d) (2 * k) a ∂muI n ≤
        (cEw ws σl * ((iotaP η (2 * k) + c2η η + c3η η ws σl) * τ)) ^ (2 * k) := by
    intro k hk τ hτ hMτ
    have hp : 2 * k ≠ 0 := by omega
    refine int_three (muI n) mK (mMs (2 * k)) (msd (fun a v => sgA D c a v - gbar D c a) mVs)
      (Kb := Ks ^ (2 * k) + Ks) (fun a => ?_) (fun a => ?_) ?_ (fun a => (bMs _ a).1)
      (fun a => Real.sqrt_nonneg _) (fun a => ?_) hcE (iotaP_pos h1 _) (iotaP_pow h1 hp) hc2 hc3
      hτ (fun a ha => ?_) hMτ
    · rw [abs_of_nonneg (bMs _ a).1]; linarith [(bMs (2 * k) a).2]
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have : √(∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂ν) ≤ Ks := by
        rw [show Ks = √(Ks ^ 2) from (Real.sqrt_sq hKs0).symm]; exact Real.sqrt_le_sqrt (bVs a).2
      have : 0 ≤ Ks ^ (2 * k) := pow_nonneg hKs0 _
      linarith
    · refine Integrable.of_bound (measurable_condMom d mE _).aestronglyMeasurable
        (eps0 ws σl ^ (2 * k)) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mE hvE (hKβ a ha) (hbE a ha) hp
      rw [Real.norm_eq_abs, abs_of_nonneg b0]; exact b1
    · rw [sd_pow (bVs a).1]
      have := jensen_pow ν (((mS a).sub_const (gbar D c a))) (bYs a) k
      simpa using this
    · obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      rw [cm_eps hn D c h0 h1 ha hp]
      exact idx_eps_mom (measurableSet_slice d a) hm (mS a) (bS a) hws.le hσl hGψ hm1 h1 (2 * k)
        (mul_pos (iotaP_pos h1 _) hτ) (mul_pos hc2 hτ) (mul_pos hc3 hτ)
  -- (Id_k)
  have Id : ∀ k : ℕ, k ≠ 0 → ∀ τ : ℝ, 0 < τ →
      ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ (2 * k) ∂ν ∂muI n ≤ τ ^ (2 * k) →
      ∫ a in K, condMom d (delF D c d) (2 * k) a ∂muI n ≤
        (√CA / σl * ((iotaP η (2 * k) + c2η η) * τ)) ^ (2 * k) := by
    intro k hk τ hτ hMτ
    have hp : 2 * k ≠ 0 := by omega
    refine int_two (muI n) mK (mMl (2 * k)) (msd (fun a v => lA D c a v - lbar D c a) mVl)
      (Kb := Kl ^ (2 * k) + Kl) (fun a => ?_) (fun a => ?_) ?_ (fun a => (bMl _ a).1)
      (fun a => Real.sqrt_nonneg _) (fun a => ?_) (by positivity) (iotaP_pos h1 _)
      (iotaP_pow h1 hp) hc2 hτ (fun a ha => ?_) hMτ
    · rw [abs_of_nonneg (bMl _ a).1]; linarith [(bMl (2 * k) a).2]
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have : √(∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν) ≤ Kl := by
        rw [show Kl = √(Kl ^ 2) from (Real.sqrt_sq hKl0).symm]; exact Real.sqrt_le_sqrt (bVl a).2
      have : 0 ≤ Kl ^ (2 * k) := pow_nonneg hKl0 _
      linarith
    · refine Integrable.of_bound (measurable_condMom d mD _).aestronglyMeasurable
        (L ^ (2 * k)) (ae_restrict_of_forall_mem mK fun a ha => ?_)
      obtain ⟨b0, b1⟩ := condMom_bounds d mD hvD (hKβ a ha) (hbD a ha) hp
      rw [Real.norm_eq_abs, abs_of_nonneg b0]; exact b1
    · rw [sd_pow (bVl a).1]
      have := jensen_pow ν (((mLa a).sub_const (lbar D c a))) (bYl a) k
      simpa using this
    · obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
      have hS0 : σl ^ 2 ≤ ∫ w, sgA D c a w ^ 2 ∂nrm ν (slice d a) := hS ▸ (hwin a ha).1
      rw [cm_del hn D c h0 h1 ha hp]
      have h := idx_del_mom (measurableSet_slice d a) hm (mLa a) (bLa a) hσl hS0
        (normSq_nonneg c.2.1.2) hm1 h1 (2 * k) (mul_pos (iotaP_pos h1 (2 * k)) hτ) (mul_pos hc2 hτ)
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt hCA) hσl.le) _)
          (pow_nonneg (add_pos (mul_pos (iotaP_pos h1 (2 * k)) hτ) (mul_pos hc2 hτ)).le _)) ?_)
      have := (bMl (2 * k) a).1
      have : 0 < iotaP η (2 * k) * τ := mul_pos (iotaP_pos h1 _) hτ
      have : 0 < c2η η * τ := mul_pos hc2 hτ
      have : (0 : ℝ) ≤ (1 - η)⁻¹ := inv_nonneg.mpr (by linarith)
      positivity
  exact ⟨Ie, Id⟩

end BstLean.BlueprintLow
