import BstLean.Part162Pap

/-! The split has normalized good-slice means and retains the original outer
measure. This exposes the window and centering premises used by HQ. -/
namespace BstLean.BlueprintLow
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162

theorem paperSplitPremises {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    {wl ws σl η CA : ℝ} (hwl : 0 ≤ wl) (hws : 0 < ws) (hσl : 0 < σl)
    (h0 : 0 < η) (h1 : η < 1) (hCA : normSq c.2.1.2 ≤ CA)
    (hε : eps0 ws σl < 1) :
    let d := dPaper D c wl ws σl η h0 h1
    let K := keptIx D c d
    0 ≤ eps0 ws σl ∧ eps0 ws σl < 1 ∧
    (∀ a ∈ K, 0 ≤ removed (stdGauss (Fin (n - 1))) d.good a ∧
      removed (stdGauss (Fin (n - 1))) d.good a < 1) ∧
    (∀ a ∈ K, σl ^ 2 ≤ d.S0 a ∧ ∀ v ∈ slice d a,
      |sA D c a v / d.S0 a - 1| ≤ eps0 ws σl ∧
      |lA D c a v - d.lam0 a| ≤ 2 * wl ∧
      normSq c.2.1.2 / d.S0 a * (lA D c a v - d.lam0 a) ^ 2 ≤
        (√CA * (2 * wl) / σl) ^ 2) ∧
    (∀ a ∈ K,
      (∫ v in slice d a, (lA D c a v - d.lam0 a) ∂stdGauss (Fin (n - 1))) = 0 ∧
      (∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂stdGauss (Fin (n - 1))) = 0) := by
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
  -- centring
  have hcent : ∀ a ∈ K, ∫ v in slice d a, (lA D c a v - d.lam0 a) ∂ν = 0 ∧
      ∫ v in slice d a, (sA D c a v / d.S0 a - 1) ∂ν = 0 := by
    intro a ha
    obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
    have ms := measurableSet_slice d a
    have key : ∀ f : (Fin (n - 1) → ℝ) → ℝ, ∫ v in slice d a, f v ∂ν =
        ν.real (slice d a) * ∫ v, f v ∂nrm ν (slice d a) := fun f => by
      rw [integral_nrm ν ms hm, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul, integral_indicator ms]
    obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, -, -⟩ := idx_scale ms hm (mS a) (bS a) hws.le hσl hGψ
    have hS0p : 0 < d.S0 a := by
      rw [hS]; exact lt_of_lt_of_le (by have := lt_of_lt_of_le hσl hlo; positivity) s1
    have iL : IntegrableOn (fun v => lA D c a v) (slice d a) ν := (intB (mLa a) (bLa a)).integrableOn
    have iSA : IntegrableOn (fun v => sA D c a v / d.S0 a) (slice d a) ν :=
      (intB (((mS a).pow_const 2).div_const _) (M := lipSig D c ^ 2 / d.S0 a) fun v => by
        rw [abs_div, abs_of_pos hS0p]
        exact div_le_div_of_nonneg_right (sq_bound_of_abs (bS a) v) hS0p.le).integrableOn
    constructor
    · rw [integral_sub iL (integrableOn_const (by simp)), setIntegral_const, key, hl]
      simp only [smul_eq_mul]; ring
    · rw [integral_sub iSA (integrableOn_const (by simp)), setIntegral_const, key, integral_div]
      simp only [sA_eq, smul_eq_mul]
      rw [← hS]; field_simp; ring
  refine ⟨hε0, hε, ?_, hwin, hcent⟩
  intro a ha
  exact ⟨measureReal_nonneg, lt_of_le_of_lt ha.2 d.eta_lt⟩

end BstLean.BlueprintLow
