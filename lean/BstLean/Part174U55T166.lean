import BstLean.Part174U55Root
import BstLean.Part166All
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Part 174 (file `U55T166`): Part 166's results that need `n ≥ 80 000`, re-proved for `n ≥ 55 000`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of file `T166` (57 000 chain) for `n ≥ 55 000`, namespace `BstLean.Part174.N55`. The
docstrings are Part 166's; numbers in them can be older. The Lean statements are authoritative.

Changed constants (57 000 → 55 000): `W128_le` with `ε = 0.0594` (was 0.0583), first term
`≤ 1.1304·(T/R)` (was 1.1277), conclusion `W₁₂₈ ≤ (1.1310·τ²/ρ²)¹²⁸` (was 1.1285); `theta_mom`:
`E(1 − s²)⁶⁴ ≤ 0.6250⁶⁴` (was 0.6235).
-/

namespace BstLean.Part174.N55

-- ===== from Part166Th.lean =====
section SPart166Th
open BstLean.Part166
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open scoped ENNReal
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part160 (WqN WqN_le exp_neg_13_le integrable_wqq)
open BstLean.Part161 (consV muI consV_map normSq_consV consV_add consV_smul measurable_consV
  stdGauss_normSq_zero)
open BstLean.Part157 (latitude)
/-- `W₁₂₈ ≤ (1.121·τ²/(|c|² + nτ²))¹²⁸` for `n ≥ 55 000` and `0.46 ≤ θ ≤ 0.55`, for any vector
`c'` with `|c'|² = |c|²`. -/
lemma W128_le {n : ℕ} (hn : 55000 ≤ n) (c c' : Fin n → ℝ) (hc : normSq c' = normSq c) {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN 128 c' τ ≤ (11310 / 10000 * (τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))) ^ 128 := by
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le (q := 128) (by omega) c' hτ (ε := 594 / 10000) (by norm_num) (by norm_num)
  rw [hc] at h
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = τ ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  have hθ : thetaC c τ = (n : ℝ) * T / R := by
    unfold thetaC rhoC
    rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le), ← hR, ← hT]
  rw [hθ] at hθ0 hθ1
  rw [← hR, ← hT]
  rw [le_div_iff₀ hR0] at hθ0
  rw [div_le_iff₀ hR0] at hθ1
  rw [← hT, show normSq c + (n : ℝ) * T - T = R - T by rw [hR, hT]] at h
  have hTR1 : 55000 * T ≤ 55 / 100 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  have hTR0 : 0 ≤ T / R := by positivity
  -- the first term
  have h1 : T / ((1 - 594 / 10000) ^ 2 * (R - T)) ≤ 11304 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 11304 / 10000 * ((1 - 594 / 10000) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (11304 / 10000 * ((1 - 594 / 10000) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 11304 / 10000 * T * ((1 - 594 / 10000) ^ 2 * (R - T)) := by ring
  have h1' := pow_le_pow_left₀ (by positivity) h1 128
  -- the second term
  have hexp : exp (-((594 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-88) ^ 2 := by
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hE : exp (-88) ^ 2 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10) ^ 2 := by
    have e88 : exp (-88) = exp (-13) ^ 6 * exp (-1) ^ 10 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h13 := pow_le_pow_left₀ (exp_pos _).le exp_neg_13_le 6
    have h1 : exp (-1) ≤ 3679 / 10000 := by
      have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
    have h1' := pow_le_pow_left₀ (exp_pos _).le h1 10
    have hb : exp (-88) ≤ (1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10 := by
      rw [e88]
      calc exp (-13) ^ 6 * exp (-1) ^ 10 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 2) ^ 6 * (3679 / 10000) ^ 10 :=
            mul_le_mul h13 h1' (by positivity) (by positivity)
        _ = (1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10 := by ring
    exact pow_le_pow_left₀ (exp_pos _).le hb 2
  have hsq : √(exp (-((594 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T))) ≤
      (1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (1504 / 10 ^ 6) ^ 12 * (3679 / 10000) ^ 10 by norm_num)]
    exact Real.sqrt_le_sqrt (hexp.trans hE)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (128 : ℕ) := by push_cast; linarith
  have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
    rw [div_le_div_iff₀ hn0 hR0]
    linarith
  have hinv : ((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹ ≤ 22 / 10 * (T / R) := by
    have h4 : ((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹ ≤ 22 / 10 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 128
  have h2 : √(exp (-((594 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T))) *
      (((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹) ^ 128 ≤
      ((1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10 * (T / R)) ^ 128 :=
    mul_le_mul hsq h2' (by positivity) (by norm_num)
  have hfin : (11304 / 10000 * (T / R)) ^ 128 +
      ((1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10 * (T / R)) ^ 128 ≤
      (11310 / 10000 * (T / R)) ^ 128 := by
    have e2 : (11310 / 10000 * (T / R)) ^ 128 - ((11304 / 10000 * (T / R)) ^ 128 +
        ((1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10 * (T / R)) ^ 128) =
        ((11310 / 10000 : ℝ) ^ 128 - (11304 / 10000) ^ 128 - ((1504 / 10 ^ 6) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10) ^ 128) *
          (T / R) ^ 128 := by ring
    have : 0 ≤ ((11310 / 10000 : ℝ) ^ 128 - (11304 / 10000) ^ 128 -
        ((1504 / 10 ^ 6) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10) ^ 128) * (T / R) ^ 128 :=
      mul_nonneg (by norm_num) (by positivity)
    linarith
  push_cast at h h2
  linarith


open MeasureTheory in
/-- **The latitude moment bound**: `E(1 − s²)⁶⁴ ≤ 0.619⁶⁴` for `n ≥ 55 000`,
`0.46 ≤ θ ≤ 0.55`. -/
theorem theta_mom {n : ℕ} (hn : 55000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c τ) (hθ1 : BstLean.Part150.thetaC c τ ≤ 55 / 100) :
    ∫⁻ a, ENNReal.ofReal ((1 - BstLean.Part157.latitude (n := n) (√(BstLean.Part130.normSq c)) τ a ^ 2) ^ 64)
        ∂(BstLean.Part161.muI n) ≤ ENNReal.ofReal ((6250 / 10000 : ℝ) ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  set a0 := √(normSq c) with ha0
  set c' : Fin n → ℝ := consV a0 0 with hc'
  have hcc : normSq c' = normSq c := by
    rw [hc', normSq_consV hn1, ha0, Real.sq_sqrt (normSq_nonneg c)]
    simp [normSq]
  set R : ℝ := normSq c + (n : ℝ) * τ ^ 2 with hR
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 11310 / 10000 * (τ ^ 2 / R) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (n : ℝ) + 2 * (128 : ℕ) := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (B / A) ^ 64 := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hl2 : 0 ≤ lam / 2 := by linarith
  have hl2' : 0 ≤ (2 * lam)⁻¹ := inv_nonneg.mpr (by linarith)
  have hA128 : 0 ≤ A ^ 128 := pow_nonneg hA0.le _
  have hB128 : 0 ≤ B ^ 128 := pow_nonneg hB0.le _
  set f : (Fin n → ℝ) → ℝ := fun ξ => (τ ^ 2 * (normSq (c' + τ • ξ))⁻¹) ^ 128 with hf
  set g : (Fin n → ℝ) → ℝ := fun ξ => (normSq ξ) ^ 128 with hg
  set h : (Fin n → ℝ) → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (lam / 2 * f ξ) + ENNReal.ofReal ((2 * lam)⁻¹ * g ξ) with hh
  have hfm : Measurable f := by
    rw [hf]
    exact (measurable_const.mul ((measurable_normSq.comp
      (measurable_const.add (measurable_id.const_smul τ))).inv)).pow_const _
  have hgm : Measurable g := measurable_normSq.pow_const _
  have hhm : Measurable h :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul hfm)).add
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hgm))
  -- step 1: the pointwise bound off a null set
  have hnull : muI n {p : ℝ × (Fin (n - 1) → ℝ) | normSq p.2 = 0} = 0 := by
    have e : {p : ℝ × (Fin (n - 1) → ℝ) | normSq p.2 = 0} =
        Set.univ ×ˢ {G : Fin (n - 1) → ℝ | normSq G = 0} := by ext p; simp
    rw [e, muI, Measure.prod_prod, stdGauss_normSq_zero (by omega), mul_zero]
  have hae : ∀ᵐ p ∂(muI n), normSq p.2 ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [this] with p hp
    exact hp
  have step1 : ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) a0 τ a ^ 2) ^ 64) ∂(muI n) ≤
      ∫⁻ a, h (consV a.1 a.2) ∂(muI n) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨h0, h1⟩ := lat_pt hn1 a0 τ hτ p hp
    set x := τ ^ 2 * (normSq (c' + τ • consV (n := n) p.1 p.2))⁻¹ with hx
    set y := normSq (consV (n := n) p.1 p.2) with hy
    have hx0 : 0 ≤ x := by rw [hx]; exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))
    have hy0 : 0 ≤ y := normSq_nonneg _
    have hp1 : (1 - latitude (n := n) a0 τ p ^ 2) ^ 64 ≤ x ^ 64 * y ^ 64 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ h0 h1 64
    have hamgm : x ^ 64 * y ^ 64 ≤ lam / 2 * x ^ 128 + (2 * lam)⁻¹ * y ^ 128 := by
      have hsq : 0 ≤ (lam * x ^ 64 - y ^ 64) ^ 2 := sq_nonneg _
      have e : lam / 2 * x ^ 128 + (2 * lam)⁻¹ * y ^ 128 - x ^ 64 * y ^ 64 =
          (lam * x ^ 64 - y ^ 64) ^ 2 / (2 * lam) := by
        field_simp; ring
      have : 0 ≤ (lam * x ^ 64 - y ^ 64) ^ 2 / (2 * lam) := div_nonneg hsq (by linarith)
      linarith
    rw [hh]
    simp only
    rw [← ENNReal.ofReal_add (mul_nonneg hl2 (pow_nonneg hx0 _))
      (mul_nonneg hl2' (pow_nonneg hy0 _))]
    apply ENNReal.ofReal_le_ofReal
    exact hp1.trans hamgm
  -- step 2: the change of variables
  have step2 : ∫⁻ a, h (consV a.1 a.2) ∂(muI n) = ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) := by
    rw [← consV_map hn1, lintegral_map hhm measurable_consV]
    rfl
  -- step 3: the two terms
  have hprob : IsProbabilityMeasure (BstLean.Part29.stdGauss (Fin n)) := by
    unfold BstLean.Part29.stdGauss; infer_instance
  have hfI : ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (A ^ 128) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_wqq (q := 128) (by omega) c' hτ)
      (ae_of_all _ fun ξ => BstLean.Part160.wqq_nonneg 128 c' τ ξ)]
    apply ENNReal.ofReal_le_ofReal
    have hW := W128_le hn c c' hcc hτ hθ0 hθ1
    rw [hA, hR]
    exact hW
  have hgI : ∫⁻ ξ, ENNReal.ofReal (g ξ) ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (B ^ 128) := by
    have := chi_mom (ι := Fin n) 128
    simpa [hg, hB, normSq] using this
  have step3 : ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (lam / 2) * ENNReal.ofReal (A ^ 128) +
        ENNReal.ofReal ((2 * lam)⁻¹) * ENNReal.ofReal (B ^ 128) := by
    have hm1 : Measurable (fun ξ => ENNReal.ofReal (lam / 2 * f ξ)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul hfm)
    show ∫⁻ ξ, (ENNReal.ofReal (lam / 2 * f ξ) + ENNReal.ofReal ((2 * lam)⁻¹ * g ξ))
      ∂(BstLean.Part29.stdGauss (Fin n)) ≤ _
    rw [lintegral_add_left hm1]
    simp_rw [ENNReal.ofReal_mul hl2, ENNReal.ofReal_mul hl2']
    rw [lintegral_const_mul _ hfm.ennreal_ofReal, lintegral_const_mul _ hgm.ennreal_ofReal]
    exact add_le_add (by gcongr) (by gcongr)
  -- step 4: the numbers
  have hval : lam / 2 * A ^ 128 + (2 * lam)⁻¹ * B ^ 128 = (A * B) ^ 64 := by
    have e1 : lam * A ^ 64 = B ^ 64 := by
      rw [hlam, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hA0.ne')]
    have e2 : lam / 2 * A ^ 128 = B ^ 64 * A ^ 64 / 2 := by
      rw [← e1]; ring
    have e3 : (2 * lam)⁻¹ * B ^ 128 = A ^ 64 * B ^ 64 / 2 := by
      rw [show B ^ 128 = B ^ 64 * B ^ 64 by ring, ← e1]; field_simp
    rw [e2, e3, mul_pow]; ring
  have hAB : A * B ≤ 6250 / 10000 := by
    have hθ : BstLean.Part150.thetaC c τ = (n : ℝ) * τ ^ 2 / R := by
      unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
      rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le)]
    rw [hθ, div_le_iff₀ hR0] at hθ1
    rw [hA, hB]
    push_cast
    rw [show 11310 / 10000 * (τ ^ 2 / R) * ((n : ℝ) + 2 * 128) =
      11310 / 10000 * (τ ^ 2 * ((n : ℝ) + 256)) / R by ring, div_le_iff₀ hR0]
    have hT := sq_nonneg τ
    have : τ ^ 2 * 256 ≤ 55 / 100 * R * (256 / 55000) := by
      have : 55000 * τ ^ 2 ≤ (n : ℝ) * τ ^ 2 := mul_le_mul_of_nonneg_right hnR hT
      linarith
    linarith
  have hfinal : (A * B) ^ 64 ≤ (6250 / 10000 : ℝ) ^ 64 := pow_le_pow_left₀ (mul_nonneg hA0.le hB0.le) hAB 64
  calc ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) a0 τ a ^ 2) ^ 64) ∂(muI n)
      ≤ ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) := step1.trans step2.le
    _ ≤ ENNReal.ofReal (lam / 2) * ENNReal.ofReal (A ^ 128) +
        ENNReal.ofReal ((2 * lam)⁻¹) * ENNReal.ofReal (B ^ 128) := step3
    _ = ENNReal.ofReal ((A * B) ^ 64) := by
        rw [← ENNReal.ofReal_mul hl2, ← ENNReal.ofReal_mul hl2',
          ← ENNReal.ofReal_add (mul_nonneg hl2 hA128) (mul_nonneg hl2' hB128), hval]
    _ ≤ ENNReal.ofReal ((6250 / 10000 : ℝ) ^ 64) := ENNReal.ofReal_le_ofReal hfinal

end SPart166Th

-- ===== from Part166End.lean =====
section SPart166End
open BstLean.Part166
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (xLat hhMat uHat consV muI latC lamX sigX Ix BIAS_hyp)
open BstLean.Part162 (xLatH tanSq psiA dPaper)
open BstLean.Part153 (nuA)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA)
open BstLean.Part165 (goodC roomC roomC_ge classifier_paper_root80k)
variable {n : ℕ}
/-- **Part 165's two certificates on the good set.** -/
theorem certs_of_goodD (hn : 55000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodD n (paperDesign n fT wT hf hw) EA) :
    (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
    (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) := by
  set D := paperDesign n fT wT hf hw with hDd
  have hn16 : 16384 ≤ n := by omega
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hD := paperDesign_agentCentre fT wT hf hw
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hS : agKey D c ∈ Scert n := hc.2.1.2.1.1.1.2 hτ
  obtain ⟨hcf, hcs⟩ := hS ⟨hτ, hθ0, hθ1⟩
  set k := agKey D c with hk
  have hmk : ∀ {Φ : AgFam n → (Fin n → ℝ) → ℝ},
      Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2) →
      Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) => psiK Φ k z.1 z.2 ^ 12) := by
    intro Φ hΦ
    have hm : Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) =>
        ((k, z.1, z.2) : AgFam n × Ix n × (Fin (n - 1) → ℝ))) :=
      measurable_const.prodMk (measurable_fst.prodMk measurable_snd)
    have h2 := hΦ.comp hm
    rw [Function.comp_def] at h2
    exact h2.pow_const 12
  -- σ
  have hsig : ∫ a, ∫ v, psiK sK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (326 / 100 * (2 / n) / n) ^ 12 :=
    integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1))) (fun a v => psiK sK k a v ^ 12)
      (hmk measurable_psiK_s) (fun _ _ => pow_nonneg (psiK_nonneg _ _ _ _) _) (by positivity) hcs
  have hfK : ∫ a, ∫ v, psiK fK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (Cf / n) ^ 12 :=
    integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1))) (fun a v => psiK fK k a v ^ 12)
      (hmk measurable_psiK_f) (fun _ _ => pow_nonneg (psiK_nonneg _ _ _ _) _)
      (by unfold Cf; positivity) hcf
  refine ⟨?_, ?_⟩
  · -- the energy lower bound `e_b ≥ 0.6425`
    have hG := goodC16_of_goodA hn16 fT wT hf hw hc
    have hU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hc.2.2.1.2 hτ
    have hlo := eb16_lower hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hU
    have hb : D.bA c.1 c.2.1.1 =
        (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := hD c
    rw [← hb] at hlo
    have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
    rw [hmA] at hlo
    set e := normSq (D.bA c.1 c.2.1.1) / n with he
    have he0 : 257 / 400 ≤ e := by
      rw [he, le_div_iff₀ hn0]
      have h2 : 2 / (n : ℝ) * (257 / 400) * (n ^ 2 / 2) ≤
          2 / (n : ℝ) ^ 2 * normSq (D.bA c.1 c.2.1.1) * (n ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hlo (by positivity)
      have l : 2 / (n : ℝ) * (257 / 400) * (n ^ 2 / 2) = 257 / 400 * n := by field_simp
      have r : 2 / (n : ℝ) ^ 2 * normSq (D.bA c.1 c.2.1.1) * (n ^ 2 / 2) =
          normSq (D.bA c.1 c.2.1.1) := by field_simp
      linarith
    have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he0
    have hpt : ∀ a v, psiA (lamX D c) D c a v ^ 12 = (e⁻¹) ^ 12 * psiK fK k a v ^ 12 := by
      intro a v
      have h := psiA_lam_eq (by omega) D hD c a v
      rw [← he] at h
      rw [← h, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hepos.ne', one_pow, one_mul]
    simp_rw [hpt, integral_const_mul]
    calc (e⁻¹) ^ 12 * ∫ a, ∫ v, psiK fK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n
        ≤ (e⁻¹) ^ 12 * (Cf / n) ^ 12 := mul_le_mul_of_nonneg_left hfK (by positivity)
      _ = (Cf / e / n) ^ 12 := by rw [← mul_pow]; congr 1; field_simp
      _ ≤ (51 / 10 / n) ^ 12 := by
          apply pow_le_pow_left₀ (by unfold Cf; positivity)
          apply div_le_div_of_nonneg_right _ hn0.le
          rw [div_le_iff₀ hepos]
          unfold Cf
          linarith
  · simp_rw [psiA_sig_eq D hD c]
    exact hsig

/-! ## The end theorem -/

end SPart166End

end BstLean.Part174.N55
