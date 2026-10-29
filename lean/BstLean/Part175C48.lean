import BstLean.Part175M48

/-!
# Part 175 (file `C48`): the certificate event in the window `θ_in ≤ 0.528` at `n ≥ 48 000`, and
the top of the 48 000 chain

No proof is left open; no `native_decide` or `axiom` is used.

File `Cert` again for `n ≥ 48 000`, namespace `BstLean.Part175.N48`. It reuses the event
`Scert528`, `winC528`, `scert_of_good528` and the room `roomF = roomC − 4·10⁻⁴` of file `Cert`.
* `W128_le528`, **`theta_mom528`**: `W₁₂₈ ≤ (1.1377·τ²/ρ²)¹²⁸` (`ε = 0.0623`) and
  `E(1 − s²)⁶⁴ ≤ 0.6040⁶⁴` for `n ≥ 48 000`, `0.46 ≤ θ ≤ 0.528`.
* `charge_one_ae528`, `delta_f_48`, `delta_s_48`, **`cert_charge528`**, `cert_ret_charge528`:
  `Pr(Scert528ᶜ) ≤ 26·10⁻⁵` for every World value.
* `certs_of_good528`, **`classifier_paper_JM47`**: as in file `Cert`, for `n ≥ 48 000`, with
  `classifier_paper_root48k` (file `M48`); room `roomF` (`26·10⁻⁵ + 5·10⁻⁵ ≤ 4·10⁻⁴`).
-/

namespace BstLean.Part175.N48

-- ===== from Part166Th.lean =====
section STh
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
/-- `W₁₂₈ ≤ (1.1377·τ²/(|c|² + nτ²))¹²⁸` for `n ≥ 48 000` and `0.46 ≤ θ ≤ 0.528`, for any vector
`c'` with `|c'|² = |c|²`. -/
lemma W128_le528 {n : ℕ} (hn : 48000 ≤ n) (c c' : Fin n → ℝ) (hc : normSq c' = normSq c) {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 128 c' τ ≤ (11377 / 10000 * (τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))) ^ 128 := by
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le (q := 128) (by omega) c' hτ (ε := 623 / 10000) (by norm_num) (by norm_num)
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
  have hTR1 : 48000 * T ≤ 528 / 1000 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  have hTR0 : 0 ≤ T / R := by positivity
  -- the first term
  have h1 : T / ((1 - 623 / 10000) ^ 2 * (R - T)) ≤ 11374 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 11374 / 10000 * ((1 - 623 / 10000) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (11374 / 10000 * ((1 - 623 / 10000) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 11374 / 10000 * T * ((1 - 623 / 10000) ^ 2 * (R - T)) := by ring
  have h1' := pow_le_pow_left₀ (by positivity) h1 128
  -- the second term
  have hexp : exp (-((623 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-88) ^ 2 := by
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
  have hsq : √(exp (-((623 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T))) ≤
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
  have h2 : √(exp (-((623 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T))) *
      (((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹) ^ 128 ≤
      ((1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10 * (T / R)) ^ 128 :=
    mul_le_mul hsq h2' (by positivity) (by norm_num)
  have hfin : (11374 / 10000 * (T / R)) ^ 128 +
      ((1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10 * (T / R)) ^ 128 ≤
      (11377 / 10000 * (T / R)) ^ 128 := by
    have e2 : (11377 / 10000 * (T / R)) ^ 128 - ((11374 / 10000 * (T / R)) ^ 128 +
        ((1504 / 10 ^ 6 : ℝ) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10 * (T / R)) ^ 128) =
        ((11377 / 10000 : ℝ) ^ 128 - (11374 / 10000) ^ 128 - ((1504 / 10 ^ 6) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10) ^ 128) *
          (T / R) ^ 128 := by ring
    have : 0 ≤ ((11377 / 10000 : ℝ) ^ 128 - (11374 / 10000) ^ 128 -
        ((1504 / 10 ^ 6) ^ 12 * (3679 / 10000) ^ 10) * (22 / 10) ^ 128) * (T / R) ^ 128 :=
      mul_nonneg (by norm_num) (by positivity)
    linarith
  push_cast at h h2
  linarith


open MeasureTheory in
/-- **The latitude moment bound in the window `θ ≤ 0.528`**: `E(1 − s²)⁶⁴ ≤ 0.6040⁶⁴` for
`n ≥ 48 000`, `0.46 ≤ θ ≤ 0.528`. -/
theorem theta_mom528 {n : ℕ} (hn : 48000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c τ) (hθ1 : BstLean.Part150.thetaC c τ ≤ 528 / 1000) :
    ∫⁻ a, ENNReal.ofReal ((1 - BstLean.Part157.latitude (n := n) (√(BstLean.Part130.normSq c)) τ a ^ 2) ^ 64)
        ∂(BstLean.Part161.muI n) ≤ ENNReal.ofReal ((6040 / 10000 : ℝ) ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  set a0 := √(normSq c) with ha0
  set c' : Fin n → ℝ := consV a0 0 with hc'
  have hcc : normSq c' = normSq c := by
    rw [hc', normSq_consV hn1, ha0, Real.sq_sqrt (normSq_nonneg c)]
    simp [normSq]
  set R : ℝ := normSq c + (n : ℝ) * τ ^ 2 with hR
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 11377 / 10000 * (τ ^ 2 / R) := ⟨_, rfl⟩
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
    have hW := W128_le528 hn c c' hcc hτ hθ0 hθ1
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
  have hAB : A * B ≤ 6040 / 10000 := by
    have hθ : BstLean.Part150.thetaC c τ = (n : ℝ) * τ ^ 2 / R := by
      unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
      rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le)]
    rw [hθ, div_le_iff₀ hR0] at hθ1
    rw [hA, hB]
    push_cast
    rw [show 11377 / 10000 * (τ ^ 2 / R) * ((n : ℝ) + 2 * 128) =
      11377 / 10000 * (τ ^ 2 * ((n : ℝ) + 256)) / R by ring, div_le_iff₀ hR0]
    have hT := sq_nonneg τ
    have : τ ^ 2 * 256 ≤ 528 / 1000 * R * (256 / 48000) := by
      have : 48000 * τ ^ 2 ≤ (n : ℝ) * τ ^ 2 := mul_le_mul_of_nonneg_right hnR hT
      linarith
    linarith
  have hfinal : (A * B) ^ 64 ≤ (6040 / 10000 : ℝ) ^ 64 := pow_le_pow_left₀ (mul_nonneg hA0.le hB0.le) hAB 64
  calc ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) a0 τ a ^ 2) ^ 64) ∂(muI n)
      ≤ ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) := step1.trans step2.le
    _ ≤ ENNReal.ofReal (lam / 2) * ENNReal.ofReal (A ^ 128) +
        ENNReal.ofReal ((2 * lam)⁻¹) * ENNReal.ofReal (B ^ 128) := step3
    _ = ENNReal.ofReal ((A * B) ^ 64) := by
        rw [← ENNReal.ofReal_mul hl2, ← ENNReal.ofReal_mul hl2',
          ← ENNReal.ofReal_add (mul_nonneg hl2 hA128) (mul_nonneg hl2' hB128), hval]
    _ ≤ ENNReal.ofReal ((6040 / 10000 : ℝ) ^ 64) := ENNReal.ofReal_le_ofReal hfinal

end STh


section SCert
open BstLean.Part167
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (muI Ix BIAS_hyp lamX sigX)
open BstLean.Part162 (dPaper psiA)
open BstLean.Part153 (nuA)
open BstLean.Part166 (psiK psiK_nonneg fK sK winC certI Cf Scert measurableSet_Scert
  markov12 measurable_psiK_f measurable_psiK_s goodD measurable_certI measurable_thetaC_key pow64_le
  integral_le_of_lintegral psiA_lam_eq psiA_sig_eq)
open BstLean.Part165 (goodC roomC roomC_ge)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA)
open BstLean.Part175.N50 (winC528 Scert528 measurableSet_Scert528 scert_of_good528 roomF roomF_ge)
variable {n : ℕ}

/-- **One certificate from the per-input moment for `v ≠ 0`** (Part 166's `charge_one`, a.e.), in the window `θ ≤ 0.528` (`Θ = 0.6040`). -/
theorem charge_one_ae528 (hn : 48000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC528 c τ)
    {Φ : AgFam n → (Fin n → ℝ) → ℝ}
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2))
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hyp : ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
      ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)) :
    nuA n {θ | ENNReal.ofReal (C ^ 12) < certI Φ ((c, τ), θ)} ≤
      ENNReal.ofReal ((6040 / 10000 * K / C) ^ 64) := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  have hdir := ae_ne_zero_dir (n := n) (by omega)
  have hm : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
      × Ix n × (Fin (n - 1) → ℝ) => psiK Φ ((c, τ), z.1) z.2.1 z.2.2) := by
    have hk : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × Ix n × (Fin (n - 1) → ℝ) =>
        ((((c, τ), z.1) : AgFam n), z.2.1, z.2.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
    have h2 := hΦ.comp hk
    rw [Function.comp_def] at h2
    exact h2
  have hM := markov12 (nuA n) (muI n) (stdGauss (Fin (n - 1)))
    (fun θ a v => psiK Φ ((c, τ), θ) a v) hm (fun _ _ _ => psiK_nonneg _ _ _ _)
    (p := 64) (by norm_num) hC
  refine hM.trans ?_
  have hnum : ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      ENNReal.ofReal ((6040 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
    calc ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n
        ≤ ∫⁻ a, ∫⁻ _v : Fin (n - 1) → ℝ,
            ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)
            ∂stdGauss (Fin (n - 1)) ∂muI n :=
          lintegral_mono fun a => lintegral_mono_ae (hdir.mono fun v hv => hyp a v hv)
      _ = ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 64) *
            ENNReal.ofReal (K ^ 64) ∂muI n := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_const, measure_univ, mul_one, mul_pow,
            ENNReal.ofReal_mul (by positivity)]
      _ = (∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 64) ∂muI n) *
            ENNReal.ofReal (K ^ 64) := by
          rw [lintegral_mul_const]
          exact ENNReal.measurable_ofReal.comp ((measurable_const.sub
            ((measurable_latitude_comp measurable_const measurable_const
              measurable_id).pow_const 2)).pow_const 64)
      _ ≤ ENNReal.ofReal ((6040 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
          gcongr
          exact theta_mom528 hn c hτ hθ0 hθ1
  calc (∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n) / ENNReal.ofReal (C ^ 64)
      ≤ ENNReal.ofReal ((6040 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) /
          ENNReal.ofReal (C ^ 64) := by gcongr
    _ = ENNReal.ofReal ((6040 / 10000 * K / C) ^ 64) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
        rw [div_pow (6040 / 10000 * K) C 64, mul_pow (6040 / 10000 : ℝ) K 64]


/-- The `f` certificate charge with `Θ = 0.6040`. -/
lemma delta_f_48 : (6040 / 10000 * (47 / 10) / Cf : ℝ) ^ 64 ≤ 11 / 100000 := by
  have h1 : (6040 / 10000 * (47 / 10) / Cf : ℝ) ≤ 8664 / 10000 := by unfold Cf; norm_num
  have h0 : (0 : ℝ) ≤ 6040 / 10000 * (47 / 10) / Cf := by unfold Cf; positivity
  calc (6040 / 10000 * (47 / 10) / Cf : ℝ) ^ 64 ≤ (8664 / 10000 : ℝ) ^ 64 := pow_le_pow_left₀ h0 h1 64
    _ ≤ 11 / 100000 := by norm_num

/-- The `σ` certificate charge with `Θ = 0.6040`. -/
lemma delta_s_48 : (6040 / 10000 * (47 / 10) / (326 / 100) : ℝ) ^ 64 ≤ 15 / 100000 := by
  have h1 : (6040 / 10000 * (47 / 10) / (326 / 100) : ℝ) ≤ 8708 / 10000 := by norm_num
  calc (6040 / 10000 * (47 / 10) / (326 / 100) : ℝ) ^ 64 ≤ (8708 / 10000 : ℝ) ^ 64 :=
        pow_le_pow_left₀ (by norm_num) h1 64
    _ ≤ 15 / 100000 := by norm_num

/-- **The charge of `Scert528` from the a.e. form of Lemma LJ**: `≤ 26·10⁻⁵` for every World
value (`n ≥ 48 000`). -/
theorem cert_charge528 (hn : 48000 ≤ n) (hLJ : LJae_hyp n (47 / 10)) (c : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ Scert528 n} ≤ 26 / 100000 := by
  have hn0 : (0 : ℝ) < n := by
    have : (48000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  by_cases hw : winC528 c τ
  · have hw' : winC c τ := ⟨hw.1, hw.2.1, hw.2.2.trans (by norm_num)⟩
    have hsub : {θ | ((c, τ), θ) ∉ Scert528 n} ⊆
        {θ | ENNReal.ofReal ((Cf / n) ^ 12) < certI fK ((c, τ), θ)} ∪
        {θ | ENNReal.ofReal ((326 / 100 * (2 / n) / n) ^ 12) < certI sK ((c, τ), θ)} := by
      intro θ hθ
      simp only [Scert528, Set.mem_ofPred_eq, not_imp, not_and_or, not_le] at hθ
      rcases hθ.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h1 := charge_one_ae528 hn hw measurable_psiK_f (K := 47 / 10 / n) (C := Cf / n)
      (by positivity) (by unfold Cf; positivity) (fun a v hv => by
        have := (hLJ c τ hw' a v hv).1
        rwa [mul_div_assoc] at this)
    have h2 := charge_one_ae528 hn hw measurable_psiK_s (K := 2 / n * (47 / 10) / n)
      (C := 326 / 100 * (2 / n) / n) (by positivity) (by positivity) (fun a v hv => by
        have := (hLJ c τ hw' a v hv).2
        rwa [mul_assoc, mul_div_assoc] at this)
    have e1 : 6040 / 10000 * (47 / 10 / n) / (Cf / n) = 6040 / 10000 * (47 / 10) / Cf := by
      field_simp
    have e2 : 6040 / 10000 * (2 / n * (47 / 10) / n) / (326 / 100 * (2 / n) / n) =
        6040 / 10000 * (47 / 10) / (326 / 100 : ℝ) := by
      field_simp
    rw [e1] at h1
    rw [e2] at h2
    have hU : nuA n {θ | ((c, τ), θ) ∉ Scert528 n} ≤
        ENNReal.ofReal (11 / 100000) + ENNReal.ofReal (15 / 100000) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
      · exact h1.trans (ENNReal.ofReal_le_ofReal delta_f_48)
      · exact h2.trans (ENNReal.ofReal_le_ofReal delta_s_48)
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hU
    have := ENNReal.toReal_le_of_le_ofReal (by norm_num) hU
    rw [measureReal_def]
    linarith
  · have e : {θ | ((c, τ), θ) ∉ Scert528 n} = ∅ := by
      ext θ
      simp only [Scert528, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact fun h => absurd h hw
    rw [e]
    simp only [measureReal_empty]
    norm_num

/-- **The charge of `Scert528` on the retained data**. -/
theorem cert_ret_charge528 (hn : 48000 ≤ n) (hLJ : LJae_hyp n (47 / 10))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (Scert528 n))ᶜ ≤
      26 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_Scert528 n) (by norm_num) (fun c τ _ => cert_charge528 hn hLJ c τ)

/-- **Part 165's two certificates on a good set that contains `agentEv D (Scert528 n)`.** -/
theorem certs_of_good528 (hn : 48000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {E : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) E)
    (hS0 : c ∈ agentEv (paperDesign n fT wT hf hw) (Scert528 n)) :
    (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
    (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) := by
  set D := paperDesign n fT wT hf hw with hDd
  have hn16 : 16384 ≤ n := by omega
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hD := paperDesign_agentCentre fT wT hf hw
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hS : agKey D c ∈ Scert528 n := hS0 hτ
  obtain ⟨hcf, hcs⟩ := hS ⟨hτ, hθ0, (BstLean.Part175.win528_goodA hn16 fT wT hf hw E hc).2.2⟩
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

/-- **The classifier theorem with Lemma LJ in its Jacobian form at `K2 = 4.7`** (every
`n ≥ 48 000`, floor `d_low = 0.22005`, room `roomF`). The good set is Part 166's `goodD n D E_A`. -/
theorem classifier_paper_JM47 (hn : 48000 ≤ n) (hJM : JM_hyp n (47 / 10))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomF)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  have hn16 : 16384 ≤ n := by omega
  have hLJ : LJae_hyp n (47 / 10) := LJae_of_JM (by omega) hJM
  have hS : MeasurableSet (agentEv D (Scert528 n)) :=
    measurableSet_agentEv D (measurableSet_Scert528 n)
  have hC := cert_ret_charge528 hn hLJ fT wT hf hw
  refine classifier_paper_root48k hn fT wT hf hw t (hEA.inter hS) (δA := δA + 26 / 100000)
    ?_ ?_ (fun c hc => ?_)
  · rw [Set.compl_inter, Set.inter_union_distrib_left]
    refine (measureReal_union_le _ _).trans (add_le_add hA ?_)
    exact (measureReal_mono Set.inter_subset_right).trans hC
  · unfold roomF at hroom; linarith
  · -- `hc : c ∈ goodC n D ((EA ∩ agentEv D (Scert528 n)) ∩ agentEv D (SXM48 n))`
    have hS0 : c ∈ agentEv D (Scert528 n) := hc.2.1.2.1.1.1.1.2
    have hcert := certs_of_good528 hn fT wT hf hw hc hS0
    refine ⟨hcert.1, hcert.2, hB c ?_⟩
    have hSc : c ∈ agentEv D (Scert n) := scert_of_good528 hn16 fT wT hf hw hc hS0
    exact ⟨hc.1, ⟨⟨hc.2.1.1, ⟨⟨⟨⟨hc.2.1.2.1.1.1.1.1, hSc⟩, hc.2.1.2.1.1.2⟩, hc.2.1.2.1.2⟩,
      hc.2.1.2.2⟩⟩, hc.2.2⟩⟩

end SCert

end BstLean.Part175.N48
