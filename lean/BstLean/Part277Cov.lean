import BstLean.Part263Covariance

/-! Part 277, covariance: the local covariance contract on a base dimension `n0 ≥ 8000`
and a World window `[.46, θhi]` with `θhi ≤ .54`.
The old chain `chi_core_M12`, `wide_radius_caps`, `core_radius_caps`, `Dq_local_gaussian`,
`localGaussian_le_envelope`, `envelope_mono`, `localCov` needs `n ≥ 11883` and `θ ≤ .528`.
The new lemmas keep the same conclusions and need only `n0 ≤ n`, `8000 ≤ n0` and `θ ≤ θhi ≤ .54`.
The chain uses only two consequences of the old core certificate: positivity of the core
radius bound and the centre guard `2.8 τ ≤ ‖c‖`. The `χ` cap `.51` is not used by the chain. -/
namespace BstLean.Part277
open MeasureTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part208 BstLean.Part238
open BstLean.Part150 (thetaC rhoC rhoC_sqP)
open BstLean.Part153 (Xi4 nrm nrm_sq)
open BstLean.Part255 (Parameters Valid delta payment Dq_gaussian_symmetric
  gaussian_exceptional_single)
open BstLean.Part254 (gaussianScalar gaussianTail gaussianOutside gaussianPair)
open BstLean.Part199 (exampleWide exampleCore example_nested radiusMinus radiusPlus)
open BstLean.Part263

/-! ## Radius caps -/

/-- Cap for `radiusMinus n θ exampleWide`, as a function of `n0` and the window top. -/
noncomputable def wMinusCap (n0 : ℕ) (θhi : ℝ) : ℝ :=
  2 * 6 * √(1 / (4 * (n0 : ℝ))) + 2 * θhi * √((20 : ℝ) / n0)

/-- Cap for `radiusPlus n θ exampleWide`. -/
noncomputable def wPlusCap (n0 : ℕ) (θhi : ℝ) : ℝ := wMinusCap n0 θhi + 40 * θhi / n0

theorem wide_radius_caps_base {n0 n : ℕ} (h0 : 1 ≤ n0) (hn : n0 ≤ n) {θhi θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθhi : θ ≤ θhi) :
    radiusMinus n θ exampleWide ≤ wMinusCap n0 θhi ∧
      radiusPlus n θ exampleWide ≤ wPlusCap n0 θhi := by
  have h0r : (1 : ℝ) ≤ n0 := by exact_mod_cast h0
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn00 : (0 : ℝ) < n0 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : √(θ * (1 - θ) / n) ≤ √(1 / (4 * (n0 : ℝ))) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hn0 (by positivity)]
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have hz : √((20 : ℝ) / n) ≤ √((20 : ℝ) / n0) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) hn00 hnn)
  have hz0 : 0 ≤ √((20 : ℝ) / n) := Real.sqrt_nonneg _
  have hr : radiusMinus n θ exampleWide ≤ wMinusCap n0 θhi := by
    unfold radiusMinus exampleWide wMinusCap
    change 2 * 6 * √(θ * (1 - θ) / n) + 2 * θ * √((20 : ℝ) / n) ≤
      2 * 6 * √(1 / (4 * (n0 : ℝ))) + 2 * θhi * √((20 : ℝ) / n0)
    have h2 : θ * √((20 : ℝ) / n) ≤ θhi * √((20 : ℝ) / n0) :=
      mul_le_mul hθhi hz hz0 (hθ0.trans hθhi)
    nlinarith
  refine ⟨hr, ?_⟩
  unfold radiusPlus wPlusCap
  change radiusMinus n θ exampleWide + 2 * θ * 20 / n ≤ wMinusCap n0 θhi + 40 * θhi / n0
  have : 2 * θ * 20 / (n : ℝ) ≤ 40 * θhi / n0 := by
    rw [div_le_div_iff₀ hn0 hn00]
    have := mul_le_mul hθhi hnn hn00.le (hθ0.trans hθhi)
    nlinarith
  linarith

/-- Uniform from 8000: the wide radius is below `13/100` for `θ ≤ .54`. -/
theorem wide_radius_small {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 54 / 100) : radiusMinus n θ exampleWide ≤ 13 / 100 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : √(θ * (1 - θ) / n) ≤ 1 / 178 := by
    apply sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have hz : √((20 : ℝ) / n) ≤ 1 / 20 := by
    apply sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith
  have hθz := mul_le_mul hθ hz (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 54 / 100)
  unfold radiusMinus exampleWide
  change 2 * 6 * √(θ * (1 - θ) / n) + 2 * θ * √((20 : ℝ) / n) ≤ 13 / 100
  nlinarith

/-- Uniform from 8000: the core radius is below `7/100` for `θ ≤ .54`. -/
theorem core_radius_small {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 54 / 100) : radiusMinus n θ exampleCore ≤ 7 / 100 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : √(θ * (1 - θ) / n) ≤ 1 / 178 := by
    apply sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have hz : √((75 / 10 : ℝ) / n) ≤ 307 / 10000 := by
    apply sqrt_le_of_sq' (by norm_num)
    rw [div_le_iff₀ hn0]
    nlinarith
  have hθz := mul_le_mul hθ hz (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 54 / 100)
  unfold radiusMinus exampleCore
  change 2 * (28 / 10) * √(θ * (1 - θ) / n) + 2 * θ * √((75 / 10 : ℝ) / n) ≤ 7 / 100
  nlinarith

/-! ## Core guards (the part of `chi_core_M12` that the chain uses) -/

theorem core_guardsP {n : ℕ} (hn : 8000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθlo : 46 / 100 ≤ thetaC c τ) (hθhi : thetaC c τ ≤ 54 / 100) :
    0 < axialRadiusLower n (nrm c) τ exampleCore.t exampleCore.z ∧
    τ * exampleCore.t ≤ nrm c := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set θ := thetaC c τ with hθd
  set a := nrm c with had
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = normSq c := nrm_sq c
  set q := normSq c + (n : ℝ) * τ ^ 2 with hqd
  have hq0 : 0 < q := by
    have := normSq_nonneg c
    positivity
  have hθq : θ * q = (n : ℝ) * τ ^ 2 := by
    rw [hθd]
    unfold thetaC
    rw [rhoC_sqP, ← hqd]
    field_simp
  have hτ2 : (n : ℝ) * τ ^ 2 ≤ 54 / 100 * q := by
    rw [← hθq]; exact mul_le_mul_of_nonneg_right hθhi hq0.le
  have ha2q : a ^ 2 = q - θ * q := by rw [hθq, ha2, hqd]; ring
  have haτ : a * τ ≤ q / 178 := by
    have h1 : (n : ℝ) * (a * τ) ^ 2 = (q - θ * q) * (θ * q) := by
      rw [← ha2q, hθq]; ring
    have h2 : (q - θ * q) * (θ * q) ≤ q ^ 2 / 4 := by
      have e : q ^ 2 / 4 - (q - θ * q) * (θ * q) = q ^ 2 * (θ - 1 / 2) ^ 2 := by ring
      have := mul_nonneg (sq_nonneg q) (sq_nonneg (θ - 1 / 2))
      linarith
    have h4 : 31684 * (a * τ) ^ 2 ≤ q ^ 2 := by
      have h5 := mul_le_mul_of_nonneg_right (show (31684 : ℝ) ≤ 4 * n by linarith)
        (sq_nonneg (a * τ))
      have e : 4 * (n : ℝ) * (a * τ) ^ 2 = 4 * ((n : ℝ) * (a * τ) ^ 2) := by ring
      rw [e, h1] at h5
      linarith
    have h3 : (a * τ) ^ 2 ≤ (q / 178) ^ 2 := by
      have e : (q / 178) ^ 2 = q ^ 2 / 31684 := by ring
      rw [e, le_div_iff₀ (by norm_num)]
      linarith
    have haτ0 : 0 ≤ a * τ := mul_nonneg ha0 hτ.le
    exact (pow_le_pow_iff_left₀ haτ0 (by positivity) two_ne_zero).1 h3
  have haτ0 : 0 ≤ a * τ := mul_nonneg ha0 hτ.le
  set s := √((n : ℝ) * (75 / 10)) with hsd
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s ≤ 307 / 10000 * (n : ℝ) := by
    apply sqrt_le_of_sq' (by positivity)
    nlinarith
  have hτs : τ ^ 2 * s ≤ 1658 / 100000 * q := by
    have h1 : τ ^ 2 * s ≤ τ ^ 2 * (307 / 10000 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    have e : τ ^ 2 * (307 / 10000 * (n : ℝ)) = 307 / 10000 * ((n : ℝ) * τ ^ 2) := by ring
    linarith
  have hτ2q : τ ^ 2 ≤ 54 / 100 * q / 8000 := by
    rw [le_div_iff₀ (by norm_num)]
    have : 8000 * τ ^ 2 ≤ (n : ℝ) * τ ^ 2 := mul_le_mul_of_nonneg_right hnR (sq_nonneg _)
    linarith
  have hRl : 9 / 10 * q ≤ axialRadiusLower n a τ exampleCore.t exampleCore.z := by
    unfold axialRadiusLower
    change 9 / 10 * q ≤ a ^ 2 + τ ^ 2 * ((n : ℝ) - 2 * s) - 2 * a * τ * (28 / 10)
    have e : a ^ 2 + τ ^ 2 * ((n : ℝ) - 2 * s) - 2 * a * τ * (28 / 10) =
        (q - θ * q) + θ * q - 2 * (τ ^ 2 * s) - 56 / 10 * (a * τ) := by
      rw [← ha2q, hθq]; ring
    rw [e]
    linarith
  refine ⟨by have : 0 < 9 / 10 * q := by positivity
             linarith, ?_⟩
  change τ * (28 / 10) ≤ a
  have h1 : (τ * (28 / 10)) ^ 2 ≤ a ^ 2 := by
    have : a ^ 2 ≥ 46 / 100 * q := by
      rw [ha2q]; have := mul_le_mul_of_nonneg_right hθhi hq0.le; linarith
    have e : (τ * (28 / 10)) ^ 2 = 784 / 100 * τ ^ 2 := by ring
    rw [e]
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) ha0 two_ne_zero).1 h1

/-! ## The local Gaussian bound, its envelope and monotonicity -/

theorem Dq_local_gaussianP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {θhi : ℝ}
    (hθhi : θhi ≤ 54 / 100) (p : Parameters) (hp : Valid p)
    (D : Design n) (k : Ret n) {lo hi : ℝ}
    (hτ : 0 < D.tau0 k)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Icc (46/100) θhi)
    (hloc : thetaC k.1.2 (D.tau0 k) ∈ Icc lo hi)
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤
      (13/10) * (2/(n : ℝ))/n)
    (hC : k ∈ agentEv D (localEvent n p lo hi payment)) (v : Fin (mA n) → ℝ) :
    Dq k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) v ≤
      localGaussian n p (thetaC k.1.2 (D.tau0 k)) * (2/(n : ℝ))/n * normSq v := by
  have hn8 : 8000 ≤ n := h8.trans hn
  have hθ1 : thetaC k.1.2 (D.tau0 k) < 1 := hw.2.trans_lt (by linarith)
  have hc := ne_zero_of_thetaC_lt (by omega : 0 < n) hτ hθ1
  obtain ⟨hR,hat⟩ := core_guardsP hn8 k.1.2 hτ hw.1 (hw.2.trans hθhi)
  have hθ0' : 0 ≤ thetaC k.1.2 (D.tau0 k) := by linarith [hw.1]
  have hr₀ := wide_radius_small hn8 hθ0' (hw.2.trans hθhi)
  have hr₁ := core_radius_small hn8 hθ0' (hw.2.trans hθhi)
  obtain ⟨hcau,ha,hu⟩ := centre_decomp hc
  have hsm1 := axialProjLower_le_one n ha hτ exampleCore.t_nonneg exampleCore.z_nonneg hat
  have hcp : p.chi^2 < 1 := pow_lt_one₀ hp.chi_nonneg hp.chi_lt (by norm_num)
  have hb : sharpBadMass n exampleWide exampleCore p.wLam p.cE p.o p.cS p.chi
      ((k.1.2,D.tau0 k),(k.2.1.1.1,k.2.1.1.2)) ≤ delta/payment := by
    rcases hC hτ with hno | hb
    · exact False.elim (hno hloc)
    · exact hb
  have hd := Dq_gaussian_symmetric (by omega : 6 ≤ n)
    k.2.1.1.1 k.2.1.1.2 k.1.2 (uC k.1.2) hcau ha hu hτ
    exampleWide exampleCore example_nested hp.cE_nonneg hp.o_nonneg hp.cS_nonneg
    hp.wLam_nonneg (by norm_num : (0 : ℝ) ≤ 13/10) hθ1
    (by linarith) (by linarith) hR hcp hsm1 (centre_proj_lower' hcau hu ha hτ hat) hb hX v
  have hθ0 : 0 ≤ thetaC k.1.2 (D.tau0 k) := by linarith [hw.1]
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn8
  have hnpos : (0 : ℝ) < n := by linarith
  have hE : 0 ≤ (1 - 4 * thetaC k.1.2 (D.tau0 k) / n)⁻¹ := by
    apply inv_nonneg.mpr
    have hd : 4 * thetaC k.1.2 (D.tau0 k) / n < 1 :=
      (div_lt_one hnpos).mpr (by linarith [hw.2])
    linarith
  refine hd.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
  apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ 2/n)
  exact BstLean.Part254.gaussianScalar_mono_K hθ0 hE ((min_le_right _ _).trans hp.core_lam)

theorem localGaussian_le_envelopeP {n : ℕ} (hn : 1 ≤ n) (p : Parameters) (hp : Valid p)
    {θ : ℝ} (hw : 0 ≤ θ)
    (hwR : radiusMinus n θ exampleWide ≤ p.wRadius)
    (hcR : radiusMinus n θ exampleCore ≤ p.cRadius)
    (hw1 : p.wRadius < 1) (hc1 : p.cRadius < 1) (hr₀ : radiusMinus n θ exampleWide < 1)
    (hr₁ : radiusMinus n θ exampleCore < 1) :
    localGaussian n p θ ≤ envelope n p θ := by
  have hθ0 : 0 ≤ θ := hw
  have hwpos : 0 < 1 - p.wRadius := by linarith
  have hcpos : 0 < 1 - p.cRadius := by linarith
  have hrw : 0 < 1 - radiusMinus n θ exampleWide := by linarith
  have hrc : 0 < 1 - radiusMinus n θ exampleCore := by linarith
  have hinvw : (1-radiusMinus n θ exampleWide)⁻¹ ≤ (1-p.wRadius)⁻¹ :=
    inv_anti₀ hwpos (by linarith)
  have hinvc : (1-radiusMinus n θ exampleCore)⁻¹ ≤ (1-p.cRadius)⁻¹ :=
    inv_anti₀ hcpos (by linarith)
  have hpair := BstLean.Part254.gaussian_core_pair_upper
  have hout := BstLean.Part254.gaussian_core_outside_upper
  have hexc := gaussian_exceptional_single (local_cutoff (n := n) hn)
  have hp0 : 0 ≤ gaussianPair exampleCore := BstLean.Part254.gaussianTail_nonneg _
  have ho0 : 0 ≤ gaussianOutside exampleCore :=
    add_nonneg (BstLean.Part254.gaussianTail_nonneg _) (by positivity)
  have hpair' := mul_le_mul (mul_le_mul_of_nonneg_left hinvc hp.wLam_nonneg) hpair
    hp0 (mul_nonneg hp.wLam_nonneg (inv_nonneg.mpr hcpos.le))
  have hout' := mul_le_mul (mul_le_mul_of_nonneg_left hinvw hp.wLam_nonneg) hout
    ho0 (mul_nonneg hp.wLam_nonneg (inv_nonneg.mpr hwpos.le))
  have hex := mul_le_mul_of_nonneg_left hexc (by norm_num : (0 : ℝ) ≤ 13/10)
  have hs := add_le_add
    (add_le_add (le_refl (p.cLam * (1-4*θ/n)⁻¹)) hpair') hout'
  unfold localGaussian gaussianScalar envelope
  simpa only [div_eq_mul_inv, Nat.cast_ofNat] using
    add_le_add (mul_le_mul_of_nonneg_left hs hθ0) hex

theorem envelope_monoP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) (p : Parameters) (hp : Valid p)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hhi : θ' ≤ 54/100)
    (hw1 : p.wRadius < 1) (hc1 : p.cRadius < 1) : envelope n p θ ≤ envelope n p θ' := by
  have hnR : (8000 : ℝ) ≤ n := by
    have : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
    have h2 : (n0 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hd : 0 < 1 - 4*θ'/n := by
    have h := (div_lt_one hnpos).mpr (by linarith : 4*θ' < (n : ℝ))
    linarith
  have hd' : 0 < 1 - 4*θ/n := by
    have h := (div_lt_one hnpos).mpr (by linarith : 4*θ < (n : ℝ))
    linarith
  have he := div_le_div_of_nonneg_left hp.cLam_nonneg hd (by
      have hdiv := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hθ (by norm_num : (0 : ℝ) ≤ 4)) hnpos.le
      linarith : 1 - 4*θ'/n ≤ 1 - 4*θ/n)
  have hterm : 0 ≤ p.cLam/(1-4*θ/n) + p.wLam/(1-p.cRadius)*(1374279/10^9) +
      p.wLam/(1-p.wRadius)*(6216465741/10^12) := by
    have := hp.cLam_nonneg
    have := hp.wLam_nonneg
    have : 0 < 1-p.cRadius := by linarith
    have : 0 < 1-p.wRadius := by linarith
    positivity
  have hsum : p.cLam/(1-4*θ/n) + p.wLam/(1-p.cRadius)*(1374279/10^9) +
      p.wLam/(1-p.wRadius)*(6216465741/10^12) ≤
      p.cLam/(1-4*θ'/n) + p.wLam/(1-p.cRadius)*(1374279/10^9) +
      p.wLam/(1-p.wRadius)*(6216465741/10^12) :=
    add_le_add (add_le_add he le_rfl) le_rfl
  exact add_le_add (mul_le_mul hθ hsum hterm (h0.trans hθ)) le_rfl

/-! ## The covariance contract on a base `n0` -/

structure CovarianceInputsP (θhi : ℝ) (n : ℕ) (G : Grid) (p : Fin 43 → Parameters)
    (caps : Fin 60 → ℝ) : Prop where
  supplies : ∀ j, Supply n (p j) (cellLower G (BstLean.Part255.sourceIndex j))
    (cellUpper G (BstLean.Part255.sourceIndex j))
  world_window : Icc G.worldLower G.worldUpper ⊆ Icc (46 / 100 : ℝ) θhi
  wide_radius : ∀ j θ, θ ∈ cell G (BstLean.Part255.sourceIndex j) →
    radiusMinus n θ exampleWide ≤ (p j).wRadius
  core_radius : ∀ j θ, θ ∈ cell G (BstLean.Part255.sourceIndex j) →
    radiusMinus n θ exampleCore ≤ (p j).cRadius
  scalar : ∀ i θ, θ ∈ cell G i → envelope n (p (select G.top θ)) θ ≤ caps i

/-- The old contract is the contract with window top `.528`. -/
theorem covToP {n : ℕ} {G : Grid} {p : Fin 43 → Parameters}
    {caps : Fin 60 → ℝ} (F : CovarianceInputs n G p caps) :
    CovarianceInputsP (528 / 1000) n G p caps :=
  ⟨F.supplies, F.world_window, F.wide_radius, F.core_radius, F.scalar⟩

theorem CovarianceInputsP.toOld {θhi : ℝ} (h : θhi ≤ 528 / 1000) {n : ℕ} {G : Grid}
    {p : Fin 43 → Parameters} {caps : Fin 60 → ℝ} (F : CovarianceInputsP θhi n G p caps) :
    CovarianceInputs n G p caps :=
  ⟨F.supplies, fun _ hθ => ⟨(F.world_window hθ).1, (F.world_window hθ).2.trans h⟩,
    F.wide_radius, F.core_radius, F.scalar⟩

theorem covarianceEvent_paymentP {n : ℕ} (hn : 2 ≤ n) {θhi : ℝ} {G : Grid}
    {p : Fin 43 → Parameters} {caps : Fin 60 → ℝ} (F : CovarianceInputsP θhi n G p caps) :
    (retDist (BstLean.Part169.paperDesignP n).toCentres).real
      (agentEv (BstLean.Part169.paperDesignP n) (covarianceEvent n G p))ᶜ ≤
        (1 / 4000 : ℝ) :=
  selected_payment hn _ (select_measurable G.top) _ _ _ F.supplies

theorem localCovP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {θhi : ℝ}
    (hθhi : θhi ≤ 54 / 100) {G : Grid}
    {p : Fin 43 → Parameters} {caps : Fin 60 → ℝ} (F : CovarianceInputsP θhi n G p caps) :
    BstLean.Part259.LocalCovarianceOn (covarianceEvent n G p) (cell G) caps := by
  have hn8 : 8000 ≤ n := h8.trans hn
  intro i θ _ hi k he hτ hC hX v
  let j := select G.top θ
  have hw : θ ∈ Icc G.worldLower G.worldUpper := cell_world hi
  have hmem : θ ∈ cell G (BstLean.Part255.sourceIndex j) := select_member G hw
  have hp := (F.supplies j).valid
  have hlocal : k ∈ agentEv (BstLean.Part169.paperDesignP n)
      (localEvent n (p j) (cellLower G (BstLean.Part255.sourceIndex j))
        (cellUpper G (BstLean.Part255.sourceIndex j)) payment) := by
    have h := BstLean.Part255.selected_agent_mem (BstLean.Part169.paperDesignP n)
      (select G.top)
      (fun j => localEvent n (p j) (cellLower G (BstLean.Part255.sourceIndex j))
        (cellUpper G (BstLean.Part255.sourceIndex j)) payment)
      k hC
    simpa only [he] using h
  have hgauss := Dq_local_gaussianP h8 hn hθhi (p j) hp (BstLean.Part169.paperDesignP n) k hτ
    (by rw [he]; exact F.world_window hw) (by rw [he]; exact hmem) hX hlocal v
  rw [he] at hgauss
  have hθw := F.world_window hw
  have hθ0 : 0 ≤ θ := by linarith [hθw.1]
  have hscalar := (localGaussian_le_envelopeP (by omega : 1 ≤ n) (p j) hp hθ0
    (F.wide_radius j θ hmem) (F.core_radius j θ hmem) hp.wRadius_lt hp.cRadius_lt
    (lt_of_le_of_lt (wide_radius_small hn8 hθ0 (hθw.2.trans hθhi)) (by norm_num))
    (lt_of_le_of_lt (core_radius_small hn8 hθ0 (hθw.2.trans hθhi)) (by norm_num))).trans
    (F.scalar i θ hi)
  refine hgauss.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
  exact mul_le_mul_of_nonneg_right hscalar (by positivity : (0 : ℝ) ≤ 2 / n)

/-- The old `Part263.localCov`, as an instance (base `11883`, window top `.528`). -/
theorem localCov_11883 {n : ℕ} (hn : 11883 ≤ n) {G : Grid}
    {p : Fin 43 → Parameters} {caps : Fin 60 → ℝ} (F : CovarianceInputs n G p caps) :
    BstLean.Part259.LocalCovarianceOn (covarianceEvent n G p) (cell G) caps :=
  localCovP (n0 := 11883) (by norm_num) hn (by norm_num) (covToP F)

/-- The same contract from base `8000`, with the same window top `.528`. -/
theorem localCov_8000 {n : ℕ} (hn : 8000 ≤ n) {G : Grid}
    {p : Fin 43 → Parameters} {caps : Fin 60 → ℝ} (F : CovarianceInputs n G p caps) :
    BstLean.Part259.LocalCovarianceOn (covarianceEvent n G p) (cell G) caps :=
  localCovP (n0 := 8000) le_rfl hn (by norm_num) (covToP F)

end BstLean.Part277
