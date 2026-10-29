import BstLean.Part254GaussianGeometry

/-! The sharp covariance assembly with actual Gaussian tails. -/
namespace BstLean.Part254
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part160 BstLean.Part182 BstLean.Part208
open BstLean.Part199 BstLean.Part238
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)
open BstLean.Part151 (jac)

noncomputable def gaussianPair (w : Window) : ℝ := gaussianTail w.pair
noncomputable def gaussianOutside (w : Window) : ℝ := gaussianTail w.t + 2 * exp (-w.z)

noncomputable def gaussianScalar (n : ℕ) (θ : ℝ) (w₀ w₁ : Window)
    (K lam₀ E M h : ℝ) : ℝ :=
  θ * (K * E + lam₀ * (1 - radiusMinus n θ w₁)⁻¹ * gaussianPair w₁ +
    lam₀ * (1 - radiusMinus n θ w₀)⁻¹ * gaussianOutside w₁) +
    M * (2 * √(√h) + √(gaussianOutside w₀))

/-- **Sharp core/wide assembly.** Fix the Agent matrices, the centre `c = a u ≠ 0`, the scale
`τ > 0`, and nested windows. Let `G ⊆ Ω₀²` be a symmetric measurable good-pair set. On core
pairs of `G` the three TI mode bounds hold with constants `n kE, n ko, n ks` and overlap cap `cp`;
on all of `G` the wide operator bound `n λ₀` holds. Then the quadratic form of `D` satisfies the
paper formula with core coefficient `min(kE + 2 ko √χ₁ + ks χ₁, λ₁)`, the paper radius mean
`(1 - 4θ/n)⁻¹`, the shell and outside terms, and the exceptional term `M(2 h^{1/4} + P_out^{1/2})`. -/
theorem Dq_core_wide_gaussian {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c u : Fin n → ℝ) {a τ : ℝ} (hcau : c = a • u) (ha : 0 < a) (hu : normSq u = 1)
    (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {kE ko ks lam₀ cp sm M h : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1) (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hR : 0 < axialRadiusLower n a τ w₁.t w₁.z) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS c w₁.t w₁.z, sm ≤ (u ⬝ᵥ sphPt (c + τ • ξ)) ^ 2)
    (G : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hGm : MeasurableSet G)
    (hGs : ∀ p ∈ G, p.swap ∈ G)
    (hGΩ : G ⊆ OmegaS c w₀.t w₀.z ×ˢ OmegaS c w₀.t w₀.z)
    (hmode : ∀ p ∈ G, p ∈ GammaS c w₁.t w₁.z w₁.pair →
      ModeBounds (jac A₁ A₂ (sphPt (c + τ • p.1))) (jac A₁ A₂ (sphPt (c + τ • p.2)))
        kE ko ks cp (sphPt (c + τ • p.1)) (sphPt (c + τ • p.2)))
    (hwide : ∀ p ∈ G, p ∉ GammaS c w₁.t w₁.z w₁.pair →
      opN ((BJ A₁ A₂ c τ p.1)ᵀ * BJ A₁ A₂ c τ p.2) ≤ (n : ℝ) * lam₀)
    (hh : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
      (Gᶜ ∩ OmegaS c w₀.t w₀.z ×ˢ OmegaS c w₀.t w₀.z) ≤ h)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n) (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤
      gaussianScalar n (thetaC c τ) w₀ w₁
        (min (sharpK kE ko ks (chiCore n a τ w₁.t w₁.z sm cp)) (ta_lam kE ko ks))
        lam₀ (1 - 4 * thetaC c τ / n)⁻¹ M h * (2 / (n : ℝ)) / n * normSq v := by
  subst hcau
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  haveI : IsProbabilityMeasure (stdGauss (Fin (d + 1))) := by unfold stdGauss; infer_instance
  have hd : 5 ≤ d := by omega
  have hn0 : 0 < d + 1 := by omega
  have hnR : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hn0
  set c : Fin (d + 1) → ℝ := a • u with hcd
  have hc0 : c ≠ 0 := by
    intro h0
    have : normSq c = 0 := by rw [h0]; simp [normSq]
    rw [hcd, normSq_smul, hu, mul_one] at this
    exact ha.ne' (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  set θ := thetaC c τ with hθd
  have hθ0 : 0 ≤ θ := by rw [hθd]; unfold thetaC; positivity
  let μ := stdGauss (Fin (d + 1))
  let Ω₀ := OmegaS c w₀.t w₀.z
  let Ω₁ := OmegaS c w₁.t w₁.z
  have hΩ₀ : MeasurableSet Ω₀ := measurableSet_OmegaS c w₀.t w₀.z
  have hΩ₁ : MeasurableSet Ω₁ := measurableSet_OmegaS c w₁.t w₁.z
  have h01 : Ω₁ ⊆ Ω₀ := omega_subset c h10
  let C := coreKernelSet c w₁
  have hCm : MeasurableSet C := measurableSet_coreKernelSet c w₁
  have hCs : ∀ p ∈ C, p.swap ∈ C := fun p hp => coreKernelSet_swap c w₁ p.1 p.2 hp
  let G₁ := G ∩ Ω₁ ×ˢ Ω₁
  have hG₁m : MeasurableSet G₁ := hGm.inter (hΩ₁.prod hΩ₁)
  have hG₁s : ∀ p ∈ G₁, p.swap ∈ G₁ := fun p hp => ⟨hGs p hp.1, hp.2.2, hp.2.1⟩
  have hW : ∀ w : Window, radiusMinus (d + 1) θ w < 1 →
      ∀ ξ ∈ OmegaS c w.t w.z, wN c τ ξ ≤ (1 - radiusMinus (d + 1) θ w)⁻¹ * θ / (d + 1 : ℕ) := by
    intro w hr ξ hξ
    have h := omega_weight hn0 hc0 hτ w.t_nonneg w.z_nonneg hξ hr
    simpa only [wN, radiusMinus, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hW₁0 : 0 ≤ (1 - radiusMinus (d + 1) θ w₁)⁻¹ * θ / (d + 1 : ℕ) := by
    have : 0 < 1 - radiusMinus (d + 1) θ w₁ := by linarith
    positivity
  have hW₀0 : 0 ≤ (1 - radiusMinus (d + 1) θ w₀)⁻¹ * θ / (d + 1 : ℕ) := by
    have : 0 < 1 - radiusMinus (d + 1) θ w₀ := by linarith
    positivity
  -- core level
  have hdcast : (((d + 1 - 1 : ℕ)) : ℝ) = (d : ℝ) := by simp
  have b1 := core_level_sharp hd A₁ A₂ u hu ha hτ w₁.t_nonneg hR hcp hsm1 hsm C G₁ hCm hG₁m
    hCs hG₁s (fun p hp => hp.2) hkE hko hks hl₀
    (fun p hp => by
      have hpΓ : p ∈ GammaS c w₁.t w₁.z w₁.pair := by
        rcases hp.2 with h' | h'
        · exact h'
        · exact absurd hp.1.2 h'
      exact hmode p hp.1.1 hpΓ)
    (fun p hp hpC => hwide p hp.1 (fun hΓ => hpC (Or.inl hΓ))) hW₁0 (hW w₁ hr₁)
    (fun ξ => coreKernelSet_row_gaussian hn0 c w₁ ξ) v
  -- shell level
  have hnl₀ : 0 ≤ ((d + 1 : ℕ) : ℝ) * lam₀ := mul_nonneg hnR.le hl₀
  have hwi := integrable_wN (n := d + 1) (by omega) c hτ
  have hw0 := wN_nonneg c τ
  have hPs : μ.real (Ω₀ \ Ω₁) ≤ gaussianOutside w₁ :=
    (measureReal_mono (fun _ h => h.2) (measure_ne_top _ _)).trans
      (omega_compl_gaussian hn0 c w₁.t_nonneg w₁.z_nonneg)
  let G₀ := G ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁)
  have hG₀m : MeasurableSet G₀ := hGm.inter ((hΩ₀.diff hΩ₁).prod (hΩ₀.diff hΩ₁))
  have hrow₀ : ∀ ξ, ∫ ξ', G₀.indicator (Function.uncurry (kern ∅ 0 (((d + 1 : ℕ) : ℝ) * lam₀)))
      (ξ, ξ') * (Ω₀ \ Ω₁).indicator (wN c τ) ξ' ∂μ ≤
      ((d + 1 : ℕ) : ℝ) * lam₀ * ((1 - radiusMinus (d + 1) θ w₀)⁻¹ * θ / (d + 1 : ℕ)) *
        gaussianOutside w₁ := by
    intro ξ
    refine (row_bound μ MeasurableSet.empty hG₀m le_rfl hnl₀
      ((Ω₀ \ Ω₁).indicator (wN c τ)) ((measurable_wN c τ).indicator (hΩ₀.diff hΩ₁))
      (fun ξ => Set.indicator_nonneg (fun _ _ => hw0 _) ξ) (hwi.indicator (hΩ₀.diff hΩ₁))
      (hΩ₀.diff hΩ₁) (fun ξ hξ => Set.indicator_of_notMem hξ _)
      (W := (1 - radiusMinus (d + 1) θ w₀)⁻¹ * θ / (d + 1 : ℕ))
      (fun ξ hξ => by rw [Set.indicator_of_mem hξ]; exact hW w₀ hr₀ ξ hξ.1) ξ).trans ?_
    have he : {ξ' | ξ' ∈ Ω₀ \ Ω₁ ∧ (ξ, ξ') ∉
        (∅ : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)))} = Ω₀ \ Ω₁ := by ext ξ'; simp
    rw [he, zero_mul, zero_add]
    exact mul_le_mul_of_nonneg_left hPs (mul_nonneg hnl₀ hW₀0)
  have b0 := schur_level A₁ A₂ c (by omega) hτ (Ω₀ \ Ω₁) (hΩ₀.diff hΩ₁)
    (kern ∅ 0 (((d + 1 : ℕ) : ℝ) * lam₀)) (measurable_kern MeasurableSet.empty _ _)
    (kern_nonneg ∅ le_rfl hnl₀) (kern_symm (fun _ _ h => h) _ _) (kern_le ∅ le_rfl hnl₀)
    G₀ hG₀m (fun a b hab => ⟨hGs (a, b) hab.1, hab.2.2, hab.2.1⟩)
    (fun a b hab => by
      rw [kern_of_notMem (Set.notMem_empty _)]
      exact hwide (a, b) hab.1 (fun hΓ => hab.2.1.2 hΓ.1))
    hrow₀ v
  have bo := out_level A₁ A₂ c (by omega) hτ Ω₀ᶜ hΩ₀.compl v
  -- exceptional masses
  have hH₁ : (μ.prod μ).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁) ≤ h := by
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hh
    rintro p ⟨hno, hp⟩
    exact ⟨fun hG => hno ⟨hG, hp⟩, h01 hp.1, h01 hp.2⟩
  have hH₀ : (μ.prod μ).real (G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁)) ≤ h := by
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hh
    rintro p ⟨hno, hp⟩
    exact ⟨fun hG => hno ⟨hG, hp⟩, hp.1.1, hp.2.1⟩
  have hPo := omega_compl_gaussian hn0 c w₀.t_nonneg w₀.z_nonneg
  -- radius mean
  have hEw : ∫ ξ, wN c τ ξ ∂μ ≤ (1 - 4 * θ / (d + 1 : ℕ))⁻¹ * θ / (d + 1 : ℕ) := by
    have h' := Ew_paper (n := d + 1) (by omega) c hτ
    convert h' using 1; ring
  -- combine
  rw [Dq_split A₁ A₂ c (by omega) hτ h01 hΩ₀ hΩ₁ v]
  have hA0 : 0 ≤ A4 A₁ A₂ c τ := integral_nonneg fun ξ => by positivity
  rw [Real.sqrt_mul (Real.sqrt_nonneg _)] at b1 b0
  rw [Real.sqrt_mul measureReal_nonneg] at bo
  set K := min (sharpK kE ko ks (chiCore (d + 1) a τ w₁.t w₁.z sm cp)) (ta_lam kE ko ks) with hKd
  have hchi : chiCore (d + 1) a τ w₁.t w₁.z sm cp =
      (axialPlaneUpper (d + 1) a τ w₁.t w₁.z * (1 - sm) + 1 / (d : ℝ)) / (1 - cp ^ 2) := by
    unfold chiCore; rw [hdcast]
  rw [← hchi, ← hKd] at b1
  have hK0 : 0 ≤ K := by
    rw [hKd]
    exact le_min (sharpK_nonneg hkE hko hks (by rw [hchi]; exact chi_nonneg hR hcp hsm1))
      (ta_lam_nonneg hkE hks)
  -- scale everything
  set V := normSq v with hVd
  have hV0 : 0 ≤ V := normSq_nonneg v
  have hm : ((mA (d + 1) : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hXi : Xi4 A₁ A₂ c τ = 2 / (mA (d + 1) : ℝ) * √(A4 A₁ A₂ c τ) := Xi4_eq_A4 A₁ A₂ c τ
  set N := ((d + 1 : ℕ) : ℝ) with hNd
  set E := (1 - 4 * θ / N)⁻¹ with hEd
  set r₀ := radiusMinus (d + 1) θ w₀
  set r₁ := radiusMinus (d + 1) θ w₁
  set Ew := ∫ ξ, wN c τ ξ ∂μ
  set sA := √(A4 A₁ A₂ c τ)
  set H₁ := (μ.prod μ).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁)
  set H₀ := (μ.prod μ).real (G₀ᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁))
  set Po := μ.real Ω₀ᶜ
  have hsA : 0 ≤ sA := Real.sqrt_nonneg _
  have hF : √(√H₁) + √(√H₀) + √Po ≤ 2 * √(√h) + √(gaussianOutside w₀) := by
    have e1 := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hH₁)
    have e0 := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hH₀)
    have eo := Real.sqrt_le_sqrt hPo
    unfold gaussianOutside
    linarith
  have hm0 : (0 : ℝ) < (mA (d + 1) : ℝ) := by rw [hm]; positivity
  have ht : 0 ≤ 2 / (mA (d + 1) : ℝ) := by positivity
  -- the three level bounds
  have hsum := add_le_add (add_le_add b1 b0) bo
  have hmain : 2 / (mA (d + 1) : ℝ) *
      (∫ ξ, (OmegaS c w₁.t w₁.z).indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂μ +
       ∫ ξ, (Ω₀ \ Ω₁).indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂μ +
       ∫ ξ, Ω₀ᶜ.indicator (wN c τ) ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂μ) ≤
      (2 / (mA (d + 1) : ℝ) * (N * K * Ew + N * lam₀ * ((1 - r₁)⁻¹ * θ / N) * gaussianPair w₁ +
        N * lam₀ * ((1 - r₀)⁻¹ * θ / N) * gaussianOutside w₁) +
        Xi4 A₁ A₂ c τ * (√(√H₁) + √(√H₀) + √Po)) * V := by
    refine (mul_le_mul_of_nonneg_left hsum ht).trans (le_of_eq ?_)
    rw [hXi]
    unfold gaussianPair
    ring
  refine hmain.trans ?_
  -- replace each quantity by its bound
  have hEw' : N * K * Ew ≤ N * K * (E * θ / N) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hnR.le hK0)
    simpa only [hEd, hNd] using hEw
  have hXF := mul_le_mul hX hF (by positivity) (by positivity)
  have hfin : (2 / (mA (d + 1) : ℝ) * (N * K * Ew + N * lam₀ * ((1 - r₁)⁻¹ * θ / N) * gaussianPair w₁ +
        N * lam₀ * ((1 - r₀)⁻¹ * θ / N) * gaussianOutside w₁) +
        Xi4 A₁ A₂ c τ * (√(√H₁) + √(√H₀) + √Po)) * V ≤
      (2 / (mA (d + 1) : ℝ) * (N * K * (E * θ / N) + N * lam₀ * ((1 - r₁)⁻¹ * θ / N) * gaussianPair w₁ +
        N * lam₀ * ((1 - r₀)⁻¹ * θ / N) * gaussianOutside w₁) +
        M * (2 / N) / N * (2 * √(√h) + √(gaussianOutside w₀))) * V := by
    apply mul_le_mul_of_nonneg_right _ hV0
    exact add_le_add (mul_le_mul_of_nonneg_left (by linarith [hEw']) ht) hXF
  refine hfin.trans (le_of_eq ?_)
  unfold gaussianScalar
  rw [hm]
  field_simp
  ring

end BstLean.Part254
