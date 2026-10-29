import BstLean.Part291WeightedDensity
import BstLean.Part291RWGeometry
import BstLean.Part254GaussianAssembly
import BstLean.Part238Network
import BstLean.Part254GaussianJoint

/- Component: Part291CoreWeighted.lean -/

/-! WS on the core, with RW supplying both dependent rows. No invariance
of the capped weight is used. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part182 BstLean.Part188 BstLean.Part208 BstLean.Part238
open BstLean.Part151 (jac)
open BstLean.Part152 (opN)

theorem core_level_capped {k m : ℕ} (hk : 5 ≤ k)
    (A₁ : Matrix (Fin m) (Fin (k + 1)) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (u : Fin (k + 1) → ℝ) (hu : normSq u = 1) {r τ t z cp sm : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (ht : 0 ≤ t)
    (hRad : 0 < axialRadiusLower (k + 1) r τ t z) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS (r • u) t z, sm ≤ (u ⬝ᵥ sphPt (r • u + τ • ξ)) ^ 2)
    (C G : Set ((Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ)))
    (hCm : MeasurableSet C) (hGm : MeasurableSet G)
    (hCs : ∀ p ∈ C, p.swap ∈ C) (hGs : ∀ p ∈ G, p.swap ∈ G)
    (hGΩ : G ⊆ OmegaS (r • u) t z ×ˢ OmegaS (r • u) t z)
    {kE ko ks lam₀ : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks) (hl₀ : 0 ≤ lam₀)
    (hmode : ∀ p ∈ G ∩ C, ModeBounds (jac A₁ A₂ (sphPt (r • u + τ • p.1)))
      (jac A₁ A₂ (sphPt (r • u + τ • p.2))) kE ko ks cp
      (sphPt (r • u + τ • p.1)) (sphPt (r • u + τ • p.2)))
    (hwide : ∀ p ∈ G, p ∉ C →
      opN ((BJ A₁ A₂ (r • u) τ p.1)ᵀ * BJ A₁ A₂ (r • u) τ p.2) ≤ ((k + 1 : ℕ) : ℝ) * lam₀)
    (f : (Fin (k + 1) → ℝ) → ℝ) (hfm : Measurable f)
    {a d μ s K R W Pp : ℝ} (hd : 0 < d) (hY : d < a - μ ^ 2)
    (hμ : 0 ≤ μ) (hs : 0 ≤ s) (hR : 0 ≤ R) (hfK : ∀ ξ, |f ξ| ≤ K)
    (hw2 : (∫ ξ, wN (r • u) τ ξ ^ 2 ∂stdGauss (Fin (k + 1))) ≤ R ^ 2)
    (hD : RWDeficitMoments (stdGauss (Fin (k + 1))) f μ s)
    (hW0 : 0 ≤ W) (hW : ∀ ξ ∈ OmegaS (r • u) t z, wN (r • u) τ ξ ≤ W)
    (hPp : ∀ ξ, (stdGauss (Fin (k + 1))).real
      {ξ' | ξ' ∈ OmegaS (r • u) t z ∧ (ξ, ξ') ∉ C} ≤ Pp)
    (v : Fin m → ℝ) :
    let w := fun ξ => wN (r • u) τ ξ * weightSq a d (f ξ)
    let Ew := ∫ ξ, wN (r • u) τ ξ ∂stdGauss (Fin (k + 1))
    let Wr := Ew / (a - μ ^ 2) + rwDelta a d μ s * R
    let Tr := (Ew * (axialPlaneUpper (k + 1) r τ t z * (1 - sm) + 1 / (k : ℝ)) /
      (a - μ ^ 2) + rwDelta a d μ s * R) / (1 - cp ^ 2)
    (∫ ξ, (OmegaS (r • u) t z).indicator w ξ *
      normSq (vecMul v (BJ A₁ A₂ (r • u) τ ξ)) ∂stdGauss (Fin (k + 1))) ≤
      (((k + 1 : ℕ) : ℝ) * min
        (kE * Wr + 2 * ko * √(Wr * Tr) + ks * Tr) (ta_lam kE ko ks * Wr) +
       ((k + 1 : ℕ) : ℝ) * lam₀ * (W / d) * Pp +
       √(√(((stdGauss (Fin (k + 1))).prod (stdGauss (Fin (k + 1)))).real
        (Gᶜ ∩ OmegaS (r • u) t z ×ˢ OmegaS (r • u) t z)) *
         (∫ ξ, w ξ ^ 2 * opN (BJ A₁ A₂ (r • u) τ ξ) ^ 4 ∂stdGauss (Fin (k + 1))))) * normSq v := by
  dsimp only
  let ν := stdGauss (Fin (k + 1))
  let w := fun ξ => wN (r • u) τ ξ * weightSq a d (f ξ)
  have hden : 0 < 1 - cp ^ 2 := by linarith
  have hY0 : 0 < a - μ ^ 2 := hd.trans hY
  have hq : Measurable (fun ξ => weightSq a d (f ξ)) := by unfold weightSq; fun_prop
  have hwi := integrable_wN (by omega) (r • u) hτ
  have hwi2 := integrable_wN2 (by omega) (r • u) hτ
  have hi := weighted_density_integrable ν (wN (r • u) τ) f (measurable_wN _ _) hfm
    (a := a) hd (wN_nonneg _ _) hwi hwi2
  have hE0 : 0 ≤ ∫ ξ, wN (r • u) τ ξ ∂ν := integral_nonneg (wN_nonneg _ _)
  have hDelta : 0 ≤ rwDelta a d μ s := by
    have := BstLean.Part195.rotationConstant_nonneg 2
    unfold rwDelta rwD2 rwD4
    positivity
  have hplane : 0 ≤ axialPlaneUpper (k + 1) r τ t z := by
    unfold axialPlaneUpper
    positivity
  have hrow := rw_row_of_bounds ν f (wN (r • u) τ) (fun _ => 1)
    (A := ∫ ξ, wN (r • u) τ ξ ∂ν)
    hfm (measurable_wN _ _) measurable_const hd hY hμ hs hR (by norm_num : (0 : ℝ) ≤ 1)
    hfK (wN_nonneg _ _) (fun _ => zero_le_one) (fun _ => le_rfl) hwi hwi2
    (by simp) hw2 hD
  simp only [mul_one, one_mul] at hrow
  apply core_level_dependent_rows hk A₁ A₂ u hu hr hτ ht hRad hcp hsm1 hsm
    C G hCm hGm hCs hGs hGΩ hkE hko hks hl₀ hmode hwide
    w ((measurable_wN _ _).mul hq) (fun ξ => mul_nonneg (wN_nonneg _ _ ξ) (weightSq_nonneg hd))
    hi.1 hi.2 (by positivity) (by positivity) ?_ ?_ (div_nonneg hW0 hd.le) ?_ hPp v
  · simpa only [w, mul_comm] using hrow
  · intro ξ hξ v hv
    let H := {ξ' | (ξ, ξ') ∈ G ∩ C}
    have hHm : MeasurableSet H := (hGm.inter hCm).preimage measurable_prodMk_left
    have hHΩ : H ⊆ OmegaS (r • u) t z := fun ξ' hξ' => (hGΩ hξ'.1).2
    have hc : ∀ ξ' ∈ H, (sphPt (r • u + τ • ξ) ⬝ᵥ sphPt (r • u + τ • ξ')) ^ 2 ≤ cp ^ 2 :=
      fun ξ' hξ' => (hmode (ξ, ξ') hξ').1
    have h := rw_tangent_row hk u (sphPt (r • u + τ • ξ)) v hu (normSq_sphPt (by omega) _)
      hv hr hτ ht hRad hcp (hsm ξ hξ) H hHm hHΩ hc f hfm hd hY hμ hs hR hfK hw2 hD
    calc
      (∫ ξ' in H, w ξ' * (eTan (sphPt (r • u + τ • ξ))
          (sphPt (r • u + τ • ξ')) ⬝ᵥ v) ^ 2 ∂stdGauss (Fin (k + 1)))
          = ∫ ξ' in H, weightSq a d (f ξ') * wN (r • u) τ ξ' *
              (eTan (sphPt (r • u + τ • ξ))
                (sphPt (r • u + τ • ξ')) ⬝ᵥ v) ^ 2 ∂stdGauss (Fin (k + 1)) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ξ' => by dsimp [w]; ring
      _ ≤ _ := by
        calc
          _ ≤ (((∫ ξ, wN (r • u) τ ξ ∂ν) *
              ((axialPlaneUpper (k + 1) r τ t z * (1 - sm) + 1 / (k : ℝ)) /
                (1 - cp ^ 2)) / (a - μ ^ 2) +
                rwDelta a d μ s * R / (1 - cp ^ 2)) * normSq v) := h
          _ = _ := by
            simp only [ν]
            field_simp [ne_of_gt (sub_pos.mpr hcp), ne_of_gt (lt_trans hd hY)]
            <;> ring_nf
  · intro ξ hξ
    exact (mul_le_mul (hW ξ hξ) (weightSq_le_inv hd) (weightSq_nonneg hd) hW0).trans_eq (by ring)

end BstLean.BlueprintLow

/- Component: Part291WeightedLevels.lean -/

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part188

/-- The core receives its dependent Schur estimate. Only the shell and the
outside receive the crude inverse-cutoff factor. -/
theorem weighted_three_levels {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    {a d : ℝ} (hd : 0 < d) (hg0 : ∀ x, 0 ≤ g x) (hi : Integrable g μ)
    {Ω₀ Ω₁ : Set X} (h0 : MeasurableSet Ω₀) (h1 : MeasurableSet Ω₁) (h10 : Ω₁ ⊆ Ω₀)
    {C S O : ℝ}
    (hc : (∫ x in Ω₁, weightSq a d (f x) * g x ∂μ) ≤ C)
    (hs : (∫ x in Ω₀ \ Ω₁, g x ∂μ) ≤ S)
    (ho : (∫ x in Ω₀ᶜ, g x ∂μ) ≤ O) :
    (∫ x, weightSq a d (f x) * g x ∂μ) ≤ C + (S + O) / d := by
  have hq := weighted_integral_domination μ f g hf hg (a := a) hd hg0 hi
  have hqs := weighted_integral_domination (μ.restrict (Ω₀ \ Ω₁)) f g hf hg (a := a) hd hg0 hi.integrableOn
  have hqo := weighted_integral_domination (μ.restrict Ω₀ᶜ) f g hf hg (a := a) hd hg0 hi.integrableOn
  have hsum : (∫ x, weightSq a d (f x) * g x ∂μ) =
      (∫ x in Ω₁, weightSq a d (f x) * g x ∂μ) +
      (∫ x in Ω₀ \ Ω₁, weightSq a d (f x) * g x ∂μ) +
      (∫ x in Ω₀ᶜ, weightSq a d (f x) * g x ∂μ) := by
    rw [← integral_indicator h1, ← integral_indicator (h0.diff h1), ← integral_indicator h0.compl]
    have h12 : Integrable (fun x =>
        Ω₁.indicator (fun x => weightSq a d (f x) * g x) x +
        (Ω₀ \ Ω₁).indicator (fun x => weightSq a d (f x) * g x) x) μ :=
      (hq.1.indicator h1).add (hq.1.indicator (h0.diff h1))
    rw [← integral_add (hq.1.indicator h1) (hq.1.indicator (h0.diff h1)),
      ← integral_add h12 (hq.1.indicator h0.compl)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      by_cases hx1 : x ∈ Ω₁
      · have hx0 := h10 hx1
        simp [hx1, hx0]
      · by_cases hx0 : x ∈ Ω₀ <;> simp [hx1, hx0]
  rw [hsum]
  have hS := hqs.2.trans (div_le_div_of_nonneg_right hs hd.le)
  have hO := hqo.2.trans (div_le_div_of_nonneg_right ho hd.le)
  calc
    _ ≤ C + S / d + O / d := add_le_add (add_le_add hc hS) hO
    _ = _ := by ring

end BstLean.BlueprintLow

/- Component: Part291ExceptionalScalar.lean -/

namespace BstLean.BlueprintLow
open Real

theorem weighted_exceptional_sqrt {A Aw H h M d : ℝ}
    (hA0 : 0 ≤ A) (hH0 : 0 ≤ H) (hH : H ≤ h) (hM : 0 ≤ M) (hd : 0 < d)
    (hA : A ≤ M ^ 2) (hAw : Aw ≤ A / d ^ 2) :
    √(√H * Aw) ≤ M / d * √(√h) := by
  have hAw' : Aw ≤ M ^ 2 / d ^ 2 := hAw.trans (div_le_div_of_nonneg_right hA (sq_nonneg _))
  calc
    _ ≤ √(√h * (M ^ 2 / d ^ 2)) := by
      apply sqrt_le_sqrt
      exact (mul_le_mul_of_nonneg_left hAw' (sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (sqrt_le_sqrt hH) (by positivity))
    _ = M / d * √(√h) := by
      rw [sqrt_mul (sqrt_nonneg _), sqrt_div (sq_nonneg _), sqrt_sq hM, sqrt_sq hd.le]
      ring

theorem exceptional_sqrt {A H h M : ℝ}
    (hA0 : 0 ≤ A) (hH : H ≤ h) (hM : 0 ≤ M) (hA : A ≤ M ^ 2) :
    √(√H * A) ≤ M * √(√h) := by
  calc
    _ ≤ √(√h * M ^ 2) := by gcongr
    _ = _ := by rw [sqrt_mul (sqrt_nonneg _), sqrt_sq hM]; ring

theorem outside_sqrt {A P p M : ℝ}
    (hA0 : 0 ≤ A) (hP0 : 0 ≤ P) (hP : P ≤ p) (hM : 0 ≤ M) (hA : A ≤ M ^ 2) :
    √(P * A) ≤ M * √p := by
  have hp : 0 ≤ p := hP0.trans hP
  calc
    _ ≤ √(p * M ^ 2) := by gcongr
    _ = _ := by rw [sqrt_mul hp, sqrt_sq hM]; ring

end BstLean.BlueprintLow

/- Component: Part291WeightedAssembly.lean -/

/-! Core, shell and outside assembly with a dependent capped core weight. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part160 BstLean.Part182 BstLean.Part188 BstLean.Part208 BstLean.Part238
open BstLean.Part199 (Window radiusMinus omega_subset pairRowBound outsideBound
  coreKernelSet measurableSet_coreKernelSet coreKernelSet_swap coreKernelSet_row schur_scalar)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)
open BstLean.Part151 (jac)
open BstLean.Part254

theorem weighted_core_wide {n : ℕ} (hn : 6 ≤ n)
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
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n) (f : (Fin n → ℝ) → ℝ) (hfm : Measurable f)
    {α dcut μ0 s R Kf : ℝ} (hdcut : 0 < dcut) (hY : dcut < α - μ0 ^ 2)
    (hμ : 0 ≤ μ0) (hs : 0 ≤ s) (hR0 : 0 ≤ R) (hfK : ∀ ξ, |f ξ| ≤ Kf)
    (hw2 : (∫ ξ, wN c τ ξ ^ 2 ∂stdGauss (Fin n)) ≤ R ^ 2)
    (hD : RWDeficitMoments (stdGauss (Fin n)) f μ0 s)
    (v : Fin (mA n) → ℝ) :
    let Ew := ∫ ξ, wN c τ ξ ∂stdGauss (Fin n)
    let Wr := Ew / (α - μ0 ^ 2) + rwDelta α dcut μ0 s * R
    let Tr := (Ew * (axialPlaneUpper n a τ w₁.t w₁.z * (1 - sm) + 1 / ((n - 1 : ℕ) : ℝ)) /
      (α - μ0 ^ 2) + rwDelta α dcut μ0 s * R) / (1 - cp ^ 2)
    (∫ ξ, weightSq α dcut (f ξ) * (wN c τ ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)))
      ∂stdGauss (Fin n)) ≤
      ((n : ℝ) * min (kE * Wr + 2 * ko * √(Wr * Tr) + ks * Tr) (ta_lam kE ko ks * Wr) +
        (thetaC c τ * lam₀ / (1 - radiusMinus n (thetaC c τ) w₁) * gaussianPair w₁ +
         thetaC c τ * lam₀ / (1 - radiusMinus n (thetaC c τ) w₀) * gaussianOutside w₁ +
         M * (2 * √(√h) + √(gaussianOutside w₀))) / dcut) * normSq v := by
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
  have b1 := core_level_capped hd A₁ A₂ u hu ha hτ w₁.t_nonneg hR hcp hsm1 hsm C G₁ hCm hG₁m
    hCs hG₁s (fun p hp => hp.2) hkE hko hks hl₀
    (fun p hp => by
      have hpΓ : p ∈ GammaS c w₁.t w₁.z w₁.pair := by
        rcases hp.2 with h' | h'
        · exact h'
        · exact absurd hp.1.2 h'
      exact hmode p hp.1.1 hpΓ)
    (fun p hp hpC => hwide p hp.1 (fun hΓ => hpC (Or.inl hΓ)))
    f hfm hdcut hY hμ hs hR0 hfK hw2 hD hW₁0 (hW w₁ hr₁)
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
  dsimp only at b1 ⊢
  have hA0 : 0 ≤ A4 A₁ A₂ c τ := integral_nonneg fun ξ => by positivity
  have hm : ((mA (d + 1) : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hXi := Xi4_eq_A4 A₁ A₂ c τ
  have hsA : √(A4 A₁ A₂ c τ) ≤ M := by
    rw [hXi, hm] at hX
    have he : M * (2 / ((d + 1 : ℕ) : ℝ)) / ((d + 1 : ℕ) : ℝ) =
      2 / ((d + 1 : ℕ) : ℝ) ^ 2 * M := by ring
    rw [he] at hX
    exact le_of_mul_le_mul_left hX (by positivity)
  have hA : A4 A₁ A₂ c τ ≤ M ^ 2 := (sqrt_le_iff.mp hsA).2
  have hAw := weighted_fourth_domination μ f
    (fun ξ => wN c τ ξ ^ 2 * opN (BJ A₁ A₂ c τ ξ) ^ 4) hfm
    (((measurable_wN c τ).pow_const 2).mul
      ((BstLean.Part182.measurable_opN_BJ A₁ A₂ c).pow_const 4))
    (a := α) hdcut (fun ξ => by positivity) (integrable_wN2_opN4 A₁ A₂ c (by omega) hτ)
  have hAw' : (∫ ξ, (wN c τ ξ * weightSq α dcut (f ξ)) ^ 2 * opN (BJ A₁ A₂ c τ ξ) ^ 4 ∂μ) ≤
      A4 A₁ A₂ c τ / dcut ^ 2 := by
    refine le_trans (le_of_eq ?_) hAw.2
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by ring
  have e1 := weighted_exceptional_sqrt hA0 measureReal_nonneg hH₁ hM hdcut hA hAw'
  have e0 := exceptional_sqrt hA0 hH₀ hM hA
  have eo := outside_sqrt hA0 measureReal_nonneg hPo hM hA
  have hv0 := normSq_nonneg v
  have b1' := b1.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl e1) hv0)
  have b0' := b0.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl e0) hv0)
  have bo' := bo.trans (mul_le_mul_of_nonneg_right eo hv0)
  let g := fun ξ => wN c τ ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ))
  have mg : Measurable g := by
    apply (measurable_wN _ _).mul
    have hJ : Measurable (fun ξ => BstLean.Part153.jacT A₁ A₂ (sphPt (c + τ • ξ))) :=
      (BstLean.Part153.measurable_jacT A₁ A₂).comp
        (measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ)))
    have hv : Measurable (fun ξ => vecMul v (BJ A₁ A₂ c τ ξ)) := by
      change Measurable (fun ξ =>
        vecMul v (BstLean.Part153.jacT A₁ A₂ (sphPt (c + τ • ξ))))
      exact BstLean.Part167.measurable_vecMul_joint.comp (measurable_const.prodMk hJ)
    exact BstLean.Part130.measurable_normSq.comp hv
  have ig : Integrable g μ := by
    simpa only [Set.indicator_univ] using integrable_level A₁ A₂ c (by omega) hτ univ MeasurableSet.univ v
  have hconv (S : Set (Fin (d + 1) → ℝ)) (hS : MeasurableSet S) (w : (Fin (d + 1) → ℝ) → ℝ) :
      (∫ ξ, S.indicator w ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂μ) =
      ∫ ξ in S, w ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by by_cases hξ : ξ ∈ S <;> simp [hξ]
  rw [hconv _ hΩ₁] at b1'
  rw [hconv _ (hΩ₀.diff hΩ₁)] at b0'
  rw [hconv _ hΩ₀.compl] at bo'
  have bc := by
    calc
      (∫ ξ in Ω₁, weightSq α dcut (f ξ) * g ξ ∂μ) =
          ∫ ξ in Ω₁, wN c τ ξ * weightSq α dcut (f ξ) *
            normSq (vecMul v (BJ A₁ A₂ c τ ξ)) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ξ => by dsimp [g]; ring
      _ ≤ _ := b1'
  have h := weighted_three_levels μ f g hfm mg hdcut
    (fun ξ => mul_nonneg (wN_nonneg _ _ ξ) (normSq_nonneg _)) ig hΩ₀ hΩ₁ h01 bc b0' bo'
  dsimp only [g] at h
  set Ew0 := ∫ ξ, wN (a • u) τ ξ ∂stdGauss (Fin (d + 1))
  set Wr0 := Ew0 / (α - μ0 ^ 2) + rwDelta α dcut μ0 s * R
  set Tr0 := (Ew0 * (axialPlaneUpper (d + 1) a τ w₁.t w₁.z * (1 - sm) + 1 / (d : ℝ)) /
      (α - μ0 ^ 2) + rwDelta α dcut μ0 s * R) / (1 - cp ^ 2)
  have hWrTarget : Ew0 / (α - μ0 ^ 2) + rwDelta α dcut μ0 s * R = Wr0 := rfl
  have hTrTarget :
      (Ew0 * (axialPlaneUpper (d + 1) a τ w₁.t w₁.z * (1 - sm) + 1 / (d : ℝ)) /
        (α - μ0 ^ 2) + rwDelta α dcut μ0 s * R) / (1 - cp ^ 2) = Tr0 := rfl
  dsimp only [c] at h
  refine h.trans ?_
  rw [hdcast]
  rw [hTrTarget]
  simp only [Nat.add_sub_cancel_right, gaussianOutside, gaussianPair]
  push_cast
  have hdplus : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  exact le_of_eq (by
    field_simp [ne_of_gt hdplus, ne_of_gt hdcut]
    <;> ring)

end BstLean.BlueprintLow

/- Component: Part291WeightedJoint.lean -/

/-! Core, shell and outside assembly with a dependent capped core weight. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part160 BstLean.Part182 BstLean.Part188 BstLean.Part208 BstLean.Part238
open BstLean.Part199 (Window radiusMinus omega_subset pairRowBound outsideBound
  coreKernelSet measurableSet_coreKernelSet coreKernelSet_swap coreKernelSet_row schur_scalar
  pairFailure measurableSet_pairFailure commonGood measurableSet_commonGood commonGood_swap)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)
open BstLean.Part151 (jac)
open BstLean.Part254

theorem weighted_sharp_joint {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c u : Fin n → ℝ) {a τ : ℝ} (hcau : c = a • u) (ha : 0 < a) (hu : normSq u = 1)
    (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {kE ko ks lam₀ cp sm M b : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1) (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hR : 0 < axialRadiusLower n a τ w₁.t w₁.z) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS c w₁.t w₁.z, sm ≤ (u ⬝ᵥ sphPt (c + τ • ξ)) ^ 2)
    (hb : sharpBadMass n w₀ w₁ lam₀ kE ko ks cp ((c, τ), (A₁, A₂)) ≤ b)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n) (f : (Fin n → ℝ) → ℝ) (hfm : Measurable f)
    {α dcut μ0 s R Kf : ℝ} (hdcut : 0 < dcut) (hY : dcut < α - μ0 ^ 2)
    (hμ : 0 ≤ μ0) (hs : 0 ≤ s) (hR0 : 0 ≤ R) (hfK : ∀ ξ, |f ξ| ≤ Kf)
    (hw2 : (∫ ξ, wN c τ ξ ^ 2 ∂stdGauss (Fin n)) ≤ R ^ 2)
    (hD : RWDeficitMoments (stdGauss (Fin n)) f μ0 s)
    (v : Fin (mA n) → ℝ) :
    let Ew := ∫ ξ, wN c τ ξ ∂stdGauss (Fin n)
    let Wr := Ew / (α - μ0 ^ 2) + rwDelta α dcut μ0 s * R
    let Tr := (Ew * (axialPlaneUpper n a τ w₁.t w₁.z * (1 - sm) + 1 / ((n - 1 : ℕ) : ℝ)) /
      (α - μ0 ^ 2) + rwDelta α dcut μ0 s * R) / (1 - cp ^ 2)
    (∫ ξ, weightSq α dcut (f ξ) * (wN c τ ξ * normSq (vecMul v (BJ A₁ A₂ c τ ξ)))
      ∂stdGauss (Fin n)) ≤
      ((n : ℝ) * min (kE * Wr + 2 * ko * √(Wr * Tr) + ks * Tr) (ta_lam kE ko ks * Wr) +
        (thetaC c τ * lam₀ / (1 - radiusMinus n (thetaC c τ) w₁) * gaussianPair w₁ +
         thetaC c τ * lam₀ / (1 - radiusMinus n (thetaC c τ) w₀) * gaussianOutside w₁ +
         M * (2 * √(√(gaussianTail w₀.pair + 2 * b)) + √(gaussianOutside w₀))) / dcut) * normSq v := by
  have hn0 : 0 < n := by omega
  let B := pairFailure A₁ A₂ c τ w₀ lam₀ ∪ modeFailure A₁ A₂ c τ w₁ kE ko ks cp
  have hBm : MeasurableSet B :=
    (measurableSet_pairFailure A₁ A₂ c τ w₀ lam₀).union
      (measurableSet_modeFailure A₁ A₂ c τ w₁ kE ko ks cp)
  let G := commonGood c w₀ B
  have hB : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b := hb
  apply weighted_core_wide hn A₁ A₂ c u hcau ha hu hτ w₀ w₁ h10 hkE hko hks hl₀ hM hθ hr₀ hr₁
    hR hcp hsm1 hsm G (measurableSet_commonGood c w₀ hBm)
    (fun p hp => commonGood_swap c w₀ B p.1 p.2 hp)
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (fun p hp hp₁ => by
      by_contra hno
      exact hp.2 (Or.inl (Or.inr ⟨hp₁, hno⟩)))
    (fun p hp _ => by
      apply not_lt.mp
      intro hbad
      exact hp.2 (Or.inl (Or.inl ⟨hp.1, hbad⟩)))
    (commonGood_exception_gaussian hn0 c w₀ hBm hB) hX f hfm hdcut hY hμ hs hR0 hfK hw2 hD v


end BstLean.BlueprintLow
