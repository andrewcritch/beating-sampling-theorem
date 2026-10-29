import BstLean.Part72Tilt
import BstLean.Part56PropD_Polar

/-!
# Part 72: the block direction of a tilt that depends only on `‖Π_V x‖²`

Coordinates `Fin (b + r)`, `V` = the first `b` coordinates. `xV x`, `xP x` are the two blocks,
`UV x = ‖xV x‖²`. For every measurable weight `W` and every measurable `G ≥ 0`:
`E_σ[W(UV x)·G(xV/‖xV‖)] = E_{σ_b}[G]·E_σ[W(UV x)]` (`block_split`).
So under every distribution with density `∝ W(UV x)` relative to `σ`, the direction `xV/‖xV‖`
is uniform on `S^{b−1}`, whatever `W` is (omOV-cx §2, omOV-opus §4.1).
Route: `σ` is the law of `g/‖g‖` (Part 56); `γ_{b+r} = γ_b ⊗ γ_r`; the Gaussian polar formula
`gauss_polar_gen` (Part 53) on the block `V`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (uniformSphere stdGauss)
open BstLean.Part53 (unitF53 radF53)

variable {b r : ℕ}

/-- The block `V` (the first `b` coordinates). -/
def xV (x : Fin (b + r) → ℝ) : Fin b → ℝ := fun j => x (Fin.castAdd r j)

/-- The block `V^⊥` (the last `r` coordinates). -/
def xP (x : Fin (b + r) → ℝ) : Fin r → ℝ := fun j => x (Fin.natAdd b j)

/-- `UV x = ‖xV x‖²`. -/
def UV (x : Fin (b + r) → ℝ) : ℝ := ∑ j, xV x j ^ 2

lemma measurable_xV : Measurable (xV (b := b) (r := r)) := by
  unfold xV; fun_prop

lemma measurable_xP : Measurable (xP (b := b) (r := r)) := by
  unfold xP; fun_prop

lemma sum_split (f : ℝ → ℝ) (x : Fin (b + r) → ℝ) :
    ∑ i, f (x i) = ∑ j, f (xV x j) + ∑ j, f (xP x j) := by
  rw [Fin.sum_univ_add]; rfl

lemma split_mp : MeasurePreserving (fun x : Fin (b + r) → ℝ => (xV x, xP x))
    (stdGauss (Fin (b + r))) ((stdGauss (Fin b)).prod (stdGauss (Fin r))) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (b + r) => ProbabilityTheory.gaussianReal 0 1)
    (finSumFinEquiv (m := b) (n := r))).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin b ⊕ Fin r => ProbabilityTheory.gaussianReal 0 1)
  have h := h2.comp h1
  unfold stdGauss
  convert h using 1
  funext x
  ext j
  · simp [xV, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · simp [xP, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

lemma unitF53_smul {ι : Type} [Fintype ι] (c : ℝ) (hc : 0 < c) (z : ι → ℝ) :
    unitF53 (c • z) = unitF53 z := by
  unfold unitF53
  have hs : ∑ i, (c • z) i ^ 2 = c ^ 2 * ∑ i, z i ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hs, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, smul_smul]
  congr 1
  rcases eq_or_ne (Real.sqrt (∑ i, z i ^ 2)) 0 with h | h
  · rw [h]; simp
  · field_simp

lemma xV_smul (c : ℝ) (x : Fin (b + r) → ℝ) : xV (c • x) = c • xV x := rfl

lemma xP_smul (c : ℝ) (x : Fin (b + r) → ℝ) : xP (c • x) = c • xP x := rfl

lemma unit_xV_unit (g : Fin (b + r) → ℝ) : unitF53 (xV (unitF53 g)) = unitF53 (xV g) := by
  have hs : 0 ≤ Real.sqrt (∑ i, g i ^ 2) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs with h | h
  · have hg : g = 0 := by
      have h0 : ∑ i, g i ^ 2 = 0 := by
        have := Real.sqrt_eq_zero'.mp h.symm
        exact le_antisymm this (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g i))).mp h0 i
        (Finset.mem_univ i)
      simpa using this
    subst hg
    simp [unitF53, xV]
  · unfold unitF53
    rw [xV_smul]
    exact unitF53_smul _ (by positivity) _

lemma UV_unit (g : Fin (b + r) → ℝ) :
    UV (unitF53 g) = radF53 (xV g) ^ 2 / (radF53 (xV g) ^ 2 + ∑ j, xP g j ^ 2) := by
  have hV : radF53 (xV g) ^ 2 = ∑ j, xV g j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [hV]
  have htot : ∑ i, g i ^ 2 = ∑ j, xV g j ^ 2 + ∑ j, xP g j ^ 2 := sum_split (fun t => t ^ 2) g
  unfold UV unitF53
  rw [xV_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [← htot, div_pow, one_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  ring

/-- **Block splitting** (Gaussian form). -/
private lemma block_key (hbr : 1 ≤ b + r) (W : ℝ → ℝ≥0∞) (hW : Measurable W)
    (G : (Fin b → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, W (UV x) * G (unitF53 (xV x)) ∂uniformSphere (b + r) =
      (∫⁻ z, G (unitF53 z) ∂stdGauss (Fin b)) *
        ∫⁻ h, ∫⁻ z', W (radF53 z' ^ 2 / (radF53 z' ^ 2 + ∑ j, h j ^ 2)) ∂stdGauss (Fin b)
          ∂stdGauss (Fin r) := by
  have hUV : Measurable (UV (b := b) (r := r)) := by
    unfold UV; exact Finset.measurable_sum _ (fun j _ => (measurable_xV.eval).pow_const 2)
  have hU := BstLean.Part53.measurable_unitF (ι := Fin b)
  have hR := BstLean.Part53.measurable_radF (ι := Fin b)
  let Φ : ℝ → (Fin r → ℝ) → ℝ≥0∞ := fun s h => W (s ^ 2 / (s ^ 2 + ∑ j, h j ^ 2))
  have hΦ : Measurable (fun p : ℝ × (Fin r → ℝ) => Φ p.1 p.2) := by
    simp only [Φ]; apply hW.comp; fun_prop
  let K : (Fin b → ℝ) × (Fin r → ℝ) → ℝ≥0∞ := fun p => Φ (radF53 p.1) p.2 * G (unitF53 p.1)
  have hK : Measurable K := by
    simp only [K]
    exact (hΦ.comp ((hR.comp measurable_fst).prodMk measurable_snd)).mul (hG.comp (hU.comp measurable_fst))
  rw [BstLean.Part56.uniformSphere_lintegral_gauss (b + r) hbr
    (fun x => W (UV x) * G (unitF53 (xV x)))
    ((hW.comp hUV).mul (hG.comp (hU.comp measurable_xV)))]
  have hpt : ∀ g : Fin (b + r) → ℝ, W (UV (unitF53 g)) * G (unitF53 (xV (unitF53 g))) =
      K (xV g, xP g) := by
    intro g
    simp only [K, Φ]
    rw [UV_unit, unit_xV_unit]
  simp_rw [hpt]
  rw [split_mp.lintegral_comp hK, lintegral_prod_symm _ hK.aemeasurable]
  have hin : ∀ h : Fin r → ℝ, ∫⁻ z, K (z, h) ∂stdGauss (Fin b) =
      (∫⁻ z, G (unitF53 z) ∂stdGauss (Fin b)) * ∫⁻ z', Φ (radF53 z') h ∂stdGauss (Fin b) := by
    intro h
    have hF : Measurable (Function.uncurry (fun (u : Fin b → ℝ) (s : ℝ) => G u * Φ s h)) := by
      change Measurable (fun p : (Fin b → ℝ) × ℝ => G p.1 * Φ p.2 h)
      exact (hG.comp measurable_fst).mul (hΦ.comp (measurable_snd.prodMk measurable_const))
    have hpol := BstLean.Part53.gauss_polar_gen (fun (u : Fin b → ℝ) (s : ℝ) => G u * Φ s h) hF
    have hΦh : Measurable (fun z' : Fin b → ℝ => Φ (radF53 z') h) :=
      hΦ.comp (hR.prodMk measurable_const)
    calc ∫⁻ z, K (z, h) ∂stdGauss (Fin b)
        = ∫⁻ z, G (unitF53 z) * Φ (radF53 z) h ∂stdGauss (Fin b) := by
          apply lintegral_congr; intro z; simp only [K]; rw [mul_comm]
      _ = ∫⁻ z, ∫⁻ z', G (unitF53 z) * Φ (radF53 z') h ∂stdGauss (Fin b) ∂stdGauss (Fin b) := hpol
      _ = ∫⁻ z, G (unitF53 z) * ∫⁻ z', Φ (radF53 z') h ∂stdGauss (Fin b) ∂stdGauss (Fin b) := by
          apply lintegral_congr; intro z; rw [lintegral_const_mul _ hΦh]
      _ = _ := lintegral_mul_const _ (hG.comp hU)
  simp_rw [hin]
  have hQ : Measurable (fun h : Fin r → ℝ => ∫⁻ z', Φ (radF53 z') h ∂stdGauss (Fin b)) := by
    have : Measurable (fun p : (Fin b → ℝ) × (Fin r → ℝ) => Φ (radF53 p.1) p.2) :=
      hΦ.comp ((hR.comp measurable_fst).prodMk measurable_snd)
    exact this.lintegral_prod_left'
  rw [lintegral_const_mul _ hQ]

/-- **Block splitting**: `E_σ[W(UV x)·G(xV/‖xV‖)] = E_{σ_b}[G]·E_σ[W(UV x)]`. -/
theorem block_split (hb : 1 ≤ b) (W : ℝ → ℝ≥0∞) (hW : Measurable W)
    (G : (Fin b → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, W (UV x) * G (unitF53 (xV x)) ∂uniformSphere (b + r) =
      (∫⁻ y, G y ∂uniformSphere b) * ∫⁻ x, W (UV x) ∂uniformSphere (b + r) := by
  have hbr : 1 ≤ b + r := by omega
  have h1 := block_key hbr W hW G hG
  have h2 := block_key (r := r) hbr W hW (fun _ => 1) measurable_const
  simp only [mul_one, lintegral_const, measure_univ, one_mul] at h2
  rw [h1, h2, BstLean.Part56.uniformSphere_lintegral_gauss b hb G hG]

lemma unit_xP_unit (g : Fin (b + r) → ℝ) : unitF53 (xP (unitF53 g)) = unitF53 (xP g) := by
  have hs : 0 ≤ Real.sqrt (∑ i, g i ^ 2) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs with h | h
  · have hg : g = 0 := by
      have h0 : ∑ i, g i ^ 2 = 0 := by
        have := Real.sqrt_eq_zero'.mp h.symm
        exact le_antisymm this (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g i))).mp h0 i
        (Finset.mem_univ i)
      simpa using this
    subst hg
    simp [unitF53, xP]
  · unfold unitF53
    rw [xP_smul]
    exact unitF53_smul _ (by positivity) _

lemma UV_unit' (g : Fin (b + r) → ℝ) :
    UV (unitF53 g) = (∑ j, xV g j ^ 2) / (∑ j, xV g j ^ 2 + radF53 (xP g) ^ 2) := by
  have hP : radF53 (xP g) ^ 2 = ∑ j, xP g j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [hP]
  have htot : ∑ i, g i ^ 2 = ∑ j, xV g j ^ 2 + ∑ j, xP g j ^ 2 := sum_split (fun t => t ^ 2) g
  unfold UV unitF53
  rw [xV_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [← htot, div_pow, one_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  ring

private lemma block_keyP (hbr : 1 ≤ b + r) (W : ℝ → ℝ≥0∞) (hW : Measurable W)
    (G : (Fin r → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, W (UV x) * G (unitF53 (xP x)) ∂uniformSphere (b + r) =
      (∫⁻ z, G (unitF53 z) ∂stdGauss (Fin r)) *
        ∫⁻ y, ∫⁻ z', W ((∑ j, y j ^ 2) / (∑ j, y j ^ 2 + radF53 z' ^ 2)) ∂stdGauss (Fin r)
          ∂stdGauss (Fin b) := by
  have hUV : Measurable (UV (b := b) (r := r)) := by
    unfold UV; exact Finset.measurable_sum _ (fun j _ => (measurable_xV.eval).pow_const 2)
  have hU := BstLean.Part53.measurable_unitF (ι := Fin r)
  have hR := BstLean.Part53.measurable_radF (ι := Fin r)
  let Φ : (Fin b → ℝ) → ℝ → ℝ≥0∞ := fun y s => W ((∑ j, y j ^ 2) / (∑ j, y j ^ 2 + s ^ 2))
  have hΦ : Measurable (fun p : (Fin b → ℝ) × ℝ => Φ p.1 p.2) := by
    simp only [Φ]; apply hW.comp; fun_prop
  let K : (Fin b → ℝ) × (Fin r → ℝ) → ℝ≥0∞ := fun p => Φ p.1 (radF53 p.2) * G (unitF53 p.2)
  have hK : Measurable K := by
    simp only [K]
    exact (hΦ.comp (measurable_fst.prodMk (hR.comp measurable_snd))).mul
      (hG.comp (hU.comp measurable_snd))
  rw [BstLean.Part56.uniformSphere_lintegral_gauss (b + r) hbr
    (fun x => W (UV x) * G (unitF53 (xP x)))
    ((hW.comp hUV).mul (hG.comp (hU.comp measurable_xP)))]
  have hpt : ∀ g : Fin (b + r) → ℝ, W (UV (unitF53 g)) * G (unitF53 (xP (unitF53 g))) =
      K (xV g, xP g) := by
    intro g
    simp only [K, Φ]
    rw [UV_unit', unit_xP_unit]
  simp_rw [hpt]
  rw [split_mp.lintegral_comp hK, lintegral_prod _ hK.aemeasurable]
  have hin : ∀ y : Fin b → ℝ, ∫⁻ z, K (y, z) ∂stdGauss (Fin r) =
      (∫⁻ z, G (unitF53 z) ∂stdGauss (Fin r)) * ∫⁻ z', Φ y (radF53 z') ∂stdGauss (Fin r) := by
    intro y
    have hF : Measurable (Function.uncurry (fun (u : Fin r → ℝ) (s : ℝ) => G u * Φ y s)) := by
      change Measurable (fun p : (Fin r → ℝ) × ℝ => G p.1 * Φ y p.2)
      refine (hG.comp measurable_fst).mul ?_
      simp only [Φ]
      exact hW.comp (by fun_prop)
    have hpol := BstLean.Part53.gauss_polar_gen (fun (u : Fin r → ℝ) (s : ℝ) => G u * Φ y s) hF
    have hΦh : Measurable (fun z' : Fin r → ℝ => Φ y (radF53 z')) := by
      simp only [Φ]
      exact hW.comp (by fun_prop)
    calc ∫⁻ z, K (y, z) ∂stdGauss (Fin r)
        = ∫⁻ z, G (unitF53 z) * Φ y (radF53 z) ∂stdGauss (Fin r) := by
          apply lintegral_congr; intro z; simp only [K]; rw [mul_comm]
      _ = ∫⁻ z, ∫⁻ z', G (unitF53 z) * Φ y (radF53 z') ∂stdGauss (Fin r) ∂stdGauss (Fin r) := hpol
      _ = ∫⁻ z, G (unitF53 z) * ∫⁻ z', Φ y (radF53 z') ∂stdGauss (Fin r) ∂stdGauss (Fin r) := by
          apply lintegral_congr; intro z; rw [lintegral_const_mul _ hΦh]
      _ = _ := lintegral_mul_const _ (hG.comp hU)
  simp_rw [hin]
  have hQ : Measurable (fun y : Fin b → ℝ => ∫⁻ z', Φ y (radF53 z') ∂stdGauss (Fin r)) := by
    have : Measurable (fun p : (Fin b → ℝ) × (Fin r → ℝ) => Φ p.1 (radF53 p.2)) := by
      simp only [Φ]
      exact hW.comp (by fun_prop)
    exact this.lintegral_prod_right'
  rw [lintegral_const_mul _ hQ]

/-- **Block splitting, second block**: `E_σ[W(UV x)·G(xP/‖xP‖)] = E_{σ_r}[G]·E_σ[W(UV x)]`. -/
theorem block_splitP (hr : 1 ≤ r) (W : ℝ → ℝ≥0∞) (hW : Measurable W)
    (G : (Fin r → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, W (UV x) * G (unitF53 (xP x)) ∂uniformSphere (b + r) =
      (∫⁻ y, G y ∂uniformSphere r) * ∫⁻ x, W (UV x) ∂uniformSphere (b + r) := by
  have hbr : 1 ≤ b + r := by omega
  have h1 := block_keyP (b := b) hbr W hW G hG
  have h2 := block_keyP (b := b) hbr W hW (fun _ => 1) measurable_const
  simp only [mul_one, lintegral_const, measure_univ, one_mul] at h2
  rw [h1, h2, BstLean.Part56.uniformSphere_lintegral_gauss r hr G hG]

end BstLean.Part72
