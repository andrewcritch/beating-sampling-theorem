import BstLean.Part71Defs
import BstLean.Part71Feature
import BstLean.Part59Floor_Moments

/-!
# Part 71: the chi-square transfers P1χ, P2χ and the coordinate mean

`ChiLaw n μ K` gives `E_μ f ≤ √(1+K)·√(E_σ f²)` for continuous `f` (Lemma CS, Cauchy–Schwarz).
From it:

* `chi_dev`: `E_μ δ°^{2i} ≤ √(1+K)·√((16i−1)!!)·d^{2i}/n^{2i}` (P1χ; Lemmas U and S at `q = 4i`);
* `chi_coord_mean`: `Σ_i (E_μ x_i)² ≤ (1+K)·cG 2/n` (omQT-cx §4);
* `chi_feature`: `E_μ (a·φ)² ≤ √(1+K)·√C·(d+1)/n·‖a‖²` for `a₀ = 0`, given Lemma SH
  `SphereFourth71 d C` (P2χ).
* `upLaw_chiLaw`: `UpLaw n μ K → ChiLaw n μ (K − 1)`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part71

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM phiSq varU)
open BstLean.Part53 (c0 p4 nsq cG LemmaU53 LemmaS53)
open BstLean.Part53.FloorEnergy (sphere_cont_integrable sphere_var_expansion)

variable {n d : ℕ}

lemma unif_sph (hn : 1 ≤ n) : SphLaw n (uniformSphere n) :=
  ⟨BstLean.Part29.uniformSphere_isProbability n hn, BstLean.Part29.uniformSphere_ae_sphere n⟩

/-- A `ChiLaw` distribution lives on the sphere. -/
lemma chiLaw_sph {μ : Measure (Fin n → ℝ)} {K : ℝ} (h : ChiLaw n μ K) : SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := h
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)

/-- **Lemma CS** (chi-square transfer): `E_μ f ≤ √(1+K)·√(E_σ f²)` for continuous `f`. -/
lemma chi_cs (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : ChiLaw n μ K)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
    ∫ x, f x ∂μ ≤ Real.sqrt (1 + K) * Real.sqrt (∫ x, f x ^ 2 ∂uniformSphere n) := by
  obtain ⟨hp, ρ, hρm, hρ0, hμρ, hρi, hρb⟩ := hμ
  have hσ := unif_sph hn
  have hf2 : Integrable (fun x => f x ^ 2) (uniformSphere n) := sphere_cont_integrable hσ (hf.pow 2)
  have hw : (∫ x, f x ∂μ) = ∫ x, ρ x * f x ∂uniformSphere n := by
    rw [hμρ, integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal (by simp)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [ENNReal.toReal_ofReal (hρ0 x)]
  have hρL : MemLp ρ (ENNReal.ofReal 2) (uniformSphere n) := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hρm.aestronglyMeasurable).mpr hρi
  have hfL : MemLp (fun x => |f x|) (ENNReal.ofReal 2) (uniformSphere n) := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    refine (memLp_two_iff_integrable_sq hf.abs.aestronglyMeasurable).mpr ?_
    simpa only [sq_abs] using hf2
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x => hρ0 x)) (Filter.Eventually.of_forall (fun x => abs_nonneg (f x)))
    hρL hfL
  have e1 : (∫ x, ρ x ^ (2 : ℝ) ∂uniformSphere n) ^ (1 / (2 : ℝ)) =
      Real.sqrt (∫ x, ρ x ^ 2 ∂uniformSphere n) := by
    rw [Real.sqrt_eq_rpow]; congr 1; apply integral_congr_ae
    filter_upwards [] with x; exact Real.rpow_two (ρ x)
  have e2 : (∫ x, |f x| ^ (2 : ℝ) ∂uniformSphere n) ^ (1 / (2 : ℝ)) =
      Real.sqrt (∫ x, f x ^ 2 ∂uniformSphere n) := by
    rw [Real.sqrt_eq_rpow]; congr 1; apply integral_congr_ae
    filter_upwards [] with x; simp [sq_abs]
  rw [e1, e2] at hcs
  have hint : Integrable (fun x => ρ x * |f x|) (uniformSphere n) := by
    refine ((hρi.add hf2).div_const 2).mono' (hρm.mul hf.measurable.abs).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 x) (abs_nonneg _))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (ρ x - |f x|), sq_abs (f x)]
  have hint' : Integrable (fun x => ρ x * f x) (uniformSphere n) :=
    hint.mono' (hρm.mul hf.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x)]))
  have hle : (∫ x, ρ x * f x ∂uniformSphere n) ≤ ∫ x, ρ x * |f x| ∂uniformSphere n :=
    integral_mono hint' hint (fun x => mul_le_mul_of_nonneg_left (le_abs_self _) (hρ0 x))
  rw [hw]
  refine hle.trans (hcs.trans ?_)
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hρb) (Real.sqrt_nonneg _)

private lemma continuous_feature_sq : Continuous (fun x : Fin n → ℝ => phiSq d x) := by
  unfold phiSq
  apply continuous_finsetSum
  intro p hp
  have h : Continuous (fun x : Fin n → ℝ => phiM x p) :=
    continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)
  exact h.pow 2

private lemma continuous_p4 : Continuous (p4 (n := n)) := by
  unfold p4
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 4)

/-- **P1χ** (trace moment): `E_μ δ°^{2i} ≤ √(1+K)·√((16i−1)!!)·d^{2i}/n^{2i}`. -/
lemma chi_dev (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : ChiLaw n μ K)
    (hU : LemmaU53 d) (hS : LemmaS53) (i : ℕ) (hi : 1 ≤ i) :
    (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤
      Real.sqrt (1 + K) * Real.sqrt ((16 * i - 1).doubleFactorial : ℝ) * (d : ℝ) ^ (2 * i) /
        (n : ℝ) ^ (2 * i) := by
  have hf : Continuous (fun x : Fin n → ℝ => (phiSq d x - c0 d) ^ (2 * i)) :=
    (continuous_feature_sq.sub continuous_const).pow _
  have hσ := unif_sph hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set X : ℝ := ((16 * i - 1).doubleFactorial : ℝ)
  set r : ℝ := (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i)
  have hr : 0 ≤ r := by positivity
  have hdev : (∫ x, ((phiSq d x - c0 d) ^ (2 * i)) ^ 2 ∂uniformSphere n) ≤ r ^ 2 * X := by
    have hp4 : (∫ x, p4 x ^ (4 * i) ∂uniformSphere n) ≤ X / (n : ℝ) ^ (4 * i) := by
      have hs := hS n hn (4 * i) (by omega)
      have hdf : 4 * (4 * i) - 1 = 16 * i - 1 := by omega
      rw [hdf] at hs
      exact hs
    have h1 : (∫ x, ((phiSq d x - c0 d) ^ (2 * i)) ^ 2 ∂uniformSphere n) ≤
        (d : ℝ) ^ (4 * i) * (∫ x, p4 x ^ (4 * i) ∂uniformSphere n) := by
      rw [← integral_const_mul]
      apply integral_mono_ae (sphere_cont_integrable hσ (hf.pow 2))
        (sphere_cont_integrable hσ (continuous_const.mul (continuous_p4.pow _)))
      filter_upwards [hσ.sphere] with x hx
      have hb := hU n x hx
      calc
        _ = (phiSq d x - c0 d) ^ (4 * i) := by
          simp only [Pi.pow_apply]; rw [← pow_mul]; ring_nf
        _ ≤ ((d : ℝ) * p4 x) ^ (4 * i) := pow_le_pow_left₀ hb.1 hb.2 _
        _ = _ := mul_pow _ _ _
    calc
      _ ≤ _ := h1
      _ ≤ (d : ℝ) ^ (4 * i) * (X / (n : ℝ) ^ (4 * i)) :=
        mul_le_mul_of_nonneg_left hp4 (by positivity)
      _ = r ^ 2 * X := by
        simp only [r, div_pow, ← pow_mul]
        rw [show 2 * i * 2 = 4 * i by ring]
        ring
  calc
    _ ≤ Real.sqrt (1 + K) * Real.sqrt (∫ x, ((phiSq d x - c0 d) ^ (2 * i)) ^ 2 ∂uniformSphere n) :=
      chi_cs hn hμ _ hf
    _ ≤ Real.sqrt (1 + K) * Real.sqrt (r ^ 2 * X) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdev) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
      simp only [r]
      ring

/-- **P2χ** (feature operator), from Lemma SH: for `a₀ = 0`,
`E_μ (a·φ)² ≤ √(1+K)·√C·((d+1)/n)·‖a‖²`. -/
lemma chi_feature (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K C : ℝ} (hμ : ChiLaw n μ K)
    (hSH : SphereFourth71 d C) (a : Mono n d → ℝ) (ha : a default = 0) :
    ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂μ ≤
      Real.sqrt (1 + K) * Real.sqrt C * (((d : ℝ) + 1) / n * nsq a) := by
  have hφ : Continuous (fun x : Fin n → ℝ => ∑ p, a p * phiM x p) :=
    continuous_finsetSum _ fun p _ =>
      (continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)).const_mul (a p)
  have hσ := unif_sph hn
  set E2 := ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂uniformSphere n
  have hE2 : 0 ≤ E2 := integral_nonneg (fun _ => sq_nonneg _)
  have h4 := hSH n hn a
  have hG := BstLean.Part71.Feat71.featureBound d n hn a ha
  calc
    _ ≤ Real.sqrt (1 + K) * Real.sqrt (∫ x, ((∑ p, a p * phiM x p) ^ 2) ^ 2 ∂uniformSphere n) :=
      chi_cs hn hμ _ (hφ.pow 2)
    _ ≤ Real.sqrt (1 + K) * Real.sqrt (C * E2 ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_sqrt
      simpa only [← pow_mul] using h4
    _ = Real.sqrt (1 + K) * Real.sqrt C * E2 := by
      by_cases hC : 0 ≤ C
      · rw [Real.sqrt_mul hC, Real.sqrt_sq hE2]; ring
      · push Not at hC
        have h1 : C * E2 ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (sq_nonneg _)
        rw [Real.sqrt_eq_zero'.mpr h1, Real.sqrt_eq_zero'.mpr hC.le]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hG (by positivity)

private def linearFeature (hd : 1 ≤ d) (a : Fin n) : Mono n d :=
  ⟨⟨1, by omega⟩, Sym.oneEquiv a⟩

private lemma linearFeature_eval (hd : 1 ≤ d) (a : Fin n) (x : Fin n → ℝ) :
    phiM x (linearFeature hd a) = x a := by
  change (({a} : Multiset (Fin n)).map x).prod = x a
  simp

private lemma linearFeature_injective (hd : 1 ≤ d) :
    Function.Injective (linearFeature (n := n) hd) := by
  classical
  intro a b h
  have he := congrArg (phiM (fun i => if i = a then (1 : ℝ) else 0)) h
  rw [linearFeature_eval, linearFeature_eval] at he
  by_contra hab
  have hba : b ≠ a := Ne.symm hab
  simp [hba] at he

private lemma sum_on_embedding {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (H : κ → ℝ)
    (h0 : ∀ b, b ∉ Finset.univ.image f → H b = 0) :
    (∑ b, H b) = ∑ a, H (f a) := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image f, H b :=
      (Finset.sum_subset (Finset.subset_univ _) (fun b _ hb => h0 b hb)).symm
    _ = _ := Finset.sum_image (fun a _ b _ h => hf h)

/-- **The coordinate mean** under a chi-square bound: `Σ_i (E_μ x_i)² ≤ (1+K)·cG 2/n`. -/
lemma chi_coord_mean (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : ChiLaw n μ K) :
    (∑ i : Fin n, (∫ x, x i ∂μ) ^ 2) ≤ (1 + K) * cG 2 / (n : ℝ) := by
  classical
  let β : Fin n → ℝ := fun i => ∫ x, x i ∂μ
  let a : Mono n 2 → ℝ := Function.extend (linearFeature (d := 2) (by decide)) β (fun _ => 0)
  let q : ℝ := ∑ i, β i ^ 2
  let ℓ : (Fin n → ℝ) → ℝ := fun x => ∑ i, β i * x i
  have hinj := linearFeature_injective (n := n) (d := 2) (by decide)
  have hae (i : Fin n) : a (linearFeature (d := 2) (by decide) i) = β i :=
    hinj.extend_apply β (fun _ => 0) i
  have ha0 (p : Mono n 2) (hp : p ∉ Finset.univ.image (linearFeature (d := 2) (by decide))) :
      a p = 0 := by
    apply Function.extend_apply'
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hp
  have had : a default = 0 := by
    apply ha0
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    have he := congrArg (fun p : Mono n 2 => p.1.val) hi
    change 1 = 0 at he
    omega
  have haq : nsq a = q := by
    unfold nsq q
    rw [sum_on_embedding (linearFeature (d := 2) (by decide)) hinj (fun p => a p ^ 2)
      (fun p hp => by rw [ha0 p hp]; norm_num)]
    simp only [hae]
  have hal (x : Fin n → ℝ) : (∑ p, a p * phiM x p) = ℓ x := by
    rw [sum_on_embedding (linearFeature (d := 2) (by decide)) hinj (fun p => a p * phiM x p)
      (fun p hp => by rw [ha0 p hp]; simp)]
    simp only [hae, linearFeature_eval, ℓ]
  have hℓ : Continuous ℓ :=
    continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))
  have hsph := chiLaw_sph hμ
  have hcoord (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i) μ :=
    sphere_cont_integrable hsph (continuous_apply i)
  have hmean : (∫ x, ℓ x ∂μ) = q := by
    dsimp only [ℓ]
    rw [integral_finsetSum _ (fun i _ => (hcoord i).const_mul (β i))]
    simp only [integral_const_mul, β, q, pow_two]
  have hg := BstLean.Part53.lemmaG53 2 (by decide) n hn a had
  simp_rw [hal] at hg
  rw [haq] at hg
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcs := chi_cs hn hμ ℓ hℓ
  rw [hmean] at hcs
  -- q ≤ √(1+K) √(cG2/n q), so q² ≤ (1+K) (cG2/n) q
  have hK : 0 ≤ 1 + K := by
    obtain ⟨-, ρ, -, -, -, -, hρb⟩ := hμ
    have := integral_nonneg (f := fun x => ρ x ^ 2) (μ := uniformSphere n) (fun x => sq_nonneg (ρ x))
    linarith
  have h2 : q ^ 2 ≤ (1 + K) * (cG 2 / (n : ℝ) * q) := by
    have hq' : q ≤ Real.sqrt (1 + K) * Real.sqrt (cG 2 / (n : ℝ) * q) :=
      hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _))
    have hs : (Real.sqrt (1 + K) * Real.sqrt (cG 2 / (n : ℝ) * q)) ^ 2 =
        (1 + K) * (cG 2 / (n : ℝ) * q) := by
      rw [mul_pow, Real.sq_sqrt hK, Real.sq_sqrt (by unfold cG; positivity)]
    rw [← hs]
    exact pow_le_pow_left₀ hq hq' 2
  change q ≤ _
  by_cases hz : q = 0
  · rw [hz]; unfold cG; positivity
  · have hp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    have : q * q ≤ ((1 + K) * cG 2 / (n : ℝ)) * q := by
      calc q * q = q ^ 2 := by ring
        _ ≤ _ := h2
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hp

/-- `UpLaw n μ K` implies `ChiLaw n μ (K − 1)`: `E_σ ρ² ≤ K·E_σ ρ = K`. -/
lemma upLaw_chiLaw (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K : ℝ}
    (h : BstLean.Part59.UpLaw n μ K) : ChiLaw n μ (K - 1) := by
  obtain ⟨hp, ρ, hρm, hρ0, hμρ, hρb⟩ := h
  have hσ := unif_sph hn
  let := hσ.prob
  have hK : ∀ᵐ x ∂uniformSphere n, ρ x ≤ max K 0 := by
    filter_upwards [hσ.sphere] with x hx
    exact (hρb x hx).trans (le_max_left _ _)
  -- `∫ ρ dσ = 1`
  have hint1 : (∫⁻ x, ENNReal.ofReal (ρ x) ∂uniformSphere n) = 1 := by
    have := hp.measure_univ
    rw [hμρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  have hρint : Integrable ρ (uniformSphere n) := by
    refine Integrable.of_bound hρm.aestronglyMeasurable (max K 0) ?_
    filter_upwards [hK] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]; exact hx
  have hρ1 : ∫ x, ρ x ∂uniformSphere n = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hρ0)
      hρm.aestronglyMeasurable, hint1]
    simp
  have hρ2 : Integrable (fun x => ρ x ^ 2) (uniformSphere n) := by
    refine Integrable.of_bound (hρm.pow_const 2).aestronglyMeasurable (max K 0 ^ 2) ?_
    filter_upwards [hK] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hρ0 x) hx 2
  refine ⟨hp, ρ, hρm, hρ0, hμρ, hρ2, ?_⟩
  have hle : (∫ x, ρ x ^ 2 ∂uniformSphere n) ≤ ∫ x, max K 0 * ρ x ∂uniformSphere n := by
    apply integral_mono_ae hρ2 (hρint.const_mul _)
    filter_upwards [hK] with x hx
    rw [sq]; exact mul_le_mul_of_nonneg_right hx (hρ0 x)
  rw [integral_const_mul, hρ1, mul_one] at hle
  by_cases hK0 : 0 ≤ K
  · rw [max_eq_left hK0] at hle; linarith
  · push Not at hK0
    exfalso
    -- density `≤ K < 0` contradicts `∫ ρ = 1`
    have : ∫ x, ρ x ∂uniformSphere n ≤ 0 := by
      have h0 : ∀ᵐ x ∂uniformSphere n, ρ x ≤ 0 := by
        filter_upwards [hσ.sphere] with x hx; exact (hρb x hx).trans hK0.le
      calc _ ≤ ∫ _x, (0 : ℝ) ∂uniformSphere n := integral_mono_ae hρint (integrable_const _) h0
        _ = 0 := by simp
    linarith

end BstLean.Part71
