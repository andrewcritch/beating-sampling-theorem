import BstLean.Part157Repl
import BstLean.Part138Gauss

/-!
# Part 157, item 4: the World root replacement is PROVED for the Hellinger radius

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-02-world.tex`, "The Hellinger moment and the replacement event" and
Lemma `t7:p02:replacement` (second conclusion: `|√q_W − √q'_W| ≤ H̄_W` for every indicator).

* `hu2 n l s τ₀`: the squared Hellinger distance `H_u²` of `N(ĉ, (s/l)²·I_n)` and
  `N(ĉ, τ₀²·I_n)` (`hellG` of Part 138) when `l > 0`, `s > 0`, `τ₀ > 0`, and `2` otherwise.
* `HbarW2 D c = E_u H_u²`, `HbarW D c = √(HbarW2 D c)`: the World replacement radius `H̄_W`
  of the paper, a concrete function of the retained data.
* `root_set_hell`: `(√P(A) − √Q(A))² ≤ 2 − 2∫√(dP/dQ) dQ` for every measurable set `A`.
* `pt_root`: the bound for one input `u`. `mix_root`: the reverse triangle inequality in `L²(u)`.
* **`replw_hellinger`**: for EVERY retained value `c` and every measurable set `T`:
  `|√(ν(T)) − √(ν'(T))| ≤ HbarW D c`. No hypothesis on `c`.
* `replw_test_of_Hbar`: `REPLW_test_hyp D h_W (H ∩ {HbarW D ≤ h_W} ∩ E₁)` holds.
* `measurable_HbarW`: the radius is measurable in the retained data.
* `classifier_networks_conditional_hell`: the conditional theorem without a World replacement
  hypothesis.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part138 (cs_sq densN rootN hellG hellG_le_two hellG_nonneg integral_scale rootN_sq
  measurable_rootN rootN_nonneg integrable_densN integral_densN aff_densN)
open BstLean.Part132 (sphPt_smul)
open BstLean.Part156

/-! ## Two abstract inequalities -/

section abstract

variable {α : Type*} [MeasurableSpace α]

/-- **The Hellinger bound for a set, in root form.** `ρ` a probability measure, `a ≥ 0` the square
root of a probability density (`∫ a² dρ = 1`), `A` a measurable set:
`(√(∫_A a² dρ) − √(ρ(A)))² ≤ 2 − 2∫ a dρ`. -/
theorem root_set_hell (ρ : Measure α) [IsProbabilityMeasure ρ] {a : α → ℝ} (ha : Measurable a)
    (ha0 : ∀ x, 0 ≤ a x) (ia : Integrable (fun x => a x ^ 2) ρ) (h1 : ∫ x, a x ^ 2 ∂ρ = 1)
    {A : Set α} (hA : MeasurableSet A) :
    (√(∫ x, A.indicator 1 x * a x ^ 2 ∂ρ) - √(ρ.real A)) ^ 2 ≤ 2 - 2 * ∫ x, a x ∂ρ := by
  set I : α → ℝ := A.indicator 1 with hI
  have mI : Measurable I := measurable_one.indicator hA
  have I01 : ∀ x, I x = 0 ∨ I x = 1 := by
    intro x
    by_cases h : x ∈ A
    · right; simp [hI, h]
    · left; simp [hI, h]
  have I0 : ∀ x, 0 ≤ I x := fun x => by rcases I01 x with h | h <;> simp [h]
  have I1 : ∀ x, I x ≤ 1 := fun x => by rcases I01 x with h | h <;> simp [h]
  have Isq : ∀ x, I x ^ 2 = I x := fun x => by rcases I01 x with h | h <;> simp [h]
  have iI : Integrable I ρ := (integrable_const (1 : ℝ)).indicator hA
  have hIaI : ∀ x, I x * a x * I x = I x * a x := fun x => by
    calc I x * a x * I x = I x ^ 2 * a x := by ring
      _ = I x * a x := by rw [Isq]
  have hY : ρ.real A = ∫ x, I x ∂ρ := (integral_indicator_one hA).symm
  -- integrability
  have iAa : Integrable (fun x => a x) ρ := by
    refine ((integrable_const (1 : ℝ)).add ia).mono' ha.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ha0 x)]
    change a x ≤ 1 + a x ^ 2
    nlinarith [sq_nonneg (a x - 1)]
  have iIa2 : Integrable (fun x => I x * a x ^ 2) ρ := by
    refine ia.mono' (mI.mul (ha.pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (I0 x) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (I1 x)
  have iIa : Integrable (fun x => I x * a x) ρ := by
    refine iAa.mono' (mI.mul ha).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (I0 x) (ha0 x))]
    exact mul_le_of_le_one_left (ha0 x) (I1 x)
  set X := ∫ x, I x * a x ^ 2 ∂ρ with hX
  set Y := ∫ x, I x ∂ρ with hYdef
  have hX0 : 0 ≤ X := integral_nonneg fun x => mul_nonneg (I0 x) (sq_nonneg _)
  have hY0 : 0 ≤ Y := integral_nonneg I0
  -- Cauchy–Schwarz
  have hcs := cs_sq ρ (f := fun x => I x * a x) (g := I)
    (by
      have e : (fun x => (I x * a x) ^ 2) = fun x => I x * a x ^ 2 := by
        funext x; rw [mul_pow, Isq]
      rw [e]; exact iIa2)
    (by simp_rw [Isq]; exact iI)
    (by simp_rw [hIaI]; exact iIa)
  have e1 : (fun x => I x * a x * I x) = fun x => I x * a x := funext hIaI
  have e2 : (fun x => (I x * a x) ^ 2) = fun x => I x * a x ^ 2 := by
    funext x; rw [mul_pow, Isq]
  simp_rw [Isq] at hcs
  rw [e1, e2] at hcs
  have hZ0 : 0 ≤ ∫ x, I x * a x ∂ρ := integral_nonneg fun x => mul_nonneg (I0 x) (ha0 x)
  have hZ : ∫ x, I x * a x ∂ρ ≤ √X * √Y := by
    rw [← Real.sqrt_mul hX0]
    exact Real.le_sqrt_of_sq_le hcs
  -- the pointwise bound
  have hpt : ∫ x, I x * a x ^ 2 ∂ρ + ∫ x, I x ∂ρ - 2 * ∫ x, I x * a x ∂ρ ≤
      2 - 2 * ∫ x, a x ∂ρ := by
    have i3 : Integrable (fun x => I x * a x ^ 2 + I x - 2 * (I x * a x)) ρ :=
      (iIa2.add iI).sub (iIa.const_mul 2)
    have i4 : Integrable (fun x => a x ^ 2 + 1 - 2 * a x) ρ :=
      (ia.add (integrable_const 1)).sub (iAa.const_mul 2)
    have hm := integral_mono i3 i4 (fun x => by
      change I x * a x ^ 2 + I x - 2 * (I x * a x) ≤ a x ^ 2 + 1 - 2 * a x
      have h3 : I x * a x ^ 2 + I x - 2 * (I x * a x) = I x * (a x - 1) ^ 2 := by ring
      have h4 : a x ^ 2 + 1 - 2 * a x = (a x - 1) ^ 2 := by ring
      rw [h3, h4]
      exact mul_le_of_le_one_left (sq_nonneg _) (I1 x))
    have s1 : ∫ x, I x * a x ^ 2 + I x - 2 * (I x * a x) ∂ρ =
        ∫ x, I x * a x ^ 2 ∂ρ + ∫ x, I x ∂ρ - 2 * ∫ x, I x * a x ∂ρ := by
      rw [integral_sub (f := fun x => I x * a x ^ 2 + I x) (g := fun x => 2 * (I x * a x))
        (iIa2.add iI) (iIa.const_mul 2),
        integral_add (f := fun x => I x * a x ^ 2) (g := fun x => I x) iIa2 iI,
        integral_const_mul]
    have s2 : ∫ x, a x ^ 2 + 1 - 2 * a x ∂ρ = 2 - 2 * ∫ x, a x ∂ρ := by
      rw [integral_sub (f := fun x => a x ^ 2 + 1) (g := fun x => 2 * a x)
        (ia.add (integrable_const 1)) (iAa.const_mul 2),
        integral_add (f := fun x => a x ^ 2) (g := fun _ => (1 : ℝ)) ia (integrable_const 1),
        integral_const_mul, h1]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      norm_num
    rw [s1, s2] at hm
    exact hm
  rw [hY]
  have hsq : (√X - √Y) ^ 2 = X + Y - 2 * (√X * √Y) := by
    have e : (√X - √Y) ^ 2 = √X ^ 2 + √Y ^ 2 - 2 * (√X * √Y) := by ring
    rw [e, Real.sq_sqrt hX0, Real.sq_sqrt hY0]
  rw [hsq]
  linarith

/-- **The reverse triangle inequality in `L²` of a probability space.** `0 ≤ X(u) ≤ 1`
measurable, `Y ≥ 0`, and `(√X(u) − √Y)² ≤ K(u)` with `K` integrable:
`(√(E X) − √Y)² ≤ E K`. -/
theorem mix_root (μ : Measure α) [IsProbabilityMeasure μ] {X : α → ℝ} (hX : Measurable X)
    (hX0 : ∀ u, 0 ≤ X u) (hX1 : ∀ u, X u ≤ 1) {Y : ℝ} (hY0 : 0 ≤ Y) {K : α → ℝ}
    (hK : Integrable K μ) (h : ∀ u, (√(X u) - √Y) ^ 2 ≤ K u) :
    (√(∫ u, X u ∂μ) - √Y) ^ 2 ≤ ∫ u, K u ∂μ := by
  have iX : Integrable X μ :=
    Integrable.of_bound hX.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 u)]; exact hX1 u)
  have hf1 : ∀ u, √(X u) ≤ 1 := fun u => by
    have := Real.sqrt_le_sqrt (hX1 u)
    rwa [Real.sqrt_one] at this
  have iF : Integrable (fun u => √(X u)) μ :=
    Integrable.of_bound hX.sqrt.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; exact hf1 u)
  have hsq : ∀ u, √(X u) ^ 2 = X u := fun u => Real.sq_sqrt (hX0 u)
  have hcs := cs_sq μ (f := fun u => √(X u)) (g := fun _ => (1 : ℝ))
    (by simp_rw [hsq]; exact iX) (integrable_const _) (by simpa using iF)
  simp only [hsq, mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul] at hcs
  have hEX0 : 0 ≤ ∫ u, X u ∂μ := integral_nonneg hX0
  have hF : ∫ u, √(X u) ∂μ ≤ √(∫ u, X u ∂μ) := Real.le_sqrt_of_sq_le hcs
  have i1 : Integrable (fun u => (√(X u) - √Y) ^ 2) μ := by
    have e : (fun u => (√(X u) - √Y) ^ 2) = fun u => X u - 2 * √Y * √(X u) + √Y ^ 2 := by
      funext u
      have e' : (√(X u) - √Y) ^ 2 = √(X u) ^ 2 - 2 * √Y * √(X u) + √Y ^ 2 := by ring
      rw [e', hsq u]
    rw [e]
    exact (iX.sub (iF.const_mul _)).add (integrable_const _)
  have hm := integral_mono i1 hK h
  have e2 : ∫ u, (√(X u) - √Y) ^ 2 ∂μ =
      ∫ u, X u ∂μ - 2 * √Y * ∫ u, √(X u) ∂μ + Y := by
    have e : (fun u => (√(X u) - √Y) ^ 2) = fun u => X u - 2 * √Y * √(X u) + √Y ^ 2 := by
      funext u
      have e' : (√(X u) - √Y) ^ 2 = √(X u) ^ 2 - 2 * √Y * √(X u) + √Y ^ 2 := by ring
      rw [e', hsq u]
    rw [e, integral_add (f := fun u => X u - 2 * √Y * √(X u)) (g := fun _ => √Y ^ 2)
        (iX.sub (iF.const_mul _)) (integrable_const _),
      integral_sub (f := fun u => X u) (g := fun u => 2 * √Y * √(X u)) iX (iF.const_mul _),
      integral_const_mul]
    simp [Real.sq_sqrt hY0]
  rw [e2] at hm
  have h3 : (√(∫ u, X u ∂μ) - √Y) ^ 2 =
      ∫ u, X u ∂μ - 2 * √Y * √(∫ u, X u ∂μ) + Y := by
    have e' : (√(∫ u, X u ∂μ) - √Y) ^ 2 =
        √(∫ u, X u ∂μ) ^ 2 - 2 * √Y * √(∫ u, X u ∂μ) + √Y ^ 2 := by ring
    rw [e', Real.sq_sqrt hEX0, Real.sq_sqrt hY0]
  rw [h3]
  have : 2 * √Y * ∫ u, √(X u) ∂μ ≤ 2 * √Y * √(∫ u, X u ∂μ) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  linarith

end abstract

/-! ## One input -/

variable {n : ℕ}

/-- **The root bound for one input.** For `l > 0`, `s > 0`, `τ₀ > 0` and a measurable set `T`:
`(√Pr(sphPt (l·c + s·γ) ∈ T) − √Pr(sphPt (c + τ₀·ξ) ∈ T))² ≤ hellG n (s/l) τ₀`, the squared
Hellinger distance of `N(c, (s/l)²·I_n)` and `N(c, τ₀²·I_n)`. -/
theorem pt_root (c : Fin n → ℝ) {l s τ₀ : ℝ} (hl : 0 < l) (hs : 0 < s) (hτ₀ : 0 < τ₀)
    {T : Set (Fin n → ℝ)} (hT : MeasurableSet T) :
    (√((stdGauss (Fin n)).real {γ | sphPt (l • c + s • γ) ∈ T}) -
      √((stdGauss (Fin n)).real {ξ | sphPt (c + τ₀ • ξ) ∈ T})) ^ 2 ≤ hellG n (s / l) τ₀ := by
  set κ := s / l / τ₀ with hκ
  have hκ0 : 0 < κ := by positivity
  set A : Set (Fin n → ℝ) := {ξ | sphPt (c + τ₀ • ξ) ∈ T} with hA
  have mG : Measurable (fun ξ : Fin n → ℝ => sphPt (c + τ₀ • ξ)) :=
    measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ₀))
  have mA : MeasurableSet A := mG hT
  have e1 : {γ : Fin n → ℝ | sphPt (l • c + s • γ) ∈ T} = (fun γ : Fin n → ℝ => κ • γ) ⁻¹' A := by
    ext γ
    change sphPt (l • c + s • γ) ∈ T ↔ sphPt (c + τ₀ • (κ • γ)) ∈ T
    have h1 : l • c + s • γ = l • (c + τ₀ • (κ • γ)) := by
      rw [smul_add, smul_smul, smul_smul]
      congr 2
      rw [hκ]
      field_simp
    rw [h1, sphPt_smul hl]
  have mI : Measurable (A.indicator (1 : (Fin n → ℝ) → ℝ)) := measurable_one.indicator mA
  have e2 : (stdGauss (Fin n)).real ((fun γ : Fin n → ℝ => κ • γ) ⁻¹' A) =
      ∫ x, A.indicator 1 x * rootN κ x ^ 2 ∂stdGauss (Fin n) := by
    rw [← integral_indicator_one (mA.preimage (measurable_const_smul κ))]
    have h2 := integral_scale (ι := Fin n) hκ0 (g := A.indicator 1) mI
    simp_rw [rootN_sq hκ0]
    rw [← h2]
    rfl
  have h := root_set_hell (stdGauss (Fin n)) (a := rootN κ) (measurable_rootN κ)
    (rootN_nonneg κ) (by simp_rw [rootN_sq hκ0]; exact integrable_densN hκ0)
    (by simp_rw [rootN_sq hκ0]; exact integral_densN hκ0) mA
  rw [aff_densN hκ0, Fintype.card_fin] at h
  rw [e1, e2]
  have e3 : 2 * (s / l) * τ₀ / ((s / l) ^ 2 + τ₀ ^ 2) = 2 * κ / (1 + κ ^ 2) := by
    rw [hκ]
    field_simp
    ring
  unfold hellG
  rw [e3]
  exact h

/-- **`H_u²`**: the squared Hellinger distance of `N(ĉ, (s/l)²·I_n)` and `N(ĉ, τ₀²·I_n)` for
`l > 0`, `s > 0`, `τ₀ > 0`, and the upper value `2` otherwise (the convention of the paper for
degenerate inputs). -/
noncomputable def hu2 (n : ℕ) (l s τ₀ : ℝ) : ℝ :=
  if 0 < l ∧ 0 < s ∧ 0 < τ₀ then hellG n (s / l) τ₀ else 2

lemma hu2_nonneg (n : ℕ) (l s τ₀ : ℝ) : 0 ≤ hu2 n l s τ₀ := by
  unfold hu2
  split_ifs
  · exact hellG_nonneg _ _ _
  · norm_num

lemma hu2_le_two (n : ℕ) (l s τ₀ : ℝ) : hu2 n l s τ₀ ≤ 2 := by
  unfold hu2
  split_ifs
  · exact hellG_le_two _ _ _
  · exact le_rfl

lemma measurable_hu2 (n : ℕ) : Measurable (fun p : ℝ × ℝ × ℝ => hu2 n p.1 p.2.1 p.2.2) := by
  unfold hu2
  have m1 : Measurable (fun p : ℝ × ℝ × ℝ => p.1) := measurable_fst
  have m2 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have m3 : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  refine Measurable.ite ?_ ?_ measurable_const
  · exact ((measurableSet_lt measurable_const m1).inter
      ((measurableSet_lt measurable_const m2).inter (measurableSet_lt measurable_const m3)))
  · unfold hellG
    exact measurable_const.sub (measurable_const.mul
      (((((measurable_const.mul (m2.div m1)).mul m3).div
        (((m2.div m1).pow_const 2).add (m3.pow_const 2))).sqrt).pow_const n))

/-- The root bound for one input, every `l`, `s`, `τ₀`. -/
theorem pt_root_all (c : Fin n → ℝ) (l s τ₀ : ℝ) {T : Set (Fin n → ℝ)} (hT : MeasurableSet T) :
    (√((stdGauss (Fin n)).real {γ | sphPt (l • c + s • γ) ∈ T}) -
      √((stdGauss (Fin n)).real {ξ | sphPt (c + τ₀ • ξ) ∈ T})) ^ 2 ≤ hu2 n l s τ₀ := by
  unfold hu2
  split_ifs with h
  · exact pt_root c h.1 h.2.1 h.2.2 hT
  · have b1 : ∀ S : Set (Fin n → ℝ), √((stdGauss (Fin n)).real S) ≤ 1 := fun S => by
      have := Real.sqrt_le_sqrt (measureReal_le_one (μ := stdGauss (Fin n)) (s := S))
      rwa [Real.sqrt_one] at this
    have h1 := b1 {γ | sphPt (l • c + s • γ) ∈ T}
    have h2 := b1 {ξ | sphPt (c + τ₀ • ξ) ∈ T}
    have h3 := Real.sqrt_nonneg ((stdGauss (Fin n)).real {γ | sphPt (l • c + s • γ) ∈ T})
    have h4 := Real.sqrt_nonneg ((stdGauss (Fin n)).real {ξ | sphPt (c + τ₀ • ξ) ∈ T})
    nlinarith

/-! ## The World replacement radius -/

/-- `λ_W(u) = ⟨a₂^W(u), b_W⟩/|b_W|²` for the retained data `c`. -/
noncomputable def lamWu (D : Centres n) (c : Ret n) (u : Fin (2 * n) → ℝ) : ℝ :=
  lam (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u)

/-- `σ_W(u) = √(2/m_W)·|r_W(u)|` for the retained data `c`. -/
noncomputable def sigWu (D : Centres n) (c : Ret n) (u : Fin (2 * n) → ℝ) : ℝ :=
  sig (2 / (mW n : ℝ)) (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u)

/-- **`H̄_W² = E_u H_u²`**, `u` uniform on the unit sphere of `ℝ^{2n}`. -/
noncomputable def HbarW2 (D : Design n) (c : Ret n) : ℝ :=
  ∫ u, hu2 n (lamWu D.toCentres c u) (sigWu D.toCentres c u) (D.tau0 c) ∂uniformSphere (2 * n)

/-- **The World replacement radius `H̄_W`** of the paper: a function of the retained data. -/
noncomputable def HbarW (D : Design n) (c : Ret n) : ℝ := √(HbarW2 D c)

lemma measurable_lam_joint {m : ℕ} :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => lam p.1 p.2) := by
  unfold lam
  exact (Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply j).comp measurable_snd).mul
      ((measurable_pi_apply j).comp measurable_fst)).div (measurable_normSq.comp measurable_fst)

lemma measurable_sig_joint {m : ℕ} (v : ℝ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => sig v p.1 p.2) := by
  unfold sig res
  exact measurable_const.mul ((measurable_normSq.comp
    (measurable_snd.sub (measurable_lam_joint.smul measurable_fst))).sqrt)

lemma measurable_hu2W (D : Design n) :
    Measurable (fun p : Ret n × (Fin (2 * n) → ℝ) =>
      hu2 n (lamWu D.toCentres p.1 p.2) (sigWu D.toCentres p.1 p.2) (D.tau0 p.1)) := by
  have hb : Measurable (fun p : Ret n × (Fin (2 * n) → ℝ) => D.bW p.1.1.1) :=
    D.mbW.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hh : Measurable (fun p : Ret n × (Fin (2 * n) → ℝ) => hid2 p.1.1.1.1 p.1.1.1.2 p.2) := by
    have h := (BstLean.Part136.continuous_hid2_joint (N := 2 * n) (m := mW n)).measurable.comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd :
        Measurable (fun p : Ret n × (Fin (2 * n) → ℝ) => (p.1.1.1, p.2)))
    exact h
  have h1 : Measurable (fun p : Ret n × (Fin (2 * n) → ℝ) => lamWu D.toCentres p.1 p.2) := by
    have h := measurable_lam_joint.comp (hb.prodMk hh)
    exact h
  have h2 : Measurable (fun p : Ret n × (Fin (2 * n) → ℝ) => sigWu D.toCentres p.1 p.2) := by
    have h := (measurable_sig_joint (2 / (mW n : ℝ))).comp (hb.prodMk hh)
    exact h
  have h3 := (measurable_hu2 n).comp (h1.prodMk (h2.prodMk (D.mtau0.comp measurable_fst)))
  exact h3

/-- **The radius `H̄_W` is measurable in the retained data.** -/
theorem measurable_HbarW (D : Design n) : Measurable (HbarW D) := by
  unfold HbarW HbarW2
  exact ((measurable_hu2W D).stronglyMeasurable.integral_prod_right').measurable.sqrt

lemma HbarW_sq (D : Design n) (c : Ret n) : HbarW D c ^ 2 = HbarW2 D c := by
  unfold HbarW
  exact Real.sq_sqrt (integral_nonneg fun u => hu2_nonneg _ _ _ _)

/-- The measure of a set under a product of probability measures, as an integral of the measures
of the sections. -/
lemma real_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsProbabilityMeasure ν] {S : Set (α × β)} (hS : MeasurableSet S) :
    (μ.prod ν).real S = ∫ x, ν.real (Prod.mk x ⁻¹' S) ∂μ := by
  unfold Measure.real
  rw [Measure.prod_apply hS, integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
    (Filter.Eventually.of_forall fun x => measure_lt_top _ _)]

/-- **The World root replacement, PROVED for the Hellinger radius.** For every retained value
`c` and every measurable set `T` of `ℝⁿ`: `|√(ν(T)) − √(ν'(T))| ≤ H̄_W`. Here `ν` is the
distribution of `sphPt (λ_W(u)·ĉ + σ_W(u)·γ)` and `ν'` is the distribution of `sphPt (ĉ + τ₀ ξ)`.
There is no hypothesis on `c`: at degenerate inputs `H_u² = 2`. -/
theorem replw_hellinger (hn : 1 ≤ n) (D : Design n) (c : Ret n) {T : Set (Fin n → ℝ)}
    (hT : MeasurableSet T) :
    |√((nuW D.toCentres c).real T) - √((nuStand D c).real T)| ≤ HbarW D c := by
  have hprob := BstLean.Part29.uniformSphere_isProbability (2 * n) (by omega)
  have mS : MeasurableSet (nuWmap D.toCentres c ⁻¹' T) := (measurable_nuWmap D.toCentres c) hT
  have eν : (nuW D.toCentres c).real T = ∫ u, (stdGauss (Fin n)).real
      {γ | sphPt (lamWu D.toCentres c u • c.1.2 + sigWu D.toCentres c u • γ) ∈ T}
        ∂uniformSphere (2 * n) := by
    unfold nuW
    rw [map_measureReal_apply (measurable_nuWmap D.toCentres c) hT, real_prod_eq _ _ mS]
    rfl
  have mG : Measurable (fun ξ : Fin n → ℝ => sphPt (c.1.2 + D.tau0 c • ξ)) :=
    measurable_sphPt.comp (measurable_const.add (measurable_const_smul (D.tau0 c)))
  have eν' : (nuStand D c).real T =
      (stdGauss (Fin n)).real {ξ | sphPt (c.1.2 + D.tau0 c • ξ) ∈ T} := by
    unfold nuStand
    rw [map_measureReal_apply mG hT]
    rfl
  have mX : Measurable (fun u : Fin (2 * n) → ℝ => (stdGauss (Fin n)).real
      {γ | sphPt (lamWu D.toCentres c u • c.1.2 + sigWu D.toCentres c u • γ) ∈ T}) :=
    (measurable_measure_prodMk_left (ν := stdGauss (Fin n)) mS).ennreal_toReal
  have mK : Measurable (fun u : Fin (2 * n) → ℝ =>
      hu2 n (lamWu D.toCentres c u) (sigWu D.toCentres c u) (D.tau0 c)) := by
    have h := (measurable_hu2W D).comp (measurable_prodMk_left (x := c))
    exact h
  have iK : Integrable (fun u : Fin (2 * n) → ℝ =>
      hu2 n (lamWu D.toCentres c u) (sigWu D.toCentres c u) (D.tau0 c)) (uniformSphere (2 * n)) :=
    Integrable.of_bound mK.aestronglyMeasurable 2 (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hu2_nonneg _ _ _ _)]
      exact hu2_le_two _ _ _ _)
  have key := mix_root (uniformSphere (2 * n)) mX (fun u => measureReal_nonneg)
    (fun u => measureReal_le_one)
    (Y := (stdGauss (Fin n)).real {ξ | sphPt (c.1.2 + D.tau0 c • ξ) ∈ T}) measureReal_nonneg iK
    (fun u => pt_root_all c.1.2 _ _ _ hT)
  rw [eν, eν']
  exact Real.abs_le_sqrt key

/-- **`REPLW_test_hyp` holds on every event inside `{H̄_W ≤ h_W}`**: the World root replacement
needs no hypothesis when the radius is the Hellinger radius `HbarW D`. -/
theorem replw_test_of_Hbar (hn : 1 ≤ n) (D : Design n) (hW : ℝ) (H E₁ : Set (Ret n)) :
    REPLW_test_hyp D hW (goodSet H E₁ (HbarW D) hW) :=
  fun c hc _ hT => (replw_hellinger hn D c hT).trans hc.1.2

/-- **The conditional classifier theorem for the actual networks, without a World replacement
hypothesis (every `n ≥ 16 384`).** The radius of `EVENTS_hyp` is the Hellinger radius `HbarW D`
(so that `E[1_H H̄_W²] ≤ v_W` is the statement of Lemma `t7:p02:moment` of the paper). IF
`GaussFrameMGF` holds (no network), the retained-data events have the charges of the ledger, and
on `H ∩ {H̄_W ≤ h_W} ∩ E₁` the two frame bounds and the Agent replacement hold, THEN the program
succeeds with probability at least `99/100`. -/
theorem classifier_networks_conditional_hell (hn : 16384 ≤ n) (hG : GaussFrameMGF)
    (D : Design n) (t : ℝ) {H E₁ : Set (Ret n)}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhidL vWL δextraL)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_frame hn hG D t hEv hFW hFA
    (replw_test_of_Hbar (by omega) D hWL H E₁) hRA

end BstLean.Part157

open BstLean.Part157 in
#print axioms root_set_hell
open BstLean.Part157 in
#print axioms mix_root
open BstLean.Part157 in
#print axioms pt_root
open BstLean.Part157 in
#print axioms replw_hellinger
open BstLean.Part157 in
#print axioms measurable_HbarW
open BstLean.Part157 in
#print axioms classifier_networks_conditional_hell
