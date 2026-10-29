import BstLean.Part150Final
import BstLean.Part149CentreDet
import BstLean.Part140Prog

/-!
# Part 150, item 5, tools: the normalization of the stand-in input, Gaussian facts

Role: `delegations/statements/p150-spec.md`, item 5 (a part). The paper's oracle first layer uses
the UNNORMALIZED stand-in input `y = c + τγ` and divides by `ρ = √(|c|² + nτ²)`; the oracle first
layer of Part 149 uses `sphPt y = y/|y|`. This file has the Gaussian facts of the comparison.

* `cs_int`: Cauchy–Schwarz for square-integrable functions.
* `pi_centred_sum_sq`: `E(Σ_i g_i(ω_i))² = Σ_i E g_i²` for centred `g_i`, independent coordinates.
* `uN c τ γ = 1 − |y|²/ρ²`, `wN c τ γ = 1 − |y|/ρ`, `VN c τ = (4τ²|c|² + 2nτ⁴)/ρ⁴`.
* `uN_int : E uN = 0`, `uN_sq_int : E uN² = VN`, `VN_le : VN ≤ 6/n`,
  `wN_sq_int_le : E wN² ≤ VN`, `wN_int_nonneg`, `wN_int_le : 0 ≤ E wN ≤ VN/2`.
* `stdGauss_lin_map`: `⟨γ, r⟩` has the distribution of `|r|·Z`; `hO_eq_gauss`, `relu_sq_eq_gauss`,
  `gO_eq_gauss`: the oracle first layer of the paper as means over `γ`.
* `kern_weighted`: `|Σ_i (E u a_i)(E v a_i) − k(E u|a|)(E v|a|)| ≤ √(E u²)·√(E v²)·√(QkG a k)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part134 BstLean.Part137 BstLean.Part141 BstLean.Part149
open BstLean.Part132 (nrm nrm_nonneg nrm_sq)
open BstLean.Part136 (hbar bm_fst bm_snd)

/-! ## Cauchy–Schwarz -/

/-- Cauchy–Schwarz: `(∫ f g)² ≤ ∫ f² · ∫ g²`. -/
lemma cs_int {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, g x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, f x * g x ∂μ) * t +
      ∫ x, f x ^ 2 ∂μ := by
    intro t
    have h0 : 0 ≤ ∫ x, (f x + t * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have h1 : (fun x => (f x + t * g x) ^ 2) =
        fun x => (f x ^ 2 + (2 * t) * (f x * g x)) + (t * t) * g x ^ 2 := by
      funext x; ring
    have i1 : Integrable (fun x => f x ^ 2 + (2 * t) * (f x * g x)) μ := hf.add (hfg.const_mul _)
    rw [h1, integral_add i1 (hg.const_mul _), integral_add hf (hfg.const_mul _),
      integral_const_mul, integral_const_mul] at h0
    linarith
  have h := discrim_le_zero key
  unfold discrim at h
  nlinarith

lemma abs_int_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    |∫ x, f x * g x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  exact Real.abs_le_sqrt (cs_int hf hg hfg)

/-! ## Sums of independent centred coordinates -/

section pi

variable {ι : Type*} [Fintype ι] {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma pi_centred_sum_sq {g : ι → ℝ → ℝ} (hg : ∀ i, Integrable (g i) μ)
    (hg2 : ∀ i, Integrable (fun x => g i x ^ 2) μ) (h0 : ∀ i, ∫ x, g i x ∂μ = 0) :
    Integrable (fun ω : ι → ℝ => ∑ i, g i (ω i)) (Measure.pi fun _ : ι => μ) ∧
    ∫ ω : ι → ℝ, ∑ i, g i (ω i) ∂(Measure.pi fun _ : ι => μ) = 0 ∧
    Integrable (fun ω : ι → ℝ => (∑ i, g i (ω i)) ^ 2) (Measure.pi fun _ : ι => μ) ∧
    ∫ ω : ι → ℝ, (∑ i, g i (ω i)) ^ 2 ∂(Measure.pi fun _ : ι => μ) =
      ∑ i, ∫ x, g i x ^ 2 ∂μ := by
  classical
  have hi : ∀ i, Integrable (fun ω : ι → ℝ => g i (ω i)) (Measure.pi fun _ : ι => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : ι => μ) (i := i) (hg i)
  have hmul : ∀ i j, Integrable (fun ω : ι → ℝ => g i (ω i) * g j (ω j))
      (Measure.pi fun _ : ι => μ) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have := integrable_comp_eval (μ := fun _ : ι => μ) (i := i) (hg2 i)
      simpa [sq] using this
    · have hind := (iIndepFun_pi (μ := fun _ : ι => μ) (X := g)
        (fun i => (hg i).aestronglyMeasurable.aemeasurable)).indepFun hij
      exact hind.integrable_mul (hi i) (hi j)
  have key : ∀ i j : ι, ∫ ω : ι → ℝ, g i (ω i) * g j (ω j) ∂(Measure.pi fun _ : ι => μ) =
      if i = j then ∫ x, g i x ^ 2 ∂μ else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      have := integral_comp_eval (μ := fun _ : ι => μ) (i := i) (hg2 i).aestronglyMeasurable
      simpa [sq] using this
    · simp only [hij, ↓reduceIte]
      have hind := (iIndepFun_pi (μ := fun _ : ι => μ) (X := g)
        (fun i => (hg i).aestronglyMeasurable.aemeasurable)).indepFun hij
      have h := hind.integral_mul_eq_mul_integral (hi i).aestronglyMeasurable
        (hi j).aestronglyMeasurable
      have h3 : ∫ ω : ι → ℝ, g i (ω i) ∂(Measure.pi fun _ : ι => μ) = 0 := by
        rw [integral_comp_eval (μ := fun _ : ι => μ) (i := i) (hg i).aestronglyMeasurable]
        exact h0 i
      have h' : ∫ ω : ι → ℝ, g i (ω i) * g j (ω j) ∂(Measure.pi fun _ : ι => μ) =
          (∫ ω : ι → ℝ, g i (ω i) ∂(Measure.pi fun _ : ι => μ)) *
            ∫ ω : ι → ℝ, g j (ω j) ∂(Measure.pi fun _ : ι => μ) := h
      rw [h', h3, zero_mul]
  have e : (fun ω : ι → ℝ => (∑ i, g i (ω i)) ^ 2) = fun ω => ∑ i, ∑ j, g i (ω i) * g j (ω j) := by
    funext ω; rw [sq, Finset.sum_mul_sum]
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_, ?_, ?_⟩
  · rw [integral_finsetSum _ fun i _ => hi i]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_comp_eval (μ := fun _ : ι => μ) (i := i) (hg i).aestronglyMeasurable]
    exact h0 i
  · rw [e]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hmul i j
  · rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hmul i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hmul i j]
    simp_rw [key]
    simp

end pi

/-- A polynomial of degree at most 4 under the standard Gaussian. -/
lemma gauss_poly4 (a0 a1 a2 a3 a4 : ℝ) :
    Integrable (fun x : ℝ => a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4)
      (gaussianReal 0 1) ∧
    ∫ x : ℝ, a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4 ∂gaussianReal 0 1 =
      a0 + a2 + 3 * a4 := by
  have h1 : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  have i1 : Integrable (fun x : ℝ => a0 + a1 * x) (gaussianReal 0 1) :=
    (integrable_const a0).add (h1.const_mul a1)
  have i2 : Integrable (fun x : ℝ => a0 + a1 * x + a2 * x ^ 2) (gaussianReal 0 1) :=
    i1.add ((integrable_pow_gauss 2).const_mul a2)
  have i3 : Integrable (fun x : ℝ => a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3) (gaussianReal 0 1) :=
    i2.add ((integrable_pow_gauss 3).const_mul a3)
  refine ⟨i3.add ((integrable_pow_gauss 4).const_mul a4), ?_⟩
  have m2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    rw [gaussMom_eq 2]; norm_num [gaussMom, Nat.doubleFactorial, Nat.even_iff]
  have m3 : ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 = 0 := by
    rw [gaussMom_eq 3]; norm_num [gaussMom, Nat.doubleFactorial, Nat.even_iff]
  have m4 : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
    rw [gaussMom_eq 4]; norm_num [gaussMom, Nat.doubleFactorial, Nat.even_iff]
  rw [integral_add i3 ((integrable_pow_gauss 4).const_mul a4),
    integral_add i2 ((integrable_pow_gauss 3).const_mul a3),
    integral_add i1 ((integrable_pow_gauss 2).const_mul a2),
    integral_add (integrable_const a0) (h1.const_mul a1),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_id_gaussianReal, m2, m3, m4]
  simp
  ring

/-! ## The squared length of the stand-in input -/

variable {n m : ℕ}

/-- `1 − |c + τγ|²/ρ²`. -/
noncomputable def uN (c : Fin n → ℝ) (τ : ℝ) (γ : Fin n → ℝ) : ℝ :=
  1 - normSq (c + τ • γ) / rhoC c τ ^ 2

/-- `1 − |c + τγ|/ρ`. -/
noncomputable def wN (c : Fin n → ℝ) (τ : ℝ) (γ : Fin n → ℝ) : ℝ :=
  1 - nrm (c + τ • γ) / rhoC c τ

/-- `Var(|c + τγ|²)/ρ⁴ = (4τ²|c|² + 2nτ⁴)/ρ⁴`. -/
noncomputable def VN (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  (4 * τ ^ 2 * normSq c + 2 * n * τ ^ 4) / rhoC c τ ^ 4

lemma rhoC_sq (c : Fin n → ℝ) (τ : ℝ) : rhoC c τ ^ 2 = normSq c + (n : ℝ) * τ ^ 2 := by
  unfold rhoC
  exact Real.sq_sqrt (add_nonneg (normSq_nonneg c) (by positivity))

lemma rhoC_pos (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) : 0 < rhoC c τ := by
  unfold rhoC
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg c) (by positivity))

lemma measurable_uN (c : Fin n → ℝ) (τ : ℝ) : Measurable (uN c τ) := by
  unfold uN
  exact measurable_const.sub ((measurable_normSq.comp
    (measurable_const.add (measurable_id.const_smul τ))).div_const _)

lemma measurable_wN (c : Fin n → ℝ) (τ : ℝ) : Measurable (wN c τ) := by
  unfold wN nrm
  exact measurable_const.sub (((measurable_normSq.comp
    (measurable_const.add (measurable_id.const_smul τ))).sqrt).div_const _)

/-- The mean and the second moment of `uN`. -/
theorem uN_moments (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (uN c τ) (stdGauss (Fin n)) ∧ ∫ γ, uN c τ γ ∂stdGauss (Fin n) = 0 ∧
    Integrable (fun γ => uN c τ γ ^ 2) (stdGauss (Fin n)) ∧
    ∫ γ, uN c τ γ ^ 2 ∂stdGauss (Fin n) = VN c τ := by
  have hρ := rhoC_pos hn c hτ
  have hρ2 := rhoC_sq c τ
  set g : Fin n → ℝ → ℝ := fun i x => 2 * c i * τ * x + τ ^ 2 * (x ^ 2 - 1) with hg
  have eg : ∀ i, g i = fun x : ℝ => -τ ^ 2 + (2 * c i * τ) * x + τ ^ 2 * x ^ 2 + 0 * x ^ 3 +
      0 * x ^ 4 := fun i => by funext x; simp only [hg]; ring
  have eg2 : ∀ i, (fun x => g i x ^ 2) = fun x : ℝ => τ ^ 4 + (-(4 * c i * τ ^ 3)) * x +
      (4 * c i ^ 2 * τ ^ 2 - 2 * τ ^ 4) * x ^ 2 + (4 * c i * τ ^ 3) * x ^ 3 + τ ^ 4 * x ^ 4 :=
    fun i => by funext x; simp only [hg]; ring
  have h1 : ∀ i, Integrable (g i) (gaussianReal 0 1) := fun i => by
    rw [eg i]; exact (gauss_poly4 _ _ _ _ _).1
  have h0 : ∀ i, ∫ x, g i x ∂gaussianReal 0 1 = 0 := fun i => by
    rw [eg i, (gauss_poly4 _ _ _ _ _).2]; ring
  have h2 : ∀ i, Integrable (fun x => g i x ^ 2) (gaussianReal 0 1) := fun i => by
    rw [eg2 i]; exact (gauss_poly4 _ _ _ _ _).1
  have h2v : ∀ i, ∫ x, g i x ^ 2 ∂gaussianReal 0 1 = 4 * c i ^ 2 * τ ^ 2 + 2 * τ ^ 4 := fun i => by
    rw [eg2 i, (gauss_poly4 _ _ _ _ _).2]; ring
  obtain ⟨a1, a2, a3, a4⟩ := pi_centred_sum_sq (ι := Fin n) h1 h2 h0
  have eu : uN c τ = fun γ : Fin n → ℝ => (-(1 / rhoC c τ ^ 2)) * ∑ i, g i (γ i) := by
    funext γ
    unfold uN
    have hs : ∑ i, g i (γ i) = normSq (c + τ • γ) - rhoC c τ ^ 2 := by
      rw [hρ2]
      simp only [hg, normSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (n : ℝ) * τ ^ 2 = ∑ _i : Fin n, τ ^ 2 := by simp
      rw [this, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs]
    field_simp
    ring
  have eu2 : (fun γ => uN c τ γ ^ 2) =
      fun γ : Fin n → ℝ => (1 / rhoC c τ ^ 4) * (∑ i, g i (γ i)) ^ 2 := by
    funext γ
    rw [eu]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eu]; exact a1.const_mul _
  · rw [eu, integral_const_mul]
    unfold stdGauss
    rw [a2, mul_zero]
  · rw [eu2]; exact a3.const_mul _
  · rw [eu2, integral_const_mul]
    unfold stdGauss
    rw [a4]
    simp_rw [h2v]
    unfold VN normSq
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e3 : ∑ x : Fin n, 4 * c x ^ 2 * τ ^ 2 = ∑ i : Fin n, 4 * τ ^ 2 * c i ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [e3]
    field_simp

lemma VN_nonneg (c : Fin n → ℝ) (τ : ℝ) : 0 ≤ VN c τ := by
  unfold VN
  have := normSq_nonneg c
  positivity

/-- `VN ≤ 6/n`. -/
theorem VN_le (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) : VN c τ ≤ 6 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ := rhoC_pos hn c hτ
  have hρ2 := rhoC_sq c τ
  have hc := normSq_nonneg c
  unfold VN
  rw [div_le_div_iff₀ (pow_pos hρ 4) hnR]
  have e : rhoC c τ ^ 4 = (normSq c + (n : ℝ) * τ ^ 2) ^ 2 := by rw [← hρ2]; ring
  rw [e]
  have ht : 0 ≤ τ ^ 2 := sq_nonneg τ
  nlinarith [mul_nonneg hc (mul_nonneg hnR.le ht), mul_nonneg hc hc,
    mul_nonneg (mul_nonneg hnR.le ht) (mul_nonneg hnR.le ht), sq_nonneg (normSq c)]

lemma wN_abs_le (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (γ : Fin n → ℝ) :
    |wN c τ γ| ≤ |uN c τ γ| ∧ wN c τ γ = uN c τ γ / 2 + wN c τ γ ^ 2 / 2 := by
  have hρ := rhoC_pos hn c hτ
  set t := nrm (c + τ • γ) / rhoC c τ with ht
  have ht0 : 0 ≤ t := div_nonneg (nrm_nonneg _) hρ.le
  have eu : uN c τ γ = 1 - t ^ 2 := by
    unfold uN; rw [ht, div_pow, nrm_sq]
  have ew : wN c τ γ = 1 - t := rfl
  rw [eu, ew]
  constructor
  · rw [show 1 - t ^ 2 = (1 - t) * (1 + t) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + t)]
    nlinarith [abs_nonneg (1 - t)]
  · ring

/-- The moments of `wN`: `E wN² ≤ VN` and `0 ≤ E wN ≤ VN/2`. -/
theorem wN_moments (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (wN c τ) (stdGauss (Fin n)) ∧
    Integrable (fun γ => wN c τ γ ^ 2) (stdGauss (Fin n)) ∧
    ∫ γ, wN c τ γ ^ 2 ∂stdGauss (Fin n) ≤ VN c τ ∧
    0 ≤ ∫ γ, wN c τ γ ∂stdGauss (Fin n) ∧ ∫ γ, wN c τ γ ∂stdGauss (Fin n) ≤ VN c τ / 2 := by
  obtain ⟨u1, u0, u2, uV⟩ := uN_moments hn c hτ
  have hw : Integrable (wN c τ) (stdGauss (Fin n)) :=
    u1.abs.mono' (measurable_wN c τ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun γ => by
        rw [Real.norm_eq_abs]; exact (wN_abs_le hn c hτ γ).1)
  have hw2 : Integrable (fun γ => wN c τ γ ^ 2) (stdGauss (Fin n)) :=
    u2.mono' ((measurable_wN c τ).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun γ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (wN c τ γ), ← sq_abs (uN c τ γ)]
        exact pow_le_pow_left₀ (abs_nonneg _) (wN_abs_le hn c hτ γ).1 2)
  have hle : ∫ γ, wN c τ γ ^ 2 ∂stdGauss (Fin n) ≤ VN c τ := by
    rw [← uV]
    refine integral_mono hw2 u2 fun γ => ?_
    show wN c τ γ ^ 2 ≤ uN c τ γ ^ 2
    rw [← sq_abs (wN c τ γ), ← sq_abs (uN c τ γ)]
    exact pow_le_pow_left₀ (abs_nonneg _) (wN_abs_le hn c hτ γ).1 2
  have e : ∫ γ, wN c τ γ ∂stdGauss (Fin n) = (∫ γ, wN c τ γ ^ 2 ∂stdGauss (Fin n)) / 2 := by
    have e1 : wN c τ = fun γ => uN c τ γ / 2 + wN c τ γ ^ 2 / 2 := by
      funext γ; exact (wN_abs_le hn c hτ γ).2
    have i1 : Integrable (fun γ => uN c τ γ / 2) (stdGauss (Fin n)) := u1.div_const 2
    have i2 : Integrable (fun γ => wN c τ γ ^ 2 / 2) (stdGauss (Fin n)) := hw2.div_const 2
    calc ∫ γ, wN c τ γ ∂stdGauss (Fin n)
        = ∫ γ, (uN c τ γ / 2 + wN c τ γ ^ 2 / 2) ∂stdGauss (Fin n) := by rw [← e1]
      _ = _ := by rw [integral_add i1 i2, integral_div, integral_div, u0]; ring
  refine ⟨hw, hw2, hle, ?_, ?_⟩
  · rw [e]; exact div_nonneg (integral_nonneg fun γ => sq_nonneg _) (by norm_num)
  · rw [e]; linarith

end BstLean.Part150
