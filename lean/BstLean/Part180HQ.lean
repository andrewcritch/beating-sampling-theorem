import BstLean.Part180Def

/-!
# Part 180 (file `HQ`): Lemma HQ for a location-scale Gaussian mixture

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `delegations/answers/onC52-opus.md`, §1 (Lemma HQ). For the mixture `P = E_π N(l c, S I)`
and the Gaussian `Q = N(l₀ c, S₀ I)` with `E_π l = l₀`, `E_π S = S₀` and the window
`|S/S₀ − 1| ≤ ε₀ < 1`, `|l − l₀| ≤ δ₀`, and every measurable event `B`:
`(√P(B) − √Q(B))² ≤ χ²(P ‖ Q)/4 + (3/4)·(K̂³/λ² + Ŷ/(1 − λ)²)` (`mix_root_hq`), with
`K̂ = n(1 + 3ε₀)/(4(1 − ε₀))·X + Y/(2(1 − ε₀))`, `Ŷ = (nX² + 2XY)/(1 − ε₀)²`,
`X = E_π (S/S₀ − 1)²`, `Y = E_π (|c|²/S₀)(l − l₀)²`, any `λ ∈ (0, 1)`.

Differences from the paper's proof: the cubic term `E_Q (1 − R)₊³` is bounded by
`(1 − R)₊ ≤ |K| + min(1, |Y(z)|)` (Jensen `R ≥ exp L̄`, `L̄ = K + Y(z)`), the convexity split
`(a + b)³ ≤ a³/λ² + b³/(1 − λ)²` and `min(1, |Y|)³ ≤ Y²`; only second Gaussian moments are used
(`gauss_dot_sq`, `gauss_W_sq`), no hypercontractivity. The constant term uses
`|log(1 + x) − x/(1 + x)| ≤ x²(1 + 3ε₀)/(2(1 − ε₀))` (paper: `x²/(2(1 − ε₀)²)`).

* `hq_point`: `(√r − 1)² ≤ (r − 1)²/4 + (3/4)(1 − r)₊³`.
* `cube_split`, `log_sub_frac`, `cubic_point`: elementary inequalities.
* `gauss_dot_sq`, `gauss_W_sq`: `E(Σuᵢzᵢ)² = Σuᵢ²`, `E(Σzᵢ² − D)² = 2D`.
* `log_gdN_eq`, `log_gdN_muN`: the log-density of a component.
* `jensen_mix`, `mix_coef_bounds`: Jensen at a fixed point and the coefficients of `L̄`.
* **`mix_root_hq`**.
-/

namespace BstLean.Part180

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part161

/-- **The pointwise inequality of Lemma HQ**: `(√r − 1)² ≤ (r − 1)²/4 + (3/4)·(1 − r)₊³`. -/
lemma hq_point {r : ℝ} (hr : 0 ≤ r) :
    (√r - 1) ^ 2 ≤ (r - 1) ^ 2 / 4 + 3 / 4 * max 0 (1 - r) ^ 3 := by
  set s := √r with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg r
  have hrs : r = s ^ 2 := (Real.sq_sqrt hr).symm
  rw [hrs]
  rcases le_or_gt 1 s with h | h
  · have hm : max 0 (1 - s ^ 2) = 0 := max_eq_left (by nlinarith)
    rw [hm]
    have e : (s ^ 2 - 1) ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by ring
    rw [e]
    have : 4 ≤ (s + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (s - 1)]
  · have hm : max 0 (1 - s ^ 2) = 1 - s ^ 2 := max_eq_right (by nlinarith)
    rw [hm]
    have e : (s ^ 2 - 1) ^ 2 / 4 + 3 / 4 * (1 - s ^ 2) ^ 3 - (s - 1) ^ 2 =
        (1 - s) ^ 3 * s * (3 / 4 * (1 + s) ^ 2 + 3 / 4 * (1 + s) + 1 / 2) := by ring
    have : 0 ≤ (1 - s) ^ 3 * s * (3 / 4 * (1 + s) ^ 2 + 3 / 4 * (1 + s) + 1 / 2) := by
      have : 0 ≤ 1 - s := by linarith
      positivity
    linarith

/-- `(a + b)³ ≤ a³/λ² + b³/(1 − λ)²` for `a, b ≥ 0`, `0 < λ < 1` (convexity of the cube). -/
lemma cube_split {a b lam : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl0 : 0 < lam) (hl1 : lam < 1) :
    (a + b) ^ 3 ≤ a ^ 3 / lam ^ 2 + b ^ 3 / (1 - lam) ^ 2 := by
  set x := a / lam
  set y := b / (1 - lam)
  have hm : 0 < 1 - lam := by linarith
  have hx : a = lam * x := by simp only [x]; field_simp
  have hy : b = (1 - lam) * y := by simp only [y]; field_simp
  have hx0 : 0 ≤ x := div_nonneg ha hl0.le
  have hy0 : 0 ≤ y := div_nonneg hb hm.le
  have e1 : a ^ 3 / lam ^ 2 = lam * x ^ 3 := by rw [hx]; field_simp
  have e2 : b ^ 3 / (1 - lam) ^ 2 = (1 - lam) * y ^ 3 := by rw [hy]; field_simp
  rw [e1, e2, hx, hy]
  have key : lam * x ^ 3 + (1 - lam) * y ^ 3 - (lam * x + (1 - lam) * y) ^ 3 =
      lam * (1 - lam) * (x - y) ^ 2 * ((1 + lam) * x + (2 - lam) * y) := by ring
  have : 0 ≤ lam * (1 - lam) * (x - y) ^ 2 * ((1 + lam) * x + (2 - lam) * y) := by
    have : 0 ≤ (1 + lam) * x + (2 - lam) * y := by nlinarith
    positivity
  linarith

/-- `|log(1 + x) − x/(1 + x)| ≤ x²(1 + 3ε₀)/(2(1 − ε₀))` for `|x| ≤ ε₀ < 1`. -/
lemma log_sub_frac {x ε₀ : ℝ} (hx : |x| ≤ ε₀) (hε : ε₀ < 1) :
    |log (1 + x) - x / (1 + x)| ≤ x ^ 2 * ((1 + 3 * ε₀) / (2 * (1 - ε₀))) := by
  have hx1 : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have hε0 : 0 ≤ ε₀ := (abs_nonneg x).trans hx
  have hxl := abs_le.mp hx
  have hpos : 0 < 1 + x := by linarith
  have hd : 0 < 1 - |x| := by linarith
  set E := -x + x ^ 2 / 2 + log (1 + x) with hE
  have hE' : |E| ≤ |x| ^ 3 / (1 - |x|) := by
    have : -x + (-x) ^ 2 / 2 + log (1 + x) = E := by rw [hE]; ring
    simpa [this, abs_neg, sub_neg_eq_add] using h
  have key : log (1 + x) - x / (1 + x) = x ^ 2 * (1 - x) / (2 * (1 + x)) + E := by
    rw [hE]; field_simp; ring
  rw [key]
  have h1 : |x ^ 2 * (1 - x) / (2 * (1 + x))| ≤ x ^ 2 * ((1 + ε₀) / (2 * (1 - ε₀))) := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg x), abs_of_pos (by linarith : (0:ℝ) < 2 * (1 + x)),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - x)]
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg x)
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : |x| ^ 3 / (1 - |x|) ≤ x ^ 2 * (ε₀ / (1 - ε₀)) := by
    have e : |x| ^ 3 = x ^ 2 * |x| := by rw [pow_succ, sq_abs]
    rw [e, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg x)
    rw [div_le_div_iff₀ hd (by linarith)]
    nlinarith [abs_nonneg x]
  have h3 : x ^ 2 * ((1 + ε₀) / (2 * (1 - ε₀))) + x ^ 2 * (ε₀ / (1 - ε₀)) =
      x ^ 2 * ((1 + 3 * ε₀) / (2 * (1 - ε₀))) := by
    have : (1 - ε₀) ≠ 0 := by linarith
    field_simp; ring
  calc |x ^ 2 * (1 - x) / (2 * (1 + x)) + E| ≤ |x ^ 2 * (1 - x) / (2 * (1 + x))| + |E| :=
        abs_add_le _ _
    _ ≤ _ := by linarith


section gauss
variable {ι : Type*} [Fintype ι]

lemma mp_eval (i : ι) : MeasurePreserving (Function.eval i : (ι → ℝ) → ℝ) (stdGauss ι)
    (gaussianReal 0 1) := by
  unfold stdGauss
  exact measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i

/-- **`E(Σ uᵢ zᵢ)² = Σ uᵢ²`** under the standard Gaussian distribution. -/
lemma gauss_dot_sq (u : ι → ℝ) :
    Integrable (fun z : ι → ℝ => (∑ i, u i * z i) ^ 2) (stdGauss ι) ∧
      ∫ z, (∑ i, u i * z i) ^ 2 ∂stdGauss ι = ∑ i, u i ^ 2 := by
  classical
  set X : ι → (ι → ℝ) → ℝ := fun i ξ => u i * ξ i with hX
  have hmem1 : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hmem : ∀ i, MemLp (X i) 2 (stdGauss ι) := fun i =>
    (hmem1.const_mul (u i)).comp_measurePreserving (mp_eval i)
  have hind : iIndepFun X (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1) (X := fun i (x : ℝ) => u i * x)
      (fun _ => by fun_prop)
  have hvar_i : ∀ i, Var[X i; stdGauss ι] = u i ^ 2 := fun i => by
    have : X i = (fun x : ℝ => u i * x) ∘ (Function.eval i) := rfl
    rw [this, ← variance_map (by fun_prop) (mp_eval i).measurable.aemeasurable, (mp_eval i).map_eq]
    have h := variance_const_mul (u i) (id : ℝ → ℝ) (gaussianReal 0 1)
    simp only [variance_id_gaussianReal] at h
    have e : (fun x : ℝ => u i * x) = fun x => u i * id x := rfl
    rw [e, h]; simp
  have hmean_i : ∀ i, ∫ ξ, X i ξ ∂stdGauss ι = 0 := fun i => by
    have h := integral_map (μ := stdGauss ι) (φ := Function.eval i)
      (mp_eval i).measurable.aemeasurable (f := fun x : ℝ => u i * x) (by fun_prop)
    rw [(mp_eval i).map_eq] at h
    rw [show (fun ξ => X i ξ) = fun ξ => u i * Function.eval i ξ from rfl, ← h, integral_const_mul,
      integral_id_gaussianReal]
    simp
  have hsum : (fun ξ : ι → ℝ => ∑ i, u i * ξ i) = ∑ i, X i := by
    funext ξ; simp [hX]
  have hm2 : MemLp (fun ξ : ι → ℝ => ∑ i, u i * ξ i) 2 (stdGauss ι) := by
    rw [hsum]; exact memLp_finsetSum' _ (fun i _ => hmem i)
  have hvar : Var[fun ξ : ι → ℝ => ∑ i, u i * ξ i; stdGauss ι] = ∑ i, u i ^ 2 := by
    rw [hsum, IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp [hvar_i]
  have hmean : ∫ ξ : ι → ℝ, ∑ i, u i * ξ i ∂stdGauss ι = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    simp [hmean_i]
  refine ⟨hm2.integrable_sq, ?_⟩
  rw [variance_eq_integral hm2.aemeasurable, hmean] at hvar
  simpa using hvar

/-- **`E(Σ zᵢ² − D)² = 2D`** under the standard Gaussian distribution. -/
lemma gauss_W_sq :
    Integrable (fun z : ι → ℝ => (∑ i, z i ^ 2 - (Fintype.card ι : ℝ)) ^ 2) (stdGauss ι) ∧
      ∫ z, (∑ i, z i ^ 2 - (Fintype.card ι : ℝ)) ^ 2 ∂stdGauss ι = 2 * (Fintype.card ι : ℝ) := by
  classical
  set X : ι → (ι → ℝ) → ℝ := fun i ξ => ξ i ^ 2 with hX
  have hmem : ∀ i, MemLp (X i) 2 (stdGauss ι) := fun i =>
    BstLean.Part106.memLp_sq_gauss.comp_measurePreserving (mp_eval i)
  have hind : iIndepFun X (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1) (X := fun _ (x : ℝ) => x ^ 2)
      (fun _ => by fun_prop)
  have hvar_i : ∀ i, Var[X i; stdGauss ι] = 2 := fun i => by
    have : X i = (fun x : ℝ => x ^ 2) ∘ (Function.eval i) := rfl
    rw [this, ← variance_map (by fun_prop) (mp_eval i).measurable.aemeasurable, (mp_eval i).map_eq]
    exact BstLean.Part106.var_sq_gauss
  have hmean_i : ∀ i, ∫ ξ, X i ξ ∂stdGauss ι = 1 := fun i => by
    have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
      rw [BstLean.Part29.gaussMom_eq 2]
      norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
    have h := integral_map (μ := stdGauss ι) (φ := Function.eval i)
      (mp_eval i).measurable.aemeasurable (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [(mp_eval i).map_eq, h2] at h
    exact h.symm
  have hsum : (fun ξ : ι → ℝ => ∑ i, ξ i ^ 2) = ∑ i, X i := by
    funext ξ; simp [hX]
  have hvar : Var[fun ξ : ι → ℝ => ∑ i, ξ i ^ 2; stdGauss ι] = 2 * (Fintype.card ι : ℝ) := by
    rw [hsum, IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp [hvar_i, mul_comm]
  have hmean : ∫ ξ : ι → ℝ, ∑ i, ξ i ^ 2 ∂stdGauss ι = (Fintype.card ι : ℝ) := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    rw [Finset.sum_congr rfl (fun i _ => hmean_i i)]
    simp
  have hm2 : MemLp (fun ξ : ι → ℝ => ∑ i, ξ i ^ 2) 2 (stdGauss ι) := by
    rw [hsum]; exact memLp_finsetSum' _ (fun i _ => hmem i)
  have hm3 : MemLp (fun ξ : ι → ℝ => ∑ i, ξ i ^ 2 - (Fintype.card ι : ℝ)) 2 (stdGauss ι) :=
    hm2.sub (memLp_const _)
  refine ⟨hm3.integrable_sq, ?_⟩
  rw [variance_eq_integral hm2.aemeasurable, hmean] at hvar
  exact hvar

end gauss

/-- `log gdN = Σᵢ (−(log v)/2 − (zᵢ − μᵢ)²/(2v) + zᵢ²/2)`. -/
lemma log_gdN_eq {ι : Type*} [Fintype ι] (μ : ι → ℝ) {v : ℝ} (hv : 0 < v) (z : ι → ℝ) :
    log (gdN μ v z) = ∑ i, (-(log v) / 2 - (z i - μ i) ^ 2 / (2 * v) + z i ^ 2 / 2) := by
  unfold gdN
  rw [Real.log_prod (fun i _ => (gd1_pos hv (μ i) (z i)).ne')]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold gd1
  rw [Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr hv).ne') (exp_pos _).ne', Real.log_inv,
    Real.log_sqrt hv.le, Real.log_exp]
  ring

/-- The log-density of a component of the mixture in the variables of Lemma HQ:
`r = S/S₀`, `δ = l − l₀`, `u = S₀^{−1/2} c`. -/
lemma log_gdN_muN {n : ℕ} (c : Fin n → ℝ) {l0 S0 : ℝ} (hS0 : 0 < S0) (l S : ℝ) (hS : 0 < S)
    (z : Fin n → ℝ) :
    log (gdN (muN c l0 S0 l) (S / S0) z) =
      -(n / 2) * log (S / S0) + 1 / 2 * (1 - 1 / (S / S0)) * (∑ i, z i ^ 2) +
        (l - l0) / (S / S0) * (∑ i, (√S0)⁻¹ * c i * z i) -
        (l - l0) ^ 2 * (normSq c / S0) / (2 * (S / S0)) := by
  have hr : 0 < S / S0 := div_pos hS hS0
  rw [log_gdN_eq _ hr]
  have hu : normSq c / S0 = ∑ i, ((√S0)⁻¹ * c i) ^ 2 := by
    unfold normSq
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, inv_pow, Real.sq_sqrt hS0.le]; ring
  rw [hu]
  have hi : ∀ i, -(log (S / S0)) / 2 - (z i - muN c l0 S0 l i) ^ 2 / (2 * (S / S0)) + z i ^ 2 / 2 =
      -(log (S / S0)) / 2 + 1 / 2 * (1 - 1 / (S / S0)) * z i ^ 2 +
        (l - l0) / (S / S0) * ((√S0)⁻¹ * c i * z i) -
        (l - l0) ^ 2 / (2 * (S / S0)) * ((√S0)⁻¹ * c i) ^ 2 := by
    intro i
    unfold muN
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun i _ => hi i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The pointwise cubic bound**: if `exp(K + Y) ≤ R` and `R ≥ 0`, then
`(1 − R)₊³ ≤ |K|³/λ² + Y²/(1 − λ)²`. -/
lemma cubic_point {R K Y lam : ℝ} (hR : 0 ≤ R) (hJ : exp (K + Y) ≤ R) (hl0 : 0 < lam)
    (hl1 : lam < 1) :
    max 0 (1 - R) ^ 3 ≤ |K| ^ 3 / lam ^ 2 + Y ^ 2 / (1 - lam) ^ 2 := by
  set m := max 0 (1 - R) with hm
  have hm0 : 0 ≤ m := le_max_left _ _
  have hm1 : m ≤ 1 := max_le (by norm_num) (by linarith)
  have hmL : m ≤ |K + Y| := by
    rcases le_or_gt (1 - R) 0 with h | h
    · rw [hm, max_eq_left h]; exact abs_nonneg _
    · rw [hm, max_eq_right h.le]
      have := add_one_le_exp (K + Y)
      have := neg_le_abs (K + Y)
      linarith
  set μ := min 1 |Y| with hμ
  have hμ0 : 0 ≤ μ := le_min (by norm_num) (abs_nonneg _)
  have hμ1 : μ ≤ 1 := min_le_left _ _
  have hμY : μ ≤ |Y| := min_le_right _ _
  have hmK : m ≤ |K| + μ := by
    rcases le_or_gt |Y| 1 with h | h
    · rw [hμ, min_eq_right h]
      exact hmL.trans (abs_add_le _ _)
    · rw [hμ, min_eq_left h.le]
      linarith [abs_nonneg K]
  have h3 : m ^ 3 ≤ (|K| + μ) ^ 3 := pow_le_pow_left₀ hm0 hmK 3
  have h4 := cube_split (abs_nonneg K) hμ0 hl0 hl1
  have h5 : μ ^ 3 ≤ Y ^ 2 := by
    have : μ ^ 3 ≤ μ ^ 2 := by nlinarith [sq_nonneg μ]
    have : μ ^ 2 ≤ |Y| ^ 2 := pow_le_pow_left₀ hμ0 hμY 2
    rw [sq_abs] at this
    linarith
  have hd : 0 < (1 - lam) ^ 2 := by have : 0 < 1 - lam := by linarith
                                    positivity
  have h6 : μ ^ 3 / (1 - lam) ^ 2 ≤ Y ^ 2 / (1 - lam) ^ 2 := div_le_div_of_nonneg_right h5 hd.le
  linarith

section mix
variable {V : Type*} [MeasurableSpace V]

lemma ibd (pm : Measure V) [IsProbabilityMeasure pm] {f : V → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ v, |f v| ≤ M) : Integrable f pm :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hM v)

lemma abs_log_le {x ε₀ : ℝ} (hx : |x - 1| ≤ ε₀) (hε : ε₀ < 1) : |log x| ≤ ε₀ / (1 - ε₀) := by
  have h1 : |(1 - x)| < 1 := by rw [abs_sub_comm]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one, sub_sub_cancel] at h
  rw [abs_sub_comm] at h
  have hd : 0 < 1 - |x - 1| := by linarith
  refine h.trans ?_
  rw [div_le_div_iff₀ hd (by linarith)]
  nlinarith [abs_nonneg (x - 1)]

/-- **Jensen for the mixture density at a fixed point `z`** (Lemma HQ, step (ii)). -/
theorem jensen_mix {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ} (hl : Measurable l) (hS : Measurable S)
    {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1) (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (z : Fin n → ℝ) :
    exp ((∫ v, (-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
          (l v - l0) ^ 2 * (normSq c / S0) / (2 * (S v / S0))) ∂pm) +
        1 / 2 * (∫ v, (1 - 1 / (S v / S0)) ∂pm) * (∑ i, z i ^ 2 - n) +
        (∫ v, (l v - l0) / (S v / S0) ∂pm) * (∑ i, (√S0)⁻¹ * c i * z i)) ≤
      ∫ v, gdN (muN c l0 S0 (l v)) (S v / S0) z ∂pm := by
  have : Nonempty V := nonempty_of_isProbabilityMeasure pm
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans (hwS (Classical.arbitrary V))
  have hd : 0 < 1 - ε₀ := by linarith
  have hr1 : ∀ v, 1 - ε₀ ≤ S v / S0 := fun v => by have := (abs_le.mp (hwS v)).1; linarith
  have hrp : ∀ v, 0 < S v / S0 := fun v => lt_of_lt_of_le hd (hr1 v)
  have hSp : ∀ v, 0 < S v := fun v => by
    have := hrp v; rwa [div_pos_iff_of_pos_right hS0] at this
  set S2 := ∑ i, z i ^ 2
  set D1 := ∑ i, (√S0)⁻¹ * c i * z i
  set a2 := normSq c / S0
  have ha2 : 0 ≤ a2 := div_nonneg (normSq_nonneg c) hS0.le
  set A : V → ℝ := fun v => -(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
    (l v - l0) ^ 2 * a2 / (2 * (S v / S0)) with hA
  set Bf : V → ℝ := fun v => 1 - 1 / (S v / S0) with hBf
  set Cf : V → ℝ := fun v => (l v - l0) / (S v / S0) with hCf
  have mr : Measurable (fun v => S v / S0) := hS.div_const S0
  have mA : Measurable A := by
    simp only [hA]
    exact ((measurable_const.mul mr.log).add (measurable_const.mul (measurable_const.sub
      (measurable_const.div mr)))).sub ((((hl.sub_const l0).pow_const 2).mul_const a2).div
        (measurable_const.mul mr))
  have mB : Measurable Bf := measurable_const.sub (measurable_const.div mr)
  have mC : Measurable Cf := (hl.sub_const l0).div mr
  -- pointwise bounds
  have bB : ∀ v, |Bf v| ≤ ε₀ / (1 - ε₀) := fun v => by
    simp only [hBf]
    have e : 1 - 1 / (S v / S0) = (S v / S0 - 1) / (S v / S0) := by
      field_simp [(hSp v).ne', hS0.ne']
    rw [e, abs_div, abs_of_pos (hrp v)]
    exact div_le_div₀ hε0 (hwS v) hd (hr1 v)
  have bC : ∀ v, |Cf v| ≤ δ₀ / (1 - ε₀) := fun v => by
    simp only [hCf]
    rw [abs_div, abs_of_pos (hrp v)]
    exact div_le_div₀ ((abs_nonneg _).trans (hwl v)) (hwl v) hd (hr1 v)
  have hδ0 : 0 ≤ δ₀ := (abs_nonneg _).trans (hwl (Classical.arbitrary V))
  have bA : ∀ v, |A v| ≤ n / 2 * (ε₀ / (1 - ε₀)) + n / 2 * (ε₀ / (1 - ε₀)) +
      δ₀ ^ 2 * a2 / (2 * (1 - ε₀)) := fun v => by
    simp only [hA]
    have h1 : |log (S v / S0)| ≤ ε₀ / (1 - ε₀) := abs_log_le (hwS v) hε₀
    have h2 := bB v
    simp only [hBf] at h2
    have h3 : |(l v - l0) ^ 2 * a2 / (2 * (S v / S0))| ≤ δ₀ ^ 2 * a2 / (2 * (1 - ε₀)) := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg ha2,
        abs_of_pos (by have := hrp v; positivity)]
      have hsq : (l v - l0) ^ 2 ≤ δ₀ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hwl v) 2
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hsq ha2) (by positivity)
        (by linarith [hr1 v])
    have hn0 : (0 : ℝ) ≤ n / 2 := by positivity
    calc |-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
          (l v - l0) ^ 2 * a2 / (2 * (S v / S0))|
        ≤ |-(n / 2) * log (S v / S0)| + |n / 2 * (1 - 1 / (S v / S0))| +
          |(l v - l0) ^ 2 * a2 / (2 * (S v / S0))| := by
          have := abs_add_le (-(n / 2 : ℝ) * log (S v / S0)) (n / 2 * (1 - 1 / (S v / S0)))
          have := abs_sub (-(n / 2 : ℝ) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)))
            ((l v - l0) ^ 2 * a2 / (2 * (S v / S0)))
          linarith
      _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hn0]
          gcongr
  have iA := ibd pm mA bA
  have iB := ibd pm mB bB
  have iC := ibd pm mC bC
  -- the log-density
  set L : V → ℝ := fun v => log (gdN (muN c l0 S0 (l v)) (S v / S0) z) with hL
  have hLe : ∀ v, L v = A v + 1 / 2 * Bf v * (S2 - n) + Cf v * D1 := fun v => by
    simp only [hL, hA, hBf, hCf]
    rw [log_gdN_muN c hS0 (l v) (S v) (hSp v) z]
    ring
  have mL : Measurable L := by
    have e : L = fun v => A v + 1 / 2 * Bf v * (S2 - n) + Cf v * D1 := funext hLe
    rw [e]; exact (mA.add ((measurable_const.mul mB).mul_const _)).add (mC.mul_const _)
  have bL : ∀ v, |L v| ≤ (n / 2 * (ε₀ / (1 - ε₀)) + n / 2 * (ε₀ / (1 - ε₀)) +
      δ₀ ^ 2 * a2 / (2 * (1 - ε₀))) + 1 / 2 * (ε₀ / (1 - ε₀)) * |S2 - n| +
      δ₀ / (1 - ε₀) * |D1| := fun v => by
    rw [hLe v]
    calc |A v + 1 / 2 * Bf v * (S2 - n) + Cf v * D1|
        ≤ |A v| + |1 / 2 * Bf v * (S2 - n)| + |Cf v * D1| := by
          have := abs_add_le (A v) (1 / 2 * Bf v * (S2 - n))
          have := abs_add_le (A v + 1 / 2 * Bf v * (S2 - n)) (Cf v * D1)
          linarith
      _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
          gcongr
          · exact bA v
          · exact bB v
          · exact bC v
  have iL := ibd pm mL bL
  have hint : ∫ v, L v ∂pm = (∫ v, A v ∂pm) + 1 / 2 * (∫ v, Bf v ∂pm) * (S2 - n) +
      (∫ v, Cf v ∂pm) * D1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hLe)]
    have i2 : Integrable (fun v => 1 / 2 * Bf v * (S2 - n)) pm := (iB.const_mul _).mul_const _
    have i3 : Integrable (fun v => Cf v * D1) pm := iC.mul_const _
    rw [integral_add (f := fun v => A v + 1 / 2 * Bf v * (S2 - n)) (g := fun v => Cf v * D1)
      (iA.add i2) i3, integral_add (f := A) (g := fun v => 1 / 2 * Bf v * (S2 - n)) iA i2,
      integral_mul_const, integral_mul_const, integral_const_mul]
  -- Jensen
  have hg : ∀ v, gdN (muN c l0 S0 (l v)) (S v / S0) z = exp (L v) := fun v =>
    (exp_log (gdN_pos (hrp v) _ z)).symm
  have iE : Integrable (fun v => exp (L v)) pm := by
    refine ibd pm (mL.exp) (M := exp ((n / 2 * (ε₀ / (1 - ε₀)) + n / 2 * (ε₀ / (1 - ε₀)) +
      δ₀ ^ 2 * a2 / (2 * (1 - ε₀))) + 1 / 2 * (ε₀ / (1 - ε₀)) * |S2 - n| +
      δ₀ / (1 - ε₀) * |D1|)) fun v => ?_
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr ((le_abs_self _).trans (bL v))
  have hJ := (convexOn_exp).map_integral_le (μ := pm) (f := L) continuousOn_exp isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) iL iE
  rw [hint] at hJ
  simp_rw [hg]
  exact hJ

/-- **The coefficients of the averaged log-density** (Lemma HQ, step (iii)). -/
theorem mix_coef_bounds {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ} (hl : Measurable l) (hS : Measurable S)
    {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1) (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (hml : ∫ v, (l v - l0) ∂pm = 0) (hmS : ∫ v, (S v / S0 - 1) ∂pm = 0) :
    |∫ v, (-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
          (l v - l0) ^ 2 * (normSq c / S0) / (2 * (S v / S0))) ∂pm| ≤
        n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) * (∫ v, (S v / S0 - 1) ^ 2 ∂pm) +
          (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) / (2 * (1 - ε₀)) ∧
      (∫ v, (1 - 1 / (S v / S0)) ∂pm) ^ 2 ≤ (∫ v, (S v / S0 - 1) ^ 2 ∂pm) ^ 2 / (1 - ε₀) ^ 2 ∧
      normSq c / S0 * (∫ v, (l v - l0) / (S v / S0) ∂pm) ^ 2 ≤
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) * (∫ v, (S v / S0 - 1) ^ 2 ∂pm) /
          (1 - ε₀) ^ 2 := by
  have : Nonempty V := nonempty_of_isProbabilityMeasure pm
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans (hwS (Classical.arbitrary V))
  have hδ0 : 0 ≤ δ₀ := (abs_nonneg _).trans (hwl (Classical.arbitrary V))
  have hd : 0 < 1 - ε₀ := by linarith
  have hr1 : ∀ v, 1 - ε₀ ≤ S v / S0 := fun v => by have := (abs_le.mp (hwS v)).1; linarith
  have hrp : ∀ v, 0 < S v / S0 := fun v => lt_of_lt_of_le hd (hr1 v)
  set a2 := normSq c / S0 with ha2d
  have ha2 : 0 ≤ a2 := div_nonneg (normSq_nonneg c) hS0.le
  set x : V → ℝ := fun v => S v / S0 - 1 with hx
  set δ : V → ℝ := fun v => l v - l0 with hδ
  have mr : Measurable (fun v => S v / S0) := hS.div_const S0
  have mx : Measurable x := mr.sub_const 1
  have mδ : Measurable δ := hl.sub_const l0
  have bx : ∀ v, |x v| ≤ ε₀ := hwS
  have bδ : ∀ v, |δ v| ≤ δ₀ := hwl
  have bx2 : ∀ v, |x v ^ 2| ≤ ε₀ ^ 2 := fun v => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bx v) 2
  have bδ2 : ∀ v, |a2 * δ v ^ 2| ≤ a2 * δ₀ ^ 2 := fun v => by
    rw [abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ ha2
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bδ v) 2
  have iX : Integrable (fun v => x v ^ 2) pm := ibd pm (mx.pow_const 2) bx2
  have iY : Integrable (fun v => a2 * δ v ^ 2) pm := ibd pm (measurable_const.mul (mδ.pow_const 2)) bδ2
  have er : ∀ v, S v / S0 = 1 + x v := fun v => by simp only [hx]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- the constant term
    have hpt : ∀ v, |-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
        (l v - l0) ^ 2 * a2 / (2 * (S v / S0))| ≤
        n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) * x v ^ 2 + a2 * δ v ^ 2 / (2 * (1 - ε₀)) := by
      intro v
      have e1 : -(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
          (l v - l0) ^ 2 * a2 / (2 * (S v / S0)) =
          -(n / 2) * (log (1 + x v) - x v / (1 + x v)) - a2 * δ v ^ 2 / (2 * (1 + x v)) := by
        rw [er v]
        have : (1 + x v) ≠ 0 := by rw [← er v]; exact (hrp v).ne'
        simp only [hδ]
        field_simp
        ring
      rw [e1]
      have h1 := log_sub_frac (bx v) hε₀
      have h2 : |a2 * δ v ^ 2 / (2 * (1 + x v))| ≤ a2 * δ v ^ 2 / (2 * (1 - ε₀)) := by
        have hp : 0 < 1 + x v := by rw [← er v]; exact hrp v
        rw [abs_div, abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        have := hr1 v; rw [er v] at this; linarith
      have hn0 : (0 : ℝ) ≤ n / 2 := by positivity
      calc |-(n / 2) * (log (1 + x v) - x v / (1 + x v)) - a2 * δ v ^ 2 / (2 * (1 + x v))|
          ≤ |-(n / 2) * (log (1 + x v) - x v / (1 + x v))| + |a2 * δ v ^ 2 / (2 * (1 + x v))| :=
            abs_sub _ _
        _ ≤ n / 2 * (x v ^ 2 * ((1 + 3 * ε₀) / (2 * (1 - ε₀)))) + a2 * δ v ^ 2 / (2 * (1 - ε₀)) := by
            rw [abs_mul, abs_neg, abs_of_nonneg hn0]
            gcongr
        _ = _ := by field_simp; ring
    have iR : Integrable (fun v => n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) * x v ^ 2 +
        a2 * δ v ^ 2 / (2 * (1 - ε₀))) pm := (iX.const_mul _).add (iY.div_const _)
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => abs_nonneg _) iR
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_add (iX.const_mul _) (iY.div_const _), integral_const_mul, integral_div]
  · -- the coefficient of `|z|² − n`
    have hpt : ∀ v, 1 - 1 / (S v / S0) = x v - x v ^ 2 / (S v / S0) := fun v => by
      rw [er v]
      have : (1 + x v) ≠ 0 := by rw [← er v]; exact (hrp v).ne'
      field_simp; ring
    have bq : ∀ v, |x v ^ 2 / (S v / S0)| ≤ ε₀ ^ 2 / (1 - ε₀) := fun v => by
      rw [abs_div, abs_of_pos (hrp v)]
      exact div_le_div₀ (sq_nonneg _) (bx2 v) hd (hr1 v)
    have iq : Integrable (fun v => x v ^ 2 / (S v / S0)) pm :=
      ibd pm ((mx.pow_const 2).div mr) bq
    have ix : Integrable x pm := ibd pm mx bx
    have e : ∫ v, (1 - 1 / (S v / S0)) ∂pm = -∫ v, x v ^ 2 / (S v / S0) ∂pm := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub ix iq]
      have : ∫ v, x v ∂pm = 0 := hmS
      rw [this]; ring
    rw [e, neg_sq]
    have h0 : 0 ≤ ∫ v, x v ^ 2 / (S v / S0) ∂pm :=
      integral_nonneg fun v => div_nonneg (sq_nonneg _) (hrp v).le
    have h1 : ∫ v, x v ^ 2 / (S v / S0) ∂pm ≤ (∫ v, x v ^ 2 ∂pm) / (1 - ε₀) := by
      rw [← integral_div]
      refine integral_mono iq (iX.div_const _) fun v => ?_
      exact div_le_div_of_nonneg_left (sq_nonneg _) hd (hr1 v)
    have := pow_le_pow_left₀ h0 h1 2
    rw [div_pow] at this
    exact this
  · -- the coefficient of `⟨u, z⟩`
    have hpt : ∀ v, (l v - l0) / (S v / S0) = δ v - δ v * (x v / (S v / S0)) := fun v => by
      rw [er v]
      have : (1 + x v) ≠ 0 := by rw [← er v]; exact (hrp v).ne'
      simp only [hδ]
      field_simp; ring
    have bq : ∀ v, |x v / (S v / S0)| ≤ ε₀ / (1 - ε₀) := fun v => by
      rw [abs_div, abs_of_pos (hrp v)]
      exact div_le_div₀ hε0 (bx v) hd (hr1 v)
    have mq : Measurable (fun v => x v / (S v / S0)) := mx.div mr
    have iq : Integrable (fun v => x v / (S v / S0)) pm := ibd pm mq bq
    have iδ : Integrable δ pm := ibd pm mδ bδ
    have iδq : Integrable (fun v => δ v * (x v / (S v / S0))) pm :=
      ibd pm (mδ.mul mq) (M := δ₀ * (ε₀ / (1 - ε₀))) fun v => by
        rw [abs_mul]; exact mul_le_mul (bδ v) (bq v) (abs_nonneg _) hδ0
    have e : ∫ v, (l v - l0) / (S v / S0) ∂pm = -∫ v, δ v * (x v / (S v / S0)) ∂pm := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub iδ iδq]
      have : ∫ v, δ v ∂pm = 0 := hml
      rw [this]; ring
    rw [e, neg_sq]
    have iδ2 : Integrable (fun v => δ v ^ 2) pm := ibd pm (mδ.pow_const 2) (M := δ₀ ^ 2) fun v => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bδ v) 2
    have iq2 : Integrable (fun v => (x v / (S v / S0)) ^ 2) pm :=
      ibd pm (mq.pow_const 2) (M := (ε₀ / (1 - ε₀)) ^ 2) fun v => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bq v) 2
    have hcs := BstLean.Part138.cs_sq pm iδ2 iq2 iδq
    have hq2 : ∫ v, (x v / (S v / S0)) ^ 2 ∂pm ≤ (∫ v, x v ^ 2 ∂pm) / (1 - ε₀) ^ 2 := by
      rw [← integral_div]
      refine integral_mono iq2 (iX.div_const _) fun v => ?_
      rw [div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ hd.le (hr1 v) 2)
    have hY : ∫ v, a2 * δ v ^ 2 ∂pm = a2 * ∫ v, δ v ^ 2 ∂pm := integral_const_mul _ _
    rw [hY]
    have hδ2 : 0 ≤ ∫ v, δ v ^ 2 ∂pm := integral_nonneg fun v => sq_nonneg _
    calc a2 * (∫ v, δ v * (x v / (S v / S0)) ∂pm) ^ 2
        ≤ a2 * ((∫ v, δ v ^ 2 ∂pm) * ∫ v, (x v / (S v / S0)) ^ 2 ∂pm) :=
          mul_le_mul_of_nonneg_left hcs ha2
      _ ≤ a2 * ((∫ v, δ v ^ 2 ∂pm) * ((∫ v, x v ^ 2 ∂pm) / (1 - ε₀) ^ 2)) := by gcongr
      _ = _ := by ring

/-- **Lemma HQ at the level of densities**: `R ≥ 0` a density for `γ` with
`exp(K + (b/2)(|z|² − n) + c⟨u, z⟩) ≤ R(z)` for every `z`; then
`H²(R, 1) ≤ E(R − 1)²/4 + (3/4)(|K|³/λ² + (n b² + 2|u|²c²)/(1 − λ)²)`. -/
theorem hell_hq_dens {n : ℕ} {R : (Fin n → ℝ) → ℝ} (mR : Measurable R) (R0 : ∀ z, 0 ≤ R z)
    (iR : Integrable R (stdGauss (Fin n)))
    (i2 : Integrable (fun z => (R z - 1) ^ 2) (stdGauss (Fin n))) {K bb cc lam : ℝ}
    (u : Fin n → ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hJ : ∀ z, exp (K + (1 / 2 * bb * (∑ i, z i ^ 2 - n) + cc * ∑ i, u i * z i)) ≤ R z) :
    BstLean.Part138.hellSq (stdGauss (Fin n)) R (fun _ => 1) ≤
      (∫ z, (R z - 1) ^ 2 ∂stdGauss (Fin n)) / 4 +
        3 / 4 * (|K| ^ 3 / lam ^ 2 + (n * bb ^ 2 + 2 * (∑ i, u i ^ 2) * cc ^ 2) / (1 - lam) ^ 2) := by
  set γ := stdGauss (Fin n)
  have mM : Measurable (fun z => max 0 (1 - R z) ^ 3) :=
    (measurable_const.max (measurable_const.sub mR)).pow_const 3
  have iM : Integrable (fun z => max 0 (1 - R z) ^ 3) γ := by
    refine Integrable.of_bound mM.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun z => ?_)
    have h0 : 0 ≤ max 0 (1 - R z) := le_max_left _ _
    have h1 : max 0 (1 - R z) ≤ 1 := max_le (by norm_num) (by linarith [R0 z])
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 3)]
    exact pow_le_one₀ h0 h1
  have isq : Integrable (fun z => √(R z * 1)) γ := by
    refine (iR.add (integrable_const (1 : ℝ))).mono' (mR.mul measurable_const).sqrt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
    change √(R z) ≤ R z + 1
    nlinarith [Real.sq_sqrt (R0 z), Real.sqrt_nonneg (R z), sq_nonneg (√(R z) - 1)]
  have hH : BstLean.Part138.hellSq γ R (fun _ => 1) ≤
      (∫ z, (R z - 1) ^ 2 ∂γ) / 4 + 3 / 4 * ∫ z, max 0 (1 - R z) ^ 3 ∂γ := by
    have e : BstLean.Part138.hellSq γ R (fun _ => 1) = ∫ z, R z + 1 - 2 * √(R z * 1) ∂γ := by
      unfold BstLean.Part138.hellSq
      rw [integral_sub (f := fun z => R z + 1) (g := fun z => 2 * √(R z * 1))
          (iR.add (integrable_const 1)) (isq.const_mul 2),
        integral_add (f := R) (g := fun _ => (1 : ℝ)) iR (integrable_const 1), integral_const_mul]
    rw [e, ← integral_div, ← integral_const_mul, ← integral_add (i2.div_const _) (iM.const_mul _)]
    refine integral_mono ((iR.add (integrable_const 1)).sub (isq.const_mul 2))
      ((i2.div_const _).add (iM.const_mul _)) (fun z => ?_)
    change R z + 1 - 2 * √(R z * 1) ≤ (R z - 1) ^ 2 / 4 + 3 / 4 * max 0 (1 - R z) ^ 3
    rw [mul_one]
    have h1 := Real.sq_sqrt (R0 z)
    have e1 : R z + 1 - 2 * √(R z) = (√(R z) - 1) ^ 2 := by nlinarith
    rw [e1]
    exact hq_point (R0 z)
  obtain ⟨iW, hW⟩ := gauss_W_sq (ι := Fin n)
  obtain ⟨iD, hD⟩ := gauss_dot_sq u
  rw [Fintype.card_fin] at iW hW
  have iF : Integrable (fun z : Fin n → ℝ => |K| ^ 3 / lam ^ 2 +
      (bb ^ 2 / 2 * (∑ i, z i ^ 2 - n) ^ 2 + 2 * cc ^ 2 * (∑ i, u i * z i) ^ 2) / (1 - lam) ^ 2) γ :=
    (integrable_const _).add ((((iW.const_mul _)).add (iD.const_mul _)).div_const _)
  have hpt : ∀ z, max 0 (1 - R z) ^ 3 ≤ |K| ^ 3 / lam ^ 2 +
      (bb ^ 2 / 2 * (∑ i, z i ^ 2 - n) ^ 2 + 2 * cc ^ 2 * (∑ i, u i * z i) ^ 2) / (1 - lam) ^ 2 :=
    fun z => by
      refine (cubic_point (R0 z) (hJ z) hl0 hl1).trans ?_
      have hd : 0 < (1 - lam) ^ 2 := by have : 0 < 1 - lam := by linarith
                                        positivity
      have : (1 / 2 * bb * (∑ i, z i ^ 2 - n) + cc * ∑ i, u i * z i) ^ 2 ≤
          bb ^ 2 / 2 * (∑ i, z i ^ 2 - n) ^ 2 + 2 * cc ^ 2 * (∑ i, u i * z i) ^ 2 := by
        nlinarith [sq_nonneg (1 / 2 * bb * (∑ i, z i ^ 2 - n) - cc * ∑ i, u i * z i)]
      have := div_le_div_of_nonneg_right this hd.le
      linarith
  have hC : ∫ z, max 0 (1 - R z) ^ 3 ∂γ ≤ |K| ^ 3 / lam ^ 2 +
      (n * bb ^ 2 + 2 * (∑ i, u i ^ 2) * cc ^ 2) / (1 - lam) ^ 2 := by
    refine (integral_mono iM iF hpt).trans (le_of_eq ?_)
    have i3 : Integrable (fun z : Fin n → ℝ => bb ^ 2 / 2 * (∑ i, z i ^ 2 - n) ^ 2) γ :=
      iW.const_mul _
    have i4 : Integrable (fun z : Fin n → ℝ => 2 * cc ^ 2 * (∑ i, u i * z i) ^ 2) γ :=
      iD.const_mul _
    have i5 : Integrable (fun z : Fin n → ℝ => (bb ^ 2 / 2 * (∑ i, z i ^ 2 - n) ^ 2 +
        2 * cc ^ 2 * (∑ i, u i * z i) ^ 2) / (1 - lam) ^ 2) γ := (i3.add i4).div_const _
    rw [integral_add (integrable_const _) i5, integral_const, integral_div,
      integral_add (f := fun z : Fin n → ℝ => bb ^ 2 / 2 * (∑ i, z i ^ 2 - n) ^ 2)
        (g := fun z : Fin n → ℝ => 2 * cc ^ 2 * (∑ i, u i * z i) ^ 2) i3 i4,
      integral_const_mul, integral_const_mul, hW, hD]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  linarith

/-- The arithmetic of the last step of `mix_root_hq`. -/
lemma hq_tail {n : ℕ} {K bb cc a2 X Yd ε₀ lam κ : ℝ} (hK : |K| ≤ n * κ * X + Yd / (2 * (1 - ε₀)))
    (hb : bb ^ 2 ≤ X ^ 2 / (1 - ε₀) ^ 2) (hc : a2 * cc ^ 2 ≤ Yd * X / (1 - ε₀) ^ 2) :
    |K| ^ 3 / lam ^ 2 + (n * bb ^ 2 + 2 * a2 * cc ^ 2) / (1 - lam) ^ 2 ≤
      (n * κ * X + Yd / (2 * (1 - ε₀))) ^ 3 / lam ^ 2 +
        (n * X ^ 2 + 2 * X * Yd) / ((1 - ε₀) ^ 2 * (1 - lam) ^ 2) := by
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have hKh : |K| ^ 3 ≤ (n * κ * X + Yd / (2 * (1 - ε₀))) ^ 3 := pow_le_pow_left₀ hK0 hK 3
  have hY : n * bb ^ 2 + 2 * a2 * cc ^ 2 ≤ (n * X ^ 2 + 2 * X * Yd) / (1 - ε₀) ^ 2 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : n * bb ^ 2 ≤ n * (X ^ 2 / (1 - ε₀) ^ 2) := mul_le_mul_of_nonneg_left hb hn0
    have : (n * X ^ 2 + 2 * X * Yd) / (1 - ε₀) ^ 2 =
        n * (X ^ 2 / (1 - ε₀) ^ 2) + 2 * (Yd * X / (1 - ε₀) ^ 2) := by ring
    rw [this]; linarith
  rw [show (n * X ^ 2 + 2 * X * Yd) / ((1 - ε₀) ^ 2 * (1 - lam) ^ 2) =
    (n * X ^ 2 + 2 * X * Yd) / (1 - ε₀) ^ 2 / (1 - lam) ^ 2 by rw [div_div]]
  gcongr

/-- **Lemma HQ for a location-scale Gaussian mixture on one event.** -/
theorem mix_root_hq {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ}
    (hl : Measurable l) (hS : Measurable S) {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1)
    (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (hml : ∫ v, (l v - l0) ∂pm = 0) (hmS : ∫ v, (S v / S0 - 1) ∂pm = 0)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    (√(∫ v, gP B (l v • c) (S v) ∂pm) - √(gP B (l0 • c) S0)) ^ 2 ≤
      (∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1) (l w.2 - l0) (S w.2 / S0 - 1)
        ∂(pm.prod pm) - 1) / 4 +
      3 / 4 * ((n * ((1 + 3 * ε₀) / (4 * (1 - ε₀))) * (∫ v, (S v / S0 - 1) ^ 2 ∂pm) +
          (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) / (2 * (1 - ε₀))) ^ 3 / lam ^ 2 +
        (n * (∫ v, (S v / S0 - 1) ^ 2 ∂pm) ^ 2 +
          2 * (∫ v, (S v / S0 - 1) ^ 2 ∂pm) * (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm)) /
          ((1 - ε₀) ^ 2 * (1 - lam) ^ 2)) := by
  set γ := stdGauss (Fin n)
  have : Nonempty V := nonempty_of_isProbabilityMeasure pm
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans (hwS (Classical.arbitrary V))
  have hr : ∀ v, 0 < S v / S0 := fun v => by
    have := (abs_le.mp (hwS v)).1; linarith
  have hSp : ∀ v, 0 < S v := fun v => by
    have := hr v; rwa [div_pos_iff_of_pos_right hS0] at this
  set mu : V → Fin n → ℝ := fun v => muN c l0 S0 (l v) with hmu
  set r : V → ℝ := fun v => S v / S0 with hrd
  have mmu : Measurable mu := by
    simp only [hmu, muN]
    exact (measurable_const (a := (√S0)⁻¹)).smul ((hl.sub_const l0).smul_const c)
  have mr : Measurable r := hS.div_const S0
  set g : V → (Fin n → ℝ) → ℝ := fun v z => gdN (mu v) (r v) z with hg
  have mg : Measurable (Function.uncurry g) :=
    measurable_gdN_joint.comp (((mmu.comp measurable_fst).prodMk (mr.comp measurable_fst)).prodMk
      measurable_snd)
  have g0 : ∀ v z, 0 ≤ g v z := fun v z => gdN_nonneg _ _ _
  have ig : ∀ v, Integrable (g v) γ := fun v => integrable_gdN _ (hr v)
  have ig1 : ∀ v, ∫ z, g v z ∂γ = 1 := fun v => integral_gdN _ (hr v)
  -- the single product
  have iG : Integrable (Function.uncurry g) (pm.prod γ) := by
    refine (integrable_prod_iff mg.aestronglyMeasurable).mpr ⟨Filter.Eventually.of_forall ig, ?_⟩
    have e : (fun v => ∫ z, ‖Function.uncurry g (v, z)‖ ∂γ) = fun _ => (1 : ℝ) := by
      funext v
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (g0 v _)]
      exact ig1 v
    rw [e]; exact integrable_const _
  set R : (Fin n → ℝ) → ℝ := fun z => ∫ v, g v z ∂pm with hR
  have mR : Measurable R := mg.stronglyMeasurable.integral_prod_left.measurable
  have R0 : ∀ z, 0 ≤ R z := fun z => integral_nonneg fun v => g0 v z
  have iR : Integrable R γ := iG.integral_prod_right
  have intR : ∫ z, R z ∂γ = 1 := by
    simp only [hR]
    rw [← integral_integral_swap iG]
    simp [ig1]
  -- the event
  set B' : Set (Fin n → ℝ) := {z | l0 • c + √S0 • z ∈ B} with hB'
  have mB' : MeasurableSet B' := ((measurable_const_smul (√S0)).const_add (l0 • c)) hB
  have hP : ∫ v, gP B (l v • c) (S v) ∂pm = ∫ z, B'.indicator 1 z * R z ∂γ := by
    have e1 : ∀ v, gP B (l v • c) (S v) = ∫ z, B'.indicator 1 z * g v z ∂γ := fun v =>
      gP_eq_dens c hB hS0 (l v) (S v) (hSp v)
    simp_rw [e1]
    have iH : Integrable (Function.uncurry fun v z => B'.indicator (1 : (Fin n → ℝ) → ℝ) z * g v z)
        (pm.prod γ) := by
      refine iG.mono' ((measurable_one.indicator mB').comp measurable_snd |>.mul mg).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      change ‖B'.indicator (1 : (Fin n → ℝ) → ℝ) p.2 * g p.1 p.2‖ ≤ g p.1 p.2
      rw [Real.norm_eq_abs]
      by_cases h : p.2 ∈ B'
      · simp [h, abs_of_nonneg (g0 p.1 p.2)]
      · simp [h, g0 p.1 p.2]
    rw [integral_integral_swap iH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hR]
    rw [integral_const_mul]
  have hQ : gP B (l0 • c) S0 = ∫ z, B'.indicator 1 z * (fun _ => (1 : ℝ)) z ∂γ := by
    simp only [mul_one]
    rw [integral_indicator_one mB']
    rfl
  have hroot := root_dens_le γ (p := R) (q := fun _ => (1 : ℝ)) mR measurable_const R0
    (fun _ => zero_le_one) iR (integrable_const 1) mB'
  rw [← hP, ← hQ] at hroot
  -- the two-copy product
  set F : (V × V) × (Fin n → ℝ) → ℝ := fun p => g p.1.1 p.2 * g p.1.2 p.2 with hF
  have mF : Measurable F :=
    (mg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (mg.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hDw : ∀ w : V × V, 0 < 1 - (S w.1 / S0 - 1) * (S w.2 / S0 - 1) := fun w => by
    have h1 := hwS w.1
    have h2 := hwS w.2
    have : |(S w.1 / S0 - 1) * (S w.2 / S0 - 1)| ≤ ε₀ ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hε0
    have := (abs_le.mp this).2
    nlinarith
  have tw : ∀ w : V × V, Integrable (fun z => F (w, z)) γ ∧ ∫ z, F (w, z) ∂γ =
      kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1) (l w.2 - l0) (S w.2 / S0 - 1) :=
    fun w => twocopy_kTwo c hS0 (l w.1) (l w.2) (S w.1) (S w.2) (hSp _) (hSp _) (hDw w)
  set M := (√(1 - ε₀ ^ 2))⁻¹ ^ n * exp ((1 + ε₀) * (normSq c / S0) * δ₀ ^ 2 / (1 - ε₀ ^ 2))
  have hK : ∀ w : V × V, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1) (l w.2 - l0)
      (S w.2 / S0 - 1) ≤ M := fun w =>
    kTwo_le n (div_nonneg (normSq_nonneg c) hS0.le) hε₀ (hwS _) (hwS _) (hwl _) (hwl _)
  have mK : Measurable (fun w : V × V => kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
      (l w.2 - l0) (S w.2 / S0 - 1)) := by
    refine (measurable_kTwo n).comp (measurable_const.prodMk
      (((hl.comp measurable_fst).sub_const l0).prodMk ((hS.comp measurable_fst).div_const S0 |>.sub_const 1)
        |>.prodMk (((hl.comp measurable_snd).sub_const l0).prodMk
          ((hS.comp measurable_snd).div_const S0 |>.sub_const 1))))
  have iK : Integrable (fun w : V × V => kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
      (l w.2 - l0) (S w.2 / S0 - 1)) (pm.prod pm) :=
    Integrable.of_bound mK.aestronglyMeasurable M (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (kTwo_nonneg _ _ _ _ _ _)]; exact hK w)
  have F0 : ∀ p, 0 ≤ F p := fun p => mul_nonneg (g0 _ _) (g0 _ _)
  have iF : Integrable F ((pm.prod pm).prod γ) := by
    refine (integrable_prod_iff mF.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall fun w => (tw w).1, ?_⟩
    have e : (fun w => ∫ z, ‖F (w, z)‖ ∂γ) = fun w =>
        kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1) (l w.2 - l0) (S w.2 / S0 - 1) := by
      funext w
      simp only [Real.norm_eq_abs, abs_of_nonneg (F0 _)]
      exact (tw w).2
    rw [e]; exact iK
  have hR2 : ∀ z, R z ^ 2 = ∫ w, F (w, z) ∂(pm.prod pm) := fun z => by
    simp only [hF, hR]
    rw [integral_prod_mul (fun v => g v z) (fun v => g v z)]
    ring
  have iR2 : Integrable (fun z => R z ^ 2) γ := by
    simp_rw [hR2]; exact iF.integral_prod_right
  have intR2 : ∫ z, R z ^ 2 ∂γ = ∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
      (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) := by
    simp_rw [hR2]
    rw [← integral_integral_swap (f := fun w z => F (w, z)) iF]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => (tw w).2)
  have i2 : Integrable (fun z => (R z - 1) ^ 2) γ := by
    have e : (fun z => (R z - 1) ^ 2) = fun z => R z ^ 2 - 2 * R z + 1 := by funext z; ring
    rw [e]; exact (iR2.sub (iR.const_mul 2)).add (integrable_const 1)
  have chi_identity : ∫ z, (R z - 1) ^ 2 ∂γ = ∫ w, kTwo n (normSq c / S0) (l w.1 - l0)
      (S w.1 / S0 - 1) (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1 := by
    have e : (fun z => (R z - 1) ^ 2) = fun z => R z ^ 2 - 2 * R z + 1 := by funext z; ring
    rw [e, integral_add (f := fun z => R z ^ 2 - 2 * R z) (g := fun _ => (1 : ℝ))
      (iR2.sub (iR.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun z => R z ^ 2) (g := fun z => 2 * R z) iR2 (iR.const_mul 2),
      integral_const_mul, intR, intR2]
    simp
    ring
  -- Lemma HQ
  obtain ⟨hK, hb, hc⟩ := mix_coef_bounds pm c hS0 hl hS hε₀ hwS hwl hml hmS
  set u : Fin n → ℝ := fun i => (√S0)⁻¹ * c i with hu
  have hu2 : ∑ i, u i ^ 2 = normSq c / S0 := by
    simp only [hu]
    unfold normSq
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, inv_pow, Real.sq_sqrt hS0.le]; ring
  have hJ : ∀ z, exp ((∫ v, (-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
        (l v - l0) ^ 2 * (normSq c / S0) / (2 * (S v / S0))) ∂pm) +
      (1 / 2 * (∫ v, (1 - 1 / (S v / S0)) ∂pm) * (∑ i, z i ^ 2 - n) +
        (∫ v, (l v - l0) / (S v / S0) ∂pm) * ∑ i, u i * z i)) ≤ R z := fun z => by
    have h := jensen_mix pm c hS0 hl hS hε₀ hwS hwl z
    simp only [hu, ← add_assoc]
    exact h
  have hH := hell_hq_dens mR R0 iR i2 u hl0 hl1 hJ
  rw [chi_identity, hu2] at hH
  refine hroot.trans (hH.trans ?_)
  gcongr ?_ / 4 + 3 / 4 * ?_
  · exact le_refl _
  · exact hq_tail hK hb hc

end mix

end BstLean.Part180
