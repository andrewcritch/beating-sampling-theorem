import BstLean.Part183Def

/-!
# Part 183 (file `EnA`): support lemmas for the centred energy bound (`Qvar`)

No proof is left open; no `native_decide` or `axiom` is used.

* `lip_mom8`: `E S⁸ ≤ (√(E S²) + c₈L)⁸` for `S ≥ 0` Euclidean `L`-Lipschitz (`c₈ = 1.8π/2`).
* `sqrtQvar_euLip`: `√Qvar(matOf t ξ)` is `√(t K2)`-Lipschitz in `ξ` (`|a(v)|² ≤ K2`);
  `Qvar_nonneg`, `Qvar_eq` (variance form), `tri_L2`, `var_eq`.
* `Qvar_mean` (Jensen `E_v ReLU(z·a(v)) ≥ ReLU(z·ā)`): `E_ξ Qvar ≤ m t E_v|a − ā|²/2`;
  `gauss_relu_sq`: `E ReLU(⟨ξ,u⟩)² = |u|²/2`.
* `trCov_lat`: `E_v|aLat − ā|² ≤ (1 − s²)·n·O²/(n − 2)` on `OpB (A1 c) O` (sphere Poincaré per row,
  `‖A₁‖_F² ≤ nO²`).
* `Qvar_mom4`, `Qvar_mom4_gm`: `E Qvar⁴ ≤ (√(m t T/2) + c₈√(t K2))⁸` if `E_v|a − ā|² ≤ T`.
-/

namespace BstLean.Part183

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip)
open BstLean.Part170 (int_comp_bdd vmean matOf int_cs relu_lip)
open BstLean.Part162 (gmom gmom_nonneg poincare_p_lint)
open BstLean.Part151 (gradSq gradSq_le gradSq_nonneg)

section L2
variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ] {m : ℕ}

/-- `E f² − (E f)² = E(f − Ef)²`. -/
lemma var_eq {f : V → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun v => f v ^ 2) μ) :
    ∫ v, f v ^ 2 ∂μ - (∫ v, f v ∂μ) ^ 2 = ∫ v, (f v - ∫ w, f w ∂μ) ^ 2 ∂μ := by
  set c := ∫ w, f w ∂μ
  have e : (fun v => (f v - c) ^ 2) = fun v => f v ^ 2 - 2 * c * f v + c ^ 2 := by
    funext v; ring
  rw [e, integral_add (f := fun v => f v ^ 2 - 2 * c * f v) (g := fun _ => c ^ 2)
    (hf2.sub (hf.const_mul _)) (integrable_const _),
    integral_sub (f := fun v => f v ^ 2) (g := fun v => 2 * c * f v) hf2 (hf.const_mul _),
    integral_const_mul, integral_const]
  simp; ring

/-- Triangle inequality in `L²(μ)^m`. -/
lemma tri_L2 (F G : Fin m → V → ℝ) (hF : ∀ j, Integrable (fun v => F j v ^ 2) μ)
    (hG : ∀ j, Integrable (fun v => G j v ^ 2) μ) (hFG : ∀ j, Integrable (fun v => F j v * G j v) μ) :
    √(∑ j, ∫ v, (F j v + G j v) ^ 2 ∂μ) ≤
      √(∑ j, ∫ v, F j v ^ 2 ∂μ) + √(∑ j, ∫ v, G j v ^ 2 ∂μ) := by
  set P := ∑ j, ∫ v, F j v ^ 2 ∂μ
  set Q := ∑ j, ∫ v, G j v ^ 2 ∂μ
  set X := ∑ j, ∫ v, F j v * G j v ∂μ
  have hP : 0 ≤ P := Finset.sum_nonneg fun j _ => integral_nonneg fun v => sq_nonneg _
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun j _ => integral_nonneg fun v => sq_nonneg _
  have hX : X ≤ √P * √Q := by
    have h1 : X ≤ ∑ j, √(∫ v, F j v ^ 2 ∂μ) * √(∫ v, G j v ^ 2 ∂μ) :=
      Finset.sum_le_sum fun j _ => int_cs (hF j) (hG j) (hFG j)
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => √(∫ v, F j v ^ 2 ∂μ))
      (fun j => √(∫ v, G j v ^ 2 ∂μ))
    have e1 : ∑ j, √(∫ v, F j v ^ 2 ∂μ) ^ 2 = P :=
      Finset.sum_congr rfl fun j _ => Real.sq_sqrt (integral_nonneg fun v => sq_nonneg _)
    have e2 : ∑ j, √(∫ v, G j v ^ 2 ∂μ) ^ 2 = Q :=
      Finset.sum_congr rfl fun j _ => Real.sq_sqrt (integral_nonneg fun v => sq_nonneg _)
    rw [e1, e2] at h2
    exact h1.trans h2
  have hS : ∑ j, ∫ v, (F j v + G j v) ^ 2 ∂μ = P + 2 * X + Q := by
    simp only [P, Q, X]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul, ← integral_add (hF j) ((hFG j).const_mul 2),
      ← integral_add (f := fun v => F j v ^ 2 + 2 * (F j v * G j v)) (g := fun v => G j v ^ 2)
        ((hF j).add ((hFG j).const_mul 2)) (hG j)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)
  rw [hS, Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt hP
  have := Real.sq_sqrt hQ
  nlinarith [Real.sqrt_nonneg P, Real.sqrt_nonneg Q]

lemma Qvar_eq {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (M : Matrix (Fin m) (Fin m) ℝ) :
    Qvar μ a M = ∑ j, ∫ v, (relu ((M *ᵥ a v) j) - ∫ w, relu ((M *ᵥ a w) j) ∂μ) ^ 2 ∂μ := by
  unfold Qvar
  refine Finset.sum_congr rfl fun j _ => ?_
  have c1 : Continuous (fun y : Fin m → ℝ => relu ((M *ᵥ y) j)) :=
    BstLean.Part130.continuous_relu.comp ((continuous_apply j).comp
      (Continuous.matrix_mulVec continuous_const continuous_id))
  exact var_eq (int_comp_bdd ha hK c1) (int_comp_bdd ha hK (c1.pow 2))

lemma Qvar_nonneg {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (M : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ Qvar μ a M := by
  rw [Qvar_eq ha hK]
  exact Finset.sum_nonneg fun j _ => integral_nonneg fun v => sq_nonneg _

/-- **`√Qvar` is Euclidean Lipschitz** in the standard coordinates of the full matrix, with
constant `√(t K2)`. -/
theorem sqrtQvar_euLip {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {K2 : ℝ} (hK2 : ∀ v, normSq (a v) ≤ K2) {t : ℝ} (ht : 0 ≤ t) :
    EuLip (fun ξ : Fin m × Fin m → ℝ => √(Qvar μ a (matOf t ξ))) (√(t * K2)) := by
  -- the one-sided bound
  have key : ∀ ξ ξ' : Fin m × Fin m → ℝ, √(Qvar μ a (matOf t ξ)) ≤
      √(Qvar μ a (matOf t ξ')) + √(t * K2) * √(∑ i, (ξ i - ξ' i) ^ 2) := by
    intro ξ ξ'
    set R : Fin m → V → ℝ := fun j v => relu ((matOf t ξ *ᵥ a v) j)
    set R' : Fin m → V → ℝ := fun j v => relu ((matOf t ξ' *ᵥ a v) j)
    have cR : ∀ (N : Matrix (Fin m) (Fin m) ℝ) j,
        Continuous (fun y : Fin m → ℝ => relu ((N *ᵥ y) j)) := fun N j =>
      BstLean.Part130.continuous_relu.comp ((continuous_apply j).comp
        (Continuous.matrix_mulVec continuous_const continuous_id))
    set c : Fin m → ℝ := fun j => ∫ w, R j w ∂μ
    set c' : Fin m → ℝ := fun j => ∫ w, R' j w ∂μ
    set F : Fin m → V → ℝ := fun j v => R' j v - c' j
    set G : Fin m → V → ℝ := fun j v => (R j v - c j) - (R' j v - c' j)
    have iR : ∀ j, Integrable (R j) μ := fun j => int_comp_bdd ha hK (cR _ j)
    have iR' : ∀ j, Integrable (R' j) μ := fun j => int_comp_bdd ha hK (cR _ j)
    have iF2 : ∀ j, Integrable (fun v => F j v ^ 2) μ := fun j =>
      int_comp_bdd (f := fun y => (relu ((matOf t ξ' *ᵥ y) j) - c' j) ^ 2) ha hK
        (((cR _ j).sub continuous_const).pow 2)
    have iG2 : ∀ j, Integrable (fun v => G j v ^ 2) μ := fun j =>
      int_comp_bdd (f := fun y => ((relu ((matOf t ξ *ᵥ y) j) - c j) -
        (relu ((matOf t ξ' *ᵥ y) j) - c' j)) ^ 2) ha hK
        ((((cR _ j).sub continuous_const).sub ((cR _ j).sub continuous_const)).pow 2)
    have iFG : ∀ j, Integrable (fun v => F j v * G j v) μ := fun j =>
      int_comp_bdd (f := fun y => (relu ((matOf t ξ' *ᵥ y) j) - c' j) *
        ((relu ((matOf t ξ *ᵥ y) j) - c j) - (relu ((matOf t ξ' *ᵥ y) j) - c' j))) ha hK
        (((cR _ j).sub continuous_const).mul
          (((cR _ j).sub continuous_const).sub ((cR _ j).sub continuous_const)))
    have hT := tri_L2 F G iF2 iG2 iFG
    have e1 : Qvar μ a (matOf t ξ) = ∑ j, ∫ v, (F j v + G j v) ^ 2 ∂μ := by
      rw [Qvar_eq ha hK]
      exact Finset.sum_congr rfl fun j _ => integral_congr_ae
        (Filter.Eventually.of_forall fun v => by simp only [F, G, R, c]; ring)
    have e2 : Qvar μ a (matOf t ξ') = ∑ j, ∫ v, F j v ^ 2 ∂μ := by
      rw [Qvar_eq ha hK]
    -- `Σ ∫ G² ≤ Σ ∫ (R − R')² ≤ t K2 |ξ − ξ'|²`
    have hG : ∑ j, ∫ v, G j v ^ 2 ∂μ ≤ t * K2 * ∑ i, (ξ i - ξ' i) ^ 2 := by
      have hD : ∀ j, ∫ v, G j v ^ 2 ∂μ ≤ ∫ v, (R j v - R' j v) ^ 2 ∂μ := by
        intro j
        have iD : Integrable (fun v => R j v - R' j v) μ := (iR j).sub (iR' j)
        have iD2 : Integrable (fun v => (R j v - R' j v) ^ 2) μ :=
          int_comp_bdd (f := fun y => (relu ((matOf t ξ *ᵥ y) j) - relu ((matOf t ξ' *ᵥ y) j)) ^ 2)
            ha hK (((cR _ j).sub (cR _ j)).pow 2)
        have hv := var_eq iD iD2
        have hmean : ∫ w, (R j w - R' j w) ∂μ = c j - c' j := integral_sub (iR j) (iR' j)
        have e : ∫ v, G j v ^ 2 ∂μ = ∫ v, (R j v - R' j v - ∫ w, (R j w - R' j w) ∂μ) ^ 2 ∂μ := by
          rw [hmean]
          exact integral_congr_ae (Filter.Eventually.of_forall fun v => by simp only [G]; ring)
        rw [e, ← hv]
        nlinarith [sq_nonneg (∫ v, (R j v - R' j v) ∂μ)]
      have hpt : ∀ v, ∑ j, (R j v - R' j v) ^ 2 ≤ t * K2 * ∑ i, (ξ i - ξ' i) ^ 2 := by
        intro v
        have hj : ∀ j, (R j v - R' j v) ^ 2 ≤
            t * ((∑ k, (ξ (j, k) - ξ' (j, k)) ^ 2) * normSq (a v)) := by
          intro j
          have h1 := relu_lip ((matOf t ξ *ᵥ a v) j) ((matOf t ξ' *ᵥ a v) j)
          have e : (matOf t ξ *ᵥ a v) j - (matOf t ξ' *ᵥ a v) j =
              √t * ∑ k, (ξ (j, k) - ξ' (j, k)) * a v k := by
            simp only [Matrix.mulVec, dotProduct, matOf, Matrix.of_apply, Finset.mul_sum,
              ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [e] at h1
          have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun k => ξ (j, k) - ξ' (j, k)) (fun k => a v k)
          calc (R j v - R' j v) ^ 2 = |R j v - R' j v| ^ 2 := (sq_abs _).symm
            _ ≤ |√t * ∑ k, (ξ (j, k) - ξ' (j, k)) * a v k| ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) h1 2
            _ = t * (∑ k, (ξ (j, k) - ξ' (j, k)) * a v k) ^ 2 := by
                rw [sq_abs, mul_pow, Real.sq_sqrt ht]
            _ ≤ t * ((∑ k, (ξ (j, k) - ξ' (j, k)) ^ 2) * normSq (a v)) := by
                refine mul_le_mul_of_nonneg_left ?_ ht
                unfold normSq; exact h2
        calc ∑ j, (R j v - R' j v) ^ 2
            ≤ ∑ j, t * ((∑ k, (ξ (j, k) - ξ' (j, k)) ^ 2) * normSq (a v)) :=
              Finset.sum_le_sum fun j _ => hj j
          _ = t * normSq (a v) * ∑ i, (ξ i - ξ' i) ^ 2 := by
              rw [Fintype.sum_prod_type, Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ ≤ t * K2 * ∑ i, (ξ i - ξ' i) ^ 2 := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hK2 v) ht)
                (Finset.sum_nonneg fun i _ => sq_nonneg _)
      have iD2 : ∀ j, Integrable (fun v => (R j v - R' j v) ^ 2) μ := fun j =>
        int_comp_bdd (f := fun y => (relu ((matOf t ξ *ᵥ y) j) - relu ((matOf t ξ' *ᵥ y) j)) ^ 2)
          ha hK (((cR _ j).sub (cR _ j)).pow 2)
      calc ∑ j, ∫ v, G j v ^ 2 ∂μ ≤ ∑ j, ∫ v, (R j v - R' j v) ^ 2 ∂μ :=
            Finset.sum_le_sum fun j _ => hD j
        _ = ∫ v, ∑ j, (R j v - R' j v) ^ 2 ∂μ := (integral_finsetSum _ fun j _ => iD2 j).symm
        _ ≤ ∫ _v, t * K2 * ∑ i, (ξ i - ξ' i) ^ 2 ∂μ :=
            integral_mono (integrable_finsetSum _ fun j _ => iD2 j) (integrable_const _) hpt
        _ = t * K2 * ∑ i, (ξ i - ξ' i) ^ 2 := by simp
    rw [e1, e2]
    refine hT.trans (add_le_add le_rfl ?_)
    rw [← Real.sqrt_mul' _ (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact Real.sqrt_le_sqrt hG
  intro ξ ξ'
  rw [abs_le]
  constructor
  · have := key ξ' ξ
    have e : ∑ i, (ξ' i - ξ i) ^ 2 = ∑ i, (ξ i - ξ' i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [e] at this
    linarith
  · linarith [key ξ ξ']

end L2

section L1
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The eighth moment of a nonnegative Lipschitz function**:
`E S⁸ ≤ (√(E S²) + c₈L)⁸`, `c₈ = 1.8π/2`. -/
theorem lip_mom8 {S : (ι → ℝ) → ℝ} {L : ℝ} (hL : 0 < L) (hS : EuLip S L) (hS0 : ∀ ξ, 0 ≤ S ξ) :
    ∫⁻ ξ, ENNReal.ofReal (S ξ ^ 8) ∂stdGauss ι ≤
      ENNReal.ofReal ((√(∫ ξ, S ξ ^ 2 ∂stdGauss ι) + π / 2 * (18 / 10) * L) ^ 8) := by
  have hc := hS.continuous hL.le
  have iS2 := BstLean.Part170.euLip_sq_integrable hL.le hS
  set sb := ∫ ξ, S ξ ∂stdGauss ι with hsb
  set qb := ∫ ξ, S ξ ^ 2 ∂stdGauss ι with hqb
  have hs0 : 0 ≤ sb := integral_nonneg hS0
  have hJ : sb ^ 2 ≤ qb := BstLean.Part133.sq_integral_le (ρ := stdGauss ι) iS2
  have hsq : sb ≤ √qb := Real.le_sqrt_of_sq_le hJ
  set B := π / 2 * (18 / 10) * L with hBd
  have hB : 0 < B := by positivity
  have hP8 := poincare_p_lint hL.le hS (p := 8) (by norm_num)
  have hg8 : ∫ x, √(gradSq S x) ^ 8 ∂stdGauss ι ≤ L ^ 8 := by
    have hpt : ∀ x, √(gradSq S x) ^ 8 ≤ L ^ 8 := fun x =>
      pow_le_pow_left₀ (Real.sqrt_nonneg _) ((Real.sqrt_le_left hL.le).mpr (gradSq_le hL.le hS x)) 8
    calc _ ≤ ∫ _x, L ^ 8 ∂stdGauss ι := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => by positivity) (integrable_const _)
          (Filter.Eventually.of_forall hpt)
      _ = L ^ 8 := by simp
  have hD : ∫⁻ ξ, ENNReal.ofReal (|S ξ - sb| ^ 8) ∂stdGauss ι ≤ ENNReal.ofReal (B ^ 8) := by
    refine hP8.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 := BstLean.Part170.gmom8_le
    have : B ^ 8 = (π / 2) ^ 8 * ((18 / 10) ^ 8 * L ^ 8) := by rw [hBd]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 hg8
      (integral_nonneg fun x => pow_nonneg (Real.sqrt_nonneg _) _) (by norm_num)) (by positivity)
  have mD : Measurable (fun ξ => |S ξ - sb|) := (hc.measurable.sub_const _).abs
  rcases (Real.sqrt_nonneg qb).eq_or_lt with hq | hq
  · -- `qb = 0`: `sb = 0`
    have hsb0 : sb = 0 := le_antisymm (hsq.trans hq.symm.le) hs0
    rw [← hq, zero_add]
    refine le_trans (le_of_eq ?_) hD
    refine lintegral_congr fun ξ => ?_
    rw [hsb0, sub_zero, abs_of_nonneg (hS0 ξ)]
  · set A := √qb
    set kA := (A + B) ^ 7 / A ^ 7
    set kB := (A + B) ^ 7 / B ^ 7
    have hpt : ∀ ξ, S ξ ^ 8 ≤ kA * A ^ 8 + kB * |S ξ - sb| ^ 8 := by
      intro ξ
      have h := BstLean.Part170.pow8_split sb (S ξ - sb) hq hB
      rw [abs_of_nonneg hs0, add_sub_cancel] at h
      have : kA * sb ^ 8 ≤ kA * A ^ 8 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsq 8) (by positivity)
      linarith
    calc ∫⁻ ξ, ENNReal.ofReal (S ξ ^ 8) ∂stdGauss ι
        ≤ ∫⁻ ξ, (ENNReal.ofReal (kA * A ^ 8) + ENNReal.ofReal kB * ENNReal.ofReal (|S ξ - sb| ^ 8))
            ∂stdGauss ι := by
          refine lintegral_mono fun ξ => ?_
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpt ξ)
      _ = ENNReal.ofReal (kA * A ^ 8) + ENNReal.ofReal kB *
            ∫⁻ ξ, ENNReal.ofReal (|S ξ - sb| ^ 8) ∂stdGauss ι := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (kA * A ^ 8) + ENNReal.ofReal kB * ENNReal.ofReal (B ^ 8) := by gcongr
      _ = ENNReal.ofReal ((A + B) ^ 8) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          simp only [kA, kB]
          field_simp

end L1

section L3
variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ] {m : ℕ}

lemma relu_sq_add_neg (x : ℝ) : relu x ^ 2 + relu (-x) ^ 2 = x ^ 2 := by
  unfold relu
  rcases le_total 0 x with hx | hx
  · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  · rw [max_eq_left hx, max_eq_right (by linarith)]; ring

lemma relu_sq_le (x : ℝ) : relu x ^ 2 ≤ x ^ 2 := by
  have := relu_sq_add_neg x; nlinarith [sq_nonneg (relu (-x))]

/-- `E relu(⟨ξ, u⟩)² = |u|²/2` for a standard Gaussian vector `ξ`. -/
lemma gauss_relu_sq {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) :
    ∫ ξ, relu (ξ ⬝ᵥ u) ^ 2 ∂stdGauss ι = (u ⬝ᵥ u) / 2 := by
  have i0 := BstLean.Part170.integrable_shift_sq (ι := ι) 0 u
  simp only [zero_add] at i0
  have cg : Continuous (fun ξ : ι → ℝ => relu (ξ ⬝ᵥ u) ^ 2) :=
    (BstLean.Part130.continuous_relu.comp (continuous_id.dotProduct continuous_const)).pow 2
  have ig : Integrable (fun ξ : ι → ℝ => relu (ξ ⬝ᵥ u) ^ 2) (stdGauss ι) :=
    Integrable.mono' i0 cg.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact relu_sq_le _)
  have hneg : ∫ ξ, relu ((-ξ) ⬝ᵥ u) ^ 2 ∂stdGauss ι = ∫ ξ, relu (ξ ⬝ᵥ u) ^ 2 ∂stdGauss ι := by
    have h := integral_map (μ := stdGauss ι) (φ := fun z : ι → ℝ => -z)
      measurable_neg.aemeasurable (f := fun ξ => relu (ξ ⬝ᵥ u) ^ 2)
      (by rw [BstLean.Part33.stdGauss_neg_invariant]; exact cg.aestronglyMeasurable)
    rw [BstLean.Part33.stdGauss_neg_invariant] at h
    exact h.symm
  have ig' : Integrable (fun ξ : ι → ℝ => relu ((-ξ) ⬝ᵥ u) ^ 2) (stdGauss ι) := by
    have h := ig
    rw [← BstLean.Part33.stdGauss_neg_invariant] at h
    exact h.comp_measurable measurable_neg
  have hsum : ∫ ξ, (relu (ξ ⬝ᵥ u) ^ 2 + relu ((-ξ) ⬝ᵥ u) ^ 2) ∂stdGauss ι = u ⬝ᵥ u := by
    have e : (fun ξ : ι → ℝ => relu (ξ ⬝ᵥ u) ^ 2 + relu ((-ξ) ⬝ᵥ u) ^ 2) =
        fun ξ => (0 + ξ ⬝ᵥ u) ^ 2 := by
      funext ξ; rw [neg_dotProduct, relu_sq_add_neg, zero_add]
    rw [e, BstLean.Part170.gauss_sq_shift]; ring
  rw [integral_add ig ig', hneg] at hsum
  linarith

/-- The coefficient vector of the `j`-th coordinate: `(matOf t ξ *ᵥ y) j = ξ ⬝ᵥ uRow t j y`. -/
noncomputable def uRow (t : ℝ) (j : Fin m) (y : Fin m → ℝ) : Fin m × Fin m → ℝ := fun p =>
  if p.1 = j then √t * y p.2 else 0

lemma uRow_mulVec (t : ℝ) (j : Fin m) (y : Fin m → ℝ) (ξ : Fin m × Fin m → ℝ) :
    (matOf t ξ *ᵥ y) j = ξ ⬝ᵥ uRow t j y := by
  simp only [Matrix.mulVec, dotProduct, matOf, Matrix.of_apply, uRow, Fintype.sum_prod_type]
  rw [eq_comm, Finset.sum_eq_single j]
  · exact Finset.sum_congr rfl fun k _ => by simp; ring
  · intro b _ hb; exact Finset.sum_eq_zero fun k _ => by simp [hb]
  · simp

lemma uRow_sq {t : ℝ} (ht : 0 ≤ t) (j : Fin m) (y : Fin m → ℝ) :
    uRow t j y ⬝ᵥ uRow t j y = t * normSq y := by
  simp only [dotProduct, uRow, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · unfold normSq; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      simp; rw [mul_mul_mul_comm, Real.mul_self_sqrt ht]; ring
  · intro b _ hb; exact Finset.sum_eq_zero fun k _ => by simp [hb]
  · simp

lemma continuous_uRow (t : ℝ) (j : Fin m) : Continuous (uRow t j) := by
  refine continuous_pi fun p => ?_
  simp only [uRow]
  split_ifs
  · exact continuous_const.mul (continuous_apply _)
  · exact continuous_const

lemma relu_uRow_bd {t : ℝ} (ht : 0 ≤ t) (j : Fin m) (ξ : Fin m × Fin m → ℝ) (y : Fin m → ℝ) :
    relu (ξ ⬝ᵥ uRow t j y) ^ 2 ≤ normSq ξ * (t * normSq y) := by
  refine (relu_sq_le _).trans ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ ξ (uRow t j y)
  have e := uRow_sq ht j y
  have e' : ∑ i, uRow t j y i ^ 2 = t * normSq y := by
    rw [← e]; simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e'] at h
  simpa [dotProduct, normSq] using h

/-- Jensen for one coordinate: `Var_v relu(X) ≤ E relu(X)² − relu(E X)²`. -/
lemma var_relu_le {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (M : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    ∫ v, relu ((M *ᵥ a v) j) ^ 2 ∂μ - (∫ v, relu ((M *ᵥ a v) j) ∂μ) ^ 2 ≤
      ∫ v, relu ((M *ᵥ a v) j) ^ 2 ∂μ - relu ((M *ᵥ vmean μ a) j) ^ 2 := by
  have cX : Continuous (fun y : Fin m → ℝ => (M *ᵥ y) j) :=
    (continuous_apply j).comp (Continuous.matrix_mulVec continuous_const continuous_id)
  have iX : Integrable (fun v => (M *ᵥ a v) j) μ := int_comp_bdd ha hK cX
  have iR : Integrable (fun v => relu ((M *ᵥ a v) j)) μ :=
    int_comp_bdd ha hK (BstLean.Part130.continuous_relu.comp cX)
  have hmean : ∫ v, (M *ᵥ a v) j ∂μ = (M *ᵥ vmean μ a) j :=
    BstLean.Part170.int_dot ha hK (fun k => M j k)
  have hJ : relu ((M *ᵥ vmean μ a) j) ≤ ∫ v, relu ((M *ᵥ a v) j) ∂μ := by
    rw [← hmean]
    unfold relu
    refine max_le (integral_nonneg fun v => le_max_left _ _) ?_
    exact integral_mono iX iR fun v => le_max_right _ _
  have h0 : 0 ≤ relu ((M *ᵥ vmean μ a) j) := le_max_left _ _
  have hJ2 := pow_le_pow_left₀ h0 hJ 2
  linarith

/-- **The mean of the centred energy** (Jensen): `E_ξ Qvar ≤ m t E_v|a − ā|²/2`. -/
theorem Qvar_mean {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {K2 : ℝ} (hK2 : ∀ v, normSq (a v) ≤ K2) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ξ, Qvar μ a (matOf t ξ) ∂stdGauss (Fin m × Fin m) ≤
      m * t * (∫ v, normSq (a v - vmean μ a) ∂μ) / 2 := by
  -- pointwise bound
  have hpt : ∀ ξ, Qvar μ a (matOf t ξ) ≤ ∑ j, ((∫ v, relu (ξ ⬝ᵥ uRow t j (a v)) ^ 2 ∂μ) -
      relu (ξ ⬝ᵥ uRow t j (vmean μ a)) ^ 2) := by
    intro ξ
    unfold Qvar
    refine Finset.sum_le_sum fun j _ => (var_relu_le ha hK (matOf t ξ) j).trans (le_of_eq ?_)
    simp only [uRow_mulVec]
  have mF : ∀ j, Measurable (fun p : (Fin m × Fin m → ℝ) × V =>
      relu (p.1 ⬝ᵥ uRow t j (a p.2)) ^ 2) :=
    fun j => by
      have hc : Continuous (fun q : (Fin m × Fin m → ℝ) × (Fin m → ℝ) =>
          relu (q.1 ⬝ᵥ uRow t j q.2) ^ 2) :=
        (BstLean.Part130.continuous_relu.comp (continuous_fst.dotProduct
          ((continuous_uRow t j).comp continuous_snd))).pow 2
      have hm : Measurable (fun p : (Fin m × Fin m → ℝ) × V => (p.1, a p.2)) :=
        measurable_fst.prodMk (ha.comp measurable_snd)
      exact Measurable.comp (f := fun p : (Fin m × Fin m → ℝ) × V => (p.1, a p.2))
        (g := fun q : (Fin m × Fin m → ℝ) × (Fin m → ℝ) => relu (q.1 ⬝ᵥ uRow t j q.2) ^ 2)
        hc.measurable hm
  have iProd : ∀ j, Integrable (fun p : (Fin m × Fin m → ℝ) × V =>
      relu (p.1 ⬝ᵥ uRow t j (a p.2)) ^ 2) ((stdGauss (Fin m × Fin m)).prod μ) := by
    intro j
    have iN : Integrable (fun p : (Fin m × Fin m → ℝ) × V => normSq p.1 * (t * K2))
        ((stdGauss (Fin m × Fin m)).prod μ) :=
      (BstLean.Part170.integrable_normSq_std.mul_const _).comp_fst μ
    refine Integrable.mono' iN (mF j).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine (relu_uRow_bd ht j p.1 (a p.2)).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK2 p.2) ht) (normSq_nonneg _)
  have iA : ∀ j, Integrable (fun ξ => ∫ v, relu (ξ ⬝ᵥ uRow t j (a v)) ^ 2 ∂μ)
      (stdGauss (Fin m × Fin m)) := fun j => (iProd j).integral_prod_left
  have iB : ∀ j, Integrable (fun ξ => relu (ξ ⬝ᵥ uRow t j (vmean μ a)) ^ 2)
      (stdGauss (Fin m × Fin m)) := by
    intro j
    have i0 := BstLean.Part170.integrable_shift_sq (ι := Fin m × Fin m) 0 (uRow t j (vmean μ a))
    simp only [zero_add] at i0
    refine Integrable.mono' i0 ((BstLean.Part130.continuous_relu.comp
      (continuous_id.dotProduct continuous_const)).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact relu_sq_le _
  have iQ : Integrable (fun ξ => Qvar μ a (matOf t ξ)) (stdGauss (Fin m × Fin m)) := by
    have := BstLean.Part170.euLip_sq_integrable (Real.sqrt_nonneg _)
      (sqrtQvar_euLip (μ := μ) ha hK hK2 ht)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact Real.sq_sqrt (Qvar_nonneg ha hK _)
  have hA : ∀ j, ∫ ξ, (∫ v, relu (ξ ⬝ᵥ uRow t j (a v)) ^ 2 ∂μ) ∂stdGauss (Fin m × Fin m) =
      ∫ v, t * normSq (a v) / 2 ∂μ := by
    intro j
    rw [integral_integral_swap (iProd j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show ∫ ξ, relu (ξ ⬝ᵥ uRow t j (a v)) ^ 2 ∂stdGauss (Fin m × Fin m) = t * normSq (a v) / 2
    rw [gauss_relu_sq, uRow_sq ht]
  have hB : ∀ j, ∫ ξ, relu (ξ ⬝ᵥ uRow t j (vmean μ a)) ^ 2 ∂stdGauss (Fin m × Fin m) =
      t * normSq (vmean μ a) / 2 := by
    intro j; rw [gauss_relu_sq, uRow_sq ht]
  have hvar : ∫ v, normSq (a v) ∂μ - normSq (vmean μ a) = ∫ v, normSq (a v - vmean μ a) ∂μ := by
    have ik : ∀ k, Integrable (fun v => a v k) μ := fun k => int_comp_bdd ha hK (continuous_apply k)
    have ik2 : ∀ k, Integrable (fun v => a v k ^ 2) μ := fun k =>
      int_comp_bdd ha hK ((continuous_apply k).pow 2)
    have ik3 : ∀ k, Integrable (fun v => (a v k - vmean μ a k) ^ 2) μ := fun k =>
      int_comp_bdd (f := fun y => (y k - vmean μ a k) ^ 2) ha hK (((continuous_apply k).sub
        continuous_const).pow 2)
    unfold normSq
    simp only [Pi.sub_apply]
    rw [integral_finsetSum _ fun k _ => ik2 k, integral_finsetSum _ fun k _ => ik3 k,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => var_eq (ik k) (ik2 k)
  calc ∫ ξ, Qvar μ a (matOf t ξ) ∂stdGauss (Fin m × Fin m)
      ≤ ∫ ξ, ∑ j, ((∫ v, relu (ξ ⬝ᵥ uRow t j (a v)) ^ 2 ∂μ) -
          relu (ξ ⬝ᵥ uRow t j (vmean μ a)) ^ 2) ∂stdGauss (Fin m × Fin m) :=
        integral_mono iQ (integrable_finsetSum _ fun j _ => (iA j).sub (iB j)) hpt
    _ = ∑ _j : Fin m, (∫ v, t * normSq (a v) / 2 ∂μ - t * normSq (vmean μ a) / 2) := by
        rw [integral_finsetSum (f := fun j ξ => (∫ v, relu (ξ ⬝ᵥ uRow t j (a v)) ^ 2 ∂μ) -
          relu (ξ ⬝ᵥ uRow t j (vmean μ a)) ^ 2) _ fun j _ => (iA j).sub (iB j)]
        exact Finset.sum_congr rfl fun j _ => by rw [integral_sub (iA j) (iB j), hA, hB]
    _ = m * t * (∫ v, normSq (a v - vmean μ a) ∂μ) / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hvar,
          integral_div, integral_const_mul]
        ring

end L3

section L4
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part148 (EuLip)

variable {n : ℕ}

/-- The latitude variance of a Lipschitz, positively homogeneous `Φ`:
`Var_v Φ(x_s(v)) ≤ (1 − s²)L²/(n − 2)`. -/
lemma var_lat (hn : 3 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {Φ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : EuLip Φ L) (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) :
    ∫ v, (Φ (xLat c s (unitF53 v)) - ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ (1 - s ^ 2) * L ^ 2 / ((n : ℝ) - 2) := by
  have hls := BstLean.Part162.ls_lat (by omega) c hs hL0 hL hhom
  have hc := hL.continuous hL0
  have bT : ∀ v, |BstLean.Part162.tanSq Φ c s v| ≤ 2 * L ^ 2 := fun v =>
    BstLean.Part162.abs_tanSq_le (by omega) c hs hL0 hL hhom v
  have bT1 : ∀ v, BstLean.Part162.tanSq Φ c s v ≤ (1 - s ^ 2) * L ^ 2 := fun v =>
    BstLean.Part173.tanSq_le_lat (by omega) c hs hL0 hL hhom v
  have mT := BstLean.Part162.measurable_tanSq_left hc c s
  have hT : ∫ v, (BstLean.Part151.gradSq (fun w => Φ (BstLean.Part162.xLatH c s w)) v -
      Φ (xLat c s (unitF53 v)) ^ 2) ∂stdGauss (Fin (n - 1)) ≤ (1 - s ^ 2) * L ^ 2 := by
    calc _ = ∫ v, BstLean.Part162.tanSq Φ c s v ∂stdGauss (Fin (n - 1)) := rfl
      _ ≤ ∫ _v, (1 - s ^ 2) * L ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mT.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact bT v))
            (integrable_const _) bT1
      _ = (1 - s ^ 2) * L ^ 2 := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [le_div_iff₀ h2n]
  nlinarith [hls, hT]

/-- **The trace of the latitude covariance**:
`E_v|a(v) − ā|² ≤ (1 − s²)·n·O²/(n − 2)`. -/
theorem trCov_lat (hn : 3 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) :
    ∫ v, normSq (aLat c s v - a1Bar c s) ∂stdGauss (Fin (n - 1)) ≤
      (1 - s ^ 2) * n * O ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hK := aLat_bdd hn1 c hs hO h1
  set A := A1 c
  -- per coordinate
  have hj : ∀ j, ∫ v, (aLat c s v j - a1Bar c s j) ^ 2 ∂stdGauss (Fin (n - 1)) ≤
      (1 - s ^ 2) * normSq (fun i => A j i) / ((n : ℝ) - 2) := by
    intro j
    set Φ : (Fin n → ℝ) → ℝ := fun x => relu ((A *ᵥ x) j) with hΦ
    have hL0 : 0 ≤ √(normSq (fun i => A j i)) := Real.sqrt_nonneg _
    have hL : EuLip Φ (√(normSq (fun i => A j i))) := by
      intro x y
      simp only [hΦ]
      refine (relu_lip _ _).trans ?_
      have e : (A *ᵥ x) j - (A *ᵥ y) j = ∑ i, A j i * (x i - y i) := by
        simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => A j i) (fun i => x i - y i)
      have hn' : normSq (fun i => A j i) = ∑ i, A j i ^ 2 := rfl
      rw [hn', ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h
    have hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x := by
      intro t x ht
      simp only [hΦ, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      unfold relu
      rw [mul_max_of_nonneg _ _ ht.le, mul_zero]
    have h := var_lat hn c hs hL0 hL hhom
    rw [Real.sq_sqrt (normSq_nonneg _)] at h
    exact h
  -- sum over coordinates
  have iT : ∀ j, Integrable (fun v => (aLat c s v j - a1Bar c s j) ^ 2) (stdGauss (Fin (n - 1))) :=
    fun j => int_comp_bdd (f := fun y : Fin (mA n) → ℝ => (y j - a1Bar c s j) ^ 2)
      (measurable_aLat c s) hK (((continuous_apply j).sub continuous_const).pow 2)
  have hrows : ∑ j, normSq (fun i => A j i) ≤ n * O ^ 2 := by
    have e : ∑ j, normSq (fun i => A j i) = ∑ i : Fin n, normSq (A *ᵥ Pi.single i 1) := by
      unfold normSq
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e]
    calc ∑ i : Fin n, normSq (A *ᵥ Pi.single i 1) ≤ ∑ _i : Fin n, O ^ 2 := by
          refine Finset.sum_le_sum fun i _ => (h1 _).trans (le_of_eq ?_)
          have : normSq (Pi.single i (1 : ℝ) : Fin n → ℝ) = 1 := by
            unfold normSq; simp [Pi.single_apply]
          rw [this, mul_one]
      _ = n * O ^ 2 := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs1 : 0 ≤ 1 - s ^ 2 := by linarith
  calc ∫ v, normSq (aLat c s v - a1Bar c s) ∂stdGauss (Fin (n - 1))
      = ∑ j, ∫ v, (aLat c s v j - a1Bar c s j) ^ 2 ∂stdGauss (Fin (n - 1)) := by
        unfold normSq
        simp only [Pi.sub_apply]
        exact integral_finsetSum _ fun j _ => iT j
    _ ≤ ∑ j, (1 - s ^ 2) * normSq (fun i => A j i) / ((n : ℝ) - 2) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = (1 - s ^ 2) * (∑ j, normSq (fun i => A j i)) / ((n : ℝ) - 2) := by
        rw [← Finset.sum_div, Finset.mul_sum]
    _ ≤ (1 - s ^ 2) * (n * O ^ 2) / ((n : ℝ) - 2) := by
        gcongr
    _ = (1 - s ^ 2) * n * O ^ 2 / ((n : ℝ) - 2) := by ring

end L4

section L5
variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ] {m : ℕ}

/-- **The fourth moment of the centred energy**:
`E_ξ Qvar⁴ ≤ (√(m t T/2) + c₈√(t K2))⁸` if `E_v|a − ā|² ≤ T`. -/
theorem Qvar_mom4 {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {K2 : ℝ} (hK2 : ∀ v, normSq (a v) ≤ K2) (hK2p : 0 < K2) {t : ℝ} (ht : 0 < t) {T : ℝ}
    (hT : ∫ v, normSq (a v - vmean μ a) ∂μ ≤ T) :
    ∫⁻ ξ, ENNReal.ofReal (Qvar μ a (matOf t ξ) ^ 4) ∂stdGauss (Fin m × Fin m) ≤
      ENNReal.ofReal ((√(m * t * T / 2) + π / 2 * (18 / 10) * √(t * K2)) ^ 8) := by
  set S : (Fin m × Fin m → ℝ) → ℝ := fun ξ => √(Qvar μ a (matOf t ξ))
  have hS := sqrtQvar_euLip (μ := μ) ha hK hK2 ht.le
  have hL : 0 < √(t * K2) := Real.sqrt_pos.mpr (mul_pos ht hK2p)
  have h := lip_mom8 hL hS (fun ξ => Real.sqrt_nonneg _)
  have e2 : ∀ ξ, S ξ ^ 2 = Qvar μ a (matOf t ξ) := fun ξ => Real.sq_sqrt (Qvar_nonneg ha hK _)
  have e8 : ∀ ξ, S ξ ^ 8 = Qvar μ a (matOf t ξ) ^ 4 := fun ξ => by
    rw [show S ξ ^ 8 = (S ξ ^ 2) ^ 4 by ring, e2]
  simp only [S] at e2 e8
  simp_rw [e8, e2] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 8))
  have hm := Qvar_mean (μ := μ) ha hK hK2 ht.le
  have : m * t * (∫ v, normSq (a v - vmean μ a) ∂μ) / 2 ≤ m * t * T / 2 := by
    have : (0 : ℝ) ≤ m * t := by positivity
    nlinarith
  linarith [Real.sqrt_le_sqrt (hm.trans this)]

/-- `Qvar_mom4` for the Gaussian matrix `gaussMat m m t`. -/
theorem Qvar_mom4_gm {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {K2 : ℝ} (hK2 : ∀ v, normSq (a v) ≤ K2) (hK2p : 0 < K2) {t : ℝ} (ht : 0 < t) {T : ℝ}
    (hT : ∫ v, normSq (a v - vmean μ a) ∂μ ≤ T) :
    ∫⁻ M, ENNReal.ofReal (Qvar μ a M ^ 4) ∂gaussMat m m t ≤
      ENNReal.ofReal ((√(m * t * T / 2) + π / 2 * (18 / 10) * √(t * K2)) ^ 8) := by
  rw [BstLean.Part170.gaussMat_eq]
  exact (lintegral_map_le _ (BstLean.Part170.measurable_matOf t).aemeasurable).trans
    (Qvar_mom4 ha hK hK2 hK2p ht hT)

end L5

end BstLean.Part183

#print axioms BstLean.Part183.lip_mom8
#print axioms BstLean.Part183.sqrtQvar_euLip
#print axioms BstLean.Part183.Qvar_mean
#print axioms BstLean.Part183.trCov_lat
#print axioms BstLean.Part183.Qvar_mom4
#print axioms BstLean.Part183.Qvar_mom4_gm
