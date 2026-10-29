import BstLean.Part162Gm
import Mathlib.Probability.ProductMeasure
import BstLean.Part157BL

/-!
# Part 162, item 2 (partial): the direction-sum factor of Lemma LJ

Role: `delegations/statements/p162-spec.md`, item 2. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:LJ`, the factor
`r^{sph}`. Route: the rows of a Gaussian array are independent (`rows_map`); radius and direction
are independent (`rows_polar_map`); Jensen over an independent copy of the radii; the moment of a
Gaussian linear combination (`lincomb_mom`); Poincaré for `|·|` (`sq_mean_radF_ge`).

* **`dirsum_le`**: `E|Σ_i c_i ω_i|^k ≤ (E|g|^k/(E|g|)^k)·|c|^k`.
* **`dirsum_le_sqrt`**: the same with `(E|g|)^k` replaced by `(d − 1)^{k/2}`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)

variable {d : ℕ}

/-- `(g, g') ↦ |g'|·g/|g|` sends `γ ⊗ γ` to `γ` (radius and direction are independent). -/
theorem polar_swap_map :
    ((stdGauss (Fin d)).prod (stdGauss (Fin d))).map
      (fun p : (Fin d → ℝ) × (Fin d → ℝ) => radF53 p.2 • unitF53 p.1) = stdGauss (Fin d) := by
  set γ := stdGauss (Fin d)
  have h1 : (γ.prod γ).map (fun p : (Fin d → ℝ) × (Fin d → ℝ) => (unitF53 p.1, radF53 p.2)) =
      (γ.map unitF53).prod (γ.map radF53) := by
    exact (Measure.map_prod_map _ _ measurable_unitF measurable_radF).symm
  have h2 : (γ.prod γ).map (fun p : (Fin d → ℝ) × (Fin d → ℝ) => radF53 p.2 • unitF53 p.1) =
      ((γ.prod γ).map (fun p : (Fin d → ℝ) × (Fin d → ℝ) => (unitF53 p.1, radF53 p.2))).map
        (fun z : (Fin d → ℝ) × ℝ => z.2 • z.1) := by
    have mf : Measurable (fun z : (Fin d → ℝ) × ℝ => z.2 • z.1) := by fun_prop
    have mg : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => (unitF53 p.1, radF53 p.2)) :=
      (measurable_unitF.comp measurable_fst).prodMk (measurable_radF.comp measurable_snd)
    rw [Measure.map_map mf mg]
    rfl
  have mf : Measurable (fun z : (Fin d → ℝ) × ℝ => z.2 • z.1) := by fun_prop
  rw [h2, h1, ← polar_map, Measure.map_map mf (measurable_unitF.prodMk measurable_radF)]
  have e : ((fun z : (Fin d → ℝ) × ℝ => z.2 • z.1) ∘ fun Z => (unitF53 Z, radF53 Z)) = id := by
    funext Z; exact unitF_smul Z
  rw [e, Measure.map_id]

variable {m : ℕ}

/-- The rows of a standard Gaussian `m × d` array are independent standard Gaussian vectors. -/
theorem rows_map :
    (stdGauss (Fin m × Fin d)).map (fun Z : Fin m × Fin d → ℝ => fun i j => Z (i, j)) =
      Measure.pi (fun _ : Fin m => stdGauss (Fin d)) := by
  have h := Measure.infinitePi_map_curry (X := ℝ) (fun (_ : Fin m) (_ : Fin d) => gaussianReal 0 1)
  rw [Measure.infinitePi_eq_pi] at h
  unfold stdGauss
  convert h using 2
  · rfl
  · simp only [Measure.infinitePi_eq_pi]

/-- `(G, G') ↦ (|G'_i|·G_i/|G_i|)_i` sends `Q ⊗ Q` to `Q` (`Q` the law of the rows). -/
theorem rows_polar_map :
    ((Measure.pi (fun _ : Fin m => stdGauss (Fin d))).prod
      (Measure.pi (fun _ : Fin m => stdGauss (Fin d)))).map
      (fun p : (Fin m → Fin d → ℝ) × (Fin m → Fin d → ℝ) =>
        fun i => radF53 (p.2 i) • unitF53 (p.1 i)) =
      Measure.pi (fun _ : Fin m => stdGauss (Fin d)) := by
  set γ := stdGauss (Fin d)
  have he := measurePreserving_arrowProdEquivProdArrow (Fin d → ℝ) (Fin d → ℝ) (Fin m)
    (fun _ => γ) (fun _ => γ)
  rw [← he.map_eq]
  have mφ : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => radF53 p.2 • unitF53 p.1) :=
    (measurable_radF.comp measurable_snd).smul (measurable_unitF.comp measurable_fst)
  have mΦ : Measurable (fun p : (Fin m → Fin d → ℝ) × (Fin m → Fin d → ℝ) =>
      fun i => radF53 (p.2 i) • unitF53 (p.1 i)) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_radF.comp ((measurable_pi_apply i).comp measurable_snd)).smul
      (measurable_unitF.comp ((measurable_pi_apply i).comp measurable_fst))
  rw [Measure.map_map mΦ
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) (Fin d → ℝ) (Fin m)).measurable]
  have e : ((fun p : (Fin m → Fin d → ℝ) × (Fin m → Fin d → ℝ) =>
      fun i => radF53 (p.2 i) • unitF53 (p.1 i)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) (Fin d → ℝ) (Fin m))) =
      fun w i => (fun p : (Fin d → ℝ) × (Fin d → ℝ) => radF53 p.2 • unitF53 p.1) (w i) := by
    funext w i; rfl
  rw [e, Measure.pi_map_pi (fun i => mφ.aemeasurable)]
  congr 1
  funext i
  exact polar_swap_map

/-- All moments of `|Z|` are finite for a standard Gaussian vector. -/
lemma integrable_radF_pow [Nonempty (Fin d)] (k : ℕ) :
    Integrable (fun g : Fin d → ℝ => radF53 g ^ k) (stdGauss (Fin d)) := by
  classical
  have i2k : Integrable (fun g : Fin d → ℝ => (radF53 g ^ 2) ^ (k + 1)) (stdGauss (Fin d)) := by
    have hb : ∀ Z : Fin d → ℝ, (radF53 Z ^ 2) ^ (k + 1) ≤ (Fintype.card (Fin d) : ℝ) ^ k *
        ∑ i, (Z i ^ 2) ^ (k + 1) := fun Z => by
      rw [radF_sq]
      have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => Z i ^ 2) (fun i _ => sq_nonneg _) k
      rw [Finset.card_univ] at h
      have hc : (0 : ℝ) < (Fintype.card (Fin d) : ℝ) ^ k := by
        have : 0 < Fintype.card (Fin d) := Fintype.card_pos
        positivity
      rw [div_le_iff₀ hc] at h
      linarith
    have ip : Integrable (fun Z : Fin d → ℝ => ∑ i, (Z i ^ 2) ^ (k + 1)) (stdGauss (Fin d)) := by
      refine integrable_finsetSum _ fun i _ => ?_
      have := BstLean.Part35.stdGauss_prod_integrable (ι := Fin d) (2 * (k + 1)) (fun _ => i)
      simpa [Finset.prod_const, ← pow_mul] using this
    refine (ip.const_mul ((Fintype.card (Fin d) : ℝ) ^ k)).mono'
      ((measurable_radF.pow_const 2).pow_const (k + 1)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
    exact hb Z
  refine (i2k.add (integrable_const 1)).mono' (measurable_radF.pow_const k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (radF_nonneg g) _)]
  have h0 := radF_nonneg g
  rcases le_total (radF53 g) 1 with h | h
  · have : radF53 g ^ k ≤ 1 := pow_le_one₀ h0 h
    have : 0 ≤ (radF53 g ^ 2) ^ (k + 1) := by positivity
    simp only [Pi.add_apply]; linarith
  · have : radF53 g ^ k ≤ (radF53 g ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ h (by omega)
    simp only [Pi.add_apply]; linarith

/-- **The linear combination of the rows**: `E|Σ_i c_i G_i|^k = |c|^k E|g|^k`. -/
theorem lincomb_mom (c : Fin m → ℝ) (k : ℕ) :
    ∫ G, radF53 (∑ i, c i • G i) ^ k ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) =
      radF53 c ^ k * ∫ g, radF53 g ^ k ∂stdGauss (Fin d) := by
  classical
  set Q := Measure.pi (fun _ : Fin m => stdGauss (Fin d))
  by_cases hc : c = 0
  · subst hc
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · simp [radF53, zero_pow hk.ne']
  have hr : 0 < radF53 c := radF_pos hc
  set u : Fin m → ℝ := fun i => c i / radF53 c with hu
  set E : Matrix (Fin d) (Fin m × Fin d) ℝ := Matrix.of fun j p => if p.2 = j then u p.1 else 0
    with hE
  have hEE : E * E.transpose = 1 := by
    ext j j'
    simp only [hE, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, ite_mul, zero_mul, mul_zero]
    by_cases hjj : j = j'
    · subst hjj
      simp only [if_true, Finset.sum_ite_eq', Finset.mem_univ]
      have : ∑ i, u i * u i = 1 := by
        simp only [hu]
        have hs : ∑ i, c i ^ 2 = radF53 c ^ 2 := (radF_sq c).symm
        rw [show ∑ i, c i / radF53 c * (c i / radF53 c) = (∑ i, c i ^ 2) / radF53 c ^ 2 by
          rw [Finset.sum_div]; congr 1; funext i; ring, hs, div_self (by positivity)]
      simpa using this
    · simp only [hjj, if_false]
      refine Finset.sum_eq_zero fun i _ => ?_
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with h1 h2 <;> simp_all
  -- rows
  have hrows : ∀ F : (Fin m → Fin d → ℝ) → ℝ, AEStronglyMeasurable F Q →
      ∫ G, F G ∂Q = ∫ Z, F (fun i j => Z (i, j)) ∂stdGauss (Fin m × Fin d) := fun F hF => by
    have h := rows_map (m := m) (d := d)
    rw [show Q = (stdGauss (Fin m × Fin d)).map (fun Z : Fin m × Fin d → ℝ => fun i j => Z (i, j))
      from h.symm]
    have hm : AEMeasurable (fun Z : Fin m × Fin d → ℝ => fun i j => Z (i, j))
        (stdGauss (Fin m × Fin d)) := by
      exact (MeasurableEquiv.curry (Fin m) (Fin d) ℝ).measurable.aemeasurable
    rw [integral_map hm (by rw [h]; exact hF)]
  have hlin : ∀ Z : Fin m × Fin d → ℝ, ∑ i, c i • (fun j => Z (i, j)) = radF53 c • E.mulVec Z :=
    fun Z => by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hE,
        Matrix.of_apply]
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single j]
      · simp only [if_true, hu]; field_simp
      · intro b _ hb; simp [hb]
      · simp
  have mF : Measurable (fun G : Fin m → Fin d → ℝ => radF53 (∑ i, c i • G i) ^ k) := by
    refine (measurable_radF.comp ?_).pow_const k
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_smul (c i)
  rw [hrows _ mF.aestronglyMeasurable]
  simp_rw [hlin, radF_smul hr, mul_pow]
  rw [integral_const_mul]
  congr 1
  rw [← BstLean.Part157.stdGauss_map_orthonormal E hEE, integral_map (by fun_prop)
    ((measurable_radF.pow_const k).aestronglyMeasurable)]

lemma convexOn_radF_pow (k : ℕ) : ConvexOn ℝ Set.univ (fun y : Fin d → ℝ => radF53 y ^ k) := by
  have h1 : ConvexOn ℝ Set.univ (radF53 (ι := Fin d)) := by
    have e : radF53 (ι := Fin d) = fun y => ‖(WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm y‖ := by
      funext y; rw [radF_eq_norm]; rfl
    rw [e]
    exact (convexOn_norm convex_univ).comp_linearMap
      ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap)
  exact h1.pow (fun y _ => radF_nonneg y) k

lemma continuous_radF : Continuous (radF53 (ι := Fin d)) := by
  unfold radF53; fun_prop

lemma radF_unitF_le' (g : Fin d → ℝ) : radF53 (unitF53 g) ≤ 1 := radF_unitF_le g

lemma radF_sum_le (a : Fin m → ℝ) (w : Fin m → Fin d → ℝ) :
    radF53 (∑ i, a i • w i) ≤ ∑ i, |a i| * radF53 (w i) := by
  rw [radF_eq_norm]
  have : (WithLp.toLp 2 (∑ i, a i • w i) : EuclideanSpace ℝ (Fin d)) =
      ∑ i, a i • (WithLp.toLp 2 (w i) : EuclideanSpace ℝ (Fin d)) := by
    simp [WithLp.toLp_sum, WithLp.toLp_smul]
  rw [this]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs, ← radF_eq_norm]

/-- **The direction-sum lemma of Lemma LJ** (proof of `t7:p07:LJ`, the factor `r_ℓ^{sph}`): for
independent uniform directions `ω_i = G_i/|G_i|` in `ℝ^d` and fixed coefficients `c`,
`E|Σ_i c_i ω_i|^k ≤ (E|g|^k/(E|g|)^k)·|c|^k`, `g` standard Gaussian in `ℝ^d`. -/
theorem dirsum_le (hm : 1 ≤ m) (hd : 1 ≤ d) (c : Fin m → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hρ : 0 < ∫ g, radF53 g ∂stdGauss (Fin d)) :
    ∫ G, radF53 (∑ i, c i • unitF53 (G i)) ^ k ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
      (∫ g, radF53 g ^ k ∂stdGauss (Fin d)) / (∫ g, radF53 g ∂stdGauss (Fin d)) ^ k *
        radF53 c ^ k := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set γ := stdGauss (Fin d) with hγ
  set Q := Measure.pi (fun _ : Fin m => γ) with hQ
  set ρ := ∫ g, radF53 g ∂γ with hρd
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hcard : (0 : ℝ) < (Fintype.card (Fin m) : ℝ) := by
    rw [Fintype.card_fin]; exact_mod_cast hm
  -- marginals
  have hmp : ∀ i : Fin m, MeasurePreserving (fun G : Fin m → Fin d → ℝ => G i) Q γ := fun i =>
    measurePreserving_eval (fun _ => γ) i
  have hmarg : ∀ (i : Fin m) {f : (Fin d → ℝ) → ℝ}, Integrable f γ →
      Integrable (fun G : Fin m → Fin d → ℝ => f (G i)) Q := fun i f hf =>
    (hmp i).integrable_comp_of_integrable hf
  have hmargI : ∀ (i : Fin m) {f : (Fin d → ℝ) → ℝ}, AEStronglyMeasurable f γ →
      ∫ G, f (G i) ∂Q = ∫ g, f g ∂γ := fun i f hf => by
    rw [← (hmp i).map_eq] at hf ⊢
    rw [integral_map (measurable_pi_apply i).aemeasurable hf]
  have iR : ∀ j : ℕ, Integrable (fun g : Fin d → ℝ => radF53 g ^ j) γ :=
    fun j => integrable_radF_pow j
  have iR1 : Integrable (fun g : Fin d → ℝ => radF53 g) γ := by simpa using iR 1
  -- the auxiliary field and its bound
  set Y : (Fin m → Fin d → ℝ) → (Fin m → Fin d → ℝ) → (Fin d → ℝ) := fun G G' =>
    ∑ i, (c i * (radF53 (G' i) / ρ)) • unitF53 (G i) with hY
  set B : (Fin m → Fin d → ℝ) → ℝ := fun G' =>
    (Fintype.card (Fin m) : ℝ) ^ k' * ∑ i, (|c i| / ρ * radF53 (G' i)) ^ (k' + 1) with hB
  have hYB : ∀ G G', radF53 (Y G G') ^ (k' + 1) ≤ B G' := fun G G' => by
    have h1 : radF53 (Y G G') ≤ ∑ i, |c i| / ρ * radF53 (G' i) := by
      refine (radF_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_div, abs_of_nonneg (radF_nonneg _), abs_of_pos hρ]
      have := radF_unitF_le' (G i)
      have h0 : 0 ≤ |c i| * (radF53 (G' i) / ρ) := by have := radF_nonneg (G' i); positivity
      calc |c i| * (radF53 (G' i) / ρ) * radF53 (unitF53 (G i)) ≤ |c i| * (radF53 (G' i) / ρ) * 1 :=
            mul_le_mul_of_nonneg_left this h0
        _ = |c i| / ρ * radF53 (G' i) := by ring
    have h2 := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => |c i| / ρ * radF53 (G' i)) (fun i _ => by have := radF_nonneg (G' i); positivity) k'
    rw [Finset.card_univ, div_le_iff₀ (pow_pos hcard _)] at h2
    calc radF53 (Y G G') ^ (k' + 1) ≤ (∑ i, |c i| / ρ * radF53 (G' i)) ^ (k' + 1) :=
          pow_le_pow_left₀ (radF_nonneg _) h1 _
      _ ≤ B G' := by simp only [hB]; linarith
  have iB : Integrable B Q := by
    refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
    have := hmarg i (iR (k' + 1))
    have e : (fun G : Fin m → Fin d → ℝ => (|c i| / ρ * radF53 (G i)) ^ (k' + 1)) =
        fun G => (|c i| / ρ) ^ (k' + 1) * radF53 (G i) ^ (k' + 1) := by funext G; ring
    rw [e]; exact this.const_mul _
  have mY : ∀ G, Measurable (Y G) := fun G => by
    simp only [hY]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_const.mul ((measurable_radF.comp (measurable_pi_apply i)).div_const _))).smul_const _
  -- for a fixed `G`: Jensen over the radii
  have hpt : ∀ G, radF53 (∑ i, c i • unitF53 (G i)) ^ (k' + 1) ≤
      ∫ G', radF53 (Y G G') ^ (k' + 1) ∂Q := fun G => by
    have iY : Integrable (Y G) Q := by
      simp only [hY]
      refine integrable_finsetSum _ fun i _ => ?_
      exact ((hmarg i iR1).div_const ρ |>.const_mul (c i)).smul_const _
    have hmean : ∫ G', Y G G' ∂Q = ∑ i, c i • unitF53 (G i) := by
      funext j
      have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).integral_comp_comm iY
      simp only [ContinuousLinearMap.proj_apply] at h1
      rw [← h1]
      simp only [hY, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finset_sum _ fun i _ => ((((hmarg i iR1).div_const ρ).const_mul (c i)).mul_const _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const, integral_const_mul, integral_div,
        hmargI i measurable_radF.aestronglyMeasurable]
      field_simp
      rfl
    have iYk : Integrable (fun G' => radF53 (Y G G') ^ (k' + 1)) Q :=
      iB.mono' ((measurable_radF.comp (mY G)).pow_const _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun G' => by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (radF_nonneg _) _)]; exact hYB G G')
    have hJ := (convexOn_radF_pow (d := d) (k' + 1)).map_integral_le (μ := Q) (f := Y G)
      (continuous_radF.pow _).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) iY iYk
    rw [hmean] at hJ
    exact hJ
  -- joint integrability on `Q ⊗ Q`
  set f : (Fin m → Fin d → ℝ) × (Fin m → Fin d → ℝ) → ℝ := fun p => radF53 (Y p.1 p.2) ^ (k' + 1)
    with hf
  have mYj : Measurable (fun p : (Fin m → Fin d → ℝ) × (Fin m → Fin d → ℝ) => Y p.1 p.2) := by
    simp only [hY]
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_const.mul ((measurable_radF.comp ((measurable_pi_apply i).comp measurable_snd)).div_const _)).smul
        (measurable_unitF.comp ((measurable_pi_apply i).comp measurable_fst))
  have mf : Measurable f := (measurable_radF.comp mYj).pow_const _
  have iBs : Integrable (fun p : (Fin m → Fin d → ℝ) × (Fin m → Fin d → ℝ) => B p.2) (Q.prod Q) :=
    MeasureTheory.Integrable.comp_snd iB Q
  have iff : Integrable f (Q.prod Q) :=
    iBs.mono' mf.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (radF_nonneg _) _)]; exact hYB p.1 p.2)
  -- the left side is integrable (bounded)
  have mL : Measurable (fun G : Fin m → Fin d → ℝ => radF53 (∑ i, c i • unitF53 (G i)) ^ (k' + 1)) :=
    (measurable_radF.comp (Finset.measurable_sum _ fun i _ =>
      (measurable_unitF.comp (measurable_pi_apply i)).const_smul (c i))).pow_const _
  have iL : Integrable (fun G : Fin m → Fin d → ℝ => radF53 (∑ i, c i • unitF53 (G i)) ^ (k' + 1)) Q := by
    refine (integrable_const ((∑ i, |c i|) ^ (k' + 1))).mono' mL.aestronglyMeasurable
      (Filter.Eventually.of_forall fun G => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (radF_nonneg _) _)]
    refine pow_le_pow_left₀ (radF_nonneg _) ((radF_sum_le _ _).trans ?_) _
    exact Finset.sum_le_sum fun i _ => by
      have := radF_unitF_le' (G i); have := abs_nonneg (c i); nlinarith
  have step1 : ∫ G, radF53 (∑ i, c i • unitF53 (G i)) ^ (k' + 1) ∂Q ≤ ∫ p, f p ∂(Q.prod Q) := by
    rw [integral_prod f iff]
    exact integral_mono iL iff.integral_prod_left hpt
  -- change of variables
  set Φ : (Fin m → Fin d → ℝ) × (Fin m → Fin d → ℝ) → (Fin m → Fin d → ℝ) :=
    fun p i => radF53 (p.2 i) • unitF53 (p.1 i) with hΦ
  have mΦ : Measurable Φ := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_radF.comp ((measurable_pi_apply i).comp measurable_snd)).smul
      (measurable_unitF.comp ((measurable_pi_apply i).comp measurable_fst))
  set a : Fin m → ℝ := fun i => c i / ρ with ha
  have hfΦ : f = (fun H : Fin m → Fin d → ℝ => radF53 (∑ i, a i • H i) ^ (k' + 1)) ∘ Φ := by
    funext p
    simp only [hf, hY, hΦ, ha, Function.comp, smul_smul]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; ring
  have mH : Measurable (fun H : Fin m → Fin d → ℝ => radF53 (∑ i, a i • H i) ^ (k' + 1)) :=
    (measurable_radF.comp (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).const_smul (a i))).pow_const _
  have step2 : ∫ p, f p ∂(Q.prod Q) = radF53 a ^ (k' + 1) * ∫ g, radF53 g ^ (k' + 1) ∂γ := by
    have h := integral_map (μ := Q.prod Q) mΦ.aemeasurable mH.aestronglyMeasurable
    rw [show (Q.prod Q).map Φ = Q from rows_polar_map] at h
    rw [hfΦ]
    exact h.symm.trans (lincomb_mom a (k' + 1))
  have hra : radF53 a = radF53 c / ρ := by
    have : a = (1 / ρ) • c := by funext i; simp [ha]; ring
    rw [this, radF_smul (by positivity)]; ring
  rw [step2, hra, div_pow] at step1
  calc _ ≤ _ := step1
    _ = _ := by ring

lemma euLip_radF : BstLean.Part148.EuLip (radF53 (ι := Fin d)) 1 := fun x y => by
  rw [one_mul]
  have h : radF53 (x - y) = √(∑ i, (x i - y i) ^ 2) := rfl
  rw [← h, radF_eq_norm, radF_eq_norm, radF_eq_norm]
  have : (WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin d)) =
      WithLp.toLp 2 x - WithLp.toLp 2 y := by simp [WithLp.toLp_sub]
  rw [this]
  exact abs_norm_sub_norm_le _ _

/-- `E|g| ≥ √(d − 1)` for a standard Gaussian vector in `ℝ^d` (Poincaré for `|·|`). -/
lemma sq_mean_radF_ge [Nonempty (Fin d)] :
    (d : ℝ) - 1 ≤ (∫ g, radF53 g ∂stdGauss (Fin d)) ^ 2 := by
  classical
  set γ := stdGauss (Fin d)
  set ρ := ∫ g, radF53 g ∂γ
  have hP := BstLean.Part151.poincare_lip_L (ι := Fin d) zero_le_one euLip_radF
  have hrad2 : ∫ Z, radF53 Z ^ 2 ∂γ = d := by
    simp_rw [radF_sq]
    rw [integral_finset_sum _ fun i _ => by
      simpa [sq] using BstLean.Part107.gauss_pair_integrable107 (ι := Fin d) i i]
    have : ∀ i : Fin d, ∫ Z, Z i ^ 2 ∂γ = 1 := fun i => by
      have := BstLean.Part107.gauss_pair107 (ι := Fin d) i i
      simpa [sq] using this
    simp [this]
  have i2 : Integrable (fun Z => radF53 Z ^ 2) γ := by simpa using integrable_radF_pow (d := d) 2
  have i1 : Integrable (fun Z => radF53 Z) γ := by simpa using integrable_radF_pow (d := d) 1
  have hexp : ∫ x, (radF53 x - ρ) ^ 2 ∂γ = ∫ Z, radF53 Z ^ 2 ∂γ - ρ ^ 2 := by
    have e : (fun x : Fin d → ℝ => (radF53 x - ρ) ^ 2) = fun x => radF53 x ^ 2 - (2 * ρ * radF53 x - ρ ^ 2) := by
      funext x; ring
    have i3 : Integrable (fun x : Fin d → ℝ => 2 * ρ * radF53 x - ρ ^ 2) γ :=
      (i1.const_mul _).sub (integrable_const _)
    rw [e, integral_sub (f := fun x => radF53 x ^ 2) i2 i3,
      integral_sub (f := fun x : Fin d → ℝ => 2 * ρ * radF53 x) (i1.const_mul _) (integrable_const _),
      integral_const_mul]
    simp; ring
  have : ∫ x, (radF53 x - ρ) ^ 2 ∂γ ≤ 1 := by simpa using hP
  rw [hexp, hrad2] at this
  linarith

/-- **The direction-sum lemma with the explicit denominator**: for `d ≥ 2`,
`E|Σ_i c_i ω_i|^k ≤ (E|g|^k/(d − 1)^{k/2})·|c|^k`. -/
theorem dirsum_le_sqrt (hm : 1 ≤ m) (hd : 2 ≤ d) (c : Fin m → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∫ G, radF53 (∑ i, c i • unitF53 (G i)) ^ k ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
      (∫ g, radF53 g ^ k ∂stdGauss (Fin d)) / √((d : ℝ) - 1) ^ k * radF53 c ^ k := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsq := sq_mean_radF_ge (d := d)
  have hρ0 : 0 ≤ ∫ g, radF53 g ∂stdGauss (Fin d) := integral_nonneg fun g => radF_nonneg g
  have hle : √((d : ℝ) - 1) ≤ ∫ g, radF53 g ∂stdGauss (Fin d) := by
    rw [← Real.sqrt_sq hρ0]; exact Real.sqrt_le_sqrt hsq
  have hs : 0 < √((d : ℝ) - 1) := Real.sqrt_pos.mpr hd1
  have hρ : 0 < ∫ g, radF53 g ∂stdGauss (Fin d) := hs.trans_le hle
  refine (dirsum_le hm (by omega) c hk hρ).trans ?_
  have hM : 0 ≤ ∫ g, radF53 g ^ k ∂stdGauss (Fin d) :=
    integral_nonneg fun g => pow_nonneg (radF_nonneg g) _
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (radF_nonneg _) _)
  exact div_le_div_of_nonneg_left hM (pow_pos hs _) (pow_le_pow_left₀ hs.le hle _)

end BstLean.Part162
