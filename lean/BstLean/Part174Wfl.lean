import BstLean.Part173All

/-!
# Part 174 (file `Wfl`): the energy fluctuation without the factor `√3`

No proof is left open; no `native_decide` or `axiom` is used.

Part 170's energy fluctuation (`exWn_mom`, and Part 173's `exWn_mom_q`) bounds the mean energy of
the transverse matrix pointwise in the plane coordinates by `t O²(|ξ₁|² + |ξ₂|² + m)`
(`M0_bound`: Cauchy–Schwarz in the plane), and pays `E(|ξ₁|² + |ξ₂|² + m)⁴ ≤ 81(m + 8)⁴`. The true
size of the mean energy is `≈ m t |y|²`: the plane part `P(y)ξ₁ + Q(y)ξ₂` is a Gaussian vector with
covariance `(P² + Q²)·I`, and `P² + Q² + t|w|² = t|y|²` (Pythagoras). This file proves that.

* `pair_comb`: `Pξ₁ + Qξ₂` has the distribution of `√(P² + Q²)·ζ` (by Part 167's `plane_split`
  for a two-column Gaussian matrix, and Part 130's `gaussMat_mulVec`).
* `chi_aff4`, `plane_mom4`: `E(c|ζ|² + D)⁴ ≤ (c(m + 8) + D)⁴`; `E(|Pξ₁ + Qξ₂|² + mT)⁴ ≤ ((m + 8)Y)⁴`
  if `P² + Q² + T ≤ Y`.
* `flQ_mean_int`: `E_N Q ≤ E_v(|M₀a(v)|² + m t|w(v)|²)` (Part 170's `flQ_mean_le` before its sup
  bounds).
* `pP`, `pQ`, `M0_eq`, `pyth_PQ`: `M₀y = P(y)ξ₁ + Q(y)ξ₂` and `P² + Q² + t|w|² = t|y|²`.
* `Xpl`, `PsiR`, `jensen4`, `PsiR_pow4_le`, `GR_int_gen`: `Ψ = E_v X`, `Ψ⁴ ≤ E_v X⁴`,
  `E_{ξ₁,ξ₂}E_v X⁴ ≤ (t O²(m + 8))⁴`.
* `outer_r`: `E_{ξ₁,ξ₂}(a₁ + b₁√Ψ)⁸ ≤ (a₁ + b₁√Y)⁸` if `E Ψ⁴ ≤ Y⁴`.
* **`exWn_mom_r`**: Part 173's `exWn_mom_q` with `WflR` in place of `WflQ`:
  `W_fl = a₁ + 2c₈√(tΛ)·√(t O²(m + 8))` instead of `a₁ + 2c₈√(tΛ)·√(t O²)·√3·√(m + 8)`.
  At `n = 59 000`, `q = 0.5743`: `WflR ≈ 0.0719` against `WflQ ≈ 0.1244`.
-/

namespace BstLean.Part174

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130

section pair
variable {m : ℕ}

/-- **A combination of two independent standard Gaussian vectors**: `Pξ₁ + Qξ₂` has the
distribution of `√(P² + Q²)·ζ`. -/
theorem pair_comb (P Q : ℝ) {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, f (P • ξ₁ + Q • ξ₂) ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      ∫⁻ ζ, f (√(P ^ 2 + Q ^ 2) • ζ) ∂stdGauss (Fin m) := by
  set e₁ : Fin 2 → ℝ := ![1, 0]
  set e₂ : Fin 2 → ℝ := ![0, 1]
  have mF : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) × Matrix (Fin m) (Fin 2) ℝ =>
      f (P • p.1 + Q • p.2.1)) := by
    refine hf.comp ?_
    exact ((measurable_const_smul P).comp measurable_fst).add
      ((measurable_const_smul Q).comp (measurable_fst.comp measurable_snd))
  have hps := BstLean.Part167.plane_split (q := m) (m := 2) 1 e₁ e₂ mF
  have n1 : normSq e₁ = 1 := by simp [normSq, e₁, Fin.sum_univ_two]
  have hl : BstLean.Part134.lam e₁ e₂ = 0 := by
    simp [BstLean.Part134.lam, e₁, e₂, Fin.sum_univ_two]
  have hr : BstLean.Part134.res e₁ e₂ = e₂ := by
    simp [BstLean.Part134.res, hl]
  have n2 : normSq e₂ = 1 := by simp [normSq, e₂, Fin.sum_univ_two]
  have c1 : ∀ ξ : Fin m → ℝ, BstLean.Part157.cOf 1 e₁ ξ = ξ := fun ξ => by
    simp [BstLean.Part157.cOf, n1]
  have c2 : ∀ ξ : Fin m → ℝ, BstLean.Part157.cOf 1 (BstLean.Part134.res e₁ e₂) ξ = ξ := fun ξ => by
    simp [BstLean.Part157.cOf, hr, n2]
  simp only [c1, c2, hl, zero_smul, zero_add, lintegral_const, measure_univ, mul_one] at hps
  rw [← hps]
  have e : ∀ M : Matrix (Fin m) (Fin 2) ℝ, P • (M *ᵥ e₁) + Q • (M *ᵥ e₂) = M *ᵥ ![P, Q] := by
    intro M; funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e₁, e₂]; ring
  simp_rw [e]
  have hmv : Measurable (fun M : Matrix (Fin m) (Fin 2) ℝ => M *ᵥ ![P, Q]) :=
    BstLean.Part167.measurable_mulVec_pair _
  rw [← lintegral_map hf hmv, gaussMat_mulVec, lintegral_map hf (measurable_const_smul _)]
  have hn : normSq (![P, Q] : Fin 2 → ℝ) = P ^ 2 + Q ^ 2 := by simp [normSq, Fin.sum_univ_two]
  simp [hn]

/-- `E(c|ζ|² + D)⁴ ≤ (c(m + 8) + D)⁴` for `c, D ≥ 0` (binomial expansion and `chi_mom`). -/
theorem chi_aff4 {c D : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D) :
    ∫⁻ ζ, ENNReal.ofReal ((c * normSq ζ + D) ^ 4) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((c * ((m : ℝ) + 8) + D) ^ 4) := by
  have hk : ∀ k : ℕ, k ≤ 4 → ∫⁻ ζ, ENNReal.ofReal ((normSq ζ) ^ k) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (((m : ℝ) + 8) ^ k) := fun k hk4 => by
    have := BstLean.Part166.chi_mom (ι := Fin m) k
    simp only [Fintype.card_fin] at this
    refine this.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ k))
    have : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
    linarith
  have hpt : ∀ ζ : Fin m → ℝ, ENNReal.ofReal ((c * normSq ζ + D) ^ 4) =
      ENNReal.ofReal (c ^ 4) * ENNReal.ofReal ((normSq ζ) ^ 4) +
      ENNReal.ofReal (4 * c ^ 3 * D) * ENNReal.ofReal ((normSq ζ) ^ 3) +
      ENNReal.ofReal (6 * c ^ 2 * D ^ 2) * ENNReal.ofReal ((normSq ζ) ^ 2) +
      ENNReal.ofReal (4 * c * D ^ 3) * ENNReal.ofReal ((normSq ζ) ^ 1) +
      ENNReal.ofReal (D ^ 4) := fun ζ => by
    have h0 : 0 ≤ normSq ζ := by unfold normSq; positivity
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  have mk : ∀ k : ℕ, Measurable (fun ζ : Fin m → ℝ => ENNReal.ofReal ((normSq ζ) ^ k)) := fun k =>
    ENNReal.measurable_ofReal.comp (continuous_normSq.measurable.pow_const k)
  simp_rw [hpt]
  have m4 := (mk 4).const_mul (ENNReal.ofReal (c ^ 4))
  have m3 := (mk 3).const_mul (ENNReal.ofReal (4 * c ^ 3 * D))
  have m2 := (mk 2).const_mul (ENNReal.ofReal (6 * c ^ 2 * D ^ 2))
  rw [lintegral_add_right _ measurable_const]
  rw [lintegral_add_left (f := fun a => ENNReal.ofReal (c ^ 4) * ENNReal.ofReal (normSq a ^ 4) +
      ENNReal.ofReal (4 * c ^ 3 * D) * ENNReal.ofReal (normSq a ^ 3) +
      ENNReal.ofReal (6 * c ^ 2 * D ^ 2) * ENNReal.ofReal (normSq a ^ 2)) (by exact (m4.add m3).add m2)]
  rw [lintegral_add_left (f := fun a => ENNReal.ofReal (c ^ 4) * ENNReal.ofReal (normSq a ^ 4) +
      ENNReal.ofReal (4 * c ^ 3 * D) * ENNReal.ofReal (normSq a ^ 3)) (by exact m4.add m3)]
  rw [lintegral_add_left m4]
  rw [lintegral_const_mul _ (mk 4), lintegral_const_mul _ (mk 3), lintegral_const_mul _ (mk 2),
    lintegral_const_mul _ (mk 1), lintegral_const, measure_univ, mul_one]
  calc _ ≤ ENNReal.ofReal (c ^ 4) * ENNReal.ofReal (((m : ℝ) + 8) ^ 4) +
        ENNReal.ofReal (4 * c ^ 3 * D) * ENNReal.ofReal (((m : ℝ) + 8) ^ 3) +
        ENNReal.ofReal (6 * c ^ 2 * D ^ 2) * ENNReal.ofReal (((m : ℝ) + 8) ^ 2) +
        ENNReal.ofReal (4 * c * D ^ 3) * ENNReal.ofReal (((m : ℝ) + 8) ^ 1) +
        ENNReal.ofReal (D ^ 4) := by
        gcongr
        · exact hk 4 le_rfl
        · exact hk 3 (by norm_num)
        · exact hk 2 (by norm_num)
        · exact hk 1 (by norm_num)
    _ = _ := by
        have hm : (0 : ℝ) ≤ (m : ℝ) + 8 := by positivity
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **The fourth moment of the plane energy**: for `P² + Q² + T ≤ t|y|²` (`T, t ≥ 0`),
`E(|Pξ₁ + Qξ₂|² + mT)⁴ ≤ ((m + 8)t|y|²)⁴`. -/
theorem plane_mom4 {P Q T Y : ℝ} (hT : 0 ≤ T) (hY : P ^ 2 + Q ^ 2 + T ≤ Y) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((normSq (P • ξ₁ + Q • ξ₂) + m * T) ^ 4)
      ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤ ENNReal.ofReal ((((m : ℝ) + 8) * Y) ^ 4) := by
  have hf : Measurable (fun z : Fin m → ℝ => ENNReal.ofReal ((normSq z + m * T) ^ 4)) :=
    ENNReal.measurable_ofReal.comp ((continuous_normSq.measurable.add_const _).pow_const 4)
  rw [pair_comb P Q hf]
  have e : ∀ ζ : Fin m → ℝ, normSq (√(P ^ 2 + Q ^ 2) • ζ) = (P ^ 2 + Q ^ 2) * normSq ζ := by
    intro ζ
    rw [BstLean.Part130.normSq_smul, Real.sq_sqrt (by positivity)]
  simp_rw [e]
  refine (chi_aff4 (by positivity) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
  refine pow_le_pow_left₀ (by positivity) ?_ 4
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

end pair

section meanInt
open BstLean.Part170
open BstLean.Part134 (res lam projPerp)
open BstLean.Part167 (perp normSq_perp_le perp_res)
open BstLean.Part148 (EuLip)
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

/-- **The mean energy, integral form**: `E_N Q ≤ E_v(|M₀a(v)|² + m t|w(v)|²)`,
`w(v) = perp r (perp h a(v))` (Part 170's `flQ_mean_le` before its sup bounds). -/
lemma flQ_mean_int {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ξ, flQ μ a h M₀ (matOf t ξ) ∂stdGauss (Fin m × Fin m) ≤
      ∫ v, (normSq (M₀ *ᵥ a v) + m * t * normSq (perp (res h (vmean μ a)) (perp h (a v)))) ∂μ := by
  set r := res h (vmean μ a)
  set w : V → Fin m → ℝ := fun v => perp r (perp h (a v))
  have hS := sqrtQ_euLip ha hK hΛ0 hΛ h M₀ ht
  have iF : Integrable (fun ξ => flQ μ a h M₀ (matOf t ξ)) (stdGauss (Fin m × Fin m)) := by
    have := euLip_sq_integrable (Real.sqrt_nonneg _) hS
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact Real.sq_sqrt (flQ_nonneg _ _ _ _)
  set u : Fin m → V → (Fin m × Fin m → ℝ) := fun j v p => if p.1 = j then √t * w v p.2 else 0
  have hu : ∀ j v (ξ : Fin m × Fin m → ℝ), (matOf t ξ *ᵥ w v) j = ξ ⬝ᵥ u j v := by
    intro j v ξ
    simp only [Matrix.mulVec, dotProduct, matOf, Matrix.of_apply, u, Fintype.sum_prod_type]
    rw [eq_comm, Finset.sum_eq_single j]
    · exact Finset.sum_congr rfl fun k _ => by simp; ring
    · intro b _ hb; exact Finset.sum_eq_zero fun k _ => by simp [hb]
    · simp
  have huu : ∀ j v, u j v ⬝ᵥ u j v = t * normSq (w v) := by
    intro j v
    simp only [dotProduct, u, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · unfold normSq; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp; rw [mul_mul_mul_comm, Real.mul_self_sqrt ht]; ring
    · intro b _ hb; exact Finset.sum_eq_zero fun k _ => by simp [hb]
    · simp
  have cw : Continuous (fun y : Fin m → ℝ => perp r (perp h y)) :=
    (continuous_perp r).comp (continuous_perp h)
  have mT : ∀ j, Measurable (fun p : (Fin m × Fin m → ℝ) × V =>
      ENNReal.ofReal (((M₀ *ᵥ a p.2) j + (matOf t p.1 *ᵥ w p.2) j) ^ 2)) := by
    intro j
    have hc : Continuous (fun q : (Fin m × Fin m → ℝ) × (Fin m → ℝ) =>
        ((M₀ *ᵥ q.2) j + (matOf t q.1 *ᵥ perp r (perp h q.2)) j) ^ 2) := by
      refine ((((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        continuous_snd))).add ((continuous_apply j).comp (Continuous.matrix_mulVec ?_
        (cw.comp continuous_snd)))).pow 2
      unfold matOf
      exact continuous_pi fun i => continuous_pi fun k =>
        continuous_const.mul ((continuous_apply (i, k)).comp continuous_fst)
    exact ENNReal.measurable_ofReal.comp (hc.measurable.comp (measurable_fst.prodMk
      (ha.comp measurable_snd)))
  -- pointwise in `ξ`
  have hpt : ∀ ξ, ENNReal.ofReal (flQ μ a h M₀ (matOf t ξ)) ≤
      ∑ j, ∫⁻ v, ENNReal.ofReal (((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ w v) j) ^ 2) ∂μ := by
    intro ξ
    unfold flQ
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => integral_nonneg fun v => sq_nonneg _]
    refine Finset.sum_le_sum fun j _ => ?_
    have cR : Continuous (fun y : Fin m → ℝ =>
        relu ((M₀ *ᵥ y) j + (matOf t ξ *ᵥ perp r (perp h y)) j) ^ 2) :=
      (continuous_relu.comp (((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        continuous_id)).add ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
        cw)))).pow 2
    rw [ofReal_integral_eq_lintegral_ofReal (int_comp_bdd ha hK cR)
      (Filter.Eventually.of_forall fun v => sq_nonneg _)]
    refine lintegral_mono fun v => ENNReal.ofReal_le_ofReal ?_
    have hr : ∀ x : ℝ, relu x ^ 2 ≤ x ^ 2 := fun x => by
      unfold relu
      rcases le_total 0 x with hx | hx
      · rw [max_eq_right hx]
      · rw [max_eq_left hx]; nlinarith [sq_nonneg x]
    exact hr _
  have hinner : ∀ j v, ∫⁻ ξ, ENNReal.ofReal (((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ w v) j) ^ 2)
      ∂stdGauss (Fin m × Fin m) = ENNReal.ofReal ((M₀ *ᵥ a v) j ^ 2 + t * normSq (w v)) := by
    intro j v
    simp_rw [hu j v]
    have iT := integrable_shift_sq (ι := Fin m × Fin m) ((M₀ *ᵥ a v) j) (u j v)
    rw [← ofReal_integral_eq_lintegral_ofReal iT (Filter.Eventually.of_forall fun ξ => sq_nonneg _),
      gauss_sq_shift, huu]
  have cX : Continuous (fun y : Fin m → ℝ => normSq (M₀ *ᵥ y) + m * t * normSq (perp r (perp h y))) :=
    (continuous_normSq.comp (Continuous.matrix_mulVec continuous_const continuous_id)).add
      (continuous_const.mul (continuous_normSq.comp cw))
  have iX : Integrable (fun v => normSq (M₀ *ᵥ a v) + m * t * normSq (w v)) μ :=
    int_comp_bdd ha hK cX
  have hX0 : ∀ v, 0 ≤ normSq (M₀ *ᵥ a v) + m * t * normSq (w v) := fun v => by
    unfold normSq; positivity
  have esum : ∀ v, ∑ j, ((M₀ *ᵥ a v) j ^ 2 + t * normSq (w v)) =
      normSq (M₀ *ᵥ a v) + m * t * normSq (w v) := fun v => by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold normSq; ring
  have key : ENNReal.ofReal (∫ ξ, flQ μ a h M₀ (matOf t ξ) ∂stdGauss (Fin m × Fin m)) ≤
      ENNReal.ofReal (∫ v, (normSq (M₀ *ᵥ a v) + m * t * normSq (w v)) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal iF (Filter.Eventually.of_forall fun ξ =>
      flQ_nonneg _ _ _ _)]
    calc ∫⁻ ξ, ENNReal.ofReal (flQ μ a h M₀ (matOf t ξ)) ∂stdGauss (Fin m × Fin m)
        ≤ ∫⁻ ξ, ∑ j, ∫⁻ v, ENNReal.ofReal (((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ w v) j) ^ 2) ∂μ
            ∂stdGauss (Fin m × Fin m) := lintegral_mono hpt
      _ = ∑ j, ∫⁻ v, ∫⁻ ξ, ENNReal.ofReal (((M₀ *ᵥ a v) j + (matOf t ξ *ᵥ w v) j) ^ 2)
            ∂stdGauss (Fin m × Fin m) ∂μ := by
          rw [lintegral_finsetSum _ fun j _ => (mT j).lintegral_prod_right']
          exact Finset.sum_congr rfl fun j _ => lintegral_lintegral_swap (mT j).aemeasurable
      _ = ∫⁻ v, ENNReal.ofReal (∑ j, ((M₀ *ᵥ a v) j ^ 2 + t * normSq (w v))) ∂μ := by
          simp_rw [hinner]
          rw [← lintegral_finsetSum]
          · refine lintegral_congr fun v => ?_
            rw [ENNReal.ofReal_sum_of_nonneg fun j _ => add_nonneg (sq_nonneg _)
              (mul_nonneg ht (normSq_nonneg _))]
          · intro j _
            refine ENNReal.measurable_ofReal.comp ?_
            exact (((measurable_pi_apply j).comp ((Continuous.matrix_mulVec continuous_const
              continuous_id).measurable.comp ha)).pow_const 2).add
              ((continuous_normSq.measurable.comp (cw.measurable.comp ha)).const_mul t)
      _ = ENNReal.ofReal (∫ v, (normSq (M₀ *ᵥ a v) + m * t * normSq (w v)) ∂μ) := by
          rw [ofReal_integral_eq_lintegral_ofReal iX (Filter.Eventually.of_forall hX0)]
          exact lintegral_congr fun v => by rw [esum]
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hX0)).mp key

end meanInt

section plane
open BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part134 (res lam projPerp glue)
open BstLean.Part167 (perp normSq_perp_le)
open BstLean.Part157 (cOf reb)
variable {n : ℕ}

/-- The coefficient of `ξ₁` in the plane part `M₀y`. -/
noncomputable def pP {m : ℕ} (t : ℝ) (h y : Fin m → ℝ) : ℝ :=
  (normSq h)⁻¹ * (∑ k, y k * h k) * (√t * √(normSq h))

/-- The coefficient of `ξ₂` in the plane part `M₀y`. -/
noncomputable def pQ {m : ℕ} (t : ℝ) (h r y : Fin m → ℝ) : ℝ :=
  (normSq r)⁻¹ * (∑ k, perp h y k * r k) * (√t * √(normSq r))

/-- **The plane part of the second layer** is `P(y)ξ₁ + Q(y)ξ₂`. -/
lemma M0_eq (t : ℝ) (h a ξ₁ ξ₂ y : Fin (mA n) → ℝ) :
    Mpl h (res h a) (cOf t h ξ₁) (cOf t (res h a) ξ₂) 0 *ᵥ y =
      pP t h y • ξ₁ + pQ t h (res h a) y • ξ₂ := by
  unfold Mpl reb glue cOf pP pQ
  simp only [Matrix.zero_mul, add_zero, Matrix.add_mulVec, Matrix.smul_mulVec,
    BstLean.Part167.vmv_mulVec, ← Matrix.mulVec_mulVec, BstLean.Part167.projPerp_mulVec, smul_smul]
  simp only [mul_assoc]

/-- Part 170's `normSq_perp_eq` for any dimension. -/
lemma normSq_perp_eq' {m : ℕ} (b z : Fin m → ℝ) :
    normSq (perp b z) = normSq z - (normSq b)⁻¹ * (∑ j, z j * b j) ^ 2 := by
  unfold perp
  set B := normSq b
  set cz := ∑ j, z j * b j
  have e1 : normSq (z - (B⁻¹ * cz) • b) = normSq z - 2 * (B⁻¹ * cz) * cz + (B⁻¹ * cz) ^ 2 * B := by
    unfold normSq
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∀ i, (z i - B⁻¹ * cz * b i) ^ 2 = z i ^ 2 - 2 * (B⁻¹ * cz) * (z i * b i) +
        (B⁻¹ * cz) ^ 2 * b i ^ 2 := fun i => by ring
    simp_rw [e]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [e1]
  by_cases hB : B = 0
  · rw [hB]; simp
  · field_simp; ring

/-- **Pythagoras in the plane**: `P(y)² + Q(y)² + t|perp r (perp h y)|² = t|y|²`. -/
lemma pyth_PQ {m : ℕ} {t : ℝ} (ht : 0 ≤ t) (h r y : Fin m → ℝ) :
    pP t h y ^ 2 + pQ t h r y ^ 2 + t * normSq (perp r (perp h y)) = t * normSq y := by
  have hp : pP t h y ^ 2 = t * ((normSq h)⁻¹ * (∑ k, y k * h k) ^ 2) := by
    unfold pP
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt (by unfold normSq; positivity)]
    by_cases hh : normSq h = 0
    · rw [hh]; simp
    · field_simp
  have hq : pQ t h r y ^ 2 = t * ((normSq r)⁻¹ * (∑ k, perp h y k * r k) ^ 2) := by
    unfold pQ
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt (by unfold normSq; positivity)]
    by_cases hh : normSq r = 0
    · rw [hh]; simp
    · field_simp
  have e1 := normSq_perp_eq' h y
  have e2 := normSq_perp_eq' r (perp h y)
  rw [hp, hq, e2, e1]; ring

lemma continuous_pP {m : ℕ} (t : ℝ) (h : Fin m → ℝ) : Continuous (pP t h) := by
  unfold pP; fun_prop

lemma continuous_pQ {m : ℕ} (t : ℝ) (h r : Fin m → ℝ) : Continuous (pQ t h r) := by
  unfold pQ
  have : Continuous (perp h) := by unfold perp; fun_prop
  refine (continuous_const.mul ?_).mul continuous_const
  exact continuous_finsetSum _ fun k _ => ((continuous_apply k).comp this).mul continuous_const

end plane

section outer
variable {m : ℕ}

/-- **The outer moment with a fourth-moment bound**: if `Ψ ≥ 0` and `Ψ⁴ ≤ G` with
`E_{ξ₁,ξ₂} G ≤ Y⁴`, then `E_{ξ₁,ξ₂}(a₁ + b₁√Ψ)⁸ ≤ (a₁ + b₁√Y)⁸`. -/
theorem outer_r {a₁ b₁ Y : ℝ} (ha : 0 < a₁) (hb : 0 < b₁) (hY : 0 < Y)
    {Ψ : (Fin m → ℝ) → (Fin m → ℝ) → ℝ} (hΨ0 : ∀ ξ₁ ξ₂, 0 ≤ Ψ ξ₁ ξ₂)
    {G : (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞} (hG : ∀ ξ₁ ξ₂, ENNReal.ofReal (Ψ ξ₁ ξ₂ ^ 4) ≤ G ξ₁ ξ₂)
    (hGi : ∫⁻ ξ₁, ∫⁻ ξ₂, G ξ₁ ξ₂ ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤ ENNReal.ofReal (Y ^ 4)) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(Ψ ξ₁ ξ₂)) ^ 8)
      ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤ ENNReal.ofReal ((a₁ + b₁ * √Y) ^ 8) := by
  set B₁ := b₁ * √Y
  have hB₁ : 0 < B₁ := by positivity
  set k₃ := (a₁ + B₁) ^ 7 / a₁ ^ 7
  set k₄ := (a₁ + B₁) ^ 7 / B₁ ^ 7
  have hk₃ : 0 ≤ k₃ := by positivity
  have hk₄ : 0 ≤ k₄ := by positivity
  have hpt : ∀ ξ₁ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(Ψ ξ₁ ξ₂)) ^ 8) ≤
      ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) * G ξ₁ ξ₂ := fun ξ₁ ξ₂ => by
    refine le_trans (b := ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) *
      ENNReal.ofReal (Ψ ξ₁ ξ₂ ^ 4)) ?_ (by gcongr; exact hG ξ₁ ξ₂)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := BstLean.Part170.pow8_split a₁ (b₁ * √(Ψ ξ₁ ξ₂)) ha hB₁
    rw [abs_of_pos ha, abs_of_nonneg (by positivity)] at h
    have e : (b₁ * √(Ψ ξ₁ ξ₂)) ^ 8 = b₁ ^ 8 * Ψ ξ₁ ξ₂ ^ 4 := by
      rw [mul_pow, show (8 : ℕ) = 2 * 4 from rfl, pow_mul (√_), Real.sq_sqrt (hΨ0 ξ₁ ξ₂)]
    rw [e] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(Ψ ξ₁ ξ₂)) ^ 8) ∂stdGauss (Fin m) ∂stdGauss (Fin m)
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) * G ξ₁ ξ₂)
          ∂stdGauss (Fin m) ∂stdGauss (Fin m) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hpt ξ₁ ξ₂
    _ = ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) *
          ∫⁻ ξ₁, ∫⁻ ξ₂, G ξ₁ ξ₂ ∂stdGauss (Fin m) ∂stdGauss (Fin m) := by
        have e1 : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal (k₃ * a₁ ^ 8) +
            ENNReal.ofReal (k₄ * b₁ ^ 8) * G ξ₁ ξ₂) ∂stdGauss (Fin m) =
            ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) *
              ∫⁻ ξ₂, G ξ₁ ξ₂ ∂stdGauss (Fin m) := fun ξ₁ => by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (k₃ * a₁ ^ 8) + ENNReal.ofReal (k₄ * b₁ ^ 8) * ENNReal.ofReal (Y ^ 4) := by
        gcongr
    _ = ENNReal.ofReal ((a₁ + B₁) ^ 8) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have e : B₁ ^ 8 = b₁ ^ 8 * Y ^ 4 := by
          simp only [B₁]
          rw [mul_pow, show (8 : ℕ) = 2 * 4 from rfl, pow_mul (√Y), Real.sq_sqrt hY.le]
        have hA7 : a₁ ^ 7 ≠ 0 := by positivity
        have hB7 : B₁ ^ 7 ≠ 0 := by positivity
        rw [show k₄ * b₁ ^ 8 * Y ^ 4 = k₄ * B₁ ^ 8 by rw [e]; ring]
        simp only [k₃, k₄]
        field_simp

/-- **Jensen for the fourth power**: `(E X)⁴ ≤ E X⁴` for a bounded measurable `X ≥ 0` on a
probability space, in `lintegral` form. -/
theorem jensen4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (h0 : ∀ ω, 0 ≤ X ω) {C : ℝ} (hC : ∀ ω, X ω ≤ C) :
    ENNReal.ofReal ((∫ ω, X ω ∂μ) ^ 4) ≤ ∫⁻ ω, ENNReal.ofReal (X ω ^ 4) ∂μ := by
  have hab : ∀ ω, |X ω| ≤ C := fun ω => by rw [abs_of_nonneg (h0 ω)]; exact hC ω
  have hab2 : ∀ ω, |X ω ^ 2| ≤ C ^ 2 := fun ω => by
    rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (h0 ω) (hC ω) 2
  have j1 := BstLean.Part172.mo_sq_int_le (μ := μ) hX hab
  have j2 := BstLean.Part172.mo_sq_int_le (μ := μ) (hX.pow_const 2) hab2
  have hE0 : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg h0
  have hj : (∫ ω, X ω ∂μ) ^ 4 ≤ ∫ ω, X ω ^ 4 ∂μ := by
    have e : (∫ ω, X ω ∂μ) ^ 4 = ((∫ ω, X ω ∂μ) ^ 2) ^ 2 := by ring
    have e2 : ∀ ω, (X ω ^ 2) ^ 2 = X ω ^ 4 := fun ω => by ring
    simp only [e2] at j2
    rw [e]
    exact (pow_le_pow_left₀ (sq_nonneg _) j1 2).trans j2
  have iX4 : Integrable (fun ω => X ω ^ 4) μ := by
    refine Integrable.mono' (integrable_const (C ^ 4)) (hX.pow_const 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := h0 ω; positivity)]
    exact pow_le_pow_left₀ (h0 ω) (hC ω) 4
  rw [← ofReal_integral_eq_lintegral_ofReal iX4
    (Filter.Eventually.of_forall fun ω => by have := h0 ω; positivity)]
  exact ENNReal.ofReal_le_ofReal hj

end outer

section planeE
open BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part134 (res lam projPerp glue)
open BstLean.Part167 (perp normSq_perp_le)
open BstLean.Part157 (cOf reb)
variable {n : ℕ}

/-- The plane energy `X(ξ₁, ξ₂, y) = |P(y)ξ₁ + Q(y)ξ₂|² + m·t|perp r (perp h y)|²`: the mean over
the transverse matrix of the energy at one point, before the sup bounds. -/
noncomputable def Xpl {m : ℕ} (t : ℝ) (h r ξ₁ ξ₂ y : Fin m → ℝ) : ℝ :=
  normSq (pP t h y • ξ₁ + pQ t h r y • ξ₂) + (m : ℝ) * (t * normSq (perp r (perp h y)))

lemma Xpl_nonneg {m : ℕ} {t : ℝ} (ht : 0 ≤ t) (h r ξ₁ ξ₂ y : Fin m → ℝ) : 0 ≤ Xpl t h r ξ₁ ξ₂ y := by
  unfold Xpl
  have := normSq_nonneg (pP t h y • ξ₁ + pQ t h r y • ξ₂)
  have := normSq_nonneg (perp r (perp h y))
  positivity

/-- `X = |M₀y|² + m t|w|²` for the plane matrix `M₀`. -/
lemma Xpl_eq (t : ℝ) (h a ξ₁ ξ₂ y : Fin (mA n) → ℝ) :
    normSq (Mpl h (res h a) (cOf t h ξ₁) (cOf t (res h a) ξ₂) 0 *ᵥ y) +
      (mA n : ℝ) * t * normSq (perp (res h a) (perp h y)) = Xpl t h (res h a) ξ₁ ξ₂ y := by
  unfold Xpl; rw [M0_eq]; ring

/-- The sup bound of `X`. -/
lemma Xpl_le {t : ℝ} (ht : 0 ≤ t) (h a ξ₁ ξ₂ y : Fin (mA n) → ℝ) {K2 : ℝ} (hy : normSq y ≤ K2) :
    Xpl t h (res h a) ξ₁ ξ₂ y ≤ t * K2 * (normSq ξ₁ + normSq ξ₂) + (mA n : ℝ) * (t * K2) := by
  rw [← Xpl_eq]
  have e1 := M0_bound ht h a ξ₁ ξ₂ y
  have e2 : normSq (perp (res h a) (perp h y)) ≤ K2 :=
    ((normSq_perp_le _ _).trans (normSq_perp_le h _)).trans hy
  have hX : 0 ≤ normSq ξ₁ + normSq ξ₂ := by unfold normSq; positivity
  have e3 := mul_le_mul_of_nonneg_left hy ht
  have hm0 : (0 : ℝ) ≤ mA n := Nat.cast_nonneg _
  have e4 : t * normSq y * (normSq ξ₁ + normSq ξ₂) ≤ t * K2 * (normSq ξ₁ + normSq ξ₂) :=
    mul_le_mul_of_nonneg_right e3 hX
  have e5 : (mA n : ℝ) * t * normSq (perp (res h a) (perp h y)) ≤ (mA n : ℝ) * (t * K2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 ht) hm0
  linarith

/-- **The fourth moment of the plane energy at one point**: `E_{ξ₁,ξ₂} X⁴ ≤ ((m + 8)t|y|²)⁴`. -/
lemma Xpl_mom4 {m : ℕ} {t : ℝ} (ht : 0 ≤ t) (h r y : Fin m → ℝ) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (Xpl t h r ξ₁ ξ₂ y ^ 4) ∂stdGauss (Fin m)
      ∂stdGauss (Fin m) ≤ ENNReal.ofReal ((((m : ℝ) + 8) * (t * normSq y)) ^ 4) := by
  have hT : 0 ≤ t * normSq (perp r (perp h y)) := mul_nonneg ht (normSq_nonneg _)
  exact plane_mom4 hT (pyth_PQ ht h r y).le

lemma meas_sec {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → β → γ} (hf : Measurable (fun p : α × β => f p.1 p.2)) (x : α) : Measurable (f x) :=
  hf.comp (measurable_prodMk_left (x := x))

/-- `Ψ(ξ₁, ξ₂) = E_v X(ξ₁, ξ₂, a(v))` at a node. -/
noncomputable def PsiR (c : Ret n) (s : ℝ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) : ℝ :=
  ∫ v, Xpl (tA n) (hB c) (res (hB c) (a1Bar c s)) ξ₁ ξ₂ (aLat c s v) ∂stdGauss (Fin (n - 1))

lemma measurable_Xv {m : ℕ} {V : Type*} [MeasurableSpace V] (t : ℝ) (h r : Fin m → ℝ)
    {a : V → Fin m → ℝ} (ha : Measurable a) :
    Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × V => Xpl t h r p.1.1 p.1.2 (a p.2)) := by
  unfold Xpl
  have c1 : Continuous (perp r) := by unfold perp; fun_prop
  have c2 : Continuous (perp h) := by unfold perp; fun_prop
  have ma : Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × V => a p.2) := ha.comp measurable_snd
  have mP : Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × V => pP t h (a p.2)) :=
    (continuous_pP t h).measurable.comp ma
  have mQ : Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × V => pQ t h r (a p.2)) :=
    (continuous_pQ t h r).measurable.comp ma
  have m1 : Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × V => p.1.1) :=
    measurable_fst.comp measurable_fst
  have m2 : Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × V => p.1.2) :=
    measurable_snd.comp measurable_fst
  have mw : Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × V => normSq (perp r (perp h (a p.2)))) :=
    continuous_normSq.measurable.comp ((c1.comp c2).measurable.comp ma)
  exact (continuous_normSq.measurable.comp ((mP.smul m1).add (mQ.smul m2))).add
    (measurable_const.mul (measurable_const.mul mw))

lemma measurable_PsiR (c : Ret n) (s : ℝ) :
    Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => PsiR c s p.1 p.2) :=
  ((measurable_Xv (tA n) (hB c) (res (hB c) (a1Bar c s)) (measurable_aLat c s)).stronglyMeasurable.integral_prod_right'
    (ν := stdGauss (Fin (n - 1)))).measurable

lemma measurable_PsiR2 (c : Ret n) (s : ℝ) (ξ₁ : Fin (mA n) → ℝ) :
    Measurable (PsiR c s ξ₁) :=
  meas_sec (measurable_PsiR c s) ξ₁

lemma PsiR_nonneg (c : Ret n) (s : ℝ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) : 0 ≤ PsiR c s ξ₁ ξ₂ :=
  integral_nonneg fun v => Xpl_nonneg (BstLean.Part171.tA_nonneg n) _ _ _ _ _

lemma measurable_Xv1 {m : ℕ} {V : Type*} [MeasurableSpace V] (t : ℝ) (h r ξ₁ ξ₂ : Fin m → ℝ)
    {a : V → Fin m → ℝ} (ha : Measurable a) :
    Measurable (fun v => Xpl t h r ξ₁ ξ₂ (a v)) := by
  unfold Xpl
  have c1 : Continuous (perp r) := by unfold perp; fun_prop
  have c2 : Continuous (perp h) := by unfold perp; fun_prop
  have mP : Measurable (fun v => pP t h (a v)) := (continuous_pP t h).measurable.comp ha
  have mQ : Measurable (fun v => pQ t h r (a v)) := (continuous_pQ t h r).measurable.comp ha
  have mw : Measurable (fun v => normSq (perp r (perp h (a v)))) :=
    continuous_normSq.measurable.comp ((c1.comp c2).measurable.comp ha)
  exact (continuous_normSq.measurable.comp ((mP.smul_const ξ₁).add (mQ.smul_const ξ₂))).add
    (measurable_const.mul (measurable_const.mul mw))

/-- **Jensen at a node**: `Ψ⁴ ≤ E_v X⁴`. -/
lemma PsiR_pow4_le (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ}
    (h1 : OpB (A1 c) O) (ξ₁ ξ₂ : Fin (mA n) → ℝ) :
    ENNReal.ofReal (PsiR c s ξ₁ ξ₂ ^ 4) ≤ ∫⁻ v, ENNReal.ofReal
      (Xpl (tA n) (hB c) (res (hB c) (a1Bar c s)) ξ₁ ξ₂ (aLat c s v) ^ 4) ∂stdGauss (Fin (n - 1)) :=
  jensen4 (measurable_Xv1 _ _ _ ξ₁ ξ₂ (measurable_aLat c s))
    (fun v => Xpl_nonneg (BstLean.Part171.tA_nonneg n) _ _ _ _ _)
    (fun v => Xpl_le (BstLean.Part171.tA_nonneg n) (hB c) (a1Bar c s) ξ₁ ξ₂ _
      (aLat_normSq_le hn c hs h1 v))

lemma measurable_Xp {m : ℕ} (t : ℝ) (h r y : Fin m → ℝ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => Xpl t h r p.1 p.2 y) := by
  unfold Xpl
  have hc : Continuous (fun p : (Fin m → ℝ) × (Fin m → ℝ) => pP t h y • p.1 + pQ t h r y • p.2) :=
    by fun_prop
  exact ((continuous_normSq.comp hc).add continuous_const).measurable

/-- `Xpl_mom4` with a bound `|y|² ≤ K2`. -/
lemma Xpl_mom4_le {m : ℕ} {t : ℝ} (ht : 0 ≤ t) (h r : Fin m → ℝ) {y : Fin m → ℝ} {K2 : ℝ}
    (hy : normSq y ≤ K2) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (Xpl t h r ξ₁ ξ₂ y ^ 4) ∂stdGauss (Fin m)
      ∂stdGauss (Fin m) ≤ ENNReal.ofReal ((t * K2 * ((m : ℝ) + 8)) ^ 4) := by
  refine (Xpl_mom4 ht h r y).trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ?_ ?_ 4))
  · exact mul_nonneg (by positivity) (mul_nonneg ht (normSq_nonneg _))
  · have h3 : t * normSq y ≤ t * K2 := mul_le_mul_of_nonneg_left hy ht
    have hm8 : (0 : ℝ) ≤ (m : ℝ) + 8 := by positivity
    nlinarith

/-- **The fourth moment of the plane energy, averaged**: for `|a(v)|² ≤ K2`,
`E_{ξ₁,ξ₂} E_v X(ξ₁, ξ₂, a(v))⁴ ≤ (t K2 (m + 8))⁴`. -/
lemma GR_int_gen {m : ℕ} {V : Type*} [MeasurableSpace V] {ν : Measure V} [IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 ≤ t) (h r : Fin m → ℝ) {a : V → Fin m → ℝ} (ha : Measurable a) {K2 : ℝ}
    (hK2 : ∀ v, normSq (a v) ≤ K2) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ v, ENNReal.ofReal (Xpl t h r ξ₁ ξ₂ (a v) ^ 4) ∂ν
      ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤ ENNReal.ofReal ((t * K2 * ((m : ℝ) + 8)) ^ 4) := by
  have mF4 : Measurable (fun p : ((Fin m → ℝ) × (Fin m → ℝ)) × V =>
      ENNReal.ofReal (Xpl t h r p.1.1 p.1.2 (a p.2) ^ 4)) :=
    ENNReal.measurable_ofReal.comp ((measurable_Xv t h r ha).pow_const 4)
  have mG : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      ∫⁻ v, ENNReal.ofReal (Xpl t h r p.1 p.2 (a v) ^ 4) ∂ν) :=
    mF4.lintegral_prod_right'
  have hv : ∀ v, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (Xpl t h r ξ₁ ξ₂ (a v) ^ 4)
      ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤ ENNReal.ofReal ((t * K2 * ((m : ℝ) + 8)) ^ 4) := by
    intro v
    exact Xpl_mom4_le ht h r (hK2 v)
  have hsec : ∀ v : V, Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      ENNReal.ofReal (Xpl t h r p.1 p.2 (a v) ^ 4)) := fun v =>
    ENNReal.measurable_ofReal.comp ((measurable_Xp t h r (a v)).pow_const 4)
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ v, ENNReal.ofReal (Xpl t h r ξ₁ ξ₂ (a v) ^ 4) ∂ν
        ∂stdGauss (Fin m) ∂stdGauss (Fin m)
      = ∫⁻ p, ∫⁻ v, ENNReal.ofReal (Xpl t h r p.1 p.2 (a v) ^ 4) ∂ν
          ∂(stdGauss (Fin m)).prod (stdGauss (Fin m)) :=
        (lintegral_prod _ mG.aemeasurable).symm
    _ = ∫⁻ v, ∫⁻ p, ENNReal.ofReal (Xpl t h r p.1 p.2 (a v) ^ 4)
          ∂(stdGauss (Fin m)).prod (stdGauss (Fin m)) ∂ν :=
        lintegral_lintegral_swap mF4.aemeasurable
    _ = ∫⁻ v, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (Xpl t h r ξ₁ ξ₂ (a v) ^ 4)
          ∂stdGauss (Fin m) ∂stdGauss (Fin m) ∂ν :=
        lintegral_congr fun v => lintegral_prod _ (hsec v).aemeasurable
    _ ≤ ∫⁻ _v, ENNReal.ofReal ((t * K2 * ((m : ℝ) + 8)) ^ 4) ∂ν := lintegral_mono hv
    _ = _ := by simp

end planeE

section momR
open BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part134 (res lam projPerp glue)
open BstLean.Part167 (perp normSq_perp_le)
open BstLean.Part157 (cOf reb)
open BstLean.Part173 (cov_bound_lat)
variable {n : ℕ}

/-- The energy fluctuation allowance without the factor `√3`:
`W_fl = a₁ + 2c₈√(tΛ)·√(t O²(m + 8))`, `Λ = q O²/(n − 2)` (Part 173's `WflQ` has
`2c₈√(tΛ)·√(tO²)·√3·√(m + 8)`). -/
noncomputable def WflR (n : ℕ) (O q : ℝ) : ℝ :=
  ((π / 2 * (25 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) ^ 2 +
    2 * (π / 2 * (18 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) +
    (π / 2 * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) ^ 2) +
  2 * (π / 2 * (18 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) *
    √(tA n * O ^ 2 * ((mA n : ℝ) + 8))

/-- **The energy fluctuation without the factor `√3`**: the same bound with `W_fl` computed from
the covariance `q·O²/(n − 2)`, for any `q ≥ 1 − s_g²`. -/
theorem exWn_mom_r (hn : 3 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 < O)
    (h1 : OpB (A1 c) O) {q : ℝ} (hq0 : 0 < q) (hq : 1 - nodeS c g ^ 2 ≤ q) {B : ℝ}
    (hB0 : 0 < B)
    (hBias : ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((WflR n O q + B) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  set s := nodeS c g with hsd
  set h := hB c
  set r := res h (a1Bar c s)
  set Λ := q * O ^ 2 / ((n : ℝ) - 2) with hΛd
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hΛ0 : 0 < Λ := by positivity
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hK2 : ∀ v, normSq (aLat c s v) ≤ O ^ 2 := aLat_normSq_le hn1 c hs h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ Λ * normSq e := fun e =>
    (cov_bound_lat hn c hs hO.le h1 e).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq (sq_nonneg O)) h2n.le)
      (normSq_nonneg e))
  set L := √(tA n * Λ) with hLd
  have hL : 0 < L := Real.sqrt_pos.mpr (mul_pos htA hΛ0)
  set a₁ := (π / 2 * (25 / 10) * L) ^ 2 + 2 * (π / 2 * (18 / 10) * L) + (π / 2 * L) ^ 2
  set b₁ := 2 * (π / 2 * (18 / 10) * L)
  set Y := tA n * O ^ 2 * ((mA n : ℝ) + 8) with hYd
  have hY : 0 < Y := by positivity
  have ha₁ : 0 < a₁ := by positivity
  have hb₁ : 0 < b₁ := by positivity
  set A := WflR n O q with hAd
  have hAe : A = a₁ + b₁ * √Y := by rw [hAd]; unfold WflR; rfl
  have hA : 0 < A := by rw [hAe]; positivity
  set k₁ := (A + B) ^ 7 / A ^ 7
  set k₂ := (A + B) ^ 7 / B ^ 7
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  -- the plane split
  have mF : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exWn_comp ((measurable_withA2 c).comp
      (measurable_snd.comp measurable_snd)) measurable_const).pow_const 8)
  have hps := BstLean.Part167.plane_split (q := mA n) (tA n) h (a1Bar c s) mF
  have e0 : ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) =
      ∫⁻ M, (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) (M *ᵥ h, M *ᵥ a1Bar c s, M)
        ∂gaussMat (mA n) (mA n) (tA n) := rfl
  rw [e0, hps]
  simp only
  have hΨ0 : ∀ ξ₁ ξ₂, 0 ≤ PsiR c s ξ₁ ξ₂ := PsiR_nonneg c s
  have mΨ : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => PsiR c s p.1 p.2) :=
    measurable_PsiR c s
  -- the inner bound at fixed plane coordinates
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
      (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(PsiR c s ξ₁ ξ₂)) ^ 8) +
        ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) := by
    intro ξ₁ ξ₂
    set c₁ := cOf (tA n) h ξ₁
    set c₂ := cOf (tA n) r ξ₂
    set M₀ := Mpl h r c₁ c₂ 0
    set C₀ := ∑ j, G2 √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)
    set E : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ := fun N =>
      exWn (withA2 c (reb h c₁ (reb r c₂ N))) g
    have mE : Measurable E :=
      measurable_exWn_comp ((measurable_withA2 c).comp (BstLean.Part157.measurable_reb_comp
        measurable_const measurable_const (BstLean.Part157.measurable_reb_comp measurable_const
          measurable_const measurable_id))) measurable_const
    have hE : ∀ N, E N = flQ (stdGauss (Fin (n - 1))) (aLat c s) h M₀ N - C₀ := fun N =>
      exWn_Mpl hn1 c g hK c₁ c₂ N
    set F : (Fin (mA n) × Fin (mA n) → ℝ) → ℝ := fun ζ =>
      flQ (stdGauss (Fin (n - 1))) (aLat c s) h M₀ (matOf (tA n) ζ)
    have hS := sqrtQ_euLip (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
    have iF : Integrable F (stdGauss (Fin (mA n) × Fin (mA n))) := by
      have := euLip_sq_integrable (Real.sqrt_nonneg _) hS
      refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
      exact Real.sq_sqrt (flQ_nonneg _ _ _ _)
    set qb := ∫ ζ, F ζ ∂stdGauss (Fin (mA n) × Fin (mA n))
    have hmE : biasW c g ξ₁ ξ₂ = qb - C₀ := by
      have e0 : biasW c g ξ₁ ξ₂ = ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) := rfl
      rw [e0, gaussMat_eq, integral_map (measurable_matOf _).aemeasurable mE.aestronglyMeasurable]
      have : (fun ζ => E (matOf (tA n) ζ)) = fun ζ => F ζ - C₀ := funext fun ζ => hE _
      rw [this]
      rw [integral_sub iF (integrable_const _)]
      simp
      rfl
    -- `qb ≤ Ψ(ξ₁, ξ₂)`
    have hqb : qb ≤ PsiR c s ξ₁ ξ₂ := by
      have := flQ_mean_int (μ := stdGauss (Fin (n - 1))) (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
      rw [vmean_aLat] at this
      refine this.trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)))
      exact Xpl_eq (tA n) h (a1Bar c s) ξ₁ ξ₂ (aLat c s v)
    have hfl := flQ_conc (measurable_aLat c s) hK hΛ0 hΛ h M₀ htA
    have hFl : (π / 2 * (25 / 10) * L) ^ 2 + 2 * (√qb + 1) * (π / 2 * (18 / 10) * L) +
        (π / 2 * L) ^ 2 ≤ a₁ + b₁ * √(PsiR c s ξ₁ ξ₂) := by
      have h1' : √qb ≤ √(PsiR c s ξ₁ ξ₂) := Real.sqrt_le_sqrt hqb
      have hc8 : 0 ≤ π / 2 * (18 / 10) * L := by positivity
      have := mul_le_mul_of_nonneg_left h1' (by positivity : (0:ℝ) ≤ 2 * (π / 2 * (18 / 10) * L))
      simp only [a₁, b₁]
      nlinarith
    have hpt : ∀ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ≤ ENNReal.ofReal k₁ *
        ENNReal.ofReal (|F ζ - qb| ^ 8) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
      intro ζ
      rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hk₂ (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow8_split (F ζ - qb) (biasW c g ξ₁ ξ₂) hA hB0
      have e8 : |biasW c g ξ₁ ξ₂| ^ 8 = biasW c g ξ₁ ξ₂ ^ 8 := (by decide : Even 8).pow_abs _
      rw [e8] at this
      have e : E (matOf (tA n) ζ) = F ζ - qb + biasW c g ξ₁ ξ₂ := by rw [hE, hmE]; ring
      rw [e]; exact this
    have cF : Continuous F :=
      ((hS.continuous (Real.sqrt_nonneg _)).pow 2).congr fun ζ => Real.sq_sqrt (flQ_nonneg _ _ _ _)
    have mfl : Measurable (fun ζ => ENNReal.ofReal (|F ζ - qb| ^ 8)) :=
      ENNReal.measurable_ofReal.comp (((cF.measurable.sub_const _).abs).pow_const 8)
    rw [gaussMat_eq, lintegral_map (f := fun N => ENNReal.ofReal (E N ^ 8))
      (ENNReal.measurable_ofReal.comp (mE.pow_const 8)) (measurable_matOf _)]
    calc ∫⁻ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ∂stdGauss (Fin (mA n) × Fin (mA n))
        ≤ ∫⁻ ζ, (ENNReal.ofReal k₁ * ENNReal.ofReal (|F ζ - qb| ^ 8) +
          ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n) × Fin (mA n)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal k₁ * ∫⁻ ζ, ENNReal.ofReal (|F ζ - qb| ^ 8)
            ∂stdGauss (Fin (mA n) × Fin (mA n)) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ mfl]
      _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(PsiR c s ξ₁ ξ₂)) ^ 8) +
            ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          gcongr
          refine hfl.trans (ENNReal.ofReal_le_ofReal ?_)
          exact pow_le_pow_left₀ (by positivity) hFl 8
      _ = _ := by rw [ENNReal.ofReal_mul hk₂]
  -- the outer integrals
  have hO8 := outer_r (m := mA n) ha₁ hb₁ hY hΨ0 (PsiR_pow4_le hn1 c hs h1)
    (by rw [hYd]; exact GR_int_gen htA.le h r (measurable_aLat c s) hK2)
  have mI : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) =>
      ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(PsiR c s p.1 p.2)) ^ 8)) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp ((measurable_const.add
      (measurable_const.mul mΨ.sqrt)).pow_const 8))
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
        (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(PsiR c s ξ₁ ξ₂)) ^ 8) +
          ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8))
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal k₁ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(PsiR c s ξ₁ ξ₂)) ^ 8)
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) +
          ENNReal.ofReal k₂ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        have e1 : ∀ ξ₁ : Fin (mA n) → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ *
            √(PsiR c s ξ₁ ξ₂)) ^ 8) + ENNReal.ofReal k₂ *
            ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n)) =
            ENNReal.ofReal k₁ * ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(PsiR c s ξ₁ ξ₂)) ^ 8)
              ∂stdGauss (Fin (mA n)) + ENNReal.ofReal k₂ *
            ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n)) := fun ξ₁ => by
          have mI1 : Measurable (fun ξ₂ : Fin (mA n) → ℝ =>
              ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(PsiR c s ξ₁ ξ₂)) ^ 8)) :=
            measurable_const.mul (ENNReal.measurable_ofReal.comp ((measurable_const.add
              (measurable_const.mul (measurable_PsiR2 c s ξ₁).sqrt)).pow_const 8))
          rw [lintegral_add_left mI1,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        have mJ : Measurable (fun ξ₁ : Fin (mA n) → ℝ => ENNReal.ofReal k₁ * ∫⁻ ξ₂,
            ENNReal.ofReal ((a₁ + b₁ * √(PsiR c s ξ₁ ξ₂)) ^ 8) ∂stdGauss (Fin (mA n))) := by
          refine measurable_const.mul ?_
          exact (ENNReal.measurable_ofReal.comp ((measurable_const.add
            (measurable_const.mul mΨ.sqrt)).pow_const 8)).lintegral_prod_right'
        rw [lintegral_add_left mJ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        gcongr
        rw [hAe]; exact hO8
    _ = ENNReal.ofReal ((A + B) ^ 8) := by
        rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_mul hk₂,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hA7 : A ^ 7 ≠ 0 := by positivity
        have hB7 : B ^ 7 ≠ 0 := by positivity
        simp only [k₁, k₂]
        field_simp

end momR

end BstLean.Part174
