import BstLean.Part50Defs
import BstLean.Part43Surr

/-!
# Part 50, wave 1 (proved): the laws `binghamA`, `binghamKA` and the shift

Specification: `delegations/answers/p50-spec-opus.md` §3 (file `Part50Laws`). Paper: omGA-opus-prover §2, §5.1.

* `qA_shiftA`: on the sphere, `qA (shiftA A i0 N) x = qA A x − A_{i0 i0} + N`.
* `shiftA_psd`, `shiftA_range`, `shiftA_entry`: for `SpreadLE A Λ`, `Λ ≤ N`: `shiftA A i0 N ⪰ 0`,
  its form is `≤ 2N` on the sphere, and (for symmetric `A`) its entries are `≤ 2N` in absolute value.
* `binghamA_antipodal`, `binghamKA_antipodal`: both laws are antipodal laws on the sphere
  (pattern: `Part40Sign.bingham_signSym`, `Part43Surr.surr_signSym`, with `x ↦ −x` for `flipAt i`).

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part50

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)
open BstLean.Part43

variable {n d : ℕ}

open scoped Pointwise

/-! ### Algebra of `qA` -/

theorem qA_smul (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    qA B (fun i => c * x i) = c ^ 2 * qA B x := by
  unfold qA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

theorem qA_neg (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : qA B (-x) = qA B x := by
  unfold qA
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [Pi.neg_apply]; ring

theorem qA_single (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    qA B (Pi.single i 1) = B i i := by
  classical
  unfold qA
  simp [Pi.single_apply]

theorem qA_pair (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (c : ℝ) :
    qA B (fun a => (Pi.single i (1 : ℝ) : Fin n → ℝ) a + c * (Pi.single j (1 : ℝ) : Fin n → ℝ) a) =
      B i i + c * B i j + c * B j i + c ^ 2 * B j j := by
  classical
  unfold qA
  simp only [Pi.single_apply, mul_add, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem qA_shiftA (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (N : ℕ) (x : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) : qA (shiftA A i0 N) x = qA A x - A i0 i0 + N := by
  classical
  have h : qA (shiftA A i0 N) x = qA A x - (A i0 i0 - N) * ∑ i, x i ^ 2 := by
    unfold qA shiftA
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    ring
  rw [h, hx]; ring

/-- Scaling: a bound on the sphere gives a bound everywhere. -/
private theorem qA_scale (B : Matrix (Fin n) (Fin n) ℝ) (lo hi : ℝ)
    (h : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → lo ≤ qA B x ∧ qA B x ≤ hi) (x : Fin n → ℝ) :
    lo * ∑ i, x i ^ 2 ≤ qA B x ∧ qA B x ≤ hi * ∑ i, x i ^ 2 := by
  set r2 := ∑ i, x i ^ 2 with hr2
  have hr0 : 0 ≤ r2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hr0.eq_or_lt with h0 | hpos
  · have hx0 : ∀ i, x i = 0 := by
      intro i
      have := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [← hr2, ← h0] at this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
    have : qA B x = 0 := by unfold qA; simp [hx0]
    rw [this, ← h0]; simp
  · set r := Real.sqrt r2 with hr
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hrr : r ^ 2 = r2 := Real.sq_sqrt hr0
    set u : Fin n → ℝ := fun i => r⁻¹ * x i with hu
    have hu1 : ∑ i, u i ^ 2 = 1 := by
      simp only [hu, mul_pow, ← Finset.mul_sum, inv_pow, hrr]
      exact inv_mul_cancel₀ hpos.ne'
    have hxu : x = fun i => r * u i := by
      funext i; simp only [hu]; field_simp
    have hq : qA B x = r2 * qA B u := by rw [hxu, qA_smul, hrr]
    obtain ⟨h1, h2⟩ := h u hu1
    rw [hq]
    constructor <;> nlinarith

private theorem shift_bounds (A : Matrix (Fin n) (Fin n) ℝ) (Λ : ℝ) (hA : SpreadLE A Λ) (i0 : Fin n)
    (N : ℕ) (hN : Λ ≤ N) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    0 ≤ qA (shiftA A i0 N) x ∧ qA (shiftA A i0 N) x ≤ 2 * N := by
  classical
  have he : ∑ i, (Pi.single i0 (1 : ℝ) : Fin n → ℝ) i ^ 2 = 1 := by
    simp [Pi.single_apply]
  have h1 := hA _ _ he hx
  have h2 := hA _ _ hx he
  rw [qA_single] at h1 h2
  rw [qA_shiftA A i0 N x hx]
  constructor <;> linarith

theorem shiftA_psd (A : Matrix (Fin n) (Fin n) ℝ) (Λ : ℝ) (hA : SpreadLE A Λ) (i0 : Fin n) (N : ℕ)
    (hN : Λ ≤ N) : PSDq (shiftA A i0 N) := by
  intro x
  have := (qA_scale (shiftA A i0 N) 0 (2 * N)
    (fun y hy => shift_bounds A Λ hA i0 N hN y hy) x).1
  simpa using this

theorem shiftA_range (A : Matrix (Fin n) (Fin n) ℝ) (Λ : ℝ) (hA : SpreadLE A Λ) (i0 : Fin n) (N : ℕ)
    (hN : Λ ≤ N) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : qA (shiftA A i0 N) x ≤ 2 * N :=
  (shift_bounds A Λ hA i0 N hN x hx).2

theorem shiftA_entry (A : Matrix (Fin n) (Fin n) ℝ) (hS : A.IsSymm) (Λ : ℝ) (hA : SpreadLE A Λ)
    (i0 : Fin n) (N : ℕ) (hN : Λ ≤ N) (i j : Fin n) : |shiftA A i0 N i j| ≤ 2 * N := by
  classical
  set B := shiftA A i0 N with hB
  have hsc := qA_scale B 0 (2 * N) (fun y hy => shift_bounds A Λ hA i0 N hN y hy)
  have hsymB : B j i = B i j := by
    rw [hB]; unfold shiftA
    have : A j i = A i j := by
      have := congrFun (congrFun hS i) j
      simpa [Matrix.transpose_apply] using this
    rw [this]
    by_cases h : i = j
    · subst h; rfl
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h'.symm h), ite_eq_right_iff.mpr (fun h' => absurd h' h)]
  have hii := hsc (Pi.single i 1)
  have hjj := hsc (Pi.single j 1)
  rw [qA_single] at hii hjj
  have hsq : ∀ a : Fin n, ∑ b, (Pi.single a (1 : ℝ) : Fin n → ℝ) b ^ 2 = 1 := by
    intro a; simp [Pi.single_apply]
  rw [hsq] at hii hjj
  by_cases hij : i = j
  · subst hij
    rw [abs_le]; constructor <;> linarith [hii.1, hii.2]
  · have hp := hsc (fun a => (Pi.single i (1 : ℝ) : Fin n → ℝ) a + 1 * (Pi.single j (1 : ℝ) : Fin n → ℝ) a)
    have hm := hsc (fun a => (Pi.single i (1 : ℝ) : Fin n → ℝ) a + (-1) * (Pi.single j (1 : ℝ) : Fin n → ℝ) a)
    rw [qA_pair] at hp hm
    have hnorm : ∀ c : ℝ, ∑ a, ((Pi.single i (1 : ℝ) : Fin n → ℝ) a + c * (Pi.single j (1 : ℝ) : Fin n → ℝ) a) ^ 2 = 1 + c ^ 2 := by
      intro c
      simp only [Pi.single_apply, add_sq, Finset.sum_add_distrib, ite_pow, one_pow,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [ite_eq_right_iff.mpr (fun h' => absurd h'.symm hij)]; ring
    rw [hnorm] at hp hm
    rw [hsymB] at hp hm
    rw [abs_le]; constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2, hii.1, hjj.1]

/-! ### Antipodal symmetry -/

private noncomputable def negIso : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.neg ℝ

private lemma negIso_apply (x : EuclideanSpace ℝ (Fin n)) :
    WithLp.ofLp (negIso x) = -(WithLp.ofLp x) := rfl

private lemma uniform_neg :
    (uniformSphere n).map (fun x => -x) = uniformSphere n := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let u : Metric.sphere (0 : E) 1 → (Fin n → ℝ) := fun x => WithLp.ofLp x.1
  have hu : Measurable u := by dsimp [u, E]; fun_prop
  have hf : Measurable (fun x : Fin n → ℝ => -x) := measurable_neg
  have he := (negIso (n := n)).measurePreserving
  have hinv (x : E) : negIso (negIso x) = x := by simp [negIso]
  have hcone (s : Set (Fin n → ℝ)) :
      Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (u ⁻¹' ((fun x : Fin n → ℝ => -x) ⁻¹' s))) =
      negIso ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (u ⁻¹' s))) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨r, hr, negIso z.1, ?_, ?_⟩
      · refine ⟨⟨negIso z.1, ?_⟩, ?_, rfl⟩
        · simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
            using z.2
        · simpa only [Set.mem_preimage, u, negIso_apply] using hz
      · exact ((negIso (n := n)).map_smul r z.1).symm
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hy⟩
      refine ⟨r, hr, negIso z.1, ?_, ?_⟩
      · refine ⟨⟨negIso z.1, ?_⟩, ?_, rfl⟩
        · simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
            using z.2
        · simpa only [Set.mem_preimage, u, negIso_apply, neg_neg] using hz
      · have hh := congrArg negIso hy
        simpa only [LinearIsometryEquiv.map_smul, hinv] using hh
  apply Measure.ext
  intro s hs
  change ((((volume : Measure E).toSphere Set.univ)⁻¹ •
      ((volume : Measure E).toSphere.map u)).map (fun x : Fin n → ℝ => -x)) s =
    (((volume : Measure E).toSphere Set.univ)⁻¹ •
      ((volume : Measure E).toSphere.map u)) s
  rw [Measure.map_smul _ hf.aemeasurable]
  rw [Measure.map_map hf hu]
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [Measure.map_apply (hf.comp hu) hs, Measure.map_apply hu hs]
  rw [Set.preimage_comp]
  rw [Measure.toSphere_apply' _ (hu (hf hs)), Measure.toSphere_apply' _ (hu hs), hcone]
  congr 1
  exact he.measure_preimage_emb (negIso (n := n)).toHomeomorph.measurableEmbedding _

private lemma sphere_cont_integrable (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma normalized_prob (hn : 1 ≤ n) {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hw0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x)
    (hz : 0 < ∫ x, w x ∂uniformSphere n) :
    IsProbabilityMeasure ((uniformSphere n).withDensity
      (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂uniformSphere n))) := by
  have hi := (sphere_cont_integrable hn hw).div_const (∫ y, w y ∂uniformSphere n)
  have h0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x / ∫ y, w y ∂uniformSphere n :=
    hw0.mono (fun x hx => div_nonneg hx hz.le)
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi h0, integral_div,
    div_self hz.ne', ENNReal.ofReal_one]

/-- A density law with an even, continuous, nonnegative weight of positive mass is antipodal. -/
private lemma antipodal_of_weight (hn : 1 ≤ n) {w : (Fin n → ℝ) → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hz : 0 < ∫ x, w x ∂uniformSphere n) (hev : ∀ x, w (-x) = w x) :
    Antipodal n ((uniformSphere n).withDensity
      (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂uniformSphere n))) := by
  classical
  refine ⟨⟨normalized_prob hn hw (Filter.Eventually.of_forall hw0) hz,
    (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)⟩, ?_⟩
  have hf : Measurable (fun x : Fin n → ℝ => -x) := measurable_neg
  let W : (Fin n → ℝ) → ENNReal := fun x => ENNReal.ofReal (w x / ∫ y, w y ∂uniformSphere n)
  have hW : Measurable W := (hw.measurable.div_const _).ennreal_ofReal
  have hp : MeasurePreserving (fun x : Fin n → ℝ => -x) (uniformSphere n) (uniformSphere n) :=
    ⟨hf, uniform_neg⟩
  apply Measure.ext
  intro s hs
  change ((uniformSphere n).withDensity W).map (fun x => -x) s = (uniformSphere n).withDensity W s
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hf hs), ← lintegral_indicator hs]
  have h := hp.lintegral_comp (hW.indicator hs)
  rw [← h]
  apply lintegral_congr
  intro x
  simp only [Set.indicator_apply, Set.mem_preimage, W, hev]

private lemma continuous_qA (B : Matrix (Fin n) (Fin n) ℝ) : Continuous (qA B) := by
  unfold qA; fun_prop

theorem binghamA_antipodal (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) : Antipodal n (binghamA n A) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hc : Continuous (fun x => Real.exp (qA A x)) := Real.continuous_exp.comp (continuous_qA A)
  have hz : 0 < ∫ x, Real.exp (qA A x) ∂uniformSphere n := by
    exact integral_exp_pos (sphere_cont_integrable hn hc)
  exact antipodal_of_weight hn hc (fun x => (Real.exp_pos _).le) hz (fun x => by rw [qA_neg])

theorem binghamKA_antipodal (hn : 1 ≤ n) (K : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : PSDq B) :
    Antipodal n (binghamKA n K B) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hc : Continuous (fun x => BstLean.Part37.taylorExp K (qA B x)) := by
    unfold BstLean.Part37.taylorExp; have := continuous_qA B; fun_prop
  have h1 : ∀ x, 1 ≤ BstLean.Part37.taylorExp K (qA B x) := by
    intro x
    unfold BstLean.Part37.taylorExp
    rw [Finset.sum_range_succ']
    have : 0 ≤ ∑ i ∈ Finset.range K, qA B x ^ (i + 1) / ((i + 1).factorial : ℝ) :=
      Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg (hB x) _) (by positivity)
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    linarith
  have hz : 0 < ∫ x, BstLean.Part37.taylorExp K (qA B x) ∂uniformSphere n := by
    have := integral_mono (integrable_const (1 : ℝ)) (sphere_cont_integrable hn hc) h1
    simp at this; linarith
  exact antipodal_of_weight hn hc (fun x => le_trans zero_le_one (h1 x)) hz
    (fun x => by rw [qA_neg])

end BstLean.Part50
