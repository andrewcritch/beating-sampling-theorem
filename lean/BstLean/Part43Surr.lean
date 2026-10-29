import BstLean.Part43Defs
import BstLean.Part40Sign
import BstLean.Part42Trunc

/-!
# Part 43, wave 1: the surrogate law (Lemmas K and B)

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`. Specification:
`delegations/answers/p43-spec-opus.md`. Replace each `sorry` by a proof. Do not edit the statements.
Do not use `native_decide` or `axiom` anywhere.

Suggested route.
* `surr_signSym`: `bmin θ ≥ 0`, so `taylorExp K (qth b x) ≥ 1` and `Z_K ≥ 1`; the density is even in each
  coordinate. Reuse Part 37's `binghamK_ae_sphere` and the pattern of Part 40's `bingham_signSym`.
* `surr_bias` (Lemmas K and B): `bingham n θ = bingham n (bmin θ)` (the shift is constant on the sphere).
  With `v = b·u ∈ [0, A]`, `p_K(v)e^{−v} = Pr{Poi(v) ≤ K} ∈ [1 − δ_P, 1]`, `δ_P = Pr{Poi(A) > K}`;
  so `ρ = dQ̃/dD ∈ [1 − δ_P, 1/(1 − δ_P)]`. The Poisson Bernstein bound (sub-gamma, variance `A`, scale
  `1/3`) and `u*² = (2/3)L u* + 2AL` give `δ_P ≤ η/(1+η)`, so `|ρ − 1| ≤ η`. Then
  `E_Q̃ h − E_D h = E_D[(ρ − 1)(h − E_D h)]` and Cauchy–Schwarz.
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)

variable {n d : ℕ}

open scoped Pointwise
open BstLean.Part40 (flipAt)
open BstLean.Part37 (qth taylorExp ZK binghamK)

private noncomputable def reflection (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

private lemma reflection_apply (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    WithLp.ofLp (reflection i x) = flipAt i (WithLp.ofLp x) := by
  classical
  ext j
  change (if j = i then LinearIsometryEquiv.neg ℝ else
    LinearIsometryEquiv.refl ℝ ℝ) (x j) = if j = i then -x j else x j
  split_ifs <;> rfl

private lemma flip_invol (i : Fin n) (x : Fin n → ℝ) : flipAt i (flipAt i x) = x := by
  ext j
  by_cases h : j = i <;> simp [flipAt, h]

private lemma measurable_flip (i : Fin n) : Measurable (flipAt i) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j = i <;> simp only [flipAt, h, ite_true, ite_false] <;> fun_prop

private lemma uniform_flip (i : Fin n) :
    (BstLean.Part29.uniformSphere n).map (flipAt i) = BstLean.Part29.uniformSphere n := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let u : Metric.sphere (0 : E) 1 → (Fin n → ℝ) := fun x => WithLp.ofLp x.1
  have hu : Measurable u := by dsimp [u, E]; fun_prop
  have hf : Measurable (flipAt i) := measurable_flip i
  have he := (reflection i).measurePreserving
  have hinv (x : E) : reflection i (reflection i x) = x := by
    apply WithLp.ofLp_injective 2
    simp only [reflection_apply, flip_invol]
  have hcone (s : Set (Fin n → ℝ)) :
      Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (u ⁻¹' (flipAt i ⁻¹' s))) =
      reflection i ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (u ⁻¹' s))) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨r, hr, reflection i z.1, ?_, ?_⟩
      · refine ⟨⟨reflection i z.1, ?_⟩, ?_, rfl⟩
        · simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
            using z.2
        · simpa only [Set.mem_preimage, u, reflection_apply] using hz
      · exact ((reflection i).map_smul r z.1).symm
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hy⟩
      refine ⟨r, hr, reflection i z.1, ?_, ?_⟩
      · refine ⟨⟨reflection i z.1, ?_⟩, ?_, rfl⟩
        · simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
            using z.2
        · simpa only [Set.mem_preimage, u, reflection_apply, flip_invol] using hz
      · have hh := congrArg (reflection i) hy
        simpa only [LinearIsometryEquiv.map_smul, hinv] using hh
  apply Measure.ext
  intro s hs
  change ((((volume : Measure E).toSphere Set.univ)⁻¹ •
      ((volume : Measure E).toSphere.map u)).map (flipAt i)) s =
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
  exact he.measure_preimage_emb (reflection i).toHomeomorph.measurableEmbedding _

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


private lemma taylor_ge_one (K : ℕ) (v : ℝ) (hv : 0 ≤ v) : 1 ≤ taylorExp K v := by
  classical
  have h := Finset.single_le_sum (s := Finset.range (K + 1))
    (f := fun j => v ^ j / (j.factorial : ℝ))
    (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.zero_lt_succ K))
  simpa [taylorExp] using h

private lemma bmin_nonneg (θ : Fin n → ℝ) (i : Fin n) : 0 ≤ bmin θ i := by
  classical
  exact sub_nonneg.mpr (ciInf_le (Set.finite_range θ).bddBelow i)

private lemma etaQ_pos {ε : ℝ} (hε : 0 < ε) : 0 < etaQ ε := by
  unfold etaQ xi43
  exact lt_min (by positivity) (by norm_num)

private lemma Leta_pos {ε : ℝ} (hε : 0 < ε) : 0 < Leta ε := by
  apply Real.log_pos
  apply (lt_div_iff₀ (etaQ_pos hε)).mpr
  linarith

private lemma ustar_equation {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ustar A ε ^ 2 = (2 / 3 : ℝ) * Leta ε * ustar A ε + 2 * A * Leta ε := by
  have hL := Leta_pos hε
  have hs := Real.sq_sqrt (show 0 ≤ Leta ε ^ 2 / 9 + 2 * A * Leta ε by positivity)
  unfold ustar
  nlinarith

private lemma Kof43_ge {A ε : ℝ} : A + ustar A ε ≤ (Kof43 A ε : ℝ) :=
  Nat.le_ceil _

private lemma exp_sum (s : ℝ) :
    HasSum (fun k : ℕ => s ^ k / (k.factorial : ℝ)) (Real.exp s) := by
  simpa [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp s

private lemma taylor_tail_chernoff (K : ℕ) (v t : ℝ) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    Real.exp (-v) * (Real.exp v - taylorExp K v) ≤
      Real.exp (v * (Real.exp t - 1) - t * (K + 1)) := by
  have hs := (exp_sum v).summable
  have hs' := (exp_sum (v * Real.exp t)).summable
  have htail := hs.sum_add_tsum_nat_add (K + 1)
  rw [(exp_sum v).tsum_eq] at htail
  have htail' := hs'.sum_add_tsum_nat_add (K + 1)
  rw [(exp_sum (v * Real.exp t)).tsum_eq] at htail'
  have hbound : (∑' j : ℕ, (v * Real.exp t) ^ (j + (K + 1)) /
      ((j + (K + 1)).factorial : ℝ)) ≤ Real.exp (v * Real.exp t) := by
    have h0 : 0 ≤ ∑ j ∈ Finset.range (K + 1),
        (v * Real.exp t) ^ j / (j.factorial : ℝ) := by positivity
    linarith
  have hterm (j : ℕ) : v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ) ≤
      Real.exp (-t * (K + 1)) *
        ((v * Real.exp t) ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have he : 1 ≤ Real.exp (-t * (K + 1)) * Real.exp ((j + (K + 1) : ℕ) * t) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      push_cast
      nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
    have h0 : 0 ≤ v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ) := by positivity
    calc
      _ ≤ (Real.exp (-t * (K + 1)) * Real.exp ((j + (K + 1) : ℕ) * t)) *
          (v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ)) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right he h0
      _ = _ := by ring
  have hle := (hs.comp_injective (add_left_injective (K + 1))).tsum_le_tsum hterm
    ((hs'.comp_injective (add_left_injective (K + 1))).mul_left (Real.exp (-t * (K + 1))))
  rw [tsum_mul_left] at hle
  have hle' := hle.trans (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le)
  have heq : Real.exp v - taylorExp K v =
      ∑' j : ℕ, v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ) := by
    unfold taylorExp
    linarith
  rw [heq]
  calc
    _ ≤ Real.exp (-v) * (Real.exp (-t * (K + 1)) * Real.exp (v * Real.exp t)) :=
      mul_le_mul_of_nonneg_left hle' (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


private lemma factorial_ge (j : ℕ) : (2 : ℝ) * 3 ^ j ≤ ((j + 2).factorial : ℝ) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h : (3 : ℝ) ≤ j + 2 + 1 := by linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
    have hj : 0 ≤ ((j + 2).factorial : ℝ) := by positivity
    calc
      2 * (3 ^ j * 3) = 3 * (2 * 3 ^ j) := by ring
      _ ≤ 3 * ((j + 2).factorial : ℝ) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ _ := by push_cast; exact mul_le_mul_of_nonneg_right h hj

private lemma exp_bernstein (t : ℝ) (ht : 0 ≤ t) (ht3 : t < 3) :
    Real.exp t - 1 - t ≤ t ^ 2 / (2 * (1 - t / 3)) := by
  have hs := (exp_sum t).summable
  have htail := hs.sum_add_tsum_nat_add 2
  rw [(exp_sum t).tsum_eq] at htail
  have hg := hasSum_geometric_of_lt_one (show 0 ≤ t / 3 by positivity)
    (show t / 3 < 1 by linarith)
  have hterm (j : ℕ) : t ^ (j + 2) / ((j + 2).factorial : ℝ) ≤
      (t ^ 2 / 2) * (t / 3) ^ j := by
    calc
      _ ≤ t ^ (j + 2) / (2 * 3 ^ j) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_ge j)
      _ = _ := by rw [pow_add, div_pow]; field_simp
  have hle := (hs.comp_injective (add_left_injective 2)).tsum_le_tsum hterm
    (hg.summable.mul_left (t ^ 2 / 2))
  rw [tsum_mul_left, hg.tsum_eq] at hle
  norm_num [Finset.sum_range_succ] at htail
  calc
    _ = ∑' j : ℕ, t ^ (j + 2) / ((j + 2).factorial : ℝ) := by linarith
    _ ≤ (t ^ 2 / 2) * (1 - t / 3)⁻¹ := hle
    _ = _ := by rw [div_mul_eq_div_mul_one_div, one_div]

private lemma cutoff_tail (A ε v : ℝ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hv : 0 ≤ v) (hvA : v ≤ A) :
    Real.exp (-v) * (Real.exp v - taylorExp (Kof43 A ε) v) ≤
      etaQ ε / (1 + etaQ ε) := by
  have hη := etaQ_pos hε
  have hL := Leta_pos hε
  have hdelta : Real.exp (-Leta ε) = etaQ ε / (1 + etaQ ε) := by
    unfold Leta
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  by_cases hAz : A = 0
  · have hvz : v = 0 := by linarith
    rw [hvz]
    have hz : taylorExp (Kof43 A ε) 0 = 1 := by
      classical
      unfold taylorExp
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro j hj hj0; simp [zero_pow hj0]
      · simp
    rw [hz]
    simp only [Real.exp_zero, sub_self, mul_zero]
    positivity
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  let u := ustar A ε
  let c := A + u / 3
  let t := u / c
  have hu : 0 < u := by dsimp [u, ustar]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht3 : t < 3 := by
    dsimp [t]
    apply (div_lt_iff₀ hc).mpr
    dsimp [c]
    linarith
  have htden : 0 < 1 - t / 3 := by linarith
  have hcut := Kof43_ge (A := A) (ε := ε)
  have he := exp_bernstein t ht ht3
  have hrem : 0 ≤ Real.exp t - 1 - t := by linarith [Real.add_one_le_exp t]
  have hexp : v * (Real.exp t - 1) - t * ((Kof43 A ε : ℝ) + 1) ≤ -Leta ε := by
    have h1 := mul_le_mul_of_nonneg_left (show v ≤ A from hvA) hrem
    have h2 := mul_le_mul_of_nonneg_left he hA
    have h3 := mul_le_mul_of_nonneg_left (show A + u ≤ (Kof43 A ε : ℝ) + 1 by
      dsimp [u]; linarith) ht
    have hid : A * (t ^ 2 / (2 * (1 - t / 3))) - t * u = -Leta ε := by
      have huEq := ustar_equation hA hε
      change u ^ 2 = (2 / 3 : ℝ) * Leta ε * u + 2 * A * Leta ε at huEq
      dsimp [t, c]
      field_simp
      nlinarith [huEq]
    have h4 := mul_le_mul_of_nonneg_left hvA ht
    nlinarith only [h1, h2, h3, h4, hid]
  calc
    _ ≤ Real.exp (v * (Real.exp t - 1) - t * ((Kof43 A ε : ℝ) + 1)) :=
      taylor_tail_chernoff _ v t hv ht
    _ ≤ Real.exp (-Leta ε) := Real.exp_le_exp.mpr hexp
    _ = _ := hdelta


private lemma q_bmin_bounds (θ : Fin n → ℝ) (x : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) : 0 ≤ qth (bmin θ) x ∧
      qth (bmin θ) x ≤ BstLean.Part42.spread θ := by
  classical
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (bmin_nonneg θ i) (sq_nonneg _)
  · have hi (i : Fin n) : bmin θ i ≤ BstLean.Part42.spread θ := by
      unfold bmin BstLean.Part42.spread
      exact sub_le_sub_right (le_ciSup (Set.finite_range θ).bddAbove i) _
    calc
      _ ≤ ∑ i, BstLean.Part42.spread θ * x i ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hi i) (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum, hx, mul_one]

private lemma taylor_le_exp (K : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    taylorExp K v ≤ Real.exp v := by
  have h := (exp_sum v).summable.sum_add_tsum_nat_add (K + 1)
  rw [(exp_sum v).tsum_eq] at h
  have h0 : 0 ≤ ∑' j : ℕ, v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ) :=
    tsum_nonneg fun j => by positivity
  unfold taylorExp
  linarith

private lemma taylor_relative (hn : 1 ≤ n) (θ : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    Real.exp (qth (bmin θ) x) ≤
      (1 + etaQ ε) * taylorExp (Kof43 (BstLean.Part42.spread θ) ε) (qth (bmin θ) x) ∧
    taylorExp (Kof43 (BstLean.Part42.spread θ) ε) (qth (bmin θ) x) ≤
      Real.exp (qth (bmin θ) x) := by
  have hv := q_bmin_bounds θ x hx
  have h := cutoff_tail _ ε _ (BstLean.Part42.spread_nonneg hn θ) hε hv.1 hv.2
  have hη := etaQ_pos hε
  have hη1 : 0 < 1 + etaQ ε := by positivity
  have he : 0 < Real.exp (qth (bmin θ) x) := Real.exp_pos _
  have h' : (Real.exp (qth (bmin θ) x) -
      taylorExp (Kof43 (BstLean.Part42.spread θ) ε) (qth (bmin θ) x)) /
      Real.exp (qth (bmin θ) x) ≤ etaQ ε / (1 + etaQ ε) := by
    simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using h
  have h'' := (div_le_div_iff₀ he hη1).mp h'
  constructor
  · nlinarith only [h'']
  · exact taylor_le_exp _ _ hv.1

private lemma normalized_ratio_abs (a e za ze η : ℝ)
    (ha : 0 ≤ a) (he : 0 < e) (hza : 0 < za) (hze : 0 < ze) (hη : 0 ≤ η)
    (hlo : e ≤ (1 + η) * a) (hhi : a ≤ e)
    (hzlo : ze ≤ (1 + η) * za) (hzhi : za ≤ ze) :
    |(a / za) / (e / ze) - 1| ≤ η := by
  have hd : 0 < za * e := mul_pos hza he
  have hnumhi : a * ze ≤ (1 + η) * (za * e) := by
    calc
      _ ≤ e * ze := mul_le_mul_of_nonneg_right hhi hze.le
      _ ≤ e * ((1 + η) * za) := mul_le_mul_of_nonneg_left hzlo he.le
      _ = _ := by ring
  have hrawlo : (1 - η) * e ≤ a := by
    have h := mul_le_mul_of_nonneg_left hhi hη
    nlinarith only [hlo, h]
  have hnumlo : (1 - η) * (za * e) ≤ a * ze := by
    calc
      _ = ((1 - η) * e) * za := by ring
      _ ≤ a * za := mul_le_mul_of_nonneg_right hrawlo hza.le
      _ ≤ a * ze := mul_le_mul_of_nonneg_left hzhi ha
  have hform : (a / za) / (e / ze) - 1 = (a * ze - za * e) / (za * e) := by
    field_simp
  rw [hform, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  exact abs_le.mpr ⟨by nlinarith only [hnumlo], by nlinarith only [hnumhi]⟩

private lemma surrogate_ratio (hn : 1 ≤ n) (θ : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    |(taylorExp (Kof43 (BstLean.Part42.spread θ) ε) (qth (bmin θ) x) /
      ZK n (Kof43 (BstLean.Part42.spread θ) ε) (bmin θ)) /
      (Real.exp (qth (bmin θ) x) / BstLean.Part37.Zth n (bmin θ)) - 1| ≤ etaQ ε := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  let K := Kof43 (BstLean.Part42.spread θ) ε
  let b := bmin θ
  have hc : Continuous (fun x => taylorExp K (qth b x)) := by
    unfold taylorExp qth; fun_prop
  have hce : Continuous (fun x => Real.exp (qth b x)) := by unfold qth; fun_prop
  have hpos : 0 < ZK n K b := by
    have hge (y : Fin n → ℝ) : 1 ≤ taylorExp K (qth b y) :=
      taylor_ge_one K _ (Finset.sum_nonneg fun i _ =>
        mul_nonneg (bmin_nonneg θ i) (sq_nonneg _))
    have h := integral_mono (integrable_const (1 : ℝ)) (sphere_cont_integrable hn hc) hge
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact zero_lt_one.trans_le h
  have hbd : ∀ᵐ y ∂uniformSphere n,
      Real.exp (qth b y) ≤ (1 + etaQ ε) * taylorExp K (qth b y) ∧
      taylorExp K (qth b y) ≤ Real.exp (qth b y) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
    exact taylor_relative hn θ ε hε y hy
  have hzlo : BstLean.Part37.Zth n b ≤ (1 + etaQ ε) * ZK n K b := by
    have h := integral_mono_ae (sphere_cont_integrable hn hce)
      ((sphere_cont_integrable hn hc).const_mul (1 + etaQ ε)) (hbd.mono fun _ h => h.1)
    simpa only [integral_const_mul, ZK, BstLean.Part37.Zth] using h
  have hzhi : ZK n K b ≤ BstLean.Part37.Zth n b :=
    integral_mono_ae (sphere_cont_integrable hn hc) (sphere_cont_integrable hn hce)
      (hbd.mono fun _ h => h.2)
  exact normalized_ratio_abs _ _ _ _ _ (zero_le_one.trans (taylor_ge_one K _ (q_bmin_bounds θ x hx).1))
    (Real.exp_pos _) hpos (BstLean.Part37.Zth_pos hn b) (etaQ_pos hε).le
    (taylor_relative hn θ ε hε x hx).1 (taylor_relative hn θ ε hε x hx).2 hzlo hzhi

private lemma bingham_shift (_hn : 1 ≤ n) (θ : Fin n → ℝ) :
    BstLean.Part37.bingham n θ = BstLean.Part37.bingham n (bmin θ) := by
  have he : (fun x => Real.exp (qth θ x)) =ᵐ[uniformSphere n]
      (fun x => Real.exp (⨅ j, θ j) * Real.exp (qth (bmin θ) x)) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    rw [← Real.exp_add]
    congr 1
    unfold qth bmin
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hx, mul_one]
    ring
  have hz : BstLean.Part37.Zth n θ = Real.exp (⨅ j, θ j) * BstLean.Part37.Zth n (bmin θ) := by
    unfold BstLean.Part37.Zth
    rw [integral_congr_ae he, integral_const_mul]
  unfold BstLean.Part37.bingham
  apply withDensity_congr_ae
  filter_upwards [he] with x hx
  rw [hx, hz, mul_div_mul_left _ _ (Real.exp_ne_zero _)]

/-- The surrogate is a sign-symmetric law on the sphere. -/
theorem surr_signSym (hn : 1 ≤ n) (θ : Fin n → ℝ) (ε : ℝ) : SignSym n (surrT n θ ε) := by

  classical
  let K := Kof43 (BstLean.Part42.spread θ) ε
  let b := bmin θ
  have hc : Continuous (fun x => taylorExp K (qth b x)) := by
    unfold taylorExp qth
    fun_prop
  have hge (x : Fin n → ℝ) : 1 ≤ taylorExp K (qth b x) :=
    taylor_ge_one K _ (Finset.sum_nonneg fun i _ =>
      mul_nonneg (bmin_nonneg θ i) (sq_nonneg _))
  have hp : IsProbabilityMeasure (binghamK n K b) := by
    apply normalized_prob hn hc (Filter.Eventually.of_forall fun x =>
      zero_le_one.trans (hge x))
    have := BstLean.Part29.uniformSphere_isProbability n hn
    have hz : 1 ≤ ∫ x, taylorExp K (qth b x) ∂uniformSphere n := by
      simpa using integral_mono (integrable_const (1 : ℝ))
        (sphere_cont_integrable hn hc) hge
    linarith
  refine ⟨⟨hp, BstLean.Part37.binghamK_ae_sphere K b⟩, ?_⟩
  intro i
  have hf : Measurable (flipAt i) := measurable_flip i
  have hq (x : Fin n → ℝ) : qth b (flipAt i x) = qth b x := by
    unfold qth
    apply Finset.sum_congr rfl
    intro j _
    simp [flipAt]
  let w : (Fin n → ℝ) → ENNReal := fun x =>
    ENNReal.ofReal (taylorExp K (qth b x) / ZK n K b)
  have hw : Measurable w := by unfold w taylorExp qth; fun_prop
  have hpres : MeasurePreserving (flipAt i) (uniformSphere n) (uniformSphere n) :=
    ⟨hf, uniform_flip i⟩
  apply Measure.ext
  intro s hs
  change ((uniformSphere n).withDensity w).map (flipAt i) s =
    (uniformSphere n).withDensity w s
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hf hs), ← lintegral_indicator hs]
  have h := hpres.lintegral_comp (hw.indicator hs)
  rw [← h]
  apply lintegral_congr
  intro x
  simp only [Set.indicator_apply, Set.mem_preimage, w, hq]

private lemma sphere_integrable {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ]
    (hs : ∀ᵐ x ∂μ, ∑ i, x i ^ 2 = 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma weighted {w : (Fin n → ℝ) → ℝ} (hw : Continuous w)
    (hw0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x) (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f x ∂(uniformSphere n).withDensity (fun x => ENNReal.ofReal (w x))) =
      ∫ x, f x * w x ∂uniformSphere n := by
  rw [integral_withDensity_eq_integral_toReal_smul
    hw.measurable.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [hw0] with x hx
  simp [ENNReal.toReal_ofReal hx, mul_comm]


private lemma continuous_fval_map (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    Continuous (fun x => fval k f0 T (mapMD M x)) := by
  classical
  have hm (a : Fin n) : Continuous (fun x => mapMD M x a) := by
    unfold mapMD
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro β hβ
    apply Continuous.mul continuous_const
    unfold BstLean.Part36.monoVal
    exact continuous_multiset_prod β.1 (fun b _ => continuous_apply b)
  unfold fval contr
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro j hj
  apply continuous_finsetSum
  intro w hw
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro t ht
  exact hm (w t)

private lemma bias_from_ratio (hn : 1 ≤ n) (b : Fin n → ℝ) (K : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hT : ∀ x, 0 ≤ taylorExp K (qth b x))
    (hZ : 0 < ZK n K b) (hQ : IsProbabilityMeasure (binghamK n K b))
    (hbound : ∀ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) →
      |(taylorExp K (qth b x) / ZK n K b) /
        (Real.exp (qth b x) / BstLean.Part37.Zth n b) - 1| ≤ η)
    (h : (Fin n → ℝ) → ℝ) (ch : Continuous h) :
    |(∫ x, h x ∂BstLean.Part37.bingham n b) - (∫ x, h x ∂binghamK n K b)| ≤
      η * Real.sqrt (varU (BstLean.Part37.bingham n b) h) := by
  let μ := BstLean.Part37.bingham n b
  have : IsProbabilityMeasure μ := BstLean.Part37.bingham_isProb hn b
  have : IsProbabilityMeasure (binghamK n K b) := hQ
  have hs := BstLean.Part37.bingham_ae_sphere b
  have hz := BstLean.Part37.Zth_pos hn b
  let r : (Fin n → ℝ) → ℝ := fun x =>
    (taylorExp K (qth b x) / ZK n K b) / (Real.exp (qth b x) / BstLean.Part37.Zth n b)
  have ct : Continuous (fun x => taylorExp K (qth b x)) := by unfold taylorExp qth; fun_prop
  have ce : Continuous (fun x => Real.exp (qth b x)) := by unfold qth; fun_prop
  have cr : Continuous r :=
    (ct.div_const _).div (ce.div_const _) (fun x => div_ne_zero (Real.exp_ne_zero _) hz.ne')
  have transfer (f : (Fin n → ℝ) → ℝ) :
      ∫ x, f x * r x ∂μ = ∫ x, f x ∂binghamK n K b := by
    dsimp [μ]
    unfold BstLean.Part37.bingham binghamK
    rw [weighted (w := fun x => Real.exp (qth b x) / BstLean.Part37.Zth n b)
      (ce.div_const _)
      (Filter.Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hz.le),
      weighted (w := fun x => taylorExp K (qth b x) / ZK n K b)
        (ct.div_const _)
        (Filter.Eventually.of_forall fun x => div_nonneg (hT x) hZ.le)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp [r]
      field_simp [hz.ne', hZ.ne']
  have ir : ∫ x, r x ∂μ = 1 := by simpa using transfer (fun _ => 1)
  let B := ∫ x, h x ∂μ
  let u : (Fin n → ℝ) → ℝ := fun x => h x - B
  have cu : Continuous u := ch.sub continuous_const
  have integrable_cont {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f μ :=
    sphere_integrable hs hf
  have iu := integrable_cont cu
  have ie : Integrable (fun x => r x - 1) μ := integrable_cont (cr.sub continuous_const)
  have ieu : Integrable (fun x => (r x - 1) * u x) μ :=
    integrable_cont ((cr.sub continuous_const).mul cu)
  have ihr : Integrable (fun x => h x * r x) μ := integrable_cont (ch.mul cr)
  have ih := integrable_cont ch
  have he : ∫ x, r x - 1 ∂μ = 0 := by
    rw [integral_sub (integrable_cont cr) (integrable_const _), ir]
    simp
  have hd : (∫ x, h x ∂binghamK n K b) - B = ∫ x, (r x - 1) * u x ∂μ := by
    have hp : (fun x => (r x - 1) * u x) =
        (fun x => (h x * r x - h x) - B * (r x - 1)) := by
      funext x
      dsimp [u]
      ring
    rw [hp, integral_sub (f := fun x => h x * r x - h x)
      (g := fun x => B * (r x - 1)) (ihr.sub ih) (ie.const_mul _),
      integral_sub ihr ih, integral_const_mul, he, transfer h]
    simp [B]
  have hb : ∀ᵐ x ∂μ, |(r x - 1) * u x| ≤ η * |u x| := by
    filter_upwards [hs] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg _)
  have ha : |∫ x, (r x - 1) * u x ∂μ| ≤ η * ∫ x, |u x| ∂μ := by
    calc
      _ ≤ ∫ x, |(r x - 1) * u x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, η * |u x| ∂μ := integral_mono_ae ieu.abs (iu.abs.const_mul _) hb
      _ = _ := integral_const_mul _ _
  let a := ∫ x, |u x| ∂μ
  have ha0 : 0 ≤ a := integral_nonneg (fun _ => abs_nonneg _)
  have hv : a ^ 2 ≤ ∫ x, u x ^ 2 ∂μ := by
    have hp : (fun x => (|u x| - a) ^ 2) =
        (fun x => (u x ^ 2 - (2 * a) * |u x|) + a ^ 2) := by
      funext x
      nlinarith [sq_abs (u x)]
    have hi2 : Integrable (fun x => u x ^ 2) μ := integrable_cont (cu.pow 2)
    have hh : 0 ≤ ∫ x, (|u x| - a) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    rw [hp, integral_add (f := fun x => u x ^ 2 - (2 * a) * |u x|)
      (g := fun _ => a ^ 2) (hi2.sub (iu.abs.const_mul _)) (integrable_const _),
      integral_sub hi2 (iu.abs.const_mul _), integral_const_mul] at hh
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    dsimp [a] at *
    nlinarith
  have hv0 : 0 ≤ ∫ x, u x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hasqrt : a ≤ Real.sqrt (∫ x, u x ^ 2 ∂μ) := by
    nlinarith [Real.sq_sqrt hv0, Real.sqrt_nonneg (∫ x, u x ^ 2 ∂μ)]
  rw [abs_sub_comm, hd]
  exact ha.trans (mul_le_mul_of_nonneg_left hasqrt hη)

/-- **Lemmas K and B**: `|B_D(M) − B_Q̃(M)| ≤ η_Q sd_D f(Mφ)` for every `M`. -/
theorem surr_bias (hn : 1 ≤ n) (θ : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (M : CoefIdxD n d → ℝ) :
    |BofQ (BstLean.Part37.bingham n θ) k f0 T M - BofQ (surrT n θ ε) k f0 T M| ≤
      etaQ ε * Real.sqrt (varFQ (BstLean.Part37.bingham n θ) k f0 T M) := by

  have hshift := bingham_shift hn θ
  rw [hshift]
  let K := Kof43 (BstLean.Part42.spread θ) ε
  let b := bmin θ
  have hge (x : Fin n → ℝ) : 1 ≤ taylorExp K (qth b x) :=
    taylor_ge_one K _ (Finset.sum_nonneg fun i _ => mul_nonneg (bmin_nonneg θ i) (sq_nonneg _))
  have hc : Continuous (fun x => taylorExp K (qth b x)) := by
    unfold taylorExp qth; fun_prop
  have hZ : 0 < ZK n K b := by
    have := BstLean.Part29.uniformSphere_isProbability n hn
    have h := integral_mono (integrable_const (1 : ℝ)) (sphere_cont_integrable hn hc) hge
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact zero_lt_one.trans_le h
  exact bias_from_ratio hn b K (etaQ ε) (etaQ_pos hε).le
    (fun x => zero_le_one.trans (hge x)) hZ (surr_signSym hn θ ε).1.1
    (surrogate_ratio hn θ ε hε) (fun x => fval k f0 T (mapMD M x))
    (continuous_fval_map k f0 T M)


end BstLean.Part43

