import BstLean.Part133World

/-!
# Part 133: the World network in `L²`, refined

Role: `delegations/statements/p133-spec.md`. Paper source: `onW4c-cx.md` §4 (links `W_3`,
`W_2`, `W_1`, `u`).

* `world_cos_L2g`: the World link with the factor `1 − κ(κ(t))²` of the cosine link kept.
* `sphere_kk_L2r`: `‖κ(κ(⟨u, u′⟩)) − κ(κ(0))‖₂ ≤ 0.507/√N + (8/25)√3/N`.
* `sphere_gW_L2`: the `L²` norm over the inputs of `c·(1 − κ(κ(⟨u, u′⟩))²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

variable {N m n : ℕ}

lemma L2le.abs_le_ae_R {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ} {a : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : L2le μ g a)
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ |g ω|) : L2le μ f a := by
  have h2 : ∀ᵐ ω ∂μ, f ω ^ 2 ≤ g ω ^ 2 := h.mono fun ω hω => by
    rw [← sq_abs (f ω), ← sq_abs (g ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hi : Integrable (fun ω => f ω ^ 2) μ := by
    refine Integrable.mono' hg.int_sq (hf.pow 2) (h2.mono fun ω hω => ?_)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ⟨hf, hi, (integral_mono_ae hi hg.int_sq h2).trans hg.le⟩

/-! ## The inputs -/

lemma sum4 (w : Fin N → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, (((if i = j ∧ k = l then (1 : ℝ) else 0) +
      (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) *
      (w i * w j * w k * w l)) = 3 * (∑ i, w i ^ 2) ^ 2 := by
  have e1 : ∑ i, ∑ j, ∑ k, ∑ l, ((if i = j ∧ k = l then (1 : ℝ) else 0) *
      (w i * w j * w k * w l)) = (∑ i, w i ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k (fun l _ hl => ?_) (by simp)]
      · simp; ring
      · simp [Ne.symm hl]
    · simp [Ne.symm hj]
  have e2 : ∑ i, ∑ j, ∑ k, ∑ l, ((if i = k ∧ j = l then (1 : ℝ) else 0) *
      (w i * w j * w k * w l)) = (∑ i, w i ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)]
    · rw [Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)]
      · simp; ring
      · simp [Ne.symm hl]
    · simp [Ne.symm hk]
  have e3 : ∑ i, ∑ j, ∑ k, ∑ l, ((if i = l ∧ j = k then (1 : ℝ) else 0) *
      (w i * w j * w k * w l)) = (∑ i, w i ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)]
    · rw [Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)]
      · simp; ring
      · simp [Ne.symm hl]
    · simp [Ne.symm hk]
  simp only [add_mul, Finset.sum_add_distrib, e1, e2, e3]
  ring

lemma dotp_pow4 (x y : Fin N → ℝ) :
    (dotp x y ^ 2) ^ 2 = ∑ i, ∑ j, ∑ k, ∑ l, (x i * x j * x k * x l) * (y i * y j * y k * y l) := by
  have e2 : dotp x y ^ 2 = ∑ i, ∑ j, (x i * y i) * (x j * y j) := by
    unfold dotp
    rw [sq, Finset.sum_mul_sum]
  rw [sq, e2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => by ring

/-- `‖⟨u, y⟩²‖_{L²(u)} ≤ √3/N` for a unit vector `y`. -/
lemma sphere_dot4 (hN : 1 ≤ N) {y : Fin N → ℝ} (hy : normSq y = 1) :
    L2le (uniformSphere N) (fun x : Fin N → ℝ => dotp x y ^ 2) (√3 / (N : ℝ)) := by
  have := uniformSphere_isProbability N hN
  have hmom := uniformSphere_moments N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmeas : Measurable (fun x : Fin N → ℝ => dotp x y ^ 2) :=
    (measurable_dotp_comp measurable_id measurable_const).pow_const 2
  have hi : ∀ i j k l, Integrable (fun x : Fin N → ℝ =>
      (x i * x j * x k * x l) * (y i * y j * y k * y l)) (uniformSphere N) := fun i j k l =>
    (hmom.int4 i j k l).mul_const _
  simp only [L2le, dotp_pow4]
  refine ⟨hmeas.aestronglyMeasurable, integrable_finsetSum _ fun i _ => integrable_finsetSum _
    fun j _ => integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi i j k l, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _
    fun j _ => integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi i j k l]
  have s1 : ∀ i : Fin N, ∫ x : Fin N → ℝ, ∑ j, ∑ k, ∑ l,
      (x i * x j * x k * x l) * (y i * y j * y k * y l) ∂uniformSphere N =
      ∑ j, ∑ k, ∑ l, (((if i = j ∧ k = l then (1 : ℝ) else 0) +
      (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) *
      (y i * y j * y k * y l)) / ((N : ℝ) * (N + 2)) := by
    intro i
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => hi i j k l]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi i j k l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => hi i j k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, hmom.m4]
    ring
  simp only [s1, ← Finset.sum_div]
  rw [sum4 y]
  have hy' : ∑ i, y i ^ 2 = 1 := hy
  rw [hy', div_pow, Real.sq_sqrt (by norm_num)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma kk_abs {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    |kappa (kappa s) - kappa (kappa 0)| ≤ 507 / 1000 * |s| + 8 / 25 * s ^ 2 := by
  obtain ⟨b, hb⟩ := kk_quad
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  obtain ⟨a', b', -, -, hb0, -, heq, hsup⟩ := hG.support (t := 0) ⟨by norm_num, by norm_num⟩
  simp only [Function.comp, mul_zero, add_zero] at heq hsup
  have q1 := kappa2_zero_le
  have q2 := kappa2_zero_ge
  have k1 := kappa_zero_ge
  have u1 := hb (-1) ⟨le_refl _, by norm_num⟩
  rw [kappa_neg_one] at u1
  have u2 := hb 1 ⟨by norm_num, le_refl _⟩
  rw [kappa_one, kappa_one] at u2
  have u3 := hsup 1 ⟨by norm_num, le_refl _⟩
  rw [kappa_one, kappa_one] at u3
  have hbu : b ≤ 507 / 1000 := by norm_num at u1; linarith
  have hbl : 0 ≤ b := by norm_num at u2; linarith
  have hb'u : b' ≤ 507 / 1000 := by linarith
  have l1 := hsup s hs
  have l2 := hb s hs
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  rcases le_total 0 s with h0 | h0
  · rw [abs_of_nonneg h0, abs_le]
    constructor
    · nlinarith
    · nlinarith
  · rw [abs_of_nonpos h0, abs_le]
    constructor
    · nlinarith
    · nlinarith

lemma kk_mem {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    0 ≤ kappa (kappa s) ∧ kappa (kappa s) ≤ 1 := by
  have h1 := kappa_mem hs.1 hs.2
  exact kappa_mem (by linarith [h1.1]) h1.2

lemma unit_dot_mem {u u' : Fin N → ℝ} (hu : normSq u = 1) (hu' : normSq u' = 1) :
    dotp u u' ∈ Icc (-1 : ℝ) 1 := by
  have h := abs_dotp_le_nrm u u'
  rw [nrm_of_normSq_one hu, nrm_of_normSq_one hu', mul_one] at h
  exact abs_le.mp h

/-- **The link of the inputs, refined**:
`‖κ(κ(⟨u, u′⟩)) − κ(κ(0))‖₂ ≤ 0.507/√N + (8/25)·√3/N`. -/
theorem sphere_kk_L2r (hN : 1 ≤ N) :
    L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0))
      (507 / 1000 / √(N : ℝ) + 8 / 25 * √3 / (N : ℝ)) := by
  have := lawU2_prob hN
  have := uniformSphere_isProbability N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨iD, eD⟩ := lawU2_dot_sq hN
  have hmd : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2) :=
    continuous_dotp.measurable
  have hmeas : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) :=
    ((continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable).sub
      measurable_const
  have hd : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => |dotp uu.1 uu.2|)
      (1 / √(N : ℝ)) := by
    refine L2le.of_sq_le hmd.abs.aestronglyMeasurable iD (fun uu => by rw [sq_abs]) ?_
    rw [eD, div_pow, Real.sq_sqrt hN'.le]
    simp
  have hd4 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2 ^ 2)
      (√3 / (N : ℝ)) := by
    unfold lawU2
    refine L2le.prod_const_left (hmd.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with y hy
    exact sphere_dot4 hN hy
  have hg := (hd.const_mul_nonneg (c := 507 / 1000) (by norm_num)).add'
    (hd4.const_mul_nonneg (c := 8 / 25) (by norm_num)) (by positivity) (by positivity)
  refine (L2le.abs_le_ae_R hmeas.aestronglyMeasurable hg ?_).congr_bound (by ring)
  filter_upwards [lawU2_ae_unit hN] with uu huu
  have h := kk_abs (unit_dot_mem huu.1 huu.2)
  refine h.trans (le_abs_self _)

/-- The `L²` norm over the inputs of `c·(1 − κ(κ(⟨u, u′⟩))²)`. -/
theorem sphere_gW_L2 (hN : 1 ≤ N) (c : ℝ) (hc : 0 ≤ c) :
    L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      c * (1 - kappa (kappa (dotp uu.1 uu.2)) ^ 2))
      (c * (1 - kappa (kappa 0) ^ 2 + 2 * (507 / 1000 / √(N : ℝ) + 8 / 25 * √3 / (N : ℝ)))) := by
  have := lawU2_prob hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := kk_mem (s := 0) ⟨by norm_num, by norm_num⟩
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hmk : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2))) :=
    (continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable
  have h1 : L2le (lawU2 N) (fun _ : (Fin N → ℝ) × (Fin N → ℝ) =>
      c * (1 - kappa (kappa 0) ^ 2)) (c * (1 - kappa (kappa 0) ^ 2)) := by
    have := L2le.const (μ := lawU2 N) (c * (1 - kappa (kappa 0) ^ 2))
    rwa [abs_of_nonneg (mul_nonneg hc hq2)] at this
  have h2 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      c * (kappa (kappa 0) ^ 2 - kappa (kappa (dotp uu.1 uu.2)) ^ 2))
      (c * 2 * (507 / 1000 / √(N : ℝ) + 8 / 25 * √3 / (N : ℝ))) := by
    have h0 := (sphere_kk_L2r hN).const_mul_nonneg (c := c * 2) (by positivity)
    refine L2le.abs_le_ae_R
      (((measurable_const.sub (hmk.pow_const 2)).const_mul c).aestronglyMeasurable) h0 ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have hk := kk_mem (unit_dot_mem huu.1 huu.2)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    have e : kappa (kappa 0) ^ 2 - kappa (kappa (dotp uu.1 uu.2)) ^ 2 =
        (kappa (kappa 0) + kappa (kappa (dotp uu.1 uu.2))) *
          (kappa (kappa 0) - kappa (kappa (dotp uu.1 uu.2))) := by ring
    rw [e, abs_mul, abs_sub_comm (kappa (kappa 0))]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg (by linarith [hq.1, hk.1])]
    linarith [hq.2, hk.2]
  have h12 := h1.add' h2 (mul_nonneg hc hq2) (by positivity)
  exact (h12.congr_fun fun uu => by ring).congr_bound (by ring)

/-! ## The World network -/

/-- The hidden-layer part of the World error. -/
noncomputable def eHid (m : ℕ) : ℝ :=
  √(5 * epsW m) + (√6 * √(1 + 5 / (m : ℝ)) / √(m : ℝ) + (5 * kappa 0 + √6) / √(m : ℝ))

/-- The World link with the factor `1 − τ²` kept, for any constant `J` of the cosine link. -/
theorem world_cos_L2g (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {J : ℝ} (hJ : 0 ≤ J)
    (hcos : ∀ h h' : Fin m → ℝ, normSq h ≠ 0 → normSq h' ≠ 0 →
      L2le (gaussMat n m (2 / (m : ℝ)))
        (fun M : Matrix (Fin n) (Fin m) ℝ =>
          dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - cosv h h')
        ((1 - cosv h h' ^ 2) / √(n : ℝ) + J))
    {u u' : Fin N → ℝ} (hu : normSq u = 1) (hu' : normSq u' = 1) :
    L2le (mlpGauss N m n)
      (fun W : MlpParam N m n => dotp (xW W u) (xW W u') - kappa (kappa (dotp u u')))
      ((1 - kappa (kappa (dotp u u')) ^ 2) / √(n : ℝ) +
        (J + (1 + 2 / √(n : ℝ)) * eHid m + 2 * √(epsW m))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := sH_pos hN hm
  have heps := epsW_pos hm
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = kappa (kappa (dotp u u')) := ⟨_, rfl⟩
  have hcm : 0 ≤ c ∧ c ≤ 1 := hcdef ▸ kk_mem (unit_dot_mem hu hu')
  have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith [hcm.1, hcm.2]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 - c ^ 2) / √(n : ℝ) + J := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  obtain ⟨cH, hcH⟩ : ∃ c : ℝ, c = √6 * √(1 + 5 / (m : ℝ)) / √(m : ℝ) +
      (5 * kappa 0 + √6) / √(m : ℝ) := ⟨_, rfl⟩
  have hcHpos : 0 < cH := by
    rw [hcH]
    have h6 : (0 : ℝ) < √6 := by positivity
    have : 0 < (5 * kappa 0 + √6) / √(m : ℝ) := div_pos (by linarith) (by positivity)
    have : 0 ≤ √6 * √(1 + 5 / (m : ℝ)) / √(m : ℝ) := by positivity
    linarith
  have hmeasC : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) := measurable_cosv_hid2 u u'
  -- (ii) the norms of the hidden layers
  have h2 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') -
          dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') / sH N m) (√(5 * epsW m)) := by
    obtain ⟨iP, uP⟩ := hid2_pair hN hm hu hu'
    have hmd : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) :=
      measurable_dotp_comp (continuous_hid2_param u).measurable
        (continuous_hid2_param u').measurable
    refine L2le.of_sq_le (hmeasC.sub (hmd.div_const _)).aestronglyMeasurable
      (iP.const_mul (1 / sH N m ^ 2)) (fun θ => ?_) ?_
    · have hc := cosv_mem (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')
      have hc2 : cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
      rw [dotp_eq_cosv_mul (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')]
      have e : (cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') -
          cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') *
            (nrm (hid2 θ.1 θ.2 u) * nrm (hid2 θ.1 θ.2 u')) / sH N m) ^ 2 =
          cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2 * (1 / sH N m ^ 2 *
            (nrm (hid2 θ.1 θ.2 u) * nrm (hid2 θ.1 θ.2 u') - sH N m) ^ 2) := by
        have : sH N m ≠ 0 := hs.ne'
        field_simp
        ring
      rw [e]
      exact mul_le_of_le_one_left (by positivity) hc2
    · rw [integral_const_mul, Real.sq_sqrt (by positivity)]
      have := mul_le_mul_of_nonneg_left uP (by positivity : (0 : ℝ) ≤ 1 / sH N m ^ 2)
      refine this.trans (le_of_eq ?_)
      have : sH N m ≠ 0 := hs.ne'
      field_simp
  -- (iii) the inner product of the hidden layers
  have h3 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        dotp (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') / sH N m - c) cH := by
    have h := (hid2_dot_L2 (two_div_nonneg N) (two_div_nonneg m) hm hm u u').const_mul_nonneg
      (c := 1 / sH N m) (by positivity)
    rw [psi_unit _ hu hu', nrm_of_normSq_one hu, nrm_of_normSq_one hu'] at h
    have hne : sH N m ≠ 0 := hs.ne'
    refine (h.congr_fun fun θ => ?_).congr_bound ?_
    · simp only [Function.comp, hcdef]
      unfold sH at hne ⊢
      field_simp
    · rw [hcH]
      unfold sH at hne ⊢
      field_simp
  have h23 : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') - c) (eHid m) := by
    have := h2.add h3 (by positivity) hcHpos
    refine (this.congr_fun fun θ => by ring).congr_bound ?_
    unfold eHid
    rw [hcH]
  have heH : 0 < eHid m := by
    unfold eHid
    rw [← hcH]
    positivity
  -- the zero events
  have hind : ∀ w : Fin N → ℝ, normSq w = 1 →
      L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
        (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
          if normSq (hid2 θ.1 θ.2 w) = 0 then (1 : ℝ) else 0) (√(epsW m)) := by
    intro w hw
    refine L2le.of_sq_le (measurable_zero_ind w).aestronglyMeasurable (integrable_zero_ind w)
      (fun θ => by split_ifs <;> simp) ?_
    rw [Real.sq_sqrt heps.le]
    exact hid2_zero hN hm hw
  have hg : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        A + (2 / √(n : ℝ) * |cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') - c| +
          ((if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0) +
          (if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0))))
      (A + (2 / √(n : ℝ) * eHid m + (√(epsW m) + √(epsW m)))) := by
    have hc : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
        (fun _ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ => A) A := by
      have := L2le.const (μ := (gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) A
      rwa [abs_of_nonneg hA0] at this
    have habs : L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
        (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
          |cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') - c|) (eHid m) :=
      L2le.of_abs_le (hmeasC.sub measurable_const).abs.aestronglyMeasurable h23
        (fun θ => by rw [abs_abs])
    exact hc.add' ((habs.const_mul_nonneg (c := 2 / √(n : ℝ)) (by positivity)).add'
      ((hind u hu).add' (hind u' hu') (by positivity) (by positivity)) (by positivity)
      (by positivity)) hA0 (by positivity)
  have hmeas1 : Measurable (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
        Matrix (Fin n) (Fin m) ℝ =>
      dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
        cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')) :=
    (measurable_lastStep u u').sub (hmeasC.comp measurable_fst)
  -- (i) the last matrix
  have h1 : L2le (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
      (gaussMat n m (2 / (m : ℝ))))
      (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
        Matrix (Fin n) (Fin m) ℝ =>
      dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
        cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u'))
      (A + (2 / √(n : ℝ) * eHid m + (√(epsW m) + √(epsW m)))) := by
    refine L2le.prod' hmeas1.aestronglyMeasurable hg (Filter.Eventually.of_forall fun θ => ?_)
    have habs0 : 0 ≤ 2 / √(n : ℝ) * |cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') - c| := by
      positivity
    by_cases hz : normSq (hid2 θ.1 θ.2 u) = 0 ∨ normSq (hid2 θ.1 θ.2 u') = 0
    · have hb : L2le (gaussMat n m (2 / (m : ℝ))) (fun M₃ : Matrix (Fin n) (Fin m) ℝ =>
          dotp (sphPt (M₃.mulVec (hid2 θ.1 θ.2 u))) (sphPt (M₃.mulVec (hid2 θ.1 θ.2 u'))) -
            cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) 1 := by
        refine L2le.of_bound (hmeas1.comp measurable_prodMk_left).aestronglyMeasurable
          (fun M₃ => ?_)
        simp only [Function.comp]
        rw [cosv_of_zero hz, sub_zero, abs_le]
        exact ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩
      refine hb.mono zero_le_one ?_
      rcases hz with hz | hz
      · simp only [hz, ↓reduceIte]
        have : (0 : ℝ) ≤ if normSq (hid2 θ.1 θ.2 u') = 0 then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        linarith
      · simp only [hz, ↓reduceIte]
        have : (0 : ℝ) ≤ if normSq (hid2 θ.1 θ.2 u) = 0 then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        linarith
    · have hz : normSq (hid2 θ.1 θ.2 u) ≠ 0 ∧ normSq (hid2 θ.1 θ.2 u') ≠ 0 :=
        ⟨fun h => hz (Or.inl h), fun h => hz (Or.inr h)⟩
      have hb := hcos (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') hz.1 hz.2
      obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') := ⟨_, rfl⟩
      have hc := cosv_mem (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')
      have hbτ : (1 - cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') ^ 2) / √(n : ℝ) + J =
          (1 - τ ^ 2) / √(n : ℝ) + J := by rw [hτ]
      rw [← hτ] at hc ⊢
      have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
      have h0 : 0 ≤ (1 - τ ^ 2) / √(n : ℝ) := div_nonneg (by linarith) (Real.sqrt_nonneg _)
      have hkey : 1 - τ ^ 2 ≤ (1 - c ^ 2) + 2 * |τ - c| := by
        have e : c ^ 2 - τ ^ 2 = (c + τ) * (c - τ) := by ring
        have h1 : |(c + τ) * (c - τ)| ≤ 2 * |τ - c| := by
          rw [abs_mul, abs_sub_comm c τ]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]
          constructor <;> linarith [hc.1, hc.2, hcm.1, hcm.2]
        have := le_abs_self ((c + τ) * (c - τ))
        linarith
      have hle : (1 - τ ^ 2) / √(n : ℝ) ≤ (1 - c ^ 2) / √(n : ℝ) + 2 / √(n : ℝ) * |τ - c| := by
        have := div_le_div_of_nonneg_right hkey hsn.le
        refine this.trans (le_of_eq ?_)
        field_simp
      refine (hb.congr_bound hbτ).mono (by linarith) ?_
      simp only [hz.1, hz.2, ↓reduceIte, hA]
      linarith
  have h23' := h23.comp_fst (ν := gaussMat n m (2 / (m : ℝ)))
  have hall := h1.add' h23' (by positivity) heH.le
  have hmap : (mlpGauss N m n).map (MeasurableEquiv.prodAssoc (α := Matrix (Fin m) (Fin N) ℝ)
      (β := Matrix (Fin m) (Fin m) ℝ) (γ := Matrix (Fin n) (Fin m) ℝ)).symm =
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ))) := by
    unfold mlpGauss
    rw [← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]
  have hfin := hall.comp_map (MeasurableEquiv.prodAssoc (α := Matrix (Fin m) (Fin N) ℝ)
      (β := Matrix (Fin m) (Fin m) ℝ) (γ := Matrix (Fin n) (Fin m) ℝ)).symm.measurable hmap
  refine (hfin.congr_fun fun W => ?_).congr_bound ?_
  · show dotp (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u))) (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u'))) -
        cosv (hid2 W.1 W.2.1 u) (hid2 W.1 W.2.1 u') +
        (cosv (hid2 W.1 W.2.1 u) (hid2 W.1 W.2.1 u') - c) =
      dotp (xW W u) (xW W u') - kappa (kappa (dotp u u'))
    have : dotp (xW W u) (xW W u') = dotp (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u)))
        (sphPt (W.2.2.mulVec (hid2 W.1 W.2.1 u'))) := rfl
    rw [this, hcdef]
    ring
  · rw [hA, hcdef]
    ring

end BstLean.Part133

open BstLean.Part133 in
#print axioms world_cos_L2g
open BstLean.Part133 in
#print axioms sphere_kk_L2r
open BstLean.Part133 in
#print axioms sphere_gW_L2
