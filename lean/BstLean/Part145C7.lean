import BstLean.Part145C3

/-!
# Part 145, helper `C7`: fourth moments (`M4le`) and the cosine link in `L⁴`

`M4le μ f B`: `f` is measurable (a.e.), `f⁴` is integrable and `∫ f⁴ dμ ≤ B`.

* Tools: `M4le.add` (Minkowski in `L⁴`, bounds `A⁴`, `B⁴` to `(A + B)⁴`), `M4le.const_mul`,
  `M4le.const`, `M4le.of_abs_le_ae`, `M4le.of_bound_l2` (`|f| ≤ c`, `‖f‖₂ ≤ e`), `M4le.prod`
  (Fubini with an additive constant), `M4le.perturb`
  (`∫ (a + b)⁴ ≤ A⁴ + 24·A²·e + 28·e²` if `|a| ≤ 3`, `|b| ≤ 2`, `‖b‖₂ ≤ e`).
* `sphere_dot8`, `sU4 N = 0.32·√(√3/N) + 1.49024·√(√105/N²)`, `sphere_kk_M4`: the link of the
  inputs in `L⁴`.
* `cos_pt4`: if `m = max(|x|, |y|) ≤ 1/2` then `|T − τ| ≤ |E| + 2|E|m + (x² + y²)`.
* `kEC n = K4 n/n`, `j4C n = 2·√(√(Q·√2·Q)) + 2·√Q`, `t4C n = 8192·Q²` (`Q = qCos n`);
  **`lin_cos_unit_M4`**, **`lin_cos_M4`**:
  `∫ (⟨sphPt (M h), sphPt (M h′)⟩ − cos(h, h′))⁴ ≤ ((1 − cos²)·√(kEC n) + j4C n)⁴ + t4C n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142 BstLean.Part143

/-! ## Fourth moments -/

section M4

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `∫ f⁴ dμ ≤ B`, with measurability and integrability. -/
def M4le (μ : Measure Ω) (f : Ω → ℝ) (B : ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ Integrable (fun ω => (f ω ^ 2) ^ 2) μ ∧
    ∫ ω, (f ω ^ 2) ^ 2 ∂μ ≤ B

lemma M4le.of_l2sq {f : Ω → ℝ} {A : ℝ} (hf : AEStronglyMeasurable f μ)
    (h : L2le μ (fun ω => f ω ^ 2) (A ^ 2)) : M4le μ f (A ^ 4) :=
  ⟨hf, h.int_sq, h.le.trans (le_of_eq (by ring))⟩

lemma M4le.l2sq {f : Ω → ℝ} {A : ℝ} (h : M4le μ f (A ^ 4)) :
    L2le μ (fun ω => f ω ^ 2) (A ^ 2) :=
  ⟨h.1.pow 2, h.2.1, h.2.2.trans (le_of_eq (by ring))⟩

lemma M4le.mono {f : Ω → ℝ} {B B' : ℝ} (h : M4le μ f B) (hB : B ≤ B') : M4le μ f B' :=
  ⟨h.1, h.2.1, h.2.2.trans hB⟩

lemma M4le.congr_fun {f g : Ω → ℝ} {B : ℝ} (h : M4le μ f B) (hfg : ∀ ω, f ω = g ω) :
    M4le μ g B := by
  have : f = g := funext hfg
  exact this ▸ h

lemma M4le.of_abs_le_ae {f g : Ω → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : M4le μ g B) (h : ∀ᵐ ω ∂μ, |f ω| ≤ |g ω|) : M4le μ f B := by
  have h2 : ∀ᵐ ω ∂μ, (f ω ^ 2) ^ 2 ≤ (g ω ^ 2) ^ 2 := h.mono fun ω hω => by
    have h1 : f ω ^ 2 ≤ g ω ^ 2 := by
      rw [← sq_abs (f ω), ← sq_abs (g ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2
    exact pow_le_pow_left₀ (sq_nonneg _) h1 2
  have hi : Integrable (fun ω => (f ω ^ 2) ^ 2) μ := by
    refine Integrable.mono' hg.2.1 ((hf.pow 2).pow 2) (h2.mono fun ω hω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  exact ⟨hf, hi, (integral_mono_ae hi hg.2.1 h2).trans hg.2.2⟩

lemma M4le.of_abs_le {f g : Ω → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : M4le μ g B) (h : ∀ ω, |f ω| ≤ |g ω|) : M4le μ f B :=
  M4le.of_abs_le_ae hf hg (Filter.Eventually.of_forall h)

/-- **Minkowski in `L⁴`**, for bounds `0 ≤ A`, `0 ≤ B`. -/
theorem M4le.add {f g : Ω → ℝ} {A B : ℝ} (hf : M4le μ f (A ^ 4)) (hg : M4le μ g (B ^ 4))
    (hA : 0 ≤ A) (hB : 0 ≤ B) : M4le μ (fun ω => f ω + g ω) ((A + B) ^ 4) := by
  have h1 := hf.l2sq
  have h2 := hg.l2sq
  have h3 := l2_abs_mul_of_sq (sq_nonneg A) (sq_nonneg B) hf.1 hg.1 h1 h2
  have e3 : √(A ^ 2 * B ^ 2) = A * B := by
    rw [← mul_pow]
    exact Real.sqrt_sq (mul_nonneg hA hB)
  rw [e3] at h3
  have htot := (h1.add' (h3.const_mul_nonneg (c := 2) (by norm_num)) (sq_nonneg A)
    (by positivity)).add' h2 (by positivity) (sq_nonneg B)
  have hm : AEStronglyMeasurable (fun ω => f ω + g ω) μ := hf.1.add hg.1
  refine M4le.of_l2sq hm ((L2le.of_abs_le (hm.pow 2) htot (fun ω => ?_)).congr_bound (by ring))
  change |(f ω + g ω) ^ 2| ≤ |f ω ^ 2 + 2 * (|f ω| * |g ω|) + g ω ^ 2|
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
  linarith [le_abs_self (f ω * g ω), abs_mul (f ω) (g ω)]

lemma M4le.const_mul {f : Ω → ℝ} {A : ℝ} (h : M4le μ f (A ^ 4)) {c : ℝ} (_hc : 0 ≤ c) :
    M4le μ (fun ω => c * f ω) ((c * A) ^ 4) := by
  have h1 := (h.l2sq).const_mul_nonneg (c := c ^ 2) (sq_nonneg c)
  exact M4le.of_l2sq (h.1.const_mul c)
    ((h1.congr_fun fun ω => by ring).congr_bound (by ring))

lemma M4le.const [IsProbabilityMeasure μ] (c : ℝ) : M4le μ (fun _ : Ω => c) (c ^ 4) := by
  have e : ∫ _ω : Ω, (c ^ 2) ^ 2 ∂μ = (c ^ 2) ^ 2 := by simp
  exact ⟨aestronglyMeasurable_const, integrable_const _, by rw [e]; exact le_of_eq (by ring)⟩

/-- A bounded function with a bound of its `L²` norm. -/
lemma M4le.of_bound_l2 {f : Ω → ℝ} {c e : ℝ} (hb : ∀ ω, |f ω| ≤ c) (h : L2le μ f e) :
    M4le μ f (c ^ 2 * e ^ 2) := by
  have h2 : ∀ ω, (f ω ^ 2) ^ 2 ≤ c ^ 2 * f ω ^ 2 := fun ω => by
    have h1 : f ω ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs (f ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) 2
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg (f ω))
    calc (f ω ^ 2) ^ 2 = f ω ^ 2 * f ω ^ 2 := by ring
      _ ≤ c ^ 2 * f ω ^ 2 := this
  have hG : Integrable (fun ω => c ^ 2 * f ω ^ 2) μ := h.int_sq.const_mul _
  have hi : Integrable (fun ω => (f ω ^ 2) ^ 2) μ := by
    refine Integrable.mono' hG ((h.aesm.pow 2).pow 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h2 ω
  refine ⟨h.aesm, hi, (integral_mono hi hG h2).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h.le (sq_nonneg c)

/-- **Fubini for fourth moments**, with an additive constant `T` in the bound of the
sections. -/
theorem M4le.prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [IsProbabilityMeasure μ] [SFinite ν] {f : α × β → ℝ} {g : α → ℝ} {G T : ℝ}
    (hT : 0 ≤ T) (hf : AEStronglyMeasurable f (μ.prod ν)) (hg : M4le μ g G)
    (h : ∀ᵐ x ∂μ, Integrable (fun y => (f (x, y) ^ 2) ^ 2) ν ∧
      ∫ y, (f (x, y) ^ 2) ^ 2 ∂ν ≤ (g x ^ 2) ^ 2 + T) :
    M4le (μ.prod ν) f (G + T) := by
  have hG0 : 0 ≤ G := (integral_nonneg fun ω => sq_nonneg _).trans hg.2.2
  have hnn : ∀ x, 0 ≤ (g x ^ 2) ^ 2 + T := fun x => by positivity
  have esq : ∀ x, √((g x ^ 2) ^ 2 + T) ^ 2 = (g x ^ 2) ^ 2 + T := fun x => Real.sq_sqrt (hnn x)
  have hgm : AEStronglyMeasurable (fun x => √((g x ^ 2) ^ 2 + T)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (((hg.1.pow 2).pow 2).add aestronglyMeasurable_const)
  have hgi : Integrable (fun x => (g x ^ 2) ^ 2 + T) μ := hg.2.1.add (integrable_const T)
  have hg' : L2le μ (fun x => √((g x ^ 2) ^ 2 + T)) (√(G + T)) := by
    refine ⟨hgm, ?_, ?_⟩
    · simp only [esq]
      exact hgi
    · simp only [esq]
      rw [integral_add hg.2.1 (integrable_const T), Real.sq_sqrt (by positivity)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      linarith [hg.2.2]
  have key := L2le.prod (f := fun z => f z ^ 2) (hf.pow 2) hg'
    (h.mono fun x hx => ⟨hx.1, hx.2.trans (le_of_eq (esq x).symm)⟩)
  exact ⟨hf, key.int_sq, key.le.trans (le_of_eq (Real.sq_sqrt (by positivity)))⟩

lemma pert_pt {a b : ℝ} (ha : |a| ≤ 3) (hb : |b| ≤ 2) :
    ((a + b) ^ 2) ^ 2 ≤ (a ^ 2) ^ 2 + 24 * (a ^ 2 * |b|) + 28 * b ^ 2 := by
  obtain ⟨α, hα⟩ : ∃ α, α = |a| := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = |b| := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := hα ▸ abs_nonneg a
  have hβ0 : 0 ≤ β := hβ ▸ abs_nonneg b
  have ea : a ^ 2 = α ^ 2 := by rw [hα, sq_abs]
  have eb : b ^ 2 = β ^ 2 := by rw [hβ, sq_abs]
  rw [← hα] at ha
  rw [← hβ] at hb
  have h1 : (a + b) ^ 2 ≤ (α + β) ^ 2 := by
    rw [← sq_abs (a + b)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [hα, hβ]; exact abs_add_le a b) 2
  have h2 : ((a + b) ^ 2) ^ 2 ≤ ((α + β) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
  have p1 : α ^ 2 * β * α ≤ α ^ 2 * β * 3 := mul_le_mul_of_nonneg_left ha (by positivity)
  have p2 : α ^ 2 * β * β ≤ α ^ 2 * β * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
  have p3 : β ^ 2 * (α * β) ≤ β ^ 2 * (3 * 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul ha hb hβ0 (by norm_num)) (sq_nonneg β)
  have p4 : β ^ 2 * (β * β) ≤ β ^ 2 * (2 * 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb hb hβ0 (by norm_num)) (sq_nonneg β)
  rw [ea, eb, ← hβ]
  have e : ((α + β) ^ 2) ^ 2 = (α ^ 2) ^ 2 + 4 * (α ^ 2 * β * α) + 6 * (α ^ 2 * β * β) +
      4 * (β ^ 2 * (α * β)) + β ^ 2 * (β * β) := by ring
  linarith

/-- **A small bounded perturbation**: `∫ (a + b)⁴ ≤ A⁴ + 24·A²·e + 28·e²`. -/
theorem M4le.perturb {a b : Ω → ℝ} {A e : ℝ} (ha : M4le μ a (A ^ 4)) (hb : L2le μ b e)
    (he : 0 ≤ e) (ha3 : ∀ ω, |a ω| ≤ 3) (hb2 : ∀ ω, |b ω| ≤ 2) :
    M4le μ (fun ω => a ω + b ω) (A ^ 4 + 24 * A ^ 2 * e + 28 * e ^ 2) := by
  have hpt : ∀ ω, ((a ω + b ω) ^ 2) ^ 2 ≤
      (a ω ^ 2) ^ 2 + 24 * (a ω ^ 2 * |b ω|) + 28 * b ω ^ 2 := fun ω =>
    pert_pt (ha3 ω) (hb2 ω)
  have i1 := ha.2.1
  have i2 : Integrable (fun ω => a ω ^ 2 * |b ω|) μ := l2_mul_integrable ha.l2sq hb.abs
  have i3 := hb.int_sq
  have i12 : Integrable (fun ω => (a ω ^ 2) ^ 2 + 24 * (a ω ^ 2 * |b ω|)) μ :=
    i1.add (i2.const_mul 24)
  have i28 : Integrable (fun ω => 28 * b ω ^ 2) μ := i3.const_mul 28
  have iG : Integrable (fun ω => (a ω ^ 2) ^ 2 + 24 * (a ω ^ 2 * |b ω|) + 28 * b ω ^ 2) μ :=
    i12.add i28
  have hm : AEStronglyMeasurable (fun ω => a ω + b ω) μ := ha.1.add hb.1
  have hi : Integrable (fun ω => ((a ω + b ω) ^ 2) ^ 2) μ := by
    refine Integrable.mono' iG ((hm.pow 2).pow 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hm, hi, (integral_mono hi iG hpt).trans ?_⟩
  rw [integral_add i12 i28, integral_add i1 (i2.const_mul 24), integral_const_mul,
    integral_const_mul]
  have b1 := ha.2.2
  have b2 := (le_abs_self _).trans (l2_abs_integral_mul_le (sq_nonneg A) he ha.l2sq hb.abs)
  have b3 := hb.le
  linarith

end M4

/-! ## The link of the inputs in `L⁴` -/

/-- `‖⟨u, y⟩⁴‖_{L²(u)} ≤ √105/N²` for a unit vector `y` (the eighth moment). -/
lemma sphere_dot8 {N : ℕ} (hN : 1 ≤ N) {y : Fin N → ℝ} (hy : normSq y = 1) :
    L2le (uniformSphere N) (fun x : Fin N → ℝ => (dotp x y ^ 2) ^ 2)
      (√105 / (N : ℝ) ^ 2) := by
  have := uniformSphere_isProbability N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcont : Continuous (fun x : Fin N → ℝ => dotp x y) :=
    continuous_dotp.comp (continuous_id.prodMk continuous_const)
  have e : ∀ x : Fin N → ℝ, ((dotp x y ^ 2) ^ 2) ^ 2 = (∑ i, y i * x i) ^ (2 * 4) := by
    intro x
    have h1 : dotp x y = ∑ i, y i * x i := by
      unfold dotp
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← h1]
    ring
  refine ⟨((hcont.pow 2).pow 2).aestronglyMeasurable,
    BstLean.Part105.sphere_cont_integrable hN (((hcont.pow 2).pow 2).pow 2), ?_⟩
  simp_rw [e]
  rw [BstLean.Part58.Kappa.sphere_linear_even hN y 4, div_pow, Real.sq_sqrt (by norm_num)]
  have hy' : ∑ i, y i ^ 2 = 1 := hy
  rw [hy']
  have hv : (1 : ℝ) ^ 4 * BstLean.Part29.gaussMom (2 * 4) / BstLean.Part36.rhoD N 4 =
      105 / ((N : ℝ) * (N + 2) * (N + 4) * (N + 6)) := by
    simp only [BstLean.Part29.gaussMom, BstLean.Part36.rhoD]
    norm_num [Finset.prod_range_succ, Nat.doubleFactorial, Nat.even_iff]
  rw [hv]
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  have : ((N : ℝ) ^ 2) ^ 2 = (N : ℝ) * N * N * N := by ring
  rw [this]
  gcongr <;> linarith

/-- The link of the inputs in `L⁴`: `0.32·(3^{1/4}/√N) + 1.49024·(105^{1/4}/N)`. -/
noncomputable def sU4 (N : ℕ) : ℝ :=
  8 / 25 * √(√3 / (N : ℝ)) + 149024 / 100000 * √(√105 / (N : ℝ) ^ 2)

lemma sU4_nonneg (N : ℕ) : 0 ≤ sU4 N := by unfold sU4; positivity

/-- **The link of the inputs in `L⁴`**: `∫ (κ(κ(⟨u, u′⟩)) − κ(κ(0)))⁴ ≤ (sU4 N)⁴`, and the same
for the absolute value. -/
theorem sphere_kk_M4 {N : ℕ} (hN : 1 ≤ N) :
    M4le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      |kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)|) (sU4 N ^ 4) := by
  have := lawU2_prob hN
  have := uniformSphere_isProbability N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmd : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2) :=
    continuous_dotp.measurable
  have hmeas : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      |kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)|) :=
    (((continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable).sub
      measurable_const).abs
  have hd4 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2 ^ 2)
      (√3 / (N : ℝ)) := by
    unfold lawU2
    refine L2le.prod_const_left (hmd.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere N] with y hy
    exact sphere_dot4 hN hy
  have hd8 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => (dotp uu.1 uu.2 ^ 2) ^ 2)
      (√105 / (N : ℝ) ^ 2) := by
    unfold lawU2
    refine L2le.prod_const_left ((hmd.pow_const 2).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere N] with y hy
    exact sphere_dot8 hN hy
  have t1 : M4le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => |dotp uu.1 uu.2|)
      (√(√3 / (N : ℝ)) ^ 4) :=
    M4le.of_l2sq hmd.abs.aestronglyMeasurable
      ((hd4.congr_fun fun uu => (sq_abs _).symm).congr_bound
        (Real.sq_sqrt (by positivity)).symm)
  have t2 : M4le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2 ^ 2)
      (√(√105 / (N : ℝ) ^ 2) ^ 4) :=
    M4le.of_l2sq (hmd.pow_const 2).aestronglyMeasurable
      (hd8.congr_bound (Real.sq_sqrt (by positivity)).symm)
  have hg := (t1.const_mul (c := 8 / 25) (by norm_num)).add
    (t2.const_mul (c := 149024 / 100000) (by norm_num)) (by positivity) (by positivity)
  refine M4le.of_abs_le_ae hmeas.aestronglyMeasurable hg ?_
  filter_upwards [lawU2_ae_unit hN] with uu huu
  have h := kk_abs2 (unit_dot_mem huu.1 huu.2)
  rw [abs_abs]
  exact h.trans (le_abs_self _)

/-! ## The pointwise bound on the event `m ≤ 1/2` -/

lemma cos_pt4 {a b c τ T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : |τ| ≤ 1)
    (hTeq : 0 < a * b → T = c / (a * b)) (hm : max |a ^ 2 - 1| |b ^ 2 - 1| ≤ 1 / 2) :
    |T - τ| ≤ |c - τ * ((a ^ 2 + b ^ 2) / 2)| +
      2 * (|c - τ * ((a ^ 2 + b ^ 2) / 2)| * max |a ^ 2 - 1| |b ^ 2 - 1|) +
      ((a ^ 2 - 1) ^ 2 + (b ^ 2 - 1) ^ 2) := by
  obtain ⟨E, hE⟩ : ∃ E, E = c - τ * ((a ^ 2 + b ^ 2) / 2) := ⟨_, rfl⟩
  obtain ⟨m, hmd⟩ : ∃ m, m = max |a ^ 2 - 1| |b ^ 2 - 1| := ⟨_, rfl⟩
  rw [← hE, ← hmd]
  rw [← hmd] at hm
  have hu : |a ^ 2 - 1| ≤ m := hmd ▸ le_max_left _ _
  have hw : |b ^ 2 - 1| ≤ m := hmd ▸ le_max_right _ _
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hu
  have hE0 := abs_nonneg E
  have h1p := abs_le.mp (one_sub_mul_le ha hb hu hw)
  obtain ⟨p, hpdef⟩ : ∃ p, p = a * b := ⟨_, rfl⟩
  rw [← hpdef] at hTeq h1p
  have hp : 1 / 2 ≤ p := by linarith [h1p.2]
  have hp0 : 0 < p := by linarith
  obtain ⟨D, hD⟩ : ∃ D, D = (a - b) ^ 2 / 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hTp0 : (T - τ) * p = c - τ * p := by
    rw [hTeq hp0]
    have := hp0.ne'
    field_simp
  have hTp : (T - τ) * p = E + τ * D := by
    rw [hTp0, hE, hD, hpdef]
    ring
  have hDx : D ≤ ((a ^ 2 - 1) ^ 2 + (b ^ 2 - 1) ^ 2) / 2 := by
    have h2 : 2 ≤ (a + b) ^ 2 := by
      have : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * p := by rw [hpdef]; ring
      linarith [hu'.1, hw'.1]
    have h3 : (a - b) ^ 2 * (a + b) ^ 2 = ((a ^ 2 - 1) - (b ^ 2 - 1)) ^ 2 := by ring
    have h4 : (a - b) ^ 2 * 2 ≤ (a - b) ^ 2 * (a + b) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have h5 : ((a ^ 2 - 1) - (b ^ 2 - 1)) ^ 2 ≤ 2 * ((a ^ 2 - 1) ^ 2 + (b ^ 2 - 1) ^ 2) := by
      linarith [sq_nonneg ((a ^ 2 - 1) + (b ^ 2 - 1))]
    rw [hD]
    linarith
  have hcτ : |E + τ * D| ≤ |E| + D := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hD0]
    have := mul_le_of_le_one_left hD0 hτ
    linarith
  have e1 : |T - τ| * p = |E + τ * D| := by
    rw [← hTp, abs_mul, abs_of_pos hp0]
  have h2 : |T - τ| ≤ 2 * (|E| + D) := by
    have := mul_le_mul_of_nonneg_left hp (abs_nonneg (T - τ))
    linarith
  have key : T - τ = (E + τ * D) + (T - τ) * (1 - p) := by linear_combination hTp
  have h3 : |T - τ| ≤ |E + τ * D| + |T - τ| * |1 - p| := by
    conv_lhs => rw [key]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
  have h4 : |T - τ| * |1 - p| ≤ 2 * (|E| + D) * m :=
    mul_le_mul h2 (abs_le.mpr h1p) (abs_nonneg _) (by positivity)
  have h5 : D * m ≤ D * (1 / 2) := mul_le_mul_of_nonneg_left hm hD0
  have e2 : 2 * (|E| + D) * m = 2 * (|E| * m) + 2 * (D * m) := by ring
  linarith

/-! ## The cosine link in `L⁴` -/

section Core

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma cos_M4_core {Ef X Y Df : Ω → ℝ} {c kE Q : ℝ} (hc0 : 0 ≤ c) (hkE : 0 ≤ kE) (hQ : 0 ≤ Q)
    (hEm : AEStronglyMeasurable Ef μ) (hXm : AEStronglyMeasurable X μ)
    (hYm : AEStronglyMeasurable Y μ) (hDm : AEStronglyMeasurable Df μ)
    (hE2 : L2le μ (fun ω => Ef ω ^ 2) (c ^ 2 * kE)) (hE4 : L2le μ (fun ω => Ef ω ^ 4) Q)
    (hX4 : L2le μ (fun ω => X ω ^ 4) Q) (hY4 : L2le μ (fun ω => Y ω ^ 4) Q)
    (hD2 : ∀ ω, |Df ω| ≤ 2)
    (hpt : ∀ ω, max |X ω| |Y ω| ≤ 1 / 2 → |Df ω| ≤ |Ef ω| +
      2 * (|Ef ω| * max |X ω| |Y ω|) + (X ω ^ 2 + Y ω ^ 2)) :
    M4le μ Df ((c * √kE + 2 * √(√(Q * (√2 * Q))) + (√Q + √Q)) ^ 4 + 8192 * Q ^ 2) := by
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hmm : AEStronglyMeasurable (fun ω => max |X ω| |Y ω|) μ :=
    (continuous_abs.comp_aestronglyMeasurable hXm).sup
      (continuous_abs.comp_aestronglyMeasurable hYm)
  have hm2m : AEStronglyMeasurable (fun ω => max |X ω| |Y ω| ^ 2) μ := hmm.pow 2
  have hE2m : AEStronglyMeasurable (fun ω => Ef ω ^ 2) μ := hEm.pow 2
  have hM4 := l2_max_pow 4 hXm hYm hX4 hY4
  have t1 : M4le μ (fun ω => |Ef ω|) ((c * √kE) ^ 4) :=
    M4le.of_l2sq (continuous_abs.comp_aestronglyMeasurable hEm)
      ((hE2.congr_fun fun ω => (sq_abs _).symm).congr_bound
        (by rw [mul_pow, Real.sq_sqrt hkE]))
  have h2 := l2_abs_mul_of_sq hQ (mul_nonneg hs2 hQ) hE2m hm2m
    (hE4.congr_fun fun ω => by ring) (hM4.congr_fun fun ω => by ring)
  have t2 : M4le μ (fun ω => |Ef ω| * max |X ω| |Y ω|) (√(√(Q * (√2 * Q))) ^ 4) := by
    refine M4le.of_l2sq ((continuous_abs.comp_aestronglyMeasurable hEm).mul hmm)
      ((h2.congr_fun fun ω => ?_).congr_bound (Real.sq_sqrt (Real.sqrt_nonneg _)).symm)
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _), mul_pow, sq_abs]
  have t3 : M4le μ (fun ω => X ω ^ 2) (√Q ^ 4) :=
    M4le.of_l2sq (hXm.pow 2)
      ((hX4.congr_fun fun ω => by ring).congr_bound (Real.sq_sqrt hQ).symm)
  have t4 : M4le μ (fun ω => Y ω ^ 2) (√Q ^ 4) :=
    M4le.of_l2sq (hYm.pow 2)
      ((hY4.congr_fun fun ω => by ring).congr_bound (Real.sq_sqrt hQ).symm)
  have hsum := ((t1.add (t2.const_mul (c := 2) (by norm_num)) (by positivity)
    (by positivity)).add (t3.add t4 (by positivity) (by positivity)) (by positivity)
    (by positivity))
  have hpt2 : ∀ ω, (Df ω ^ 2) ^ 2 ≤
      ((|Ef ω| + 2 * (|Ef ω| * max |X ω| |Y ω|) + (X ω ^ 2 + Y ω ^ 2)) ^ 2) ^ 2 +
        4096 * (max |X ω| |Y ω| ^ 4) ^ 2 := by
    intro ω
    have hm0 : 0 ≤ max |X ω| |Y ω| := le_max_of_le_left (abs_nonneg _)
    rcases le_or_gt (max |X ω| |Y ω|) (1 / 2) with h | h
    · have h1 := hpt ω h
      have h1' : Df ω ^ 2 ≤
          (|Ef ω| + 2 * (|Ef ω| * max |X ω| |Y ω|) + (X ω ^ 2 + Y ω ^ 2)) ^ 2 := by
        rw [← sq_abs (Df ω)]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have := pow_le_pow_left₀ (sq_nonneg _) h1' 2
      have : 0 ≤ 4096 * (max |X ω| |Y ω| ^ 4) ^ 2 := by positivity
      linarith
    · have h1 : Df ω ^ 2 ≤ 2 ^ 2 := by
        rw [← sq_abs (Df ω)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hD2 ω) 2
      have h2 : (Df ω ^ 2) ^ 2 ≤ (2 ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
      have h3 : (1 / 2 : ℝ) ^ 4 ≤ max |X ω| |Y ω| ^ 4 :=
        pow_le_pow_left₀ (by norm_num) h.le 4
      have h4 : ((1 / 2 : ℝ) ^ 4) ^ 2 ≤ (max |X ω| |Y ω| ^ 4) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) h3 2
      have : 0 ≤ ((|Ef ω| + 2 * (|Ef ω| * max |X ω| |Y ω|) + (X ω ^ 2 + Y ω ^ 2)) ^ 2) ^ 2 :=
        by positivity
      norm_num at h2 h4 ⊢
      linarith
  have iA : Integrable (fun ω =>
      ((|Ef ω| + 2 * (|Ef ω| * max |X ω| |Y ω|) + (X ω ^ 2 + Y ω ^ 2)) ^ 2) ^ 2) μ := hsum.2.1
  have iB : Integrable (fun ω => 4096 * (max |X ω| |Y ω| ^ 4) ^ 2) μ :=
    hM4.int_sq.const_mul 4096
  have iG : Integrable (fun ω =>
      ((|Ef ω| + 2 * (|Ef ω| * max |X ω| |Y ω|) + (X ω ^ 2 + Y ω ^ 2)) ^ 2) ^ 2 +
        4096 * (max |X ω| |Y ω| ^ 4) ^ 2) μ := iA.add iB
  have hi : Integrable (fun ω => (Df ω ^ 2) ^ 2) μ := by
    refine Integrable.mono' iG ((hDm.pow 2).pow 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt2 ω
  refine ⟨hDm, hi, (integral_mono hi iG hpt2).trans ?_⟩
  rw [integral_add iA iB, integral_const_mul]
  have b1 : ∫ ω, ((|Ef ω| + 2 * (|Ef ω| * max |X ω| |Y ω|) + (X ω ^ 2 + Y ω ^ 2)) ^ 2) ^ 2 ∂μ ≤
      (c * √kE + 2 * √(√(Q * (√2 * Q))) + (√Q + √Q)) ^ 4 := hsum.2.2
  have b2 := hM4.le
  rw [mul_pow, Real.sq_sqrt (by norm_num)] at b2
  linarith

end Core

/-- The constant of `‖E²‖₂`: `‖E²‖₂ ≤ (1 − τ²)²·kEC n`. -/
noncomputable def kEC (n : ℕ) : ℝ := K4 n / (n : ℝ)

/-- The second-order term of the cosine link in `L⁴`. -/
noncomputable def j4C (n : ℕ) : ℝ :=
  2 * √(√(qCos n * (√2 * qCos n))) + (√(qCos n) + √(qCos n))

/-- The term of the event `max(|x|, |y|) > 1/2` in the fourth moment of the cosine link. -/
noncomputable def t4C (n : ℕ) : ℝ := 8192 * qCos n ^ 2

lemma kEC_nonneg (n : ℕ) : 0 ≤ kEC n := by
  have := K4_nonneg n
  unfold kEC
  positivity

lemma j4C_nonneg (n : ℕ) : 0 ≤ j4C n := by unfold j4C; positivity

lemma t4C_nonneg (n : ℕ) : 0 ≤ t4C n := by unfold t4C; positivity

variable {n k : ℕ}

/-- The `L²` norms of `E²` and of `E⁴`, `E = (⟨Mh, Mh′⟩ − τ(|Mh|² + |Mh′|²)/2)/(n·v)`. -/
lemma lin_E_moments {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') / ((n : ℝ) * v) - dotp h h' *
        ((normSq (M.mulVec h) / ((n : ℝ) * v) + normSq (M.mulVec h') / ((n : ℝ) * v)) / 2)) ^ 2)
      ((1 - dotp h h' ^ 2) ^ 2 * kEC n) ∧
    L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') / ((n : ℝ) * v) - dotp h h' *
        ((normSq (M.mulVec h) / ((n : ℝ) * v) + normSq (M.mulVec h') / ((n : ℝ) * v)) / 2)) ^ 4)
      (qCos n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set τ := dotp h h' with hτdef
  set s := (n : ℝ) * v with hs
  have hs0 : 0 < s := mul_pos hn0 hv
  have hQ0 := qCos_nonneg n
  have hK0 := kEC_nonneg n
  have hτ : |τ| ≤ 1 := by
    have := abs_dotp_le_nrm h h'
    rwa [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one] at this
  have hτ' := abs_le.mp hτ
  have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have hτ3 : 1 - τ ^ 2 ≤ 1 := by nlinarith [sq_nonneg τ]
  have hEm : Measurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') / s -
        τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2)) :=
    ((measurable_dotp_mulVec h h').div_const _).sub
      (((((measurable_normSq_mulVec h).div_const _).add
        ((measurable_normSq_mulVec h').div_const _)).div_const _).const_mul _)
  have nP : normSq (h + h') = 2 + 2 * τ := by rw [normSq_add_eq, hh, hh']; ring
  have nM : normSq (h - h') = 2 - 2 * τ := by rw [normSq_sub_eq, hh, hh']; ring
  have epw : ∀ M : Matrix (Fin n) (Fin k) ℝ,
      dotp (M.mulVec h) (M.mulVec h') / s -
        τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2) =
      ((1 - τ) * (normSq (M.mulVec (h + h')) / s - (2 + 2 * τ)) -
        (1 + τ) * (normSq (M.mulVec (h - h')) / s - (2 - 2 * τ))) / 4 := by
    intro M
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, normSq_add_eq, normSq_sub_eq]
    field_simp
    ring
  constructor
  · have hP : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
        (normSq (M.mulVec (h + h')) / s - (2 + 2 * τ)) ^ 2) ((2 + 2 * τ) ^ 2 * kEC n) := by
      have := dev_sq_L2 hv hn (h + h')
      rw [nP, ← hs] at this
      refine this.congr_fun fun M => ?_
      congr 1; rw [hs]; field_simp
    have hMi : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
        (normSq (M.mulVec (h - h')) / s - (2 - 2 * τ)) ^ 2) ((2 - 2 * τ) ^ 2 * kEC n) := by
      have := dev_sq_L2 hv hn (h - h')
      rw [nM, ← hs] at this
      refine this.congr_fun fun M => ?_
      congr 1; rw [hs]; field_simp
    have hg := (hP.const_mul_nonneg (c := (1 - τ) ^ 2 / 8) (by positivity)).add'
      (hMi.const_mul_nonneg (c := (1 + τ) ^ 2 / 8) (by positivity)) (by positivity)
      (by positivity)
    refine (L2le.of_abs_le (hEm.pow_const 2).aestronglyMeasurable hg (fun M => ?_)).congr_bound
      (by ring)
    obtain ⟨x, hx⟩ : ∃ x, x = normSq (M.mulVec (h + h')) / s - (2 + 2 * τ) := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y = normSq (M.mulVec (h - h')) / s - (2 - 2 * τ) := ⟨_, rfl⟩
    rw [abs_of_nonneg (sq_nonneg _), epw M, ← hx, ← hy]
    refine le_trans ?_ (le_abs_self _)
    have e2 : (1 - τ) ^ 2 / 8 * x ^ 2 + (1 + τ) ^ 2 / 8 * y ^ 2 -
        (((1 - τ) * x - (1 + τ) * y) / 4) ^ 2 = (((1 - τ) * x + (1 + τ) * y) / 4) ^ 2 := by
      ring
    have := sq_nonneg (((1 - τ) * x + (1 + τ) * y) / 4)
    linarith
  · have hP : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
        (normSq (M.mulVec (h + h')) / s - (2 + 2 * τ)) ^ 4) ((2 + 2 * τ) ^ 4 * qCos n) := by
      have := dev_four_L2 hv hn (h + h')
      rw [nP, ← hs] at this
      refine this.congr_fun fun M => ?_
      congr 1; rw [hs]; field_simp
    have hMi : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
        (normSq (M.mulVec (h - h')) / s - (2 - 2 * τ)) ^ 4) ((2 - 2 * τ) ^ 4 * qCos n) := by
      have := dev_four_L2 hv hn (h - h')
      rw [nM, ← hs] at this
      refine this.congr_fun fun M => ?_
      congr 1; rw [hs]; field_simp
    have hg := (hP.const_mul_nonneg (c := (1 - τ) ^ 4 / 32) (by positivity)).add'
      (hMi.const_mul_nonneg (c := (1 + τ) ^ 4 / 32) (by positivity)) (by positivity)
      (by positivity)
    refine (L2le.of_abs_le (hEm.pow_const 4).aestronglyMeasurable hg (fun M => ?_)).mono
      (by positivity) ?_
    · obtain ⟨x, hx⟩ : ∃ x, x = normSq (M.mulVec (h + h')) / s - (2 + 2 * τ) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y, y = normSq (M.mulVec (h - h')) / s - (2 - 2 * τ) := ⟨_, rfl⟩
      rw [epw M, ← hx, ← hy]
      obtain ⟨A, hA⟩ : ∃ A, A = (1 - τ) * x := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B, B = (1 + τ) * y := ⟨_, rfl⟩
      have e1 : (1 - τ) ^ 4 / 32 * x ^ 4 + (1 + τ) ^ 4 / 32 * y ^ 4 = (A ^ 4 + B ^ 4) / 32 := by
        rw [hA, hB]; ring
      rw [e1, ← hA, ← hB, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have h1 : (A - B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by linarith [sq_nonneg (A + B)]
      have h2 : ((A - B) ^ 2) ^ 2 ≤ (2 * (A ^ 2 + B ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
      have h3 : (A ^ 2 + B ^ 2) ^ 2 ≤ 2 * (A ^ 4 + B ^ 4) := by
        linarith [sq_nonneg (A ^ 2 - B ^ 2)]
      have e2 : ((A - B) / 4) ^ 4 = ((A - B) ^ 2) ^ 2 / 256 := by ring
      rw [e2]
      linarith
    · have e : (1 - τ) ^ 4 / 32 * ((2 + 2 * τ) ^ 4 * qCos n) +
          (1 + τ) ^ 4 / 32 * ((2 - 2 * τ) ^ 4 * qCos n) = (1 - τ ^ 2) ^ 4 * qCos n := by ring
      rw [e]
      exact mul_le_of_le_one_left hQ0 (pow_le_one₀ hτ2 hτ3)

/-- **The cosine link in `L⁴`, unit inputs.** -/
theorem lin_cos_unit_M4 {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    M4le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - dotp h h')
      (((1 - dotp h h' ^ 2) * √(kEC n) + j4C n) ^ 4 + t4C n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hE2, hE4⟩ := lin_E_moments (n := n) hv hn hh hh'
  set τ := dotp h h' with hτdef
  set s := (n : ℝ) * v with hs
  have hs0 : 0 < s := mul_pos hn0 hv
  have hQ0 := qCos_nonneg n
  have hτ : |τ| ≤ 1 := by
    have := abs_dotp_le_nrm h h'
    rwa [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one] at this
  have hτ' := abs_le.mp hτ
  have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have hA4 : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h) / s - 1) ^ 4) (qCos n) := by
    have := dev_four_L2 hv hn h
    rw [hh, one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hB4 : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h') / s - 1) ^ 4) (qCos n) := by
    have := dev_four_L2 hv hn h'
    rw [hh', one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hXm : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      normSq (M.mulVec h) / s - 1) (gaussMat n k v) :=
    (((measurable_normSq_mulVec h).div_const _).sub_const _).aestronglyMeasurable
  have hYm : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      normSq (M.mulVec h') / s - 1) (gaussMat n k v) :=
    (((measurable_normSq_mulVec h').div_const _).sub_const _).aestronglyMeasurable
  have hEm : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') / s -
        τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2)) (gaussMat n k v) :=
    (((measurable_dotp_mulVec h h').div_const _).sub
      (((((measurable_normSq_mulVec h).div_const _).add
        ((measurable_normSq_mulVec h').div_const _)).div_const _).const_mul
          _)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) (gaussMat n k v) :=
    ((measurable_dotp_sphPt h h').sub_const _).aestronglyMeasurable
  have hT : ∀ M : Matrix (Fin n) (Fin k) ℝ,
      |dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h'))| ≤ 1 := fun M =>
    abs_le.2 ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩
  have hcore := cos_M4_core (c := 1 - τ ^ 2) hτ2 (kEC_nonneg n) hQ0 hEm hXm hYm hmeas hE2 hE4
    hA4 hB4 (fun M => (abs_sub _ _).trans (by linarith [hT M])) (fun M hmM => ?_)
  · exact hcore.mono (le_of_eq (by unfold j4C t4C; ring))
  -- the pointwise bound
  have hX0 : 0 ≤ normSq (M.mulVec h) := normSq_nonneg _
  have hY0 : 0 ≤ normSq (M.mulVec h') := normSq_nonneg _
  have hab : √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) =
      nrm (M.mulVec h) * nrm (M.mulVec h') / s := by
    rw [Real.sqrt_div hX0, Real.sqrt_div hY0]
    unfold nrm
    field_simp
    rw [Real.sq_sqrt hs0.le]; ring
  have hTeq : 0 < √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) →
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) = dotp (M.mulVec h) (M.mulVec h') / s /
        (√(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s)) := by
    intro hpos
    have hx : normSq (M.mulVec h) ≠ 0 := by
      intro h0
      rw [h0, zero_div, Real.sqrt_zero, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hy : normSq (M.mulVec h') ≠ 0 := by
      intro h0
      rw [h0, zero_div, Real.sqrt_zero, mul_zero] at hpos
      exact lt_irrefl _ hpos
    rw [dotp_sphPt _ _ hx hy, hab]
    have := (nrm_pos_of_ne hx).ne'
    have := (nrm_pos_of_ne hy).ne'
    field_simp
  have hpt := cos_pt4 (c := dotp (M.mulVec h) (M.mulVec h') / s) (τ := τ)
    (Real.sqrt_nonneg (normSq (M.mulVec h) / s)) (Real.sqrt_nonneg (normSq (M.mulVec h') / s))
    hτ hTeq
  rw [Real.sq_sqrt (div_nonneg hX0 hs0.le), Real.sq_sqrt (div_nonneg hY0 hs0.le)] at hpt
  exact hpt hmM

/-- **The cosine link in `L⁴`**, nonzero inputs. -/
theorem lin_cos_M4 {n k : ℕ} {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) (h h' : Fin k → ℝ)
    (hh : normSq h ≠ 0) (hh' : normSq h' ≠ 0) :
    M4le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - cosv h h')
      (((1 - cosv h h' ^ 2) * √(kEC n) + j4C n) ^ 4 + t4C n) := by
  have hp := nrm_pos_of_ne hh
  have hp' := nrm_pos_of_ne hh'
  set g : Fin k → ℝ := (1 / nrm h) • h with hg
  set g' : Fin k → ℝ := (1 / nrm h') • h' with hg'
  have hg1 : normSq g = 1 := by
    rw [hg, normSq_smul, ← nrm_sq h]; field_simp
  have hg1' : normSq g' = 1 := by
    rw [hg', normSq_smul, ← nrm_sq h']; field_simp
  have hcos : dotp g g' = cosv h h' := by
    rw [hg, hg', dotp_smul_smul]; unfold cosv; field_simp
  have e : h = nrm h • g := by
    rw [hg, smul_smul]; field_simp; simp
  have e' : h' = nrm h' • g' := by
    rw [hg', smul_smul]; field_simp; simp
  have key := lin_cos_unit_M4 (n := n) hv hn hg1 hg1'
  rw [hcos] at key
  refine key.congr_fun fun M => ?_
  have e1 : M.mulVec h = nrm h • M.mulVec g := by
    conv_lhs => rw [e]
    rw [Matrix.mulVec_smul]
  have e2 : M.mulVec h' = nrm h' • M.mulVec g' := by
    conv_lhs => rw [e']
    rw [Matrix.mulVec_smul]
  rw [e1, e2, sphPt_smul hp, sphPt_smul hp']

end BstLean.Part145

open BstLean.Part145 in
#print axioms sphere_kk_M4
open BstLean.Part145 in
#print axioms lin_cos_M4
