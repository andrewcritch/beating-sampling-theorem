import BstLean.Part136Sphere
import BstLean.Part133ReluR
import BstLean.Part105Law

/-!
# Part 136, item 2: the kernel bounds at finite width, and the good event of `(M₁, M₂)`

Role: `delegations/statements/p136-spec.md`.

`θ = (M₁, M₂)` are the two hidden matrices of a random ReLU network with `N` inputs and hidden
width `m`; `hidGauss N m` is their distribution; `h(u) = hid2 M₁ M₂ u` is the last hidden vector
and `G_θ(u, u′) = ⟨h(u), h(u′)⟩` the Gram kernel. The scale is `m/N`.

* `fK_L2`: `E_θ E_{u,u′} (G_θ(u, u′) − (m/N)·κ(κ(⟨u, u′⟩)))² ≤ ((m/N)·cF2o m)²`
  (`cF2o m² = (6(1 + 5/m) + (5κ(0) + √6)²)/m`, Part 133).
* `fD_L2`: `E_θ E_u (G_θ(u, u) − m/N)² ≤ ((m/N)·cF2o m)²`.
* `errK θ`, `errD θ`: the two integrated errors for fixed `θ`; `errK_mean`, `errD_mean`.
* `goodHid N m p₁ p₂`: the event `errK θ < ((m/N)·cF2o m)²/p₁` and
  `errD θ < ((m/N)·cF2o m)²/p₂`; `goodHid_prob`: its probability is at least `1 − p₁ − p₂`
  (Markov).
* `frame_of_good`: on the good event, for a polynomial model
  `|κ(κ(t)) − q − b·t − c₂·t²| ≤ η·t² + K₃·|t|³` of `κ∘κ`: `h̄ ≠ 0` and the unit residual
  directions have the frame bound
  `(b/N + 2c₂/(N(N+2)) + dK)/s + dK²/ε₂² + (cF2o m)²/(p₂ ε₁²)`, with
  `dK = cF2o m/√p₁ + η·√3/N + K₃·√(15/(N(N+2)(N+4)))`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part136

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134

variable {N m : ℕ}

/-- The two hidden matrices `(M₁, M₂)` of a network with `N` inputs and hidden width `m`. -/
abbrev HidParam (N m : ℕ) : Type := Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ

/-- The distribution of `(M₁, M₂)`: independent Gaussian entries of variance `2/N` and `2/m`. -/
noncomputable def hidGauss (N m : ℕ) : Measure (HidParam N m) :=
  (gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))

instance : IsProbabilityMeasure (hidGauss N m) := by unfold hidGauss; infer_instance

lemma continuous_hid2_joint :
    Continuous (fun p : HidParam N m × (Fin N → ℝ) => hid2 p.1.1 p.1.2 p.2) := by
  unfold hid2
  refine continuous_reluV.comp ?_
  refine Continuous.matrix_mulVec (by fun_prop) ?_
  refine continuous_reluV.comp ?_
  exact Continuous.matrix_mulVec (by fun_prop) (by fun_prop)

/-- The error of the Gram kernel at `(u, u′)`: `G_θ(u, u′) − (m/N)·κ(κ(⟨u, u′⟩))`. -/
noncomputable def fK (N m : ℕ) (z : ((Fin N → ℝ) × (Fin N → ℝ)) × HidParam N m) : ℝ :=
  dotp (hid2 z.2.1 z.2.2 z.1.1) (hid2 z.2.1 z.2.2 z.1.2) -
    (m : ℝ) / N * kappa (kappa (dotp z.1.1 z.1.2))

/-- The error of the diagonal of the Gram kernel at `u`: `|h(u)|² − m/N`. -/
noncomputable def fD (N m : ℕ) (z : (Fin N → ℝ) × HidParam N m) : ℝ :=
  normSq (hid2 z.2.1 z.2.2 z.1) - (m : ℝ) / N

lemma continuous_fK : Continuous (fK N m) := by
  unfold fK
  have h1 : Continuous (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × HidParam N m =>
      hid2 z.2.1 z.2.2 z.1.1) :=
    continuous_hid2_joint.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))
  have h2 : Continuous (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × HidParam N m =>
      hid2 z.2.1 z.2.2 z.1.2) :=
    continuous_hid2_joint.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  exact (continuous_dotp.comp (h1.prodMk h2)).sub (continuous_const.mul
    (continuous_kappa.comp (continuous_kappa.comp (continuous_dotp.comp continuous_fst))))

lemma continuous_fD : Continuous (fD N m) := by
  unfold fD
  have h1 : Continuous (fun z : (Fin N → ℝ) × HidParam N m => hid2 z.2.1 z.2.2 z.1) :=
    continuous_hid2_joint.comp (continuous_snd.prodMk continuous_fst)
  exact (continuous_normSq.comp h1).sub continuous_const

/-- The integrated error of the Gram kernel for fixed `θ = (M₁, M₂)`. -/
noncomputable def errK (θ : HidParam N m) : ℝ := ∫ uu, fK N m (uu, θ) ^ 2 ∂lawU2 N

/-- The integrated error of the diagonal for fixed `θ = (M₁, M₂)`. -/
noncomputable def errD (θ : HidParam N m) : ℝ := ∫ u, fD N m (u, θ) ^ 2 ∂uniformSphere N

lemma cF2o_pos (hm : 1 ≤ m) : 0 < cF2o m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold cF2o
  apply Real.sqrt_pos.mpr
  have : 0 ≤ (5 * kappa 0 + √6) ^ 2 / (m : ℝ) := by positivity
  have : 0 < 6 * (1 + 5 / (m : ℝ)) / (m : ℝ) := by positivity
  linarith

/-- **The Gram kernel at finite width**, in `L²` over the inputs and `(M₁, M₂)`. -/
theorem fK_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le ((lawU2 N).prod (hidGauss N m)) (fK N m) ((m : ℝ) / N * cF2o m) := by
  have := lawU2_prob hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine L2le.prod_const continuous_fK.measurable.aestronglyMeasurable ?_
  filter_upwards [lawU2_ae_unit hN] with uu huu
  have h := hid2_dot_L2o (m₁ := m) (m₂ := m) (k := N) (v₁ := 2 / (N : ℝ)) (v₂ := 2 / (m : ℝ))
    (by positivity) (by positivity) hm hm uu.1 uu.2
  rw [psi_unit _ huu.1 huu.2, nrm_of_normSq_one huu.1, nrm_of_normSq_one huu.2] at h
  have e1 : ∀ x : ℝ, (m : ℝ) / 2 * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (N : ℝ)) * x) =
      (m : ℝ) / N * x := by
    intro x
    field_simp
  rw [e1, e1] at h
  refine (h.congr_fun fun θ => ?_).congr_bound ?_
  · simp only [fK, Function.comp]
  · unfold cF2o
    ring

/-- **The diagonal of the Gram kernel at finite width**, in `L²` over the input and
`(M₁, M₂)`. -/
theorem fD_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le ((uniformSphere N).prod (hidGauss N m)) (fD N m) ((m : ℝ) / N * cF2o m) := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine L2le.prod_const continuous_fD.measurable.aestronglyMeasurable ?_
  filter_upwards [uniformSphere_ae_sphere N] with u hu0
  have hu : normSq u = 1 := hu0
  have h := hid2_dot_L2o (m₁ := m) (m₂ := m) (k := N) (v₁ := 2 / (N : ℝ)) (v₂ := 2 / (m : ℝ))
    (by positivity) (by positivity) hm hm u u
  rw [psi_unit _ hu hu, nrm_of_normSq_one hu] at h
  have e1 : ∀ x : ℝ, (m : ℝ) / 2 * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (N : ℝ)) * x) =
      (m : ℝ) / N * x := by
    intro x
    field_simp
  rw [e1, e1] at h
  refine (h.congr_fun fun θ => ?_).congr_bound ?_
  · simp only [fD, Function.comp, dotp_self, hu, kappa_one, mul_one]
  · unfold cF2o
    ring

theorem errK_mean (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (errK (N := N) (m := m)) (hidGauss N m) ∧
      ∫ θ, errK θ ∂hidGauss N m ≤ ((m : ℝ) / N * cF2o m) ^ 2 := by
  have := lawU2_prob hN
  have h := fK_L2 hN hm
  refine ⟨h.int_sq.integral_prod_right, ?_⟩
  have e := integral_prod_symm _ h.int_sq
  unfold errK
  rw [← e]
  exact h.le

theorem errD_mean (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (errD (N := N) (m := m)) (hidGauss N m) ∧
      ∫ θ, errD θ ∂hidGauss N m ≤ ((m : ℝ) / N * cF2o m) ^ 2 := by
  have := uniformSphere_isProbability N hN
  have h := fD_L2 hN hm
  refine ⟨h.int_sq.integral_prod_right, ?_⟩
  have e := integral_prod_symm _ h.int_sq
  unfold errD
  rw [← e]
  exact h.le

lemma measurable_errK (hN : 1 ≤ N) : Measurable (errK (N := N) (m := m)) := by
  have := lawU2_prob hN
  unfold errK
  exact ((continuous_fK.measurable.pow_const 2).stronglyMeasurable.integral_prod_left').measurable

lemma measurable_errD (hN : 1 ≤ N) : Measurable (errD (N := N) (m := m)) := by
  have := uniformSphere_isProbability N hN
  unfold errD
  exact ((continuous_fD.measurable.pow_const 2).stronglyMeasurable.integral_prod_left').measurable

lemma errK_nonneg (θ : HidParam N m) : 0 ≤ errK θ := integral_nonneg fun _ => sq_nonneg _

lemma errD_nonneg (θ : HidParam N m) : 0 ≤ errD θ := integral_nonneg fun _ => sq_nonneg _

/-- **The good event of `(M₁, M₂)`**: the two integrated errors are below their means divided by
`p₁` and `p₂`. -/
def goodHid (N m : ℕ) (p₁ p₂ : ℝ) : Set (HidParam N m) :=
  {θ | errK θ < ((m : ℝ) / N * cF2o m) ^ 2 / p₁ ∧ errD θ < ((m : ℝ) / N * cF2o m) ^ 2 / p₂}

theorem goodHid_meas (hN : 1 ≤ N) (p₁ p₂ : ℝ) : MeasurableSet (goodHid N m p₁ p₂) :=
  (measurableSet_lt (measurable_errK hN) measurable_const).inter
    (measurableSet_lt (measurable_errD hN) measurable_const)

/-- Markov, in the form used twice. -/
lemma markov_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfi : Integrable f P) {B p : ℝ} (hB : 0 < B) (hp : 0 < p)
    (hI : ∫ ω, f ω ∂P ≤ B) : P.real {ω | B / p ≤ f ω} ≤ p := by
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := f)
    (Filter.Eventually.of_forall hf0) hfi (B / p)
  have h2 : B / p * P.real {ω | B / p ≤ f ω} ≤ B := h1.trans hI
  have h3 : P.real {ω | B / p ≤ f ω} * B ≤ p * B := by
    have := mul_le_mul_of_nonneg_left h2 hp.le
    have e : p * (B / p * P.real {ω | B / p ≤ f ω}) = P.real {ω | B / p ≤ f ω} * B := by
      field_simp
    linarith
  exact le_of_mul_le_mul_right h3 hB

/-- **The probability of the good event** is at least `1 − p₁ − p₂`. -/
theorem goodHid_prob (hN : 1 ≤ N) (hm : 1 ≤ m) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) :
    1 - p₁ - p₂ ≤ (hidGauss N m).real (goodHid N m p₁ p₂) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := cF2o_pos hm
  have hB : 0 < ((m : ℝ) / N * cF2o m) ^ 2 := by positivity
  obtain ⟨iK, eK⟩ := errK_mean (m := m) hN hm
  obtain ⟨iD, eD⟩ := errD_mean (m := m) hN hm
  have m1 := markov_ge (hidGauss N m) errK_nonneg iK hB hp₁ eK
  have m2 := markov_ge (hidGauss N m) errD_nonneg iD hB hp₂ eD
  have hsub : (goodHid N m p₁ p₂)ᶜ ⊆
      {θ | ((m : ℝ) / N * cF2o m) ^ 2 / p₁ ≤ errK θ} ∪
        {θ | ((m : ℝ) / N * cF2o m) ^ 2 / p₂ ≤ errD θ} := by
    intro θ hθ
    simp only [goodHid, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_lt] at hθ
    exact hθ
  have h3 : (hidGauss N m).real (goodHid N m p₁ p₂)ᶜ ≤ p₁ + p₂ :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add m1 m2))
  rw [measureReal_compl (goodHid_meas hN p₁ p₂), probReal_univ] at h3
  linarith

lemma unit_mem_box {u : Fin N → ℝ} (hu : normSq u = 1) :
    u ∈ Set.Icc (fun _ : Fin N => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  have hx : ∑ i, u i ^ 2 = 1 := hu
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (u i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (u i - 1)]

/-- A continuous function of two points of the sphere is integrable. -/
lemma lawU2_cont_integrable (hN : 1 ≤ N) {f : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (lawU2 N) := by
  have := lawU2_prob hN
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := fun _ : Fin N => (-1 : ℝ)) (b := fun _ => (1 : ℝ))).prod
    (isCompact_Icc (a := fun _ : Fin N => (-1 : ℝ)) (b := fun _ => (1 : ℝ)))).bddAbove_image
    hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [lawU2_ae_unit hN] with x hx
  apply hC
  apply Set.mem_image_of_mem
  exact ⟨unit_mem_box hx.1, unit_mem_box hx.2⟩

/-- `‖|⟨u, y⟩|³‖_{L²(u)} = √(15/(N(N+2)(N+4)))` for a unit vector `y` (the sixth moment). -/
lemma sphere_dot6 (hN : 1 ≤ N) {y : Fin N → ℝ} (hy : normSq y = 1) :
    L2le (uniformSphere N) (fun x : Fin N → ℝ => |dotp x y| ^ 3)
      (√(15 / ((N : ℝ) * (N + 2) * (N + 4)))) := by
  have := uniformSphere_isProbability N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcont : Continuous (fun x : Fin N → ℝ => dotp x y) :=
    continuous_dotp.comp (continuous_id.prodMk continuous_const)
  have e : ∀ x : Fin N → ℝ, (|dotp x y| ^ 3) ^ 2 = (∑ i, y i * x i) ^ (2 * 3) := by
    intro x
    have h1 : dotp x y = ∑ i, y i * x i := by
      unfold dotp
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← h1, ← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, sq_abs, ← pow_mul]
  refine ⟨(hcont.abs.pow 3).aestronglyMeasurable,
    BstLean.Part105.sphere_cont_integrable hN ((hcont.abs.pow 3).pow 2), ?_⟩
  simp_rw [e]
  rw [BstLean.Part58.Kappa.sphere_linear_even hN y 3, Real.sq_sqrt (by positivity)]
  have hy' : ∑ i, y i ^ 2 = 1 := hy
  rw [hy']
  refine le_of_eq ?_
  simp only [BstLean.Part29.gaussMom, BstLean.Part36.rhoD]
  norm_num [Finset.prod_range_succ, Nat.doubleFactorial, Nat.even_iff]

/-- The `L²` distance of the Gram kernel from its model `(m/N)(q + b·t + c₂·t²)`, `t = ⟨u, u′⟩`,
in units of `m/N`, on the good event: the finite-width part `cF2o m/√p₁`, and the two parts
`η·t²`, `K₃·|t|³` of the remainder of `κ∘κ`. -/
noncomputable def dK (N m : ℕ) (p₁ η K₃ : ℝ) : ℝ :=
  cF2o m / √p₁ + η * (√3 / (N : ℝ)) + K₃ * √(15 / ((N : ℝ) * (N + 2) * (N + 4)))

/-- **The frame bound on the good event.** Hypothesis `hmodel`: a polynomial model of `κ∘κ`
on `[−1, 1]`: `|κ(κ(t)) − q − b·t − c₂·t²| ≤ η·t² + K₃·|t|³`. For `θ = (M₁, M₂)` in
`goodHid N m p₁ p₂`: `h̄ ≠ 0` and `E_u ⟨e(u), w⟩² ≤ L·|w|²` with
`L = (b/N + 2c₂/(N(N+2)) + dK)/s + dK²/ε₂² + (cF2o m)²/(p₂·ε₁²)`. -/
theorem frame_of_good (hN : 1 ≤ N) (hm : 1 ≤ m) {p₁ p₂ ε₁ ε₂ s b c2 η K₃ : ℝ} (hp₁ : 0 < p₁)
    (hp₂ : 0 < p₂) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hb0 : 0 ≤ b) (hc2 : 0 ≤ c2) (hη : 0 ≤ η)
    (hK₃ : 0 ≤ K₃)
    (hmodel : ∀ t ∈ Icc (-1 : ℝ) 1,
      |kappa (kappa t) - kappa (kappa 0) - b * t - c2 * t ^ 2| ≤ η * t ^ 2 + K₃ * |t| ^ 3)
    (hΔq : dK N m p₁ η K₃ < 49372 / 100000)
    (hs : 0 < s)
    (hsle : s ≤ 1 - ε₁ - (49376 / 100000 + c2 / (N : ℝ) + ε₂) ^ 2 /
      (49372 / 100000 - dK N m p₁ η K₃))
    {θ : HidParam N m} (hθ : θ ∈ goodHid N m p₁ p₂) :
    hbar (uniformSphere N) (hid2 θ.1 θ.2) ≠ 0 ∧ ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, eDir (hbar (uniformSphere N) (hid2 θ.1 θ.2)) (hid2 θ.1 θ.2 u) j * w j) ^ 2
          ∂uniformSphere N ≤
        ((b / (N : ℝ) + c2 * (2 / ((N : ℝ) * (N + 2))) + dK N m p₁ η K₃) / s +
          dK N m p₁ η K₃ ^ 2 / ε₂ ^ 2 + cF2o m ^ 2 / p₂ / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
  have := lawU2_prob hN
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨S0, hS0def⟩ : ∃ S0 : ℝ, S0 = (m : ℝ) / N := ⟨_, rfl⟩
  have hS0 : 0 < S0 := by rw [hS0def]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = kappa (kappa 0) := ⟨_, rfl⟩
  have q1 : q ≤ 49376 / 100000 := hq ▸ kappa2_zero_le
  have q2 : 49372 / 100000 ≤ q := hq ▸ kappa2_zero_ge
  have hcF := cF2o_pos hm
  have hsp₁ : 0 < √p₁ := Real.sqrt_pos.mpr hp₁
  have hsp₂ : 0 < √p₂ := Real.sqrt_pos.mpr hp₂
  have hdK0 : 0 ≤ dK N m p₁ η K₃ := by unfold dK; positivity
  have hcontK : Continuous (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => fK N m (uu, θ)) :=
    continuous_fK.comp (continuous_id.prodMk continuous_const)
  -- the finite-width part
  have hfw : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => fK N m (uu, θ))
      (S0 * (cF2o m / √p₁)) := by
    refine ⟨hcontK.aestronglyMeasurable, lawU2_cont_integrable hN (hcontK.pow 2), ?_⟩
    have h1 := hθ.1
    unfold errK at h1
    refine h1.le.trans (le_of_eq ?_)
    have e : (cF2o m / √p₁) ^ 2 = cF2o m ^ 2 / p₁ := by rw [div_pow, Real.sq_sqrt hp₁.le]
    rw [mul_pow S0, e, hS0def]
    ring
  -- the part of `κ∘κ`
  have hmd : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2) :=
    continuous_dotp.measurable
  have hd4 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2 ^ 2)
      (√3 / (N : ℝ)) := by
    unfold lawU2
    refine L2le.prod_const_left (hmd.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with y hy
    exact sphere_dot4 hN hy
  have hd6 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => |dotp uu.1 uu.2| ^ 3)
      (√(15 / ((N : ℝ) * (N + 2) * (N + 4)))) := by
    unfold lawU2
    refine L2le.prod_const_left ((hmd.abs).pow_const 3).aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with y hy
    exact sphere_dot6 hN hy
  have hmk : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - q - b * dotp uu.1 uu.2 - c2 * dotp uu.1 uu.2 ^ 2) :=
    ((((continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable).sub
      measurable_const).sub (hmd.const_mul b)).sub ((hmd.pow_const 2).const_mul c2)
  have hbd := (hd4.const_mul_nonneg hη).add0 (hd6.const_mul_nonneg hK₃) (by positivity)
    (by positivity)
  have hdet0 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - q - b * dotp uu.1 uu.2 - c2 * dotp uu.1 uu.2 ^ 2)
      (η * (√3 / (N : ℝ)) + K₃ * √(15 / ((N : ℝ) * (N + 2) * (N + 4)))) := by
    refine L2le.abs_le_ae_R hmk.aestronglyMeasurable hbd ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have h := hmodel _ (unit_dot_mem huu.1 huu.2)
    rw [← hq] at h
    rw [abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ η * dotp uu.1 uu.2 ^ 2 + K₃ * |dotp uu.1 uu.2| ^ 3)]
    exact h
  have hdet := hdet0.const_mul_nonneg hS0.le
  have hsum := hfw.add0 hdet (by positivity) (by positivity)
  have hD : ∫ uu, (dotp (hid2 θ.1 θ.2 uu.1) (hid2 θ.1 θ.2 uu.2) - S0 * (q + c2 / (N : ℝ)) -
      S0 * b * dotp uu.1 uu.2 - S0 * c2 * (dotp uu.1 uu.2 ^ 2 - 1 / (N : ℝ))) ^ 2 ∂lawU2 N ≤
      (S0 * dK N m p₁ η K₃) ^ 2 := by
    have h1 := (hsum.congr_fun (g := fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      dotp (hid2 θ.1 θ.2 uu.1) (hid2 θ.1 θ.2 uu.2) - S0 * (q + c2 / (N : ℝ)) -
        S0 * b * dotp uu.1 uu.2 - S0 * c2 * (dotp uu.1 uu.2 ^ 2 - 1 / (N : ℝ)))
      (fun uu => by simp only [fK, hS0def, hq]; ring)).le
    refine h1.trans (le_of_eq ?_)
    unfold dK
    ring
  have hd : ∫ u, (normSq (hid2 θ.1 θ.2 u) - S0) ^ 2 ∂uniformSphere N ≤
      (S0 * (cF2o m / √p₂)) ^ 2 := by
    have h1 := hθ.2
    unfold errD fD at h1
    rw [hS0def]
    refine h1.le.trans (le_of_eq ?_)
    have e : (cF2o m / √p₂) ^ 2 = cF2o m ^ 2 / p₂ := by rw [div_pow, Real.sq_sqrt hp₂.le]
    rw [mul_pow ((m : ℝ) / N) (cF2o m / √p₂), e]
    ring
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = q + c2 / (N : ℝ) := ⟨_, rfl⟩
  have hc2N : 0 ≤ c2 / (N : ℝ) := by positivity
  have ha1 : a' ≤ 49376 / 100000 + c2 / (N : ℝ) := by rw [ha']; linarith
  have ha2 : 49372 / 100000 ≤ a' := by rw [ha']; linarith
  have hqd : 0 < a' - dK N m p₁ η K₃ := by linarith
  have hsle' : S0 * s ≤ S0 - S0 * ε₁ -
      (S0 * a' + S0 * ε₂) ^ 2 / (S0 * a' - S0 * dK N m p₁ η K₃) := by
    have e : (S0 * a' + S0 * ε₂) ^ 2 / (S0 * a' - S0 * dK N m p₁ η K₃) =
        S0 * ((a' + ε₂) ^ 2 / (a' - dK N m p₁ η K₃)) := by
      have : S0 * a' - S0 * dK N m p₁ η K₃ = S0 * (a' - dK N m p₁ η K₃) := by ring
      rw [this]
      field_simp
    have mono : (a' + ε₂) ^ 2 / (a' - dK N m p₁ η K₃) ≤
        (49376 / 100000 + c2 / (N : ℝ) + ε₂) ^ 2 / (49372 / 100000 - dK N m p₁ η K₃) :=
      div_le_div₀ (by positivity)
        (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by linarith) (by linarith)
    rw [e]
    have := mul_le_mul_of_nonneg_left (hsle.trans (by linarith :
      1 - ε₁ - (49376 / 100000 + c2 / (N : ℝ) + ε₂) ^ 2 /
          (49372 / 100000 - dK N m p₁ η K₃) ≤
        1 - ε₁ - (a' + ε₂) ^ 2 / (a' - dK N m p₁ η K₃))) hS0.le
    linarith
  rw [← ha'] at hD
  have key := sphere_frame hN (continuous_hid2 θ.1 θ.2) (a := S0 * a') (c := S0 * b)
    (c₂ := S0 * c2) (Δ := S0 * dK N m p₁ η K₃) (d := S0) (δ := S0 * (cF2o m / √p₂))
    (ε₁ := S0 * ε₁) (ε₂ := S0 * ε₂) (s := S0 * s) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity)
    (mul_lt_mul_of_pos_left (lt_of_lt_of_le hΔq ha2) hS0) hD hd (by positivity) hsle'
  refine ⟨key.1, fun w => (key.2 w).trans (le_of_eq ?_)⟩
  congr 1
  have ha : (S0 * b * (1 / (N : ℝ)) + S0 * c2 * (2 / ((N : ℝ) * (N + 2))) +
      S0 * dK N m p₁ η K₃) / (S0 * s) =
      (b / (N : ℝ) + c2 * (2 / ((N : ℝ) * (N + 2))) + dK N m p₁ η K₃) / s := by
    field_simp
  have hb' : (S0 * dK N m p₁ η K₃) ^ 2 / (S0 * ε₂) ^ 2 = dK N m p₁ η K₃ ^ 2 / ε₂ ^ 2 := by
    field_simp
  have hc' : (S0 * (cF2o m / √p₂)) ^ 2 / (S0 * ε₁) ^ 2 = cF2o m ^ 2 / p₂ / ε₁ ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hp₂.le]
    field_simp
  rw [ha, hb', hc']

end BstLean.Part136
