import BstLean.Part48Rot

/-!
# Part 105: the Gebelein inequality in dimension `n`, for bounded measurable functions

For a standard Gaussian pair `(X, Z)` in `ℝ^ι × ℝ^ι`, `|ρ| ≤ 1` and `Y = ρ X + √(1−ρ²) Z` (so
`(X, Y)` is a centred Gaussian pair with covariance `[[I, ρI], [ρI, I]]`), and bounded measurable
`f`, `g`:

`|E f(X) g(Y) − E f(X) · E g(Y)| ≤ |ρ| · sd(f(X)) · sd(g(Y))` (`gebelein`).

Proof (no Hermite expansion, no density argument). `T_c h(x) = E h(c x + √(1−c²) Z)` is the
Ornstein–Uhlenbeck operator. From the rotation invariance of `γ ⊗ γ` (`Part48.rot_preserving`):
`T_a T_b = T_{ab}` (`Tou_Tou`), `T_c` is self-adjoint (`Tou_selfadj`), `E T_c h = E h`, and
`‖T_c h‖ ≤ ‖h‖` (Jensen). For `h` of mean zero and `κ = 2^{−1/2}`, the two functions
`T_κ h(X)`, `T_κ h(Z)` are orthogonal and are the projections of `h(κX + κZ)`, so
`2 ‖T_κ h‖² ≤ ‖h‖²` (Bessel; `bessel_half`). With `N(c) = ‖T_c h‖²` this gives
`N(κ c) ≤ N(c)/2`; self-adjointness and Cauchy–Schwarz give `N(√(ab))² ≤ N(a) N(b)`; and `N` is
monotone. So `N(2^{−t/2}) ≤ 2^{−t} N(1)` at every dyadic rational `t ≥ 0`, then at every real
`t ≥ 0`: `N(c) ≤ c² N(1)` (`Nou_le`). Finally `Cov(f(X), g(Y)) = ⟨T_{√ρ} f̃, T_{√ρ} g̃⟩`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part105

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part48 (rotX rotY rot_preserving)

/-- A bounded measurable real function. -/
structure BM {α : Type*} [MeasurableSpace α] (F : α → ℝ) : Prop where
  meas : Measurable F
  bdd : ∃ M : ℝ, ∀ x, |F x| ≤ M

namespace BM

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {F G : α → ℝ}

lemma const (c : ℝ) : BM (fun _ : α => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

lemma add (hF : BM F) (hG : BM G) : BM (fun x => F x + G x) := by
  obtain ⟨M, hM⟩ := hF.bdd
  obtain ⟨M', hM'⟩ := hG.bdd
  exact ⟨hF.meas.add hG.meas, M + M', fun x => (abs_add_le _ _).trans (add_le_add (hM x) (hM' x))⟩

lemma neg (hF : BM F) : BM (fun x => -F x) := by
  obtain ⟨M, hM⟩ := hF.bdd
  exact ⟨hF.meas.neg, M, fun x => by simpa using hM x⟩

lemma sub (hF : BM F) (hG : BM G) : BM (fun x => F x - G x) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

lemma mul (hF : BM F) (hG : BM G) : BM (fun x => F x * G x) := by
  obtain ⟨M, hM⟩ := hF.bdd
  obtain ⟨M', hM'⟩ := hG.bdd
  refine ⟨hF.meas.mul hG.meas, M * M', fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hM x) (hM' x) (abs_nonneg _) ((abs_nonneg _).trans (hM x))

lemma sq (hF : BM F) : BM (fun x => F x ^ 2) := by
  simpa [pow_two] using hF.mul hF

lemma comp (hF : BM F) {g : β → α} (hg : Measurable g) : BM (fun y => F (g y)) := by
  obtain ⟨M, hM⟩ := hF.bdd
  exact ⟨hF.meas.comp hg, M, fun y => hM _⟩

lemma integrable (hF : BM F) (μ : Measure α) [IsFiniteMeasure μ] : Integrable F μ := by
  obtain ⟨M, hM⟩ := hF.bdd
  exact Integrable.of_bound hF.meas.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by simpa using hM x)

lemma integral_right {H : α × β → ℝ} (hH : BM H) (ν : Measure β) [IsProbabilityMeasure ν] :
    BM (fun x => ∫ y, H (x, y) ∂ν) := by
  obtain ⟨M, hM⟩ := hH.bdd
  refine ⟨(hH.meas.stronglyMeasurable.integral_prod_right').measurable, M, fun x => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => H (x, y)) (C := M)
    (Filter.Eventually.of_forall fun y => by simpa using hM (x, y))
  simpa using this

lemma integral_left {H : α × β → ℝ} (hH : BM H) (μ : Measure α) [IsProbabilityMeasure μ] :
    BM (fun y => ∫ x, H (x, y) ∂μ) := by
  obtain ⟨M, hM⟩ := hH.bdd
  refine ⟨(hH.meas.stronglyMeasurable.integral_prod_left').measurable, M, fun y => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => H (x, y)) (C := M)
    (Filter.Eventually.of_forall fun x => by simpa using hM (x, y))
  simpa using this

end BM

/-- Cauchy–Schwarz for bounded measurable functions. -/
theorem bm_cauchy_schwarz {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {u v : α → ℝ} (hu : BM u) (hv : BM v) :
    (∫ x, u x * v x ∂μ) ^ 2 ≤ (∫ x, u x ^ 2 ∂μ) * ∫ x, v x ^ 2 ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, v x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, u x * v x ∂μ) * t +
      ∫ x, u x ^ 2 ∂μ := by
    intro t
    have h0 : 0 ≤ ∫ x, (u x + t * v x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have h1 : (fun x => (u x + t * v x) ^ 2) =
        fun x => (u x ^ 2 + (2 * t) * (u x * v x)) + (t * t) * v x ^ 2 := by
      funext x; ring
    rw [h1, integral_add ((hu.sq.add ((BM.const _).mul (hu.mul hv))).integrable μ)
      (((BM.const _).mul hv.sq).integrable μ),
      integral_add (hu.sq.integrable μ) (((BM.const _).mul (hu.mul hv)).integrable μ),
      integral_const_mul, integral_const_mul] at h0
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

lemma mp_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} {φ : α → β} (hmp : MeasurePreserving φ μ ν) (H : β → ℝ) (hH : Measurable H) :
    ∫ x, H (φ x) ∂μ = ∫ y, H y ∂ν := by
  rw [← hmp.map_eq]
  exact (integral_map hmp.measurable.aemeasurable hH.aestronglyMeasurable).symm

variable {ι : Type*}

lemma meas_comb (p q : ℝ) :
    Measurable (fun w : (ι → ℝ) × (ι → ℝ) => p • w.1 + q • w.2) :=
  (measurable_fst.const_smul p).add (measurable_snd.const_smul q)

variable [Fintype ι]

/-- A linear combination of two independent standard Gaussian vectors is a rescaled standard
Gaussian vector. -/
theorem gauss_comb (p q : ℝ) (hq : 0 ≤ q) (F : (ι → ℝ) → ℝ) (hF : Measurable F) :
    ∫ w, F (p • w.1 + q • w.2) ∂((stdGauss ι).prod (stdGauss ι)) =
      ∫ z, F (Real.sqrt (p ^ 2 + q ^ 2) • z) ∂stdGauss ι := by
  set r := Real.sqrt (p ^ 2 + q ^ 2) with hr
  by_cases h0 : r = 0
  · have hpq : p ^ 2 + q ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h0
    have hp : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq0 : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    simp [h0, hp, hq0]
  · have hrpos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    have hr2 : r ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt (by positivity)
    have hpr : (p / r) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_one (by positivity)]; nlinarith [sq_nonneg q]
    have habs : |p / r| ≤ 1 := by
      have := abs_le_of_sq_le_sq' (a := p / r) (b := 1) (by simpa using hpr) (by norm_num)
      exact abs_le.mpr this
    set θ := Real.arccos (p / r) with hθ
    have hc : Real.cos θ = p / r := Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2
    have hs : Real.sin θ = q / r := by
      rw [hθ, Real.sin_arccos]
      have : 1 - (p / r) ^ 2 = (q / r) ^ 2 := by
        field_simp
        nlinarith
      rw [this]
      exact Real.sqrt_sq (div_nonneg hq hrpos.le)
    have hmp := rot_preserving (ι := ι) θ
    calc ∫ w, F (p • w.1 + q • w.2) ∂((stdGauss ι).prod (stdGauss ι))
        = ∫ w, (fun v : (ι → ℝ) × (ι → ℝ) => F (r • v.1)) (rotX θ w.1 w.2, rotY θ w.1 w.2)
            ∂((stdGauss ι).prod (stdGauss ι)) := by
          congr 1
          funext w
          congr 1
          funext i
          simp only [rotX, hc, hs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
      _ = ∫ v, F (r • v.1) ∂((stdGauss ι).prod (stdGauss ι)) :=
          mp_integral hmp _ (hF.comp (measurable_fst.const_smul r))
      _ = ∫ z, F (r • z) ∂stdGauss ι := by
          rw [integral_fun_fst (fun x => F (r • x))]
          simp

/-- The standard Gaussian is symmetric. -/
theorem gauss_neg (F : (ι → ℝ) → ℝ) (hF : Measurable F) :
    ∫ z, F (-z) ∂stdGauss ι = ∫ z, F z ∂stdGauss ι := by
  have h1 := gauss_comb (ι := ι) (-1) 0 le_rfl F hF
  have h2 := gauss_comb (ι := ι) 1 0 le_rfl F hF
  simp only [neg_smul, one_smul, zero_smul, add_zero] at h1 h2
  rw [integral_fun_fst (fun x : ι → ℝ => F (-x))] at h1
  rw [integral_fun_fst (fun x : ι → ℝ => F x)] at h2
  simp only [probReal_univ, one_smul] at h1 h2
  rw [h1, h2]
  norm_num

/-- `√(1 − c²)`. -/
noncomputable def sC (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)

lemma sC_nonneg (c : ℝ) : 0 ≤ sC c := Real.sqrt_nonneg _

lemma sC_sq {c : ℝ} (hc : |c| ≤ 1) : sC c ^ 2 = 1 - c ^ 2 := by
  unfold sC
  rw [Real.sq_sqrt]
  have := sq_le_one_iff_abs_le_one c |>.mpr hc
  linarith

/-- The Ornstein–Uhlenbeck operator `T_c h(x) = E h(c x + √(1−c²) Z)`. -/
noncomputable def Tou (c : ℝ) (h : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ z, h (c • x + sC c • z) ∂stdGauss ι

variable {f g h : (ι → ℝ) → ℝ}

lemma Tou_BM (c : ℝ) (hh : BM h) : BM (Tou c h) :=
  (hh.comp (meas_comb c (sC c))).integral_right (stdGauss ι)

lemma integral_mul_Tou (c : ℝ) (hf : BM f) (hh : BM h) :
    ∫ x, f x * Tou c h x ∂stdGauss ι =
      ∫ w, f w.1 * h (c • w.1 + sC c • w.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
  rw [integral_prod _ (((hf.comp measurable_fst).mul (hh.comp (meas_comb c (sC c)))).integrable _)]
  simp only [Tou, integral_const_mul]

lemma integral_Tou {c : ℝ} (hc : |c| ≤ 1) (hh : BM h) :
    ∫ x, Tou c h x ∂stdGauss ι = ∫ x, h x ∂stdGauss ι := by
  have h1 := integral_mul_Tou (ι := ι) c (BM.const 1) hh
  simp only [one_mul] at h1
  rw [h1, gauss_comb c (sC c) (sC_nonneg c) h hh.meas, sC_sq hc]
  simp

lemma Tou_one (h : (ι → ℝ) → ℝ) : Tou 1 h = h := by
  funext x
  simp [Tou, sC]

lemma Tou_zero (h : (ι → ℝ) → ℝ) (x : ι → ℝ) : Tou 0 h x = ∫ z, h z ∂stdGauss ι := by
  simp [Tou, sC]

/-- The semigroup property. -/
theorem Tou_Tou {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hh : BM h) :
    Tou a (Tou b h) = Tou (a * b) h := by
  funext x
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]
  have h1 : Tou a (Tou b h) x =
      ∫ w, h ((a * b) • x + ((b * sC a) • w.1 + sC b • w.2))
        ∂((stdGauss ι).prod (stdGauss ι)) := by
    rw [integral_prod (fun w : (ι → ℝ) × (ι → ℝ) =>
        h ((a * b) • x + ((b * sC a) • w.1 + sC b • w.2)))
      ((hh.comp (g := fun w : (ι → ℝ) × (ι → ℝ) => (a * b) • x + ((b * sC a) • w.1 + sC b • w.2))
        (measurable_const.add (meas_comb (b * sC a) (sC b)))).integrable _)]
    simp only [Tou]
    congr 1
    funext z
    congr 1
    funext z'
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, gauss_comb (b * sC a) (sC b) (sC_nonneg b) (fun v => h ((a * b) • x + v))
    (hh.meas.comp (measurable_const.add measurable_id))]
  have h2 : Real.sqrt ((b * sC a) ^ 2 + sC b ^ 2) = sC (a * b) := by
    unfold sC
    congr 1
    rw [mul_pow, Real.sq_sqrt (by have := sq_le_one_iff_abs_le_one a |>.mpr ha; linarith),
      Real.sq_sqrt (by have := sq_le_one_iff_abs_le_one b |>.mpr hb; linarith)]
    ring
  rw [h2]
  rfl

/-- `T_c` is self-adjoint. -/
theorem Tou_selfadj {c : ℝ} (hc : |c| ≤ 1) (hf : BM f) (hg : BM g) :
    ∫ x, f x * Tou c g x ∂stdGauss ι = ∫ x, Tou c f x * g x ∂stdGauss ι := by
  rw [integral_mul_Tou c hf hg]
  set θ := Real.arccos c with hθ
  have hcos : Real.cos θ = c := Real.cos_arccos (abs_le.mp hc).1 (abs_le.mp hc).2
  have hsin : Real.sin θ = sC c := by rw [hθ, Real.sin_arccos]; rfl
  have hmp := rot_preserving (ι := ι) θ
  set H : (ι → ℝ) × (ι → ℝ) → ℝ := fun w => f (c • w.1 + sC c • (-w.2)) * g w.1 with hH
  have hHm : BM H :=
    (hf.comp ((measurable_fst.const_smul c).add (measurable_snd.neg.const_smul (sC c)))).mul
      (hg.comp measurable_fst)
  have key : ∀ w : (ι → ℝ) × (ι → ℝ), f w.1 * g (c • w.1 + sC c • w.2) =
      H (rotX θ w.1 w.2, rotY θ w.1 w.2) := by
    intro w
    simp only [hH]
    have e1 : c • rotX θ w.1 w.2 + sC c • (-rotY θ w.1 w.2) = w.1 := by
      funext i
      simp only [rotX, rotY, hcos, hsin, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      have := sC_sq hc
      linear_combination (w.1 i) * this
    have e2 : rotX θ w.1 w.2 = c • w.1 + sC c • w.2 := by
      funext i
      simp [rotX, hcos, hsin]
    rw [e1, e2]
  simp_rw [key]
  rw [mp_integral hmp H hHm.meas, integral_prod _ (hHm.integrable _)]
  congr 1
  funext x
  simp only [hH, integral_mul_const]
  congr 1
  exact gauss_neg (fun z => f (c • x + sC c • z))
    (hf.meas.comp (measurable_const.add (measurable_const_smul (sC c))))

/-! ## The norm `N(c) = E (T_c h)²` -/

/-- `N(c) = E (T_c h)²`. -/
noncomputable def Nou (c : ℝ) (h : (ι → ℝ) → ℝ) : ℝ := ∫ x, Tou c h x ^ 2 ∂stdGauss ι

lemma Nou_nonneg (c : ℝ) (h : (ι → ℝ) → ℝ) : 0 ≤ Nou c h := integral_nonneg fun _ => sq_nonneg _

lemma Nou_one (h : (ι → ℝ) → ℝ) : Nou 1 h = ∫ x, h x ^ 2 ∂stdGauss ι := by
  simp [Nou, Tou_one]

/-- Jensen: `(T_c h)² ≤ T_c (h²)`. -/
lemma Tou_sq_le (c : ℝ) (hh : BM h) (x : ι → ℝ) :
    Tou c h x ^ 2 ≤ Tou c (fun y => h y ^ 2) x := by
  have := bm_cauchy_schwarz (stdGauss ι) (u := fun z => h (c • x + sC c • z)) (v := fun _ => 1)
    (hh.comp (measurable_const.add (measurable_const_smul (sC c)))) (BM.const 1)
  simpa [Tou] using this

/-- `N` is monotone: `N(ab) ≤ N(b)`. -/
lemma Nou_mul_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hh : BM h) :
    Nou (a * b) h ≤ Nou b h := by
  have hT := Tou_BM (ι := ι) b hh
  calc Nou (a * b) h = ∫ x, Tou a (Tou b h) x ^ 2 ∂stdGauss ι := by rw [Nou, Tou_Tou ha hb hh]
    _ ≤ ∫ x, Tou a (fun y => Tou b h y ^ 2) x ∂stdGauss ι :=
        integral_mono ((Tou_BM a hT).sq.integrable _) ((Tou_BM a hT.sq).integrable _)
          (fun x => Tou_sq_le a hT x)
    _ = Nou b h := integral_Tou ha hT.sq

/-- `N(r)² ≤ N(a) N(b)` if `r² = ab` (self-adjointness and Cauchy–Schwarz). -/
lemma Nou_mid {a b r : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hr : |r| ≤ 1) (hrab : r * r = a * b)
    (hh : BM h) : Nou r h ^ 2 ≤ Nou a h * Nou b h := by
  have e : Nou r h = ∫ x, Tou a h x * Tou b h x ∂stdGauss ι := by
    calc Nou r h = ∫ x, Tou r h x * Tou r h x ∂stdGauss ι := by simp only [Nou, pow_two]
      _ = ∫ x, h x * Tou r (Tou r h) x ∂stdGauss ι := (Tou_selfadj hr hh (Tou_BM r hh)).symm
      _ = ∫ x, h x * Tou a (Tou b h) x ∂stdGauss ι := by
          rw [Tou_Tou hr hr hh, hrab, ← Tou_Tou ha hb hh]
      _ = ∫ x, Tou a h x * Tou b h x ∂stdGauss ι := Tou_selfadj ha hh (Tou_BM b hh)
  rw [e]
  exact bm_cauchy_schwarz (stdGauss ι) (Tou_BM a hh) (Tou_BM b hh)

/-! ## Bessel at `κ = 2^{−1/2}` -/

/-- `c(t) = 2^{−t/2}`. -/
noncomputable def cc (t : ℝ) : ℝ := (2 : ℝ) ^ (-t / 2)

lemma cc_pos (t : ℝ) : 0 < cc t := Real.rpow_pos_of_pos (by norm_num) _

lemma cc_add (s t : ℝ) : cc (s + t) = cc s * cc t := by
  unfold cc
  rw [← Real.rpow_add (by norm_num)]
  congr 1
  ring

lemma cc_zero : cc 0 = 1 := by simp [cc]

lemma cc_abs {t : ℝ} (ht : 0 ≤ t) : |cc t| ≤ 1 := by
  rw [abs_of_pos (cc_pos t)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)

lemma cc_sq (t : ℝ) : cc t ^ 2 = (2 : ℝ) ^ (-t) := by
  unfold cc
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

lemma cc_one_sq : cc 1 ^ 2 = 1 / 2 := by
  rw [cc_sq, Real.rpow_neg (by norm_num), Real.rpow_one]
  norm_num

lemma sC_cc_one : sC (cc 1) = cc 1 := by
  unfold sC
  rw [show (1 : ℝ) - cc 1 ^ 2 = cc 1 ^ 2 by rw [cc_one_sq]; norm_num]
  exact Real.sqrt_sq (cc_pos 1).le

/-- **Bessel**: for `h` of mean zero, `2 E (T_κ h)² ≤ E h²`, `κ = 2^{−1/2}`. -/
theorem bessel_half (hh : BM h) (h0 : ∫ x, h x ∂stdGauss ι = 0) :
    2 * Nou (cc 1) h ≤ ∫ x, h x ^ 2 ∂stdGauss ι := by
  set κ := cc 1 with hκ
  set T := Tou κ h with hT
  have bT : BM T := Tou_BM κ hh
  set A : (ι → ℝ) × (ι → ℝ) → ℝ := fun w => h (κ • w.1 + κ • w.2) with hA
  have bA : BM A := hh.comp (meas_comb κ κ)
  have bA1 : BM (fun w : (ι → ℝ) × (ι → ℝ) => T w.1) := bT.comp measurable_fst
  have bA2 : BM (fun w : (ι → ℝ) × (ι → ℝ) => T w.2) := bT.comp measurable_snd
  have iAA : ∫ w, A w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) = ∫ x, h x ^ 2 ∂stdGauss ι := by
    have h1 := gauss_comb κ κ (cc_pos 1).le (fun y => h y ^ 2) hh.sq.meas
    have h2 : Real.sqrt (κ ^ 2 + κ ^ 2) = 1 := by rw [cc_one_sq]; norm_num
    rw [h2] at h1
    simpa using h1
  have i11 : ∫ w, T w.1 ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) = Nou κ h := by
    rw [integral_fun_fst (fun x => T x ^ 2)]; simp [Nou, hT]
  have i22 : ∫ w, T w.2 ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) = Nou κ h := by
    rw [integral_fun_snd (fun x => T x ^ 2)]; simp [Nou, hT]
  have iA1 : ∫ w, A w * T w.1 ∂((stdGauss ι).prod (stdGauss ι)) = Nou κ h := by
    have h1 := integral_mul_Tou κ bT hh
    rw [sC_cc_one] at h1
    calc ∫ w, A w * T w.1 ∂((stdGauss ι).prod (stdGauss ι))
        = ∫ w, T w.1 * h (κ • w.1 + κ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
          congr 1; funext w; simp only [hA]; ring
      _ = ∫ x, T x * Tou κ h x ∂stdGauss ι := h1.symm
      _ = Nou κ h := by simp only [Nou, pow_two, hT]
  have iA2 : ∫ w, A w * T w.2 ∂((stdGauss ι).prod (stdGauss ι)) = Nou κ h := by
    rw [← iA1, ← integral_prod_swap]
    congr 1
    funext w
    simp only [hA, Prod.fst_swap, Prod.snd_swap, add_comm]
  have i12 : ∫ w, T w.1 * T w.2 ∂((stdGauss ι).prod (stdGauss ι)) = 0 := by
    rw [integral_prod_mul, hT, integral_Tou (cc_abs zero_le_one) hh, h0]
    simp
  have b1 := bA.sq
  have b2 := bA1.sq
  have b3 := bA2.sq
  have b4 := (BM.const (α := (ι → ℝ) × (ι → ℝ)) 2).mul (bA.mul bA1)
  have b5 := (BM.const (α := (ι → ℝ) × (ι → ℝ)) 2).mul (bA.mul bA2)
  have b6 := (BM.const (α := (ι → ℝ) × (ι → ℝ)) 2).mul (bA1.mul bA2)
  have hpos : 0 ≤ ∫ w, (A w - T w.1 - T w.2) ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) :=
    integral_nonneg fun w => sq_nonneg _
  have e : (fun w : (ι → ℝ) × (ι → ℝ) => (A w - T w.1 - T w.2) ^ 2) = fun w =>
      A w ^ 2 + T w.1 ^ 2 + T w.2 ^ 2 - 2 * (A w * T w.1) - 2 * (A w * T w.2) +
        2 * (T w.1 * T w.2) := by
    funext w; ring
  rw [e, integral_add (((((b1.add b2).add b3).sub b4).sub b5).integrable _) (b6.integrable _),
    integral_sub ((((b1.add b2).add b3).sub b4).integrable _) (b5.integrable _),
    integral_sub (((b1.add b2).add b3).integrable _) (b4.integrable _),
    integral_add ((b1.add b2).integrable _) (b3.integrable _),
    integral_add (b1.integrable _) (b2.integrable _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    iAA, i11, i22, iA1, iA2, i12] at hpos
  linarith

/-! ## The dyadic argument -/

section dyadic

variable (hh : BM h) (h0 : ∫ x, h x ∂stdGauss ι = 0)
include hh h0

lemma Nou_succ {t : ℝ} (ht : 0 ≤ t) : Nou (cc (t + 1)) h ≤ Nou (cc t) h / 2 := by
  have hb : BM (Tou (cc t) h) := Tou_BM _ hh
  have hm : ∫ x, Tou (cc t) h x ∂stdGauss ι = 0 := by rw [integral_Tou (cc_abs ht) hh, h0]
  have h1 := bessel_half hb hm
  have h2 : Nou (cc 1) (Tou (cc t) h) = Nou (cc (t + 1)) h := by
    simp only [Nou]
    rw [Tou_Tou (cc_abs zero_le_one) (cc_abs ht) hh, add_comm t 1, cc_add]
  rw [h2] at h1
  have h3 : ∫ x, Tou (cc t) h x ^ 2 ∂stdGauss ι = Nou (cc t) h := rfl
  linarith

/-- The target bound at exponent `t`. -/
def Good (h : (ι → ℝ) → ℝ) (t : ℝ) : Prop := Nou (cc t) h ≤ (2 : ℝ) ^ (-t) * Nou 1 h

omit hh h0 in
lemma good_zero : Good h 0 := by simp [Good, cc_zero]

lemma good_succ {t : ℝ} (ht : 0 ≤ t) (hg : Good h t) : Good h (t + 1) := by
  have h1 := Nou_succ hh h0 ht
  unfold Good at hg ⊢
  have h2 : (2 : ℝ) ^ (-(t + 1)) = (2 : ℝ) ^ (-t) / 2 := by
    rw [neg_add, Real.rpow_add (by norm_num), Real.rpow_neg_one]
    ring
  rw [h2]
  linarith

omit h0 in
lemma good_mid {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (hg : Good h t) (hg' : Good h t') :
    Good h ((t + t') / 2) := by
  unfold Good at hg hg' ⊢
  have hr : cc ((t + t') / 2) * cc ((t + t') / 2) = cc t * cc t' := by
    rw [← cc_add, ← cc_add]; congr 1; ring
  have h1 := Nou_mid (cc_abs ht) (cc_abs ht') (cc_abs (by positivity : 0 ≤ (t + t') / 2)) hr hh
  have hN := Nou_nonneg (ι := ι) 1 h
  have h2 : ((2 : ℝ) ^ (-((t + t') / 2)) * Nou 1 h) ^ 2 =
      ((2 : ℝ) ^ (-t) * Nou 1 h) * ((2 : ℝ) ^ (-t') * Nou 1 h) := by
    have : ((2 : ℝ) ^ (-((t + t') / 2))) ^ 2 = (2 : ℝ) ^ (-t) * (2 : ℝ) ^ (-t') := by
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [mul_pow, this]; ring
  have h3 : Nou (cc ((t + t') / 2)) h ^ 2 ≤ ((2 : ℝ) ^ (-((t + t') / 2)) * Nou 1 h) ^ 2 := by
    rw [h2]
    exact h1.trans (mul_le_mul hg hg' (Nou_nonneg _ _)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hN))
  exact le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hN) h3

lemma good_dyadic (k j : ℕ) : Good h ((j : ℝ) / 2 ^ k) := by
  induction k generalizing j with
  | zero =>
    induction j with
    | zero => simpa using good_zero (h := h)
    | succ j ih =>
      have := good_succ hh h0 (by positivity : (0 : ℝ) ≤ (j : ℝ) / 2 ^ 0) ih
      simpa using this
  | succ k ih =>
    obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' j
    · have : ((j : ℝ) / 2 ^ (k + 1)) = (i : ℝ) / 2 ^ k := by
        rw [hi, pow_succ]; push_cast; field_simp
      rw [this]; exact ih i
    · have : ((j : ℝ) / 2 ^ (k + 1)) = ((i : ℝ) / 2 ^ k + ((i + 1 : ℕ) : ℝ) / 2 ^ k) / 2 := by
        rw [hi, pow_succ]; push_cast; field_simp; ring
      rw [this]
      exact good_mid hh (by positivity) (by positivity) (ih i) (ih (i + 1))

lemma good_all {t : ℝ} (ht : 0 ≤ t) : Good h t := by
  have hN := Nou_nonneg (ι := ι) 1 h
  have hk : ∀ k : ℕ, Nou (cc t) h ≤ (2 : ℝ) ^ (-t + (1 / 2 : ℝ) ^ k) * Nou 1 h := by
    intro k
    set j := ⌊t * 2 ^ k⌋₊ with hj
    set q : ℝ := (j : ℝ) / 2 ^ k with hq
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have hq0 : 0 ≤ q := by positivity
    have hqt : q ≤ t := by
      rw [hq, div_le_iff₀ h2k]
      exact Nat.floor_le (by positivity)
    have htq : t < q + (1 / 2 : ℝ) ^ k := by
      have := Nat.lt_floor_add_one (t * 2 ^ k)
      rw [hq, one_div, inv_pow, ← one_div, ← add_div, lt_div_iff₀ h2k]
      exact this
    have hmono : Nou (cc t) h ≤ Nou (cc q) h := by
      have : cc t = cc (t - q) * cc q := by rw [← cc_add]; congr 1; ring
      rw [this]
      exact Nou_mul_le (cc_abs (by linarith)) (cc_abs hq0) hh
    have hgq := good_dyadic hh h0 k j
    unfold Good at hgq
    calc Nou (cc t) h ≤ Nou (cc q) h := hmono
      _ ≤ (2 : ℝ) ^ (-q) * Nou 1 h := hgq
      _ ≤ (2 : ℝ) ^ (-t + (1 / 2 : ℝ) ^ k) * Nou 1 h := by
          apply mul_le_mul_of_nonneg_right _ hN
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hlim : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ (-t + (1 / 2 : ℝ) ^ k) * Nou 1 h)
      Filter.atTop (nhds ((2 : ℝ) ^ (-t) * Nou 1 h)) := by
    have h1 : Filter.Tendsto (fun k : ℕ => -t + (1 / 2 : ℝ) ^ k) Filter.atTop (nhds (-t + 0)) :=
      tendsto_const_nhds.add
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    rw [add_zero] at h1
    exact (((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto (-t)).comp
      h1).mul_const _
  exact ge_of_tendsto' hlim hk

/-- **The contraction on mean-zero functions**: `E (T_c h)² ≤ c² E h²` for `0 ≤ c ≤ 1`. -/
theorem Nou_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Nou c h ≤ c ^ 2 * ∫ x, h x ^ 2 ∂stdGauss ι := by
  rcases hc0.eq_or_lt with hc | hc
  · subst hc
    simp [Nou, Tou_zero, h0]
  · set t := -2 * Real.logb 2 c with ht
    have ht0 : 0 ≤ t := by
      have : Real.logb 2 c ≤ 0 := Real.logb_nonpos (by norm_num) hc.le hc1
      rw [ht]; linarith
    have hcc : cc t = c := by
      unfold cc
      rw [show -t / 2 = Real.logb 2 c by rw [ht]; ring]
      exact Real.rpow_logb (by norm_num) (by norm_num) hc
    have h1 := good_all hh h0 ht0
    unfold Good at h1
    rw [← cc_sq, hcc, Nou_one] at h1
    exact h1

end dyadic

/-! ## The Gebelein inequality -/

/-- The Gebelein inequality for `0 ≤ ρ ≤ 1`. -/
theorem gebelein_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hf : BM f) (hg : BM g) :
    |∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        (∫ x, f x ∂stdGauss ι) * ∫ x, g x ∂stdGauss ι| ≤
      ρ * Real.sqrt (∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι) *
        Real.sqrt (∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι) := by
  set mf := ∫ y, f y ∂stdGauss ι with hmf
  set mg := ∫ y, g y ∂stdGauss ι with hmg
  set f' : (ι → ℝ) → ℝ := fun x => f x - mf with hf'
  set g' : (ι → ℝ) → ℝ := fun x => g x - mg with hg'
  have bf' : BM f' := hf.sub (BM.const mf)
  have bg' : BM g' := hg.sub (BM.const mg)
  have hρ : |ρ| ≤ 1 := by rw [abs_of_nonneg hρ0]; exact hρ1
  have mf' : ∫ x, f' x ∂stdGauss ι = 0 := by
    simp only [hf']
    rw [integral_sub (hf.integrable _) (integrable_const _)]
    simp [hmf]
  have mg' : ∫ x, g' x ∂stdGauss ι = 0 := by
    simp only [hg']
    rw [integral_sub (hg.integrable _) (integrable_const _)]
    simp [hmg]
  have hTg : ∀ x, Tou ρ g x = Tou ρ g' x + mg := by
    intro x
    simp only [Tou, hg']
    rw [integral_sub (f := fun z : ι → ℝ => g (ρ • x + sC ρ • z))
      ((hg.comp (g := fun z : ι → ℝ => ρ • x + sC ρ • z)
        (measurable_const.add (measurable_const_smul (sC ρ)))).integrable _)
      (integrable_const _)]
    simp
  have e1 : ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) - mf * mg =
      ∫ x, f' x * Tou ρ g' x ∂stdGauss ι := by
    rw [← integral_mul_Tou ρ hf hg]
    have bT := Tou_BM (ι := ι) ρ bg'
    have hT0 : ∫ x, Tou ρ g' x ∂stdGauss ι = 0 := by rw [integral_Tou hρ bg', mg']
    have : (fun x => f x * Tou ρ g x) = fun x => f' x * Tou ρ g' x + (mf * Tou ρ g' x + mg * f x) := by
      funext x; rw [hTg x]; simp only [hf']; ring
    rw [this, integral_add ((bf'.mul bT).integrable _)
      ((((BM.const mf).mul bT).add ((BM.const mg).mul hf)).integrable _),
      integral_add (((BM.const mf).mul bT).integrable _) (((BM.const mg).mul hf).integrable _),
      integral_const_mul, integral_const_mul, hT0]
    rw [← hmf]; ring
  rw [e1]
  set r := Real.sqrt ρ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = ρ := Real.mul_self_sqrt hρ0
  have hr1 : r ≤ 1 := by rw [hr]; exact Real.sqrt_le_one.mpr hρ1
  have hrabs : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have e2 : ∫ x, f' x * Tou ρ g' x ∂stdGauss ι =
      ∫ x, Tou r f' x * Tou r g' x ∂stdGauss ι := by
    rw [← hrr, ← Tou_Tou hrabs hrabs bg']
    exact Tou_selfadj hrabs bf' (Tou_BM r bg')
  rw [e2]
  have h1 := bm_cauchy_schwarz (stdGauss ι) (Tou_BM r bf') (Tou_BM r bg')
  have h2 := Nou_le bf' mf' hr0 hr1
  have h3 := Nou_le bg' mg' hr0 hr1
  have hr2 : r ^ 2 = ρ := by rw [pow_two, hrr]
  rw [hr2] at h2 h3
  set a := ∫ x, f' x ^ 2 ∂stdGauss ι with ha
  set b := ∫ x, g' x ^ 2 ∂stdGauss ι with hb
  have ha0 : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun _ => sq_nonneg _
  have h4 : (∫ x, Tou r f' x * Tou r g' x ∂stdGauss ι) ^ 2 ≤ ρ ^ 2 * (a * b) := by
    calc _ ≤ Nou r f' * Nou r g' := h1
      _ ≤ (ρ * a) * (ρ * b) := mul_le_mul h2 h3 (Nou_nonneg _ _) (mul_nonneg hρ0 ha0)
      _ = ρ ^ 2 * (a * b) := by ring
  have h5 := Real.abs_le_sqrt h4
  rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ0, Real.sqrt_mul ha0] at h5
  linarith

/-- **The Gebelein inequality in dimension `n`**, bounded measurable `f`, `g`: for independent
standard Gaussian vectors `X = w.1`, `Z = w.2` and `Y = ρ X + √(1−ρ²) Z`,
`|E f(X) g(Y) − E f(X) · E g(Y)| ≤ |ρ| · sd(f(X)) · sd(g(Y))`. -/
theorem gebelein {ρ : ℝ} (hρ : |ρ| ≤ 1) (hf : BM f) (hg : BM g) :
    |∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        (∫ x, f x ∂stdGauss ι) * ∫ x, g x ∂stdGauss ι| ≤
      |ρ| * Real.sqrt (∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι) *
        Real.sqrt (∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι) := by
  rcases le_or_gt 0 ρ with h0 | h0
  · rw [abs_of_nonneg h0]
    exact gebelein_nonneg h0 (by rw [abs_of_nonneg h0] at hρ; exact hρ) hf hg
  · have hρ' : -ρ ≤ 1 := by rw [abs_of_neg h0] at hρ; exact hρ
    set gn : (ι → ℝ) → ℝ := fun y => g (-y) with hgn
    have bgn : BM gn := hg.comp measurable_neg
    have h1 := gebelein_nonneg (ι := ι) (by linarith : 0 ≤ -ρ) hρ' hf bgn
    have hs : sC (-ρ) = sC ρ := by simp [sC]
    have e1 : ∫ w, f w.1 * gn ((-ρ) • w.1 + sC (-ρ) • w.2) ∂((stdGauss ι).prod (stdGauss ι)) =
        ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
      rw [hs]
      have bL : BM (fun w : (ι → ℝ) × (ι → ℝ) => f w.1 * gn ((-ρ) • w.1 + sC ρ • w.2)) :=
        (hf.comp measurable_fst).mul (bgn.comp (meas_comb (-ρ) (sC ρ)))
      have bR : BM (fun w : (ι → ℝ) × (ι → ℝ) => f w.1 * g (ρ • w.1 + sC ρ • w.2)) :=
        (hf.comp measurable_fst).mul (hg.comp (meas_comb ρ (sC ρ)))
      rw [integral_prod _ (bL.integrable _), integral_prod _ (bR.integrable _)]
      congr 1
      funext x
      simp only [integral_const_mul]
      congr 1
      have := gauss_neg (ι := ι) (fun z => g (ρ • x + sC ρ • z))
        (hg.meas.comp (measurable_const.add (measurable_const_smul (sC ρ))))
      rw [← this]
      congr 1
      funext z
      simp only [hgn]
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    have e2 : ∫ x, gn x ∂stdGauss ι = ∫ x, g x ∂stdGauss ι := gauss_neg g hg.meas
    have e3 : ∫ x, (gn x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι =
        ∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι :=
      gauss_neg (fun x => (g x - ∫ y, g y ∂stdGauss ι) ^ 2) (hg.sub (BM.const _)).sq.meas
    rw [e1, e2, e3] at h1
    rw [abs_of_neg h0]
    exact h1

end BstLean.Part105
