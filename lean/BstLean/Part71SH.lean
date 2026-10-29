import BstLean.Part71Defs
import BstLean.Part62HyperK
import BstLean.Part33Euler
import BstLean.Part56PropD_Polar
import BstLean.Part56MomProg_Sphere
import BstLean.Part56MomProg_Polynomial
import BstLean.Part48Var

/-!
# Part 71: Lemma SH (sphere fourth moment of a polynomial of degree at most `d`)

`sphereFourth71 d : SphereFourth71 d (8 * Kexp d)`.

Route: parity split into even and odd parts, homogenization by powers of `Σ xᵢ²`, polar
decomposition of the standard Gaussian (`E_γ H^{2k} = E_γ ‖g‖^{2Dk} · E_σ H^{2k}` for `H`
homogeneous of degree `D`), the Gaussian fourth moment bound `fourth_moment_explicit`, and the
radial moment inequality `(E‖g‖^{2D})² ≤ E‖g‖^{4D}`.
-/

namespace BstLean.Part71

open MeasureTheory MvPolynomial
open scoped ENNReal
open BstLean.Part29 (uniformSphere stdGauss)
open BstLean.Part41 (Mono phiM)
open BstLean.Part53 (unitF53 radF53)

variable {n : ℕ}

/-! ## Homogeneous evaluation -/

lemma sh_eval_smul {ι : Type*} [Fintype ι] (H : MvPolynomial ι ℝ) (D : ℕ) (hH : H.IsHomogeneous D)
    (c : ℝ) (x : ι → ℝ) : eval (c • x) H = c ^ D * eval x H := by
  classical
  conv_lhs => rw [H.as_sum]
  conv_rhs => rw [H.as_sum]
  simp only [map_sum, Finset.mul_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  have he (z : ι → ℝ) : d.prod (fun i e => z i ^ e) = ∏ i, z i ^ d i :=
    Finsupp.prod_fintype _ _ (by simp)
  rw [he, he]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hk : (∑ i, d i) = D := by
    have := hH.degree_eq_sum_deg_support hd
    rw [this]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi => Finsupp.notMem_support_iff.mp hi)).symm
  rw [hk]; ring

/-! ## Integrability on the sphere -/

lemma sh_sphere_int (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
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

/-! ## Negation invariance of the uniform distribution on the sphere -/

lemma sh_sphere_neg (f : (Fin n → ℝ) → ℝ) :
    ∫ x, f (-x) ∂uniformSphere n = ∫ x, f x ∂uniformSphere n := by
  have h := BstLean.Part56.MomProg.uniformSphere_involution (n := n)
    (LinearIsometryEquiv.neg ℝ) (fun x => by simp)
  have hfun : (fun x : Fin n → ℝ => WithLp.ofLp ((LinearIsometryEquiv.neg ℝ)
      (WithLp.toLp 2 x) : EuclideanSpace ℝ (Fin n))) = fun x => -x := by
    funext x; simp
  rw [hfun] at h
  conv_rhs => rw [← h]
  rw [show (fun x : Fin n → ℝ => -x) = ⇑(MeasurableEquiv.neg (Fin n → ℝ)) from rfl,
    integral_map_equiv (MeasurableEquiv.neg (Fin n → ℝ))]
  rfl

/-! ## Polar decomposition of a homogeneous moment -/

lemma sh_decomp (H : MvPolynomial (Fin n) ℝ) (D : ℕ) (hH : H.IsHomogeneous D) (k : ℕ)
    (g : Fin n → ℝ) :
    (eval g H) ^ (2 * k) = ((radF53 g) ^ 2) ^ (D * k) * (eval (unitF53 g) H) ^ (2 * k) := by
  have hs0 : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hr2 : (radF53 g) ^ 2 = ∑ i, g i ^ 2 := by unfold radF53; exact Real.sq_sqrt hs0
  have hg : g = radF53 g • unitF53 g := by
    by_cases hs : ∑ i, g i ^ 2 = 0
    · have hz : ∀ i, g i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g i))).mp hs i
          (Finset.mem_univ _)
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      have : g = 0 := funext hz
      subst this
      simp [unitF53, radF53]
    · have hr : radF53 g ≠ 0 := by
        unfold radF53; exact Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hs0 (Ne.symm hs))
      unfold unitF53
      rw [smul_smul, show radF53 g * (1 / Real.sqrt (∑ i, g i ^ 2)) = 1 by
        rw [← radF53]; field_simp, one_smul]
  conv_lhs => rw [hg, sh_eval_smul H D hH]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  congr 1
  ring_nf

lemma sh_polar (hn : 1 ≤ n) (H : MvPolynomial (Fin n) ℝ) (D : ℕ) (hH : H.IsHomogeneous D) (k : ℕ) :
    ∫ g, (eval g H) ^ (2 * k) ∂stdGauss (Fin n) =
      (∫ g, (∑ i, g i ^ 2) ^ (D * k) ∂stdGauss (Fin n)) *
        ∫ x, (eval x H) ^ (2 * k) ∂uniformSphere n := by
  have hcH : Continuous (fun x : Fin n → ℝ => eval x H) := MvPolynomial.continuous_eval H
  have hEv : ∀ x : Fin n → ℝ, 0 ≤ (eval x H) ^ (2 * k) := fun x => by
    rw [pow_mul]; positivity
  set F : (Fin n → ℝ) → ℝ → ℝ≥0∞ := fun u r =>
    ENNReal.ofReal ((r ^ 2) ^ (D * k)) * ENNReal.ofReal ((eval u H) ^ (2 * k)) with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    show Measurable (fun p : (Fin n → ℝ) × ℝ =>
      ENNReal.ofReal ((p.2 ^ 2) ^ (D * k)) * ENNReal.ofReal ((eval p.1 H) ^ (2 * k)))
    exact Measurable.mul (ENNReal.measurable_ofReal.comp ((measurable_snd.pow_const 2).pow_const _))
      (ENNReal.measurable_ofReal.comp ((hcH.measurable.comp measurable_fst).pow_const _))
  have hL : ∫⁻ g, ENNReal.ofReal ((eval g H) ^ (2 * k)) ∂stdGauss (Fin n) =
      (∫⁻ g, ENNReal.ofReal (((radF53 g) ^ 2) ^ (D * k)) ∂stdGauss (Fin n)) *
        ∫⁻ x, ENNReal.ofReal ((eval x H) ^ (2 * k)) ∂uniformSphere n := by
    have h1 : ∀ g, ENNReal.ofReal ((eval g H) ^ (2 * k)) = F (unitF53 g) (radF53 g) := by
      intro g
      rw [hFdef, sh_decomp H D hH k g, ENNReal.ofReal_mul (by positivity)]
    rw [lintegral_congr (μ := stdGauss (Fin n)) h1, BstLean.Part53.gauss_polar_gen F hFm]
    simp only [hFdef]
    have hm2 : Measurable (fun g : Fin n → ℝ => ENNReal.ofReal (((radF53 g) ^ 2) ^ (D * k))) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part53.measurable_radF.pow_const 2).pow_const _)
    simp_rw [lintegral_mul_const _ hm2]
    rw [lintegral_const_mul _ (f := fun Z => ENNReal.ofReal ((eval (unitF53 Z) H) ^ (2 * k)))
      ((ENNReal.measurable_ofReal.comp
      ((hcH.measurable.comp BstLean.Part53.measurable_unitF).pow_const _)))]
    congr 1
    exact (BstLean.Part56.uniformSphere_lintegral_gauss n hn
      (fun x => ENNReal.ofReal ((eval x H) ^ (2 * k)))
      (ENNReal.measurable_ofReal.comp (hcH.measurable.pow_const _))).symm
  have hr2 : ∀ g : Fin n → ℝ, (radF53 g) ^ 2 = ∑ i, g i ^ 2 := fun g => by
    unfold radF53; exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  simp_rw [hr2] at hL
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hEv)
      (hcH.pow _).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun g => by positivity))
      ((by fun_prop : Continuous (fun g : Fin n → ℝ => (∑ i, g i ^ 2) ^ (D * k))).aestronglyMeasurable),
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hEv)
      (hcH.pow _).aestronglyMeasurable, hL, ENNReal.toReal_mul]

/-! ## Radial moments of the standard Gaussian -/

/-- The polynomial `Σ Xᵢ²`. -/
noncomputable def shS (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ i, X i ^ 2

lemma shS_hom : (shS n).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X_pow i 2)

lemma shS_eval (x : Fin n → ℝ) : eval x (shS n) = ∑ i, x i ^ 2 := by simp [shS]

lemma sh_rad (m : ℕ) :
    ∫ g, (∑ i, g i ^ 2) ^ m ∂stdGauss (Fin n) = ∏ j ∈ Finset.range m, ((n : ℝ) + 2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := BstLean.Part33.stdGauss_normsq_mul (shS n ^ m) (2 * m) (by
      simpa [mul_comm] using (shS_hom (n := n)).pow m)
    simp only [map_pow, shS_eval, Fintype.card_fin] at h
    rw [Finset.prod_range_succ, ← ih]
    have he : ∀ g : Fin n → ℝ, (∑ i, g i ^ 2) ^ (m + 1) = (∑ i, g i ^ 2) * (∑ i, g i ^ 2) ^ m :=
      fun g => by ring
    simp_rw [he]
    rw [h]; push_cast; ring

lemma sh_rad_pos (m : ℕ) (hn : 1 ≤ n) : 0 < ∫ g, (∑ i, g i ^ 2) ^ m ∂stdGauss (Fin n) := by
  rw [sh_rad]
  apply Finset.prod_pos
  intro j _
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

lemma sh_rad_sq (D : ℕ) :
    (∫ g, (∑ i, g i ^ 2) ^ D ∂stdGauss (Fin n)) ^ 2 ≤
      ∫ g, (∑ i, g i ^ 2) ^ (2 * D) ∂stdGauss (Fin n) := by
  rw [sh_rad, sh_rad, two_mul, Finset.prod_range_add, sq]
  gcongr with j hj
  linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]

/-! ## The fourth moment of a homogeneous polynomial on the sphere -/

lemma sh_hom (hn : 1 ≤ n) (H : MvPolynomial (Fin n) ℝ) (D : ℕ) (hH : H.IsHomogeneous D)
    (d : ℕ) (hd : H.totalDegree ≤ d) :
    ∫ x, (eval x H) ^ 4 ∂uniformSphere n ≤
      BstLean.Part62.Kexp d * (∫ x, (eval x H) ^ 2 ∂uniformSphere n) ^ 2 := by
  have hF := BstLean.Part62.fourth_moment_explicit d (Fin n) H hd
  have h4 := sh_polar hn H D hH 2
  have h2 := sh_polar hn H D hH 1
  norm_num at h4 h2
  rw [h4, h2] at hF
  set c4 := ∫ g, (∑ i, g i ^ 2) ^ (D * 2) ∂stdGauss (Fin n)
  set c2 := ∫ g, (∑ i, g i ^ 2) ^ D ∂stdGauss (Fin n)
  set s4 := ∫ x, (eval x H) ^ 4 ∂uniformSphere n
  set s2 := ∫ x, (eval x H) ^ 2 ∂uniformSphere n
  have hc4 : 0 < c4 := sh_rad_pos _ hn
  have hcc : c2 ^ 2 ≤ c4 := by
    have := sh_rad_sq (n := n) D; rwa [mul_comm 2 D] at this
  have hK := (BstLean.Part62.Kexp_pos d).le
  have h3 : c4 * s4 ≤ c4 * (BstLean.Part62.Kexp d * s2 ^ 2) := by
    calc c4 * s4 ≤ BstLean.Part62.Kexp d * (c2 * s2) ^ 2 := hF
      _ = BstLean.Part62.Kexp d * s2 ^ 2 * c2 ^ 2 := by ring
      _ ≤ BstLean.Part62.Kexp d * s2 ^ 2 * c4 :=
          mul_le_mul_of_nonneg_left hcc (by positivity)
      _ = _ := by ring
  exact le_of_mul_le_mul_left h3 hc4

/-! ## Parity split and homogenization -/

/-- The homogenized parity-`b` part of `P`:
`Σ_{j ≤ d, j ≡ b (mod 2)} P_j · (Σ Xᵢ²)^{(d−j)/2}`, with `P_j` the degree-`j` component. -/
noncomputable def shH (d : ℕ) (P : MvPolynomial (Fin n) ℝ) (b : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ (Finset.range (d + 1)).filter (fun j => j % 2 = b),
    homogeneousComponent j P * shS n ^ ((d - j) / 2)

lemma shH_term_hom (d : ℕ) (P : MvPolynomial (Fin n) ℝ) (j : ℕ) :
    (homogeneousComponent j P * shS n ^ ((d - j) / 2)).IsHomogeneous (j + 2 * ((d - j) / 2)) :=
  (homogeneousComponent_isHomogeneous j P).mul ((shS_hom (n := n)).pow _)

lemma shH_hom (d : ℕ) (P : MvPolynomial (Fin n) ℝ) (b : ℕ) :
    (shH d P b).IsHomogeneous (if d % 2 = b then d else d - 1) := by
  apply IsHomogeneous.sum
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  have h := shH_term_hom d P j
  have he : j + 2 * ((d - j) / 2) = if d % 2 = b then d else d - 1 := by
    split_ifs with hb <;> omega
  rwa [he] at h

lemma shH_deg (d : ℕ) (P : MvPolynomial (Fin n) ℝ) (b : ℕ) : (shH d P b).totalDegree ≤ d :=
  (shH_hom d P b).totalDegree_le.trans (by split_ifs <;> omega)

lemma shH_eval_sphere (d : ℕ) (P : MvPolynomial (Fin n) ℝ) (b : ℕ) (x : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) :
    eval x (shH d P b) = ∑ j ∈ (Finset.range (d + 1)).filter (fun j => j % 2 = b),
      eval x (homogeneousComponent j P) := by
  simp [shH, map_sum, shS_eval, hx]

lemma shH_eval_neg (d : ℕ) (P : MvPolynomial (Fin n) ℝ) (b : ℕ) (x : Fin n → ℝ) :
    eval (-x) (shH d P b) = (-1) ^ b * eval x (shH d P b) := by
  simp only [shH, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  have h := sh_eval_smul _ _ (shH_term_hom d P j) (-1) x
  rw [neg_one_smul] at h
  rw [h, neg_one_pow_eq_pow_mod_two (n := j + 2 * ((d - j) / 2)),
    show (j + 2 * ((d - j) / 2)) % 2 = b by omega]

lemma sh_split (d : ℕ) (P : MvPolynomial (Fin n) ℝ) (hd : P.totalDegree ≤ d) (x : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) :
    eval x P = eval x (shH d P 0) + eval x (shH d P 1) := by
  rw [shH_eval_sphere d P 0 x hx, shH_eval_sphere d P 1 x hx]
  have hP : P = ∑ j ∈ Finset.range (d + 1), homogeneousComponent j P := by
    conv_lhs => rw [← sum_homogeneousComponent P]
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    · intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      exact homogeneousComponent_eq_zero _ _ (by omega)
  conv_lhs => rw [hP]
  rw [map_sum, ← Finset.sum_filter_add_sum_filter_not _ (fun j => j % 2 = 0)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega

/-! ## Lemma SH for a polynomial -/

lemma sh_poly (hn : 1 ≤ n) (d : ℕ) (P : MvPolynomial (Fin n) ℝ) (hd : P.totalDegree ≤ d) :
    ∫ x, (eval x P) ^ 4 ∂uniformSphere n ≤
      8 * BstLean.Part62.Kexp d * (∫ x, (eval x P) ^ 2 ∂uniformSphere n) ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  set a : (Fin n → ℝ) → ℝ := fun x => eval x (shH d P 0) with ha_def
  set b : (Fin n → ℝ) → ℝ := fun x => eval x (shH d P 1) with hb_def
  have ha : Continuous a := MvPolynomial.continuous_eval _
  have hb : Continuous b := MvPolynomial.continuous_eval _
  have hsplit : ∀ᵐ x ∂uniformSphere n, eval x P = a x + b x := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact sh_split d P hd x hx
  have hab : ∫ x, a x * b x ∂uniformSphere n = 0 := by
    have h1 := sh_sphere_neg (n := n) (fun x => a x * b x)
    have h2 : ∀ x, a (-x) * b (-x) = -(a x * b x) := by
      intro x
      simp only [ha_def, hb_def, shH_eval_neg]
      ring
    simp only [h2, integral_neg] at h1
    linarith
  set K := BstLean.Part62.Kexp d
  have hK := (BstLean.Part62.Kexp_pos d).le
  set A := ∫ x, a x ^ 2 ∂uniformSphere n
  set B := ∫ x, b x ^ 2 ∂uniformSphere n
  have hA : 0 ≤ A := integral_nonneg (fun x => sq_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun x => sq_nonneg _)
  have h2 : ∫ x, (eval x P) ^ 2 ∂uniformSphere n = A + B := by
    rw [integral_congr_ae (hsplit.mono (fun x hx => by
      show (eval x P) ^ 2 = a x ^ 2 + b x ^ 2 + 2 * (a x * b x)
      rw [hx]; ring))]
    rw [integral_add (sh_sphere_int hn (f := fun x => a x ^ 2 + b x ^ 2) ((ha.pow 2).add (hb.pow 2)))
      (sh_sphere_int hn (f := fun x => 2 * (a x * b x)) (continuous_const.mul (ha.mul hb))),
      integral_add (sh_sphere_int hn (f := fun x => a x ^ 2) (ha.pow 2))
        (sh_sphere_int hn (f := fun x => b x ^ 2) (hb.pow 2)),
      integral_const_mul, hab]
    ring
  have ha4 : ∫ x, a x ^ 4 ∂uniformSphere n ≤ K * A ^ 2 :=
    sh_hom hn _ _ (shH_hom d P 0) d (shH_deg d P 0)
  have hb4 : ∫ x, b x ^ 4 ∂uniformSphere n ≤ K * B ^ 2 :=
    sh_hom hn _ _ (shH_hom d P 1) d (shH_deg d P 1)
  have h4 : ∫ x, (eval x P) ^ 4 ∂uniformSphere n ≤
      8 * (∫ x, a x ^ 4 ∂uniformSphere n + ∫ x, b x ^ 4 ∂uniformSphere n) := by
    rw [← integral_add (sh_sphere_int hn (f := fun x => a x ^ 4) (ha.pow 4))
      (sh_sphere_int hn (f := fun x => b x ^ 4) (hb.pow 4)),
      ← integral_const_mul]
    apply integral_mono_ae
    · exact sh_sphere_int hn ((MvPolynomial.continuous_eval P).pow 4)
    · exact sh_sphere_int hn (f := fun x => 8 * (a x ^ 4 + b x ^ 4))
        (continuous_const.mul ((ha.pow 4).add (hb.pow 4)))
    · filter_upwards [hsplit] with x hx
      show (eval x P) ^ 4 ≤ 8 * (a x ^ 4 + b x ^ 4)
      rw [hx]
      have e1 : (a x + b x) ^ 2 ≤ 2 * (a x ^ 2 + b x ^ 2) := by nlinarith [sq_nonneg (a x - b x)]
      have e2 : (a x ^ 2 + b x ^ 2) ^ 2 ≤ 2 * (a x ^ 4 + b x ^ 4) := by
        nlinarith [sq_nonneg (a x ^ 2 - b x ^ 2)]
      have e3 : ((a x + b x) ^ 2) ^ 2 ≤ (2 * (a x ^ 2 + b x ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) e1 2
      nlinarith
  rw [h2]
  nlinarith [mul_nonneg hK (mul_nonneg hA hB)]

/-! ## Lemma SH in feature form -/

/-- **Lemma SH**: `E_σ (Σ_p a_p φ_p)⁴ ≤ 8 Kexp(d) (E_σ (Σ_p a_p φ_p)²)²` for every `n ≥ 1`. -/
theorem sphereFourth71 (d : ℕ) : SphereFourth71 d (8 * BstLean.Part62.Kexp d) := by
  intro n hn a
  set P : MvPolynomial (Fin n) ℝ :=
    ∑ p : Mono n d, C (a p) * BstLean.Part56.MomProg.monoPoly p with hP
  have hev : ∀ x, eval x P = ∑ p, a p * phiM x p := by
    intro x; simp [hP, map_sum, BstLean.Part56.MomProg.monoPoly_eval]
  have hd : P.totalDegree ≤ d := by
    apply totalDegree_finsetSum_le
    intro p _
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (BstLean.Part56.MomProg.monoPoly_degree p).trans (Nat.lt_succ_iff.mp p.1.2)
  have h := sh_poly hn d P hd
  simp only [hev] at h
  exact h

end BstLean.Part71
