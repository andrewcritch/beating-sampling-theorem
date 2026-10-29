import BstLean.Part86Defs
import BstLean.Part59RPlus
import BstLean.Part53Polar
import BstLean.Part53Remez
import BstLean.Part84Remez
import BstLean.Part84Poly
import BstLean.Part56Orth_Integrability
import Mathlib.LinearAlgebra.Lagrange

/-!
# Part 86, the sphere step (`RemezStep86`)

Remez on the radius of `W` (Lemma R+ of Part 59), polar independence (Part 53), Markov, Chebyshev
and the deterministic step, for the abstract slice model of `Part86Defs`.

`remez86`: from the Gaussian model given the anchors (`GaussModel86`) and the surrogate hypothesis
(`SurrHyp`, `η ≤ 1/40`), the failure probability over the direction of `W` is at most
`remezBound n k c1 cV`.
-/

namespace BstLean.Part86.XRemez

open MeasureTheory MvPolynomial
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part78 (zv)
open BstLean.Part84 (polar_transfer)

/-! ## Generic lemmas -/

section generic

/-- An integral of polynomials of degree `≤ N` in a parameter is a polynomial of degree `≤ N`
(Lagrange interpolation at the nodes `0, …, N`). -/
lemma poly_of_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) (N : ℕ)
    (h : ℝ → α → ℝ)
    (hpoly : ∀ a, ∃ q : Polynomial ℝ, q.natDegree ≤ N ∧ ∀ t, q.eval t = h t a)
    (hint : ∀ t, Integrable (h t) μ) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ N ∧ ∀ t, q.eval t = ∫ a, h t a ∂μ := by
  classical
  set s : Finset ℕ := Finset.range (N + 1) with hs
  set v : ℕ → ℝ := fun i => (i : ℝ) with hv
  have hvs : Set.InjOn v (s : Set ℕ) := fun a _ b _ hab => by simpa [hv] using hab
  have hcard : s.card = N + 1 := by simp [hs]
  have hrep : ∀ a t, h t a = ∑ i ∈ s, h (v i) a * (Lagrange.basis s v i).eval t := by
    intro a t
    obtain ⟨q, hq, hqe⟩ := hpoly a
    have hdeg : q.degree < s.card := by
      rw [hcard]
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hq)
    have := Lagrange.eq_interpolate hvs hdeg
    rw [← hqe t, this, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_mul, Polynomial.eval_C, hqe]
  refine ⟨Lagrange.interpolate s v (fun i => ∫ a, h (v i) a ∂μ), ?_, ?_⟩
  · have := Lagrange.degree_interpolate_lt (fun i => ∫ a, h (v i) a ∂μ) hvs
    rw [hcard] at this
    by_cases h0 : Lagrange.interpolate s v (fun i => ∫ a, h (v i) a ∂μ) = 0
    · rw [h0]; simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr this
      omega
  · intro t
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
    simp_rw [hrep _ t]
    rw [integral_finsetSum _ (fun i _ => (hint (v i)).mul_const _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_mul, Polynomial.eval_C, integral_mul_const]

variable {S : Type*} [MeasurableSpace S]

lemma bdd_integrable {μ : Measure S} [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f) (C : ℝ)
    (hb : ∀ p, |f p| ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by simpa using hb p)

/-- Jensen and the variance split, for bounded measurable `m`, `g` on a probability space. -/
lemma two_fun (μ : Measure S) [IsProbabilityMeasure μ] (m g : S → ℝ) (hm : Measurable m)
    (hg : Measurable g) (Cm Cg : ℝ) (hbm : ∀ p, |m p| ≤ Cm) (hbg : ∀ p, |g p| ≤ Cg) :
    ((∫ p, m p ∂μ) - ∫ p, g p ∂μ) ^ 2 ≤ ∫ p, (m p - g p) ^ 2 ∂μ ∧
    1 / 2 * (∫ p, (g p - ∫ p', g p' ∂μ) ^ 2 ∂μ) - ∫ p, (m p - g p) ^ 2 ∂μ ≤
      ∫ p, (m p - ∫ p', m p' ∂μ) ^ 2 ∂μ := by
  have him := bdd_integrable (μ := μ) hm Cm hbm
  have hig := bdd_integrable (μ := μ) hg Cg hbg
  set B := ∫ p, m p ∂μ with hB
  set D := ∫ p, g p ∂μ with hD
  have hsq : ∀ (f : S → ℝ), Measurable f → ∀ C : ℝ, (∀ p, |f p| ≤ C) →
      Integrable (fun p => f p ^ 2) μ := by
    intro f hf C hC
    refine bdd_integrable (hf.pow_const 2) (C ^ 2) (fun p => ?_)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC p) 2
  have hbe : ∀ p, |m p - g p| ≤ Cm + Cg := fun p =>
    (abs_sub _ _).trans (add_le_add (hbm p) (hbg p))
  have hie : Integrable (fun p => m p - g p) μ := him.sub hig
  have hie2 := hsq (fun p => m p - g p) (hm.sub hg) _ hbe
  have hEe : ∫ p, (m p - g p) ∂μ = B - D := integral_sub him hig
  have hexp : ∫ p, ((m p - g p) - (B - D)) ^ 2 ∂μ = (∫ p, (m p - g p) ^ 2 ∂μ) - (B - D) ^ 2 := by
    have h1 : ∀ p, ((m p - g p) - (B - D)) ^ 2 =
        (m p - g p) ^ 2 - 2 * (B - D) * (m p - g p) + (B - D) ^ 2 := fun p => by ring
    simp_rw [h1]
    have a := integral_add (μ := μ) (f := fun p => (m p - g p) ^ 2 - 2 * (B - D) * (m p - g p))
      (g := fun _ => (B - D) ^ 2) (hie2.sub (hie.const_mul _)) (integrable_const _)
    have b := integral_sub (μ := μ) (f := fun p => (m p - g p) ^ 2)
      (g := fun p => 2 * (B - D) * (m p - g p)) hie2 (hie.const_mul _)
    have c := integral_const_mul (μ := μ) (2 * (B - D)) (fun p => m p - g p)
    simp only [integral_const, probReal_univ, one_smul] at a
    rw [a, b, c, hEe]
    ring
  have hJ : (B - D) ^ 2 ≤ ∫ p, (m p - g p) ^ 2 ∂μ := by
    have h0 : 0 ≤ ∫ p, ((m p - g p) - (B - D)) ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
    rw [hexp] at h0
    linarith
  refine ⟨hJ, ?_⟩
  have hig2 : Integrable (fun p => (g p - D) ^ 2) μ :=
    hsq (fun p => g p - D) (hg.sub_const _) (Cg + |D|) (fun p =>
      (abs_sub _ _).trans (add_le_add (hbg p) le_rfl))
  have him2 : Integrable (fun p => (m p - B) ^ 2) μ :=
    hsq (fun p => m p - B) (hm.sub_const _) (Cm + |B|) (fun p =>
      (abs_sub _ _).trans (add_le_add (hbm p) le_rfl))
  have hic : Integrable (fun p => ((m p - g p) - (B - D)) ^ 2) μ :=
    hsq (fun p => (m p - g p) - (B - D)) ((hm.sub hg).sub_const _) (Cm + Cg + |B - D|)
      (fun p => (abs_sub _ _).trans (add_le_add (hbe p) le_rfl))
  have hpt : ∫ p, (1 / 2 * (g p - D) ^ 2 - ((m p - g p) - (B - D)) ^ 2) ∂μ ≤
      ∫ p, (m p - B) ^ 2 ∂μ := by
    apply integral_mono ((hig2.const_mul _).sub hic) him2
    intro p
    show 1 / 2 * (g p - D) ^ 2 - ((m p - g p) - (B - D)) ^ 2 ≤ (m p - B) ^ 2
    nlinarith [sq_nonneg ((g p - D) + 2 * ((m p - g p) - (B - D)))]
  rw [integral_sub (hig2.const_mul _) hic, integral_const_mul] at hpt
  have hc : ∫ p, ((m p - g p) - (B - D)) ^ 2 ∂μ ≤ ∫ p, (m p - g p) ^ 2 ∂μ := by
    rw [hexp]; nlinarith [sq_nonneg (B - D)]
  linarith

end generic

/-! ## Regularity of the model functions -/

section model

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

lemma Fm_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) (x : Fin n → ℝ) : Fm M P lam (t • W) x = Fm M P (lam * t) W x := by
  unfold Fm
  congr 2
  funext a
  cases a with
  | inl j => rfl
  | inr i =>
    simp only [Sum.elim_inr, zv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring

lemma Fs_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) : Fs M P lam (t • W) = Fs M P (lam * t) W := by
  funext p g; exact Fm_smul M P lam t W _

lemma msl_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) : msl M P lam (t • W) = msl M P (lam * t) W := by
  funext p; unfold msl; rw [Fs_smul]

lemma Bm_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) : Bm M P lam (t • W) = Bm M P (lam * t) W := by
  unfold Bm; rw [msl_smul]

lemma Vdn_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) : Vdn M P lam (t • W) = Vdn M P (lam * t) W := by
  unfold Vdn Ysl; rw [msl_smul, Fs_smul]

lemma Esl_smul (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam t : ℝ)
    (W : J × Fin n → ℝ) : Esl M P lam (t • W) = Esl M P (lam * t) W := by
  unfold Esl; rw [msl_smul]

/-- A continuous function is bounded on the unit ball. -/
lemma ball_bdd (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
    ∃ C : ℝ, ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 ≤ 1 → |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := fun _ : Fin n => (-1 : ℝ))
    (b := fun _ => (1 : ℝ))).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have := hC x ?_
  · simpa using this
  · rw [Set.mem_Icc]
    have hi : ∀ i, x i ^ 2 ≤ 1 := fun i =>
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hx
    constructor <;> intro i <;> nlinarith [hi i]

/-- The substitution that represents `F_x` as a polynomial in `W`. -/
noncomputable def Lx (M : Mod n I J S G) (lam : ℝ) (x : Fin n → ℝ) :
    I ⊕ Fin n → MvPolynomial (J × Fin n) ℝ :=
  Sum.elim (fun j => C (M.b x j)) (fun i => C lam * ∑ q : J, C (M.ps x q) * X (q, i))

lemma Lx_eval (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ)
    (W : J × Fin n → ℝ) (x : Fin n → ℝ) : eval W (aeval (Lx M lam x) P) = Fm M P lam W x := by
  rw [BstLean.Part84.eval_aeval']
  unfold Fm
  congr 2
  funext a
  cases a <;> simp [Lx, zv, mul_comm]

lemma Lx_deg (M : Mod n I J S G) (lam : ℝ) (x : Fin n → ℝ) (a : I ⊕ Fin n) :
    (Lx M lam x a).totalDegree ≤ 1 := by
  cases a with
  | inl j => simp [Lx]
  | inr i =>
    simp only [Lx, Sum.elim_inr]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine BstLean.Part84.totalDegree_finset_sum_le (fun q _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_X _).le

lemma b_cont (M : Mod n I J S G) (j : I) : Continuous fun x => M.b x j :=
  MvPolynomial.continuous_eval _

lemma ps_cont (M : Mod n I J S G) (q : J) : Continuous fun x => M.ps x q :=
  MvPolynomial.continuous_eval _

lemma Lx_cont (M : Mod n I J S G) (lam : ℝ) (a : I ⊕ Fin n) (m : J × Fin n →₀ ℕ) :
    Continuous fun x : Fin n → ℝ => (Lx M lam x a).coeff m := by
  classical
  cases a with
  | inl j =>
    simp only [Lx, Sum.elim_inl, coeff_C]
    split_ifs
    · exact b_cont M j
    · exact continuous_const
  | inr i =>
    simp only [Lx, Sum.elim_inr, coeff_C_mul, coeff_sum]
    exact continuous_const.mul
      (continuous_finsetSum _ (fun q _ => (ps_cont M q).mul continuous_const))

/-- `Φ_lam` is continuous in `x`. -/
lemma Phi_cont (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) :
    Continuous (Phi M P lam) := by
  classical
  set K := P.totalDegree
  have hfin : {m : J × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ K}.Finite := by
    have := Finsupp.finite_of_degree_le (σ := J × Fin n) K
    refine this.subset (fun m hm => ?_)
    simpa [Finsupp.degree_apply, Finsupp.sum] using hm
  have hcc := BstLean.Part84.cont_coeff (Lx M lam) (Lx_cont M lam) P
  have hev : ∀ (W : J × Fin n → ℝ) x, Fm M P lam W x =
      ∑ m ∈ hfin.toFinset, (aeval (Lx M lam x) P).coeff m * eval W (monomial m (1 : ℝ)) := by
    intro W x
    rw [← Lx_eval, eval_eq]
    simp only [eval_monomial, one_mul]
    refine Finset.sum_subset (fun m hm => ?_) (fun m _ hm => ?_)
    · rw [Set.Finite.mem_toFinset]
      exact (le_totalDegree hm).trans (BstLean.Part84.deg_aeval _ (Lx_deg M lam x) P)
    · rw [notMem_support_iff.mp hm, zero_mul]
  have hPhi : Phi M P lam = fun x => ∑ m ∈ hfin.toFinset, (aeval (Lx M lam x) P).coeff m *
      ∫ W, eval W (monomial m (1 : ℝ)) ∂stdGauss (J × Fin n) := by
    funext x
    unfold Phi
    simp_rw [hev]
    rw [integral_finsetSum _ (fun m _ =>
      (BstLean.Part56.Orth.gaussian_eval_integrable (monomial m (1 : ℝ))).const_mul _)]
    exact Finset.sum_congr rfl (fun m _ => integral_const_mul _ _)
  rw [hPhi]
  exact continuous_finsetSum _ (fun m _ => (hcc m).mul continuous_const)

end model

section mhelp
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

lemma mc3 (f : A × (B × C) → ℝ) (hf : Measurable f) :
    Measurable (fun b : (A × B) × C => f (b.1.1, (b.1.2, b.2))) :=
  hf.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma mcL (f : A × B → ℝ) (hf : Measurable f) (a : A) : Measurable (fun b => f (a, b)) :=
  hf.comp (measurable_const.prodMk measurable_id)

lemma mcLL (f : A × (B × C) → ℝ) (hf : Measurable f) (a : A) (b : B) :
    Measurable (fun c => f (a, (b, c))) :=
  hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

lemma mcfst (f : A → ℝ) (hf : Measurable f) : Measurable (fun b : A × B => f b.1) :=
  hf.comp measurable_fst

lemma mcsnd (f : B → ℝ) (hf : Measurable f) : Measurable (fun b : A × B => f b.2) :=
  hf.comp measurable_snd

end mhelp

section reg

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]
variable (M : Mod n I J S G) (d K : ℕ) (P : MvPolynomial (I ⊕ Fin n) ℝ)

lemma Fs_meas (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ) :
    Measurable (fun a : (J × Fin n → ℝ) × (S × G) => Fs M P lam a.1 a.2.1 a.2.2) :=
  (hPF K P hP).2.2.2.2.2.2.2 lam

lemma Fs_meas3 (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ) :
    Measurable (fun b : ((J × Fin n → ℝ) × S) × G => Fs M P lam b.1.1 b.1.2 b.2) := by
  exact mc3 (fun a : (J × Fin n → ℝ) × (S × G) => Fs M P lam a.1 a.2.1 a.2.2)
    (Fs_meas M d K P hPF hP lam)

lemma Fs_bdd (hR : Reg M d) (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ)
    (W : J × Fin n → ℝ) : ∃ C : ℝ, ∀ p g, |Fs M P lam W p g| ≤ C := by
  obtain ⟨Q, -, hQ⟩ := (hPF K P hP).1 lam W
  obtain ⟨C, hC⟩ := ball_bdd (fun x => eval x Q) (MvPolynomial.continuous_eval Q)
  refine ⟨C, fun p g => ?_⟩
  have := hC (M.X (p, g)) (hR.2.2.2.1 (p, g))
  rwa [hQ] at this

lemma msl_meas (hR : Reg M d) (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ) :
    Measurable (fun a : (J × Fin n → ℝ) × S => msl M P lam a.1 a.2) := by
  have := hR.2.1
  exact ((Fs_meas3 M d K P hPF hP lam).stronglyMeasurable.integral_prod_right'
    (ν := M.ga)).measurable

lemma msl_meas' (hR : Reg M d) (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ)
    (W : J × Fin n → ℝ) : Measurable (fun p => msl M P lam W p) := by
  exact mcL (fun a : (J × Fin n → ℝ) × S => msl M P lam a.1 a.2)
    (msl_meas M d K P hR hPF hP lam) W

lemma msl_bdd (hR : Reg M d) {lam : ℝ} {W : J × Fin n → ℝ} {C : ℝ}
    (hC : ∀ p g, |Fs M P lam W p g| ≤ C) (p : S) : |msl M P lam W p| ≤ C := by
  have := hR.2.1
  have := norm_integral_le_of_norm_le_const (μ := M.ga) (f := fun g => Fs M P lam W p g)
    (C := C) (Filter.Eventually.of_forall fun g => by simpa using hC p g)
  simpa [msl] using this

lemma gsl_meas (hR : Reg M d) : Measurable (gsl M P) := by
  have := hR.2.1
  have h : Measurable (fun a : S × G => Phi M P 1 (M.X a)) :=
    (Phi_cont M P 1).measurable.comp hR.2.2.1
  exact (h.stronglyMeasurable.integral_prod_right' (ν := M.ga)).measurable

lemma gsl_bdd (hR : Reg M d) : ∃ C : ℝ, ∀ p, |gsl M P p| ≤ C := by
  have := hR.2.1
  obtain ⟨C, hC⟩ := ball_bdd (Phi M P 1) (Phi_cont M P 1)
  refine ⟨C, fun p => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := M.ga) (f := fun g => Phi M P 1 (M.X (p, g)))
    (C := C) (Filter.Eventually.of_forall fun g => by
      simpa using hC (M.X (p, g)) (hR.2.2.2.1 (p, g)))
  simpa [gsl] using this

lemma Esl_meas (hR : Reg M d) (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ) :
    Measurable (fun W : J × Fin n → ℝ => Esl M P lam W) := by
  have := hR.1
  have h : Measurable (fun a : (J × Fin n → ℝ) × S => (msl M P lam a.1 a.2 - gsl M P a.2) ^ 2) :=
    ((msl_meas M d K P hR hPF hP lam).sub
      (mcsnd (gsl M P) (gsl_meas M d P hR))).pow_const 2
  exact (h.stronglyMeasurable.integral_prod_right' (ν := M.pi)).measurable

lemma Vdn_meas (hR : Reg M d) (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ) :
    Measurable (fun W : J × Fin n → ℝ => Vdn M P lam W) := by
  have := hR.1
  have := hR.2.1
  have h3 : Measurable (fun b : ((J × Fin n → ℝ) × S) × G =>
      (Fs M P lam b.1.1 b.1.2 b.2 - msl M P lam b.1.1 b.1.2) ^ 2) :=
    ((Fs_meas3 M d K P hPF hP lam).sub
      (mcfst (fun a : (J × Fin n → ℝ) × S => msl M P lam a.1 a.2)
        (msl_meas M d K P hR hPF hP lam))).pow_const 2
  have h2 : Measurable (fun a : (J × Fin n → ℝ) × S => Ysl M P lam a.1 a.2) :=
    (h3.stronglyMeasurable.integral_prod_right' (ν := M.ga)).measurable
  exact (h2.stronglyMeasurable.integral_prod_right' (ν := M.pi)).measurable

/-- `Esl` is a polynomial of degree `≤ 2K` in the scale. -/
lemma Esl_poly (hR : Reg M d) (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K)
    (W : J × Fin n → ℝ) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ 2 * K ∧ ∀ lam, q.eval lam = Esl M P lam W := by
  have := hR.1
  obtain ⟨Cg, hCg⟩ := gsl_bdd M d P hR
  refine poly_of_integral M.pi (2 * K) (fun lam p => (msl M P lam W p - gsl M P p) ^ 2) ?_ ?_
  · intro p
    obtain ⟨q, hq, hqe⟩ := (hPF K P hP).2.2.2.1 W p
    refine ⟨(q - Polynomial.C (gsl M P p)) ^ 2, ?_, fun t => by simp [hqe]⟩
    refine (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 ?_)
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hq (by simp))
  · intro lam
    obtain ⟨C, hC⟩ := Fs_bdd M d K P hR hPF hP lam W
    refine bdd_integrable (((msl_meas' M d K P hR hPF hP lam W).sub
      (gsl_meas M d P hR)).pow_const 2) ((C + Cg) ^ 2) (fun p => ?_)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_sub _ _).trans (add_le_add (msl_bdd M d P hR hC p) (hCg p))) 2

/-- The total-variance identity. -/
lemma Vm_decomp (hR : Reg M d) (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ)
    (W : J × Fin n → ℝ) :
    Vm M P lam W = Vdn M P lam W + ∫ p, (msl M P lam W p - Bm M P lam W) ^ 2 ∂M.pi := by
  have := hR.1
  have := hR.2.1
  obtain ⟨C, hC⟩ := Fs_bdd M d K P hR hPF hP lam W
  set B := Bm M P lam W
  have hmb := msl_bdd M d P hR hC
  have hFg : ∀ p, Measurable (fun g => Fs M P lam W p g) := fun p => by
    exact mcLL (fun a : (J × Fin n → ℝ) × (S × G) => Fs M P lam a.1 a.2.1 a.2.2)
      (Fs_meas M d K P hPF hP lam) W p
  have hpt : ∀ p, ∫ g, (Fs M P lam W p g - B) ^ 2 ∂M.ga =
      Ysl M P lam W p + (msl M P lam W p - B) ^ 2 := by
    intro p
    set m := msl M P lam W p
    have hi1 : Integrable (fun g => Fs M P lam W p g - m) M.ga :=
      bdd_integrable ((hFg p).sub_const m) (C + C) (fun g =>
        (abs_sub _ _).trans (add_le_add (hC p g) (hmb p)))
    have hi2 : Integrable (fun g => (Fs M P lam W p g - m) ^ 2) M.ga :=
      bdd_integrable (((hFg p).sub_const m).pow_const 2) ((C + C) ^ 2) (fun g => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (hC p g) (hmb p))) 2)
    have hF : Integrable (fun g => Fs M P lam W p g) M.ga := bdd_integrable (hFg p) C (hC p)
    have h0 : ∫ g, (Fs M P lam W p g - m) ∂M.ga = 0 := by
      rw [integral_sub hF (integrable_const _)]
      simp [m, msl]
    have h1 : ∀ g, (Fs M P lam W p g - B) ^ 2 =
        (Fs M P lam W p g - m) ^ 2 + 2 * (m - B) * (Fs M P lam W p g - m) + (m - B) ^ 2 :=
      fun g => by ring
    simp_rw [h1]
    have a := integral_add (μ := M.ga)
      (f := fun g => (Fs M P lam W p g - m) ^ 2 + 2 * (m - B) * (Fs M P lam W p g - m))
      (g := fun _ => (m - B) ^ 2) (hi2.add (hi1.const_mul _)) (integrable_const _)
    have b := integral_add (μ := M.ga) (f := fun g => (Fs M P lam W p g - m) ^ 2)
      (g := fun g => 2 * (m - B) * (Fs M P lam W p g - m)) hi2 (hi1.const_mul _)
    have c := integral_const_mul (μ := M.ga) (2 * (m - B)) (fun g => Fs M P lam W p g - m)
    simp only [integral_const, probReal_univ, one_smul] at a
    rw [a, b, c, h0]
    simp [Ysl, m]
  have hV : Vm M P lam W = ∫ p, (Ysl M P lam W p + (msl M P lam W p - B) ^ 2) ∂M.pi := by
    show (∫ p, ∫ g, (Fs M P lam W p g - B) ^ 2 ∂M.ga ∂M.pi) = _
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hY : Measurable (fun p => Ysl M P lam W p) := by
    have h4 : Measurable (fun b : S × G => Fs M P lam W b.1 b.2) :=
      mcL (fun a : (J × Fin n → ℝ) × (S × G) => Fs M P lam a.1 a.2.1 a.2.2)
        (Fs_meas M d K P hPF hP lam) W
    have h5 : Measurable (fun b : S × G => msl M P lam W b.1) :=
      mcfst (fun p => msl M P lam W p) (msl_meas' M d K P hR hPF hP lam W)
    have h3 : Measurable (fun b : S × G => (Fs M P lam W b.1 b.2 - msl M P lam W b.1) ^ 2) :=
      (h4.sub h5).pow_const 2
    exact (h3.stronglyMeasurable.integral_prod_right' (ν := M.ga)).measurable
  have hYi : Integrable (fun p => Ysl M P lam W p) M.pi := by
    refine bdd_integrable hY ((C + C) ^ 2) (fun p => ?_)
    have := norm_integral_le_of_norm_le_const (μ := M.ga)
      (f := fun g => (Fs M P lam W p g - msl M P lam W p) ^ 2) (C := (C + C) ^ 2)
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (hC p g) (hmb p))) 2)
    simpa [Ysl] using this
  have hmi : Integrable (fun p => (msl M P lam W p - B) ^ 2) M.pi := by
    refine bdd_integrable (((msl_meas' M d K P hR hPF hP lam W).sub_const B).pow_const 2)
      ((C + |B|) ^ 2) (fun p => ?_)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hmb p) le_rfl)) 2
  rw [hV, integral_add hYi hmi]
  rfl

/-- Jensen and the variance split for the slice means. -/
lemma slice_two (hR : Reg M d) (hPF : PolyFacts M d) (hP : P.totalDegree ≤ K) (lam : ℝ)
    (W : J × Fin n → ℝ) :
    (Bm M P lam W - gD M P) ^ 2 ≤ Esl M P lam W ∧
    1 / 2 * Tm M P - Esl M P lam W ≤ ∫ p, (msl M P lam W p - Bm M P lam W) ^ 2 ∂M.pi := by
  have := hR.1
  obtain ⟨C, hC⟩ := Fs_bdd M d K P hR hPF hP lam W
  obtain ⟨Cg, hCg⟩ := gsl_bdd M d P hR
  exact two_fun M.pi (fun p => msl M P lam W p) (gsl M P) (msl_meas' M d K P hR hPF hP lam W)
    (gsl_meas M d P hR) C Cg (msl_bdd M d P hR hC) hCg

end reg

/-! ## The deterministic step -/

lemma det86 (Lv Vb efl η E Vd V T R X Bv gDv gqv : ℝ) (hLv : 0 ≤ Lv)
    (hVb : (1 - efl) * Lv ≤ Vb) (hefl : efl ≤ 1 / 10) (hE : E ≤ Lv / 25) (hV : Vb / 2 ≤ Vd)
    (hR : R ≤ 2 * Lv) (hR0 : 0 ≤ R) (hT : 0 ≤ T) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 40)
    (hs : (gqv - gDv) ^ 2 ≤ η ^ 2 * (R + T)) (hVm : V = Vd + X) (hX : 1 / 2 * T - E ≤ X)
    (hJ : (Bv - gDv) ^ 2 ≤ E) : (Bv - gqv) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 * V := by
  have hη2 : η ^ 2 ≤ 1 / 1600 := by nlinarith
  have h1 : (gqv - gDv) ^ 2 ≤ (R + T) / 1600 := by
    refine hs.trans ?_
    have : 0 ≤ R + T := by linarith
    nlinarith
  have h2 : (Bv - gqv) ^ 2 ≤ 2 * (Bv - gDv) ^ 2 + 2 * (gqv - gDv) ^ 2 := by
    nlinarith [sq_nonneg ((Bv - gDv) + (gqv - gDv))]
  have h3 : 9 / 10 * Lv ≤ Vb := by nlinarith
  linarith

/-! ## The sphere step -/

section main

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

theorem remez86 (M : Mod n I J S G) (d k : ℕ) (c1 cV efl η : ℝ)
    (gq : MvPolynomial (I ⊕ Fin n) ℝ → ℝ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hR : Reg M d) (hPF : PolyFacts M d) (hG : GaussModel86 M k c1 cV efl)
    (hSu : SurrHyp M η gq) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 40) (hefl : efl ≤ 1 / 10)
    (hc1 : 0 ≤ c1) (hcV : 0 ≤ cV) (hcard : 1000 ≤ Fintype.card (J × Fin n)) :
    RemezStep86 M k gq (remezBound n k c1 cV) := by
  classical
  intro P hP lam hlam
  obtain ⟨Lv, Vb, hLv, hVb, hi1, hi2, hb1, hb2, hR1⟩ := hG P hP lam hlam
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDpos : (0 : ℝ) < DWr n J := by
    unfold DWr; exact_mod_cast (show 0 < Fintype.card (J × Fin n) by omega)
  set sD : ℝ := Real.sqrt (DWr n J) with hsDdef
  have hsD : sD ≠ 0 := (Real.sqrt_pos.mpr hDpos).ne'
  have hsDc : Real.sqrt (Fintype.card (J × Fin n) : ℝ) = sD := rfl
  set Rc1 : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2 with hRc1
  set Rc2 : ℝ := 5 / 2 * (2 * (k : ℝ) + 1) ^ 2 with hRc2
  have hRc10 : 0 ≤ Rc1 := by positivity
  have hRc20 : 0 ≤ Rc2 := by positivity
  set G1 : (J × Fin n → ℝ) → ℝ := fun W => Esl M P lam W with hG1
  set G2 : (J × Fin n → ℝ) → ℝ := fun W => (Vdn M P lam W - Vb) ^ 2 with hG2
  have hG1m : Measurable G1 := Esl_meas M d k P hR hPF hP lam
  have hG2m : Measurable G2 := ((Vdn_meas M d k P hR hPF hP lam).sub_const _).pow_const 2
  have hG10 : ∀ W, 0 ≤ G1 W := fun W => integral_nonneg fun p => sq_nonneg _
  have hsm : Measurable (fun W : J × Fin n → ℝ => sD • unitF53 W) :=
    (BstLean.Part53.measurable_unitF (ι := J × Fin n)).const_smul sD
  have hlin : (Polynomial.C lam * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  -- Remez, error
  have hrem1 : ∀ ω : J × Fin n → ℝ, G1 (sD • ω) ≤
      Rc1 * ∫ W', G1 (radF53 W' • ω) ∂stdGauss (J × Fin n) := by
    intro ω
    obtain ⟨qE, hEd, hEe⟩ := Esl_poly M d k P hR hPF hP (sD • ω)
    set Q : Polynomial ℝ := qE.comp (Polynomial.C lam * Polynomial.X) with hQ
    have hQe : ∀ t : ℝ, Q.eval t = G1 (t • sD • ω) := by
      intro t
      simp only [hQ, hG1, Esl_smul M P lam t, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, hEe]
    have hQd : Q.natDegree ≤ 2 * k := by
      refine (Polynomial.natDegree_comp_le).trans ?_
      calc qE.natDegree * _ ≤ 2 * k * 1 := Nat.mul_le_mul hEd hlin
        _ = 2 * k := mul_one _
    have h := BstLean.Part59.lemmaRp59 k (J × Fin n) hcard Q hQd
      (fun x => by rw [hQe]; exact hG10 _)
    rw [hQe 1, one_smul, hsDc] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    apply integral_congr_ae
    filter_upwards with W'
    rw [hQe, smul_smul]
    show G1 ((radF53 W' / sD * sD) • ω) = _
    rw [div_mul_cancel₀ _ hsD]
  -- Remez, variance
  have hrem2 : ∀ ω : J × Fin n → ℝ, G2 (sD • ω) ≤
      Rc2 * ∫ W', G2 (radF53 W' • ω) ∂stdGauss (J × Fin n) := by
    intro ω
    obtain ⟨qV, hVd, hVe⟩ := (hPF k P hP).2.2.2.2.2.1 (sD • ω)
    set Q : Polynomial ℝ :=
      (qV.comp (Polynomial.C lam * Polynomial.X) - Polynomial.C Vb) ^ 2 with hQ
    have hQe : ∀ t : ℝ, Q.eval t = G2 (t • sD • ω) := by
      intro t
      simp only [hQ, hG2, Vdn_smul M P lam t, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hVe]
    have hQd : Q.natDegree ≤ 2 * (2 * k) := by
      refine (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 ?_)
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      refine (Polynomial.natDegree_comp_le).trans ?_
      calc qV.natDegree * _ ≤ 2 * k * 1 := Nat.mul_le_mul hVd hlin
        _ = 2 * k := mul_one _
    have h := BstLean.Part59.lemmaRp59 (2 * k) (J × Fin n) hcard Q hQd
      (fun x => by rw [hQe]; exact sq_nonneg _)
    rw [hQe 1, one_smul, hsDc] at h
    have hc : (5 : ℝ) / 2 * (((2 * k : ℕ) : ℝ) + 1) ^ 2 = Rc2 := by rw [hRc2]; push_cast; ring
    rw [hc] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    apply integral_congr_ae
    filter_upwards with W'
    rw [hQe, smul_smul]
    show G2 ((radF53 W' / sD * sD) • ω) = _
    rw [div_mul_cancel₀ _ hsD]
  have hT1 := polar_transfer G1 hG1m hG10 hi1 Rc1 _ hRc10 hrem1
  have hT2 := polar_transfer G2 hG2m (fun W => sq_nonneg _) hi2 Rc2 _ hRc20 hrem2
  have hm1 : Measurable (fun W : J × Fin n → ℝ => ENNReal.ofReal (G1 (sD • unitF53 W))) :=
    ENNReal.measurable_ofReal.comp (hG1m.comp hsm)
  have hm2 : Measurable (fun W : J × Fin n → ℝ => ENNReal.ofReal (G2 (sD • unitF53 W))) :=
    ENNReal.measurable_ofReal.comp (hG2m.comp hsm)
  -- the deterministic step at a point
  have hdet : ∀ W : J × Fin n → ℝ, G1 W ≤ Lv / 25 → Vb / 2 ≤ Vdn M P lam W →
      (Bm M P lam W - gq P) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 * Vm M P lam W := by
    intro W hE hV
    obtain ⟨hJ, hX⟩ := slice_two M d k P hR hPF hP lam W
    exact det86 Lv Vb efl η (Esl M P lam W) (Vdn M P lam W) (Vm M P lam W) (Tm M P) (R1 M P)
      _ (Bm M P lam W) (gD M P) (gq P) hLv hVb hefl hE hV hR1
      (integral_nonneg fun p => integral_nonneg fun g => sq_nonneg _)
      (integral_nonneg fun p => sq_nonneg _) hη0 hη (hSu P)
      (Vm_decomp M d k P hR hPF hP lam W) hX hJ
  have hbad : ∀ W, W ∈ badSet86 M gq P lam →
      ¬ (G1 (sD • unitF53 W) ≤ Lv / 25 ∧ Vb / 2 ≤ Vdn M P lam (sD • unitF53 W)) := by
    intro W hW h
    have := hdet _ h.1 h.2
    simp only [badSet86, Set.mem_ofPred_eq] at hW
    exact absurd hW (not_lt.mpr this)
  have ht1 : 0 ≤ Rc1 * 25 * c1 / n := by positivity
  have ht2 : 0 ≤ Rc2 * 5 * cV / n := by positivity
  rcases hLv.eq_or_lt with hL0 | hLpos
  · -- `Lv = 0`
    have hVb0 : 0 ≤ Vb := by rw [← hL0, mul_zero] at hVb; exact hVb
    have hz1 : ∫⁻ W, ENNReal.ofReal (G1 (sD • unitF53 W)) ∂stdGauss (J × Fin n) = 0 := by
      apply le_antisymm _ bot_le
      have : ∫ W, G1 W ∂stdGauss (J × Fin n) ≤ 0 := by
        refine hb1.trans (le_of_eq ?_); rw [← hL0, mul_zero]
      exact hT1.trans (le_of_eq (ENNReal.ofReal_eq_zero.mpr
        (mul_nonpos_of_nonneg_of_nonpos hRc10 this)))
    have hz2 : ∫⁻ W, ENNReal.ofReal (G2 (sD • unitF53 W)) ∂stdGauss (J × Fin n) = 0 := by
      apply le_antisymm _ bot_le
      have : ∫ W, G2 W ∂stdGauss (J × Fin n) ≤ 0 := by
        refine hb2.trans (le_of_eq ?_); rw [← hL0]; simp
      exact hT2.trans (le_of_eq (ENNReal.ofReal_eq_zero.mpr
        (mul_nonpos_of_nonneg_of_nonpos hRc20 this)))
    have hae1 := (lintegral_eq_zero_iff hm1).mp hz1
    have hae2 := (lintegral_eq_zero_iff hm2).mp hz2
    have hnull : stdGauss (J × Fin n) (badSet86 M gq P lam) = 0 := by
      have hae : ∀ᵐ W ∂stdGauss (J × Fin n), W ∉ badSet86 M gq P lam := by
        filter_upwards [hae1, hae2] with W h1 h2 hW
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h1 h2
        refine hbad W hW ⟨?_, ?_⟩
        · rw [← hL0]; simpa using h1
        · have h3 : (Vdn M P lam (sD • unitF53 W) - Vb) ^ 2 = 0 :=
            le_antisymm h2 (sq_nonneg _)
          have h4 : Vdn M P lam (sD • unitF53 W) = Vb := by
            have := pow_eq_zero_iff (two_ne_zero) |>.mp h3
            linarith
          rw [h4]; linarith
      simpa [ae_iff] using hae
    rw [hnull]; exact bot_le
  · -- `Lv > 0`
    have hVbL : 9 / 10 * Lv ≤ Vb := by nlinarith
    have hVbpos : 0 < Vb := by linarith
    have hθ1 : 0 < Lv / 25 := by positivity
    have hθ2 : 0 < Vb ^ 2 / 4 := by positivity
    have hsub : badSet86 M gq P lam ⊆
        {W | ENNReal.ofReal (Lv / 25) ≤ ENNReal.ofReal (G1 (sD • unitF53 W))} ∪
        {W | ENNReal.ofReal (Vb ^ 2 / 4) ≤ ENNReal.ofReal (G2 (sD • unitF53 W))} := by
      intro W hW
      have hb := hbad W hW
      by_cases hE : G1 (sD • unitF53 W) ≤ Lv / 25
      · right
        have hV : ¬ Vb / 2 ≤ Vdn M P lam (sD • unitF53 W) := fun h => hb ⟨hE, h⟩
        push Not at hV
        apply ENNReal.ofReal_le_ofReal
        simp only [hG2]
        nlinarith
      · left
        push Not at hE
        exact ENNReal.ofReal_le_ofReal hE.le
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have hM1 := (meas_ge_le_lintegral_div hm1.aemeasurable (ε := ENNReal.ofReal (Lv / 25))
      (ENNReal.ofReal_pos.mpr hθ1).ne' ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hT1 _)
    have hM2 := (meas_ge_le_lintegral_div hm2.aemeasurable (ε := ENNReal.ofReal (Vb ^ 2 / 4))
      (ENNReal.ofReal_pos.mpr hθ2).ne' ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hT2 _)
    rw [← ENNReal.ofReal_div_of_pos hθ1] at hM1
    rw [← ENNReal.ofReal_div_of_pos hθ2] at hM2
    rw [show remezBound n k c1 cV = Rc1 * 25 * c1 / n + Rc2 * 5 * cV / n from rfl,
      ENNReal.ofReal_add ht1 ht2]
    refine add_le_add (hM1.trans (ENNReal.ofReal_le_ofReal ?_))
      (hM2.trans (ENNReal.ofReal_le_ofReal ?_))
    · rw [div_le_div_iff₀ hθ1 hnR]
      have := mul_le_mul_of_nonneg_left hb1 hRc10
      calc Rc1 * (∫ W, G1 W ∂stdGauss (J × Fin n)) * n
          ≤ Rc1 * (c1 / n * Lv) * n := mul_le_mul_of_nonneg_right this hnR.le
        _ = Rc1 * 25 * c1 * (Lv / 25) := by field_simp
    · rw [div_le_div_iff₀ hθ2 hnR]
      have := mul_le_mul_of_nonneg_left hb2 hRc20
      have hLV : Lv ^ 2 ≤ 100 / 81 * Vb ^ 2 := by nlinarith
      calc Rc2 * (∫ W, G2 W ∂stdGauss (J × Fin n)) * n
          ≤ Rc2 * (cV / n * Lv ^ 2) * n := mul_le_mul_of_nonneg_right this hnR.le
        _ = Rc2 * cV * Lv ^ 2 := by field_simp
        _ ≤ Rc2 * cV * (100 / 81 * Vb ^ 2) :=
            mul_le_mul_of_nonneg_left hLV (mul_nonneg hRc20 hcV)
        _ ≤ Rc2 * 5 * cV * (Vb ^ 2 / 4) := by
            have : 0 ≤ Rc2 * cV * Vb ^ 2 := by positivity
            nlinarith

end main

end BstLean.Part86.XRemez

#print axioms BstLean.Part86.XRemez.remez86
