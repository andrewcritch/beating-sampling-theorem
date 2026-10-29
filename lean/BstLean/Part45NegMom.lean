import BstLean.Part45NegMom_Scalar

/-!
# Part 45, wave 1: the negative moment (2) of a PSD Gaussian quadratic form

Specification: `delegations/answers/p45-spec-opus.md`. Replace each `sorry` by a proof. Do not edit the
statements. Do not use `native_decide` or `axiom` anywhere. The scalar helper imports the frozen
definitions and Mathlib. No other Part 45 wave-1 file is imported.

Suggested route.
* omSHARP2 §3. Diagonalize `A = Uᵀ Λ U` (`Matrix.IsHermitian.spectral_theorem`); `stdGauss` is invariant
  under the orthogonal map `U`, so `Q = Σ λ_i g_i²`, `Σ λ_i = tr A`. Normalize `tr A = 1`.
* `E e^{−sQ} = Π_i (1 + 2sλ_i)^{−1/2} ≤ (1 + 2s)^{−1/2}` (`Π(1+a_i) ≥ 1 + Σ a_i`). Write
  `x^{−r} = Γ(r)^{−1} ∫₀^∞ s^{r−1} e^{−sx} ds` (`Real.Gamma` integral, substitution) and use Tonelli in
  `ℝ≥0∞`; the right side becomes `E (g²)^{−r} = m_r` (a one-dimensional Gaussian integral, finite for
  `r < 1/2`).
* The `ℝ≥0∞` form is chosen so that `Q = 0` (a null set) gives `⊤` and no integrability side condition
  is needed.

The proof below uses finite Jensen's inequality in place of the Laplace transform. For
`t = tr A` and `w_i = λ_i / t`, convexity gives
`Q⁻ʳ ≤ t⁻ʳ Σ_i w_i (g_i²)⁻ʳ` almost everywhere. Each scalar moment is `mr r`.
-/

namespace BstLean.Part45

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι)
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part41 (Mono phiSq frob Tens TSymm varU Pcal Nn Kc thetaT etaR etaK GamP Lk Bfix Pn)
open BstLean.Part40 (SphLaw SignSym)
open BstLean.Part43 (Params43 bq tau43 xi43 nu43 FradeliziGauss)

variable {n d : ℕ}

private lemma gaussian_basis_preserving {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (b : OrthonormalBasis κ ℝ (EuclideanSpace ℝ ι)) :
    MeasurePreserving (fun z : ι → ℝ => WithLp.ofLp (b.repr (WithLp.toLp 2 z)))
      (stdGauss ι) (stdGauss κ) := by
  have hι : MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ))
      (stdGauss ι) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨(MeasurableEquiv.toLp 2 (ι → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hb : MeasurePreserving b.repr (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨b.repr.continuous.measurable, stdGaussian_map b.repr⟩
  have hκ : MeasurePreserving (MeasurableEquiv.toLp 2 (κ → ℝ))
      (stdGauss κ) (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨(MeasurableEquiv.toLp 2 (κ → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  exact hκ.symm.comp (hb.comp hι)

private lemma qform_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (z : ι → ℝ) :
    qformι A z = inner ℝ (WithLp.toLp 2 z) (A.toEuclideanLin (WithLp.toLp 2 z)) := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct, Matrix.mulVec,
    qformι, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma qform_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (z : ι → ℝ) :
    qformι A z = ∑ i, hA.eigenvalues i *
      (hA.eigenvectorBasis.repr (WithLp.toLp 2 z) i) ^ 2 := by
  let b := hA.eigenvectorBasis
  have heig (i : ι) : A.toEuclideanLin (b i) = hA.eigenvalues i • b i := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis i
  have haction (v : EuclideanSpace ℝ ι) :
      A.toEuclideanLin v = ∑ i, (b.repr v i * hA.eigenvalues i) • b i := by
    nth_rw 1 [← b.sum_repr v]
    simp only [map_sum, map_smul, heig, smul_smul]
  rw [qform_inner, haction, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right, real_inner_comm, ← b.repr_apply_apply]
  dsimp [b]
  ring

private lemma diagonal_negmom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) (ht : 0 < ∑ i, lam i)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) :
    ∫⁻ z : ι → ℝ, ENNReal.ofReal (∑ i, lam i * z i ^ 2) ^ (-r) ∂stdGauss ι ≤
      ENNReal.ofReal (mr r * (∑ i, lam i) ^ (-r)) := by
  classical
  let t := ∑ i, lam i
  let w : ι → ℝ := fun i => lam i / t
  have hw (i : ι) : 0 ≤ w i := div_nonneg (hlam i) ht.le
  have hws : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div, t, div_self ht.ne']
  have hn : ∀ᵐ z : ι → ℝ ∂stdGauss ι, ∀ i, z i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    haveI := ProbabilityTheory.nullSingletonClass_gaussianReal
      (μ := (0 : ℝ)) (by norm_num : (1 : NNReal) ≠ 0)
    exact (measurePreserving_eval (fun _ : ι => ProbabilityTheory.gaussianReal 0 1) i).quasiMeasurePreserving.ae
      (by simpa using (measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℝ))))
  have hm (i : ι) : Measurable (fun z : ι → ℝ => ENNReal.ofReal (z i ^ 2) ^ (-r)) := by
    fun_prop
  have hp : ∀ᵐ z : ι → ℝ ∂stdGauss ι,
      ENNReal.ofReal (∑ i, lam i * z i ^ 2) ^ (-r) ≤
        ENNReal.ofReal (t ^ (-r)) * ∑ i,
          ENNReal.ofReal (w i) * ENNReal.ofReal (z i ^ 2) ^ (-r) := by
    filter_upwards [hn] with z hz
    have hzpos (i : ι) : 0 < z i ^ 2 := sq_pos_of_ne_zero (hz i)
    have hspos : 0 < ∑ i, w i * z i ^ 2 := by
      have hex : ∃ i ∈ Finset.univ, 0 < w i :=
        (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).1 (by rw [hws]; norm_num)
      rcases hex with ⟨i, hi, hwi⟩
      exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (hzpos j).le)
        ⟨i, hi, mul_pos hwi (hzpos i)⟩
    have heq : (∑ i, lam i * z i ^ 2) = t * ∑ i, w i * z i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [w]
      field_simp [show t ≠ 0 from ht.ne']
    have hj := (convexOn_neg_rpow r hr0).map_sum_le
      (t := Finset.univ) (w := w) (p := fun i => z i ^ 2)
      (fun i _ => hw i) hws (fun i _ => hzpos i)
    simp only [smul_eq_mul] at hj
    rw [ENNReal.ofReal_rpow_of_pos (heq.symm ▸ mul_pos ht hspos), heq,
      Real.mul_rpow ht.le hspos.le, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    apply mul_le_mul' le_rfl
    calc
      ENNReal.ofReal ((∑ i, w i * z i ^ 2) ^ (-r)) ≤
          ENNReal.ofReal (∑ i, w i * (z i ^ 2) ^ (-r)) := ENNReal.ofReal_le_ofReal hj
      _ = _ := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (hzpos i).le _))]
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.ofReal_mul (hw i), ENNReal.ofReal_rpow_of_pos (hzpos i)]
  calc
    _ ≤ ∫⁻ z : ι → ℝ, ENNReal.ofReal (t ^ (-r)) * ∑ i,
        ENNReal.ofReal (w i) * ENNReal.ofReal (z i ^ 2) ^ (-r) ∂stdGauss ι := lintegral_mono_ae hp
    _ = ENNReal.ofReal (t ^ (-r)) * ∑ i,
        ENNReal.ofReal (w i) * ENNReal.ofReal (mr r) := by
      rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_const_mul _ (hm i)]
        have he := (measurePreserving_eval (fun _ : ι => ProbabilityTheory.gaussianReal 0 1) i).lintegral_comp
          (show Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2) ^ (-r)) by fun_prop)
        have he' : (∫⁻ z : ι → ℝ, ENNReal.ofReal (z i ^ 2) ^ (-r) ∂stdGauss ι) =
            ENNReal.ofReal (mr r) := by
          exact he.trans (scalar_negmom r hr0 hr1)
        rw [he']
      · intro i _
        exact (hm i).const_mul _
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hws]
      simp only [ENNReal.ofReal_one, one_mul]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), mul_comm]

/-- **Negative moment (2)** (omSHARP2 §3): `E Q^{−r} ≤ m_r (E Q)^{−r}` for `Q = zᵀAz`, `A ⪰ 0`,
`E Q = tr A > 0`, `0 < r < 1/2`. -/
theorem negmom_qform {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (htr : 0 < A.trace) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) :
    ∫⁻ z, ENNReal.ofReal (qformι A z) ^ (-r) ∂stdGauss ι ≤ ENNReal.ofReal (mr r * A.trace ^ (-r)) := by
  have hb := gaussian_basis_preserving hA.isHermitian.eigenvectorBasis
  have he := hb.lintegral_comp
    (show Measurable (fun z : ι → ℝ =>
      ENNReal.ofReal (∑ i, hA.isHermitian.eigenvalues i * z i ^ 2) ^ (-r)) by fun_prop)
  simp_rw [qform_eigenbasis A hA.isHermitian]
  rw [he]
  rw [hA.isHermitian.trace_eq_sum_eigenvalues]
  exact
    diagonal_negmom hA.isHermitian.eigenvalues hA.eigenvalues_nonneg
      (hA.isHermitian.trace_eq_sum_eigenvalues ▸ htr) r hr0 hr1

end BstLean.Part45
