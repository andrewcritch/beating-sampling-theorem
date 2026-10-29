import BstLean.Part56Defs
import BstLean.Part53Error_Integrability

/-! Polynomial representations for the heat predictor and its squared error. -/
namespace BstLean.Part56

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono Tens phiM contr)
open BstLean.Part43 (BofQ)
open BstLean.Part53 (heatA TF fvA sg linZ)

variable {n d : ℕ}

-- Resolve finished private lemmas; the kernel checks their applications.
elab "rkg56BPolynomial" : term => do
  let name := ("_private.BstLean.Part53Error_Integrability.0.BstLean.Part53.B_polynomial".splitOn ".").foldl
    (fun n s => if let some i := s.toNat? then Lean.Name.num n i else Lean.Name.str n s)
    Lean.Name.anonymous
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

elab "rkg56GaussianPolynomial" : term => do
  let name := ("_private.BstLean.Part53Error_Integrability.0.BstLean.Part53.gaussian_eval_integrable".splitOn ".").foldl
    (fun n s => if let some i := s.toNat? then Lean.Name.num n i else Lean.Name.str n s)
    Lean.Name.anonymous
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

elab "rkg56SphereContinuous" : term => do
  let name := ("_private.BstLean.Part53Error_Integrability.0.BstLean.Part53.sphere_cont_integrable".splitOn ".").foldl
    (fun n s => if let some i := s.toNat? then Lean.Name.num n i else Lean.Name.str n s)
    Lean.Name.anonymous
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

private lemma continuous_phi (p : Mono n d) : Continuous (fun x : Fin n → ℝ => phiM x p) := by
  exact continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)

private lemma continuous_phiB (j : ℕ) (p : Mono n d) :
    Continuous (fun x : Fin n → ℝ => phiB d j x p) := by
  classical
  unfold phiB
  split_ifs <;> first | exact continuous_phi p | exact continuous_const

private lemma continuous_betaJ (j : ℕ) (v : Fin n → ℝ) :
    Continuous (betaJ d j v) := by
  unfold betaJ kJ
  exact (continuous_finsetSum _ (fun p _ => (continuous_phiB j p).mul_const _)).div_const _

private lemma continuous_tauR (v : Fin n → ℝ) : Continuous (tauR d v) := by
  unfold tauR KR kJ
  apply continuous_finsetSum
  intro j hj
  exact (continuous_finsetSum _ (fun p _ => (continuous_phiB j p).mul
    (continuous_phiB j p))).sub
      (((continuous_finsetSum _ (fun p _ => (continuous_phiB j p).mul_const _)).mul
        (continuous_finsetSum _ (fun p _ => (continuous_phiB j p).mul_const _))).div_const _)

private lemma continuous_heat (k c : ℕ) (A : Tens n) (w : Fin c → Fin n) :
    Continuous (fun t : ℝ => heatA k t A c w) := by
  unfold heatA
  apply continuous_finsetSum
  intro i hi
  exact (((((continuous_id.div_const 2).pow i).div_const (i.factorial : ℝ)).mul_const
    (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ))).mul_const _)

private abbrev JointPoly (n d : ℕ) := MvPolynomial (CoefIdxD n d) C((Fin n → ℝ), ℝ)

private noncomputable def jointEval (p : JointPoly n d)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z p

private noncomputable def muxPoly (s : ℝ) (v : Fin n → ℝ) (a : Fin n) : JointPoly n d :=
  ∑ j ∈ Finset.range (d + 1), ∑ p : Mono n d,
    MvPolynomial.C ⟨fun x => betaJ d j v x * (s * phiB d j v p),
      (continuous_betaJ j v).mul_const _⟩ * MvPolynomial.X ⟨p.1, (p.2, a)⟩

private lemma muxPoly_eval (s : ℝ) (v : Fin n → ℝ) (a : Fin n)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (muxPoly s v a) Z x = mux (s • Z) v x a := by
  classical
  simp only [muxPoly, jointEval, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', RingHom.comp_apply, Pi.evalRingHom_apply,
    ContinuousMap.coeFnRingHom_apply, ContinuousMap.coe_mk, mux, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, ancRK, linZ, BstLean.Part41.colM, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  ring

private noncomputable def heatPoly (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ)
    (v : Fin n → ℝ) : JointPoly n d :=
  ∑ c ∈ Finset.range (k + 1), ∑ w : Fin c → Fin n,
    MvPolynomial.C ⟨fun x => heatA k (sg n d ^ 2 * tauR d v x) (TF k f0 T) c w,
      (continuous_heat k c (TF k f0 T) w).comp
        (continuous_const.mul (continuous_tauR v))⟩ * ∏ t, muxPoly s v (w t)

private lemma heatPoly_eval (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ)
    (v : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (heatPoly k f0 T s v) Z x =
      fvA k (heatA k (sg n d ^ 2 * tauR d v x) (TF k f0 T)) (mux (s • Z) v x) := by
  classical
  simp only [heatPoly, jointEval, map_sum, map_mul, map_prod, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply, ContinuousMap.coe_mk,
    fvA, contr]
  have hlin (a : Fin n) :
      MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z
        (muxPoly s v a) = mux (s • Z) v x a := muxPoly_eval s v a Z x
  simp only [hlin]

private lemma joint_integral_polynomial {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (p : JointPoly n d) : ∃ q : MvPolynomial (CoefIdxD n d) ℝ,
      ∀ Z, (∫ x, jointEval p Z x ∂μ) = MvPolynomial.eval Z q := by
  classical
  refine ⟨∑ e ∈ p.support, MvPolynomial.monomial e (∫ x, p.coeff e x ∂μ), ?_⟩
  intro Z
  have hE (x) : jointEval p Z x =
      ∑ e ∈ p.support, p.coeff e x * e.prod (fun i a => Z i ^ a) := by
    conv_lhs => unfold jointEval; rw [p.as_sum]
    simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
      Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
  simp_rw [hE]
  have hc (e) : Integrable (fun x => p.coeff e x) μ :=
    rkg56SphereContinuous hμ (p.coeff e).continuous
  rw [integral_finsetSum _ (fun e _ => (hc e).mul_const _)]
  simp only [integral_mul_const, map_sum, MvPolynomial.eval_monomial]

/-- The heat predictor is a polynomial in the coefficient array. -/
theorem rkg56_heat_polynomial {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) (v : Fin n → ℝ) :
    ∃ p : MvPolynomial (CoefIdxD n d) ℝ,
      ∀ Z, gLineH μ k f0 T v (s • Z) = MvPolynomial.eval Z p := by
  obtain ⟨p, hp⟩ := joint_integral_polynomial hμ (heatPoly (d := d) k f0 T s v)
  refine ⟨p, ?_⟩
  intro Z
  rw [gLineH, ← hp]
  exact integral_congr_ae (ae_of_all μ fun x => (heatPoly_eval k f0 T s v Z x).symm)

/-- The squared error is integrable, without the Gaussian split or maximal correlation. -/
theorem rkg56_error_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (s : ℝ) (v : Fin n → ℝ) :
    Integrable (fun Z : CoefIdxD n d → ℝ =>
      (BofQ μ k f0 T (s • Z) - gLineH μ k f0 T v (s • Z)) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
  obtain ⟨p, hp⟩ : ∃ p : MvPolynomial (CoefIdxD n d) ℝ,
      ∀ Z, BofQ μ k f0 T (s • Z) = MvPolynomial.eval Z p :=
    rkg56BPolynomial hμ k f0 T s
  obtain ⟨q, hq⟩ := rkg56_heat_polynomial (d := d) hμ k f0 T s v
  have h : Integrable (fun Z => MvPolynomial.eval Z ((p - q) ^ 2))
      (stdGauss (CoefIdxD n d)) := rkg56GaussianPolynomial ((p - q) ^ 2)
  simpa only [map_pow, map_sub, ← hp, ← hq] using h

/-- The error bound holds identically for constant output polynomials. -/
theorem rkg56_degree_zero (d : ℕ) : PropRKGErr56 d 0 := by
  classical
  intro n μ hμ v hv f0 T hT
  let := hμ.prob
  have hheat (a : ℝ) (y : Fin n → ℝ) :
      fvA 0 (heatA 0 a (TF 0 f0 T)) y = f0 := by
    have hh : heatA 0 a (TF 0 f0 T) 0 = TF 0 f0 T 0 := by
      funext w
      simp only [heatA, Finset.range_one, Finset.filter_singleton, Nat.zero_add,
        Nat.mul_zero, le_refl, ite_true, Finset.sum_singleton, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, mul_one, one_mul,
        BstLean.Part41.trL, Fintype.sum_unique]
      congr 1
    simp [fvA, hh, TF, contr]
  have hB (M : CoefIdxD n d → ℝ) : BofQ μ 0 f0 T M = f0 := by
    simp [BofQ, BstLean.Part41.fval]
  have hg (M : CoefIdxD n d → ℝ) : gLineH μ 0 f0 T v M = f0 := by
    simp only [gLineH, hheat]
    simp
  have hS (M : CoefIdxD n d → ℝ) : Sfl μ d 0 f0 T v M = 0 := by
    simp [Sfl, cvarG, BstLean.Part41.fval]
  simp only [hB, hg, sub_self, zero_pow (by decide : 2 ≠ 0), hS,
    integral_zero, mul_zero, le_refl]
  exact ⟨by simp, trivial⟩

end BstLean.Part56
