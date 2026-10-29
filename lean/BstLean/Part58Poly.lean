import BstLean.Part58Defs

/-!
# Part 58, wave 1: polynomiality of `B_μ` in the coefficients

Specification: `delegations/answers/p58-spec-opus.md` §4.
Status: PROVED (`propPoly58`, no `sorry`; proved by the specification author). Do not edit the statements.
Do not use `native_decide` or `axiom` anywhere. This file imports `Part58Defs` only (a prover may also import finished Part 29–56 files,
but no other Part 58 wave-1 file).

Suggested route. `B_μ(M) = f₀ + Σ_{j ≤ k} ∫ contr (T j) (mapMD M x) dμ`; `mapMD M x` is linear in `M`,
so each term is a polynomial of degree `j` in `M` whose coefficients are `μ`-integrals of monomials
in `x` (bounded on the sphere, hence integrable). Build `P` as a finite sum of `MvPolynomial.monomial`
terms and use linearity of the integral.
-/

namespace BstLean.Part58

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM phiSq contr trL frob Tens TSymm fval varU)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (sg)
open BstLean.Part56 (UnitV lawRK kJ EV56)

/-- A continuous function is integrable under a law on the sphere. -/
lemma sphere_integrable58 {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f μ := by
  let := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hμ.sphere] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private abbrev JointPoly58 (n d : ℕ) :=
  MvPolynomial (CoefIdxD n d) C((Fin n → ℝ), ℝ)

private noncomputable def jointEval58 (P : JointPoly58 n d)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z P

private lemma joint_integral58 {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (P : JointPoly58 n d) :
    ∃ Q : MvPolynomial (CoefIdxD n d) ℝ,
      (∀ Z, (∫ x, jointEval58 P Z x ∂μ) = MvPolynomial.eval Z Q) ∧
      Q.totalDegree ≤ P.totalDegree := by
  classical
  refine ⟨∑ e ∈ P.support, MvPolynomial.monomial e (∫ x, P.coeff e x ∂μ), ?_, ?_⟩
  · intro Z
    have hE (x) : jointEval58 P Z x =
        ∑ e ∈ P.support, P.coeff e x * e.prod (fun i a => Z i ^ a) := by
      conv_lhs => unfold jointEval58; rw [P.as_sum]
      simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
        Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply]
    simp_rw [hE]
    rw [integral_finsetSum _ (fun e _ =>
      (sphere_integrable58 hμ (P.coeff e).continuous).mul_const _)]
    simp only [integral_mul_const, map_sum, MvPolynomial.eval_monomial]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro e he
    exact (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree he)

private lemma continuous_mono58 (s : Multiset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x s) :=
  continuous_multiset_prod s (fun i _ => continuous_apply i)

private noncomputable def mapJoint58 (s : ℝ) (a : Fin n) : JointPoly58 n d :=
  ∑ i ∈ Finset.range (d + 1), ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then MvPolynomial.X ⟨⟨i, h⟩, (β, a)⟩ else 0) *
      MvPolynomial.C ⟨fun x => s * BstLean.Part36.monoVal x β.1,
        continuous_const.mul (continuous_mono58 β.1)⟩

private lemma mapJoint58_eval (s : ℝ) (a : Fin n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval58 (mapJoint58 s a) Z x = mapMD (s • Z) x a := by
  classical
  unfold mapJoint58 jointEval58 mapMD BstLean.Part36.coefD
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : i < d + 1 := Finset.mem_range.mp hi
  apply Finset.sum_congr rfl
  intro β _
  simp [h]
  ring

private lemma mapJoint58_degree (s : ℝ) (a : Fin n) :
    (mapJoint58 (d := d) s a).totalDegree ≤ 1 := by
  classical
  unfold mapJoint58
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply MvPolynomial.totalDegree_finsetSum_le
  intro β hβ
  apply (MvPolynomial.totalDegree_mul _ _).trans
  split_ifs <;> simp

private noncomputable def fJoint58 (s : ℝ) (k : ℕ) (f0 : ℝ) (T : Tens n) : JointPoly58 n d :=
  MvPolynomial.C (ContinuousMap.const _ f0) + ∑ j ∈ Finset.Icc 1 k, ∑ w : Fin j → Fin n,
    MvPolynomial.C (ContinuousMap.const _ (T j w)) * ∏ t, mapJoint58 s (w t)

private lemma fJoint58_eval (s : ℝ) (k : ℕ) (f0 : ℝ) (T : Tens n) (Z : CoefIdxD n d → ℝ)
    (x : Fin n → ℝ) : jointEval58 (fJoint58 (d := d) s k f0 T) Z x = fval k f0 T (mapMD (s • Z) x) := by
  classical
  have h : ∀ a, MvPolynomial.eval₂ ((Pi.evalRingHom (fun _ : Fin n → ℝ => ℝ) x).comp
      ContinuousMap.coeFnRingHom) Z (mapJoint58 (d := d) s a) = mapMD (s • Z) x a :=
    fun a => mapJoint58_eval (d := d) s a Z x
  simp [fJoint58, jointEval58, fval, contr, h]

private lemma fJoint58_degree (s : ℝ) (k : ℕ) (f0 : ℝ) (T : Tens n) :
    (fJoint58 (d := d) s k f0 T).totalDegree ≤ k := by
  classical
  unfold fJoint58
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply MvPolynomial.totalDegree_finsetSum_le
  intro w hw
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ t : Fin j, (mapJoint58 (d := d) s (w t)).totalDegree ≤ ∑ _t : Fin j, 1 :=
      Finset.sum_le_sum fun t ht => mapJoint58_degree _ _
    _ = j := by simp
    _ ≤ k := (Finset.mem_Icc.mp hj).2

/-- **Polynomiality**. -/
theorem propPoly58 (d k : ℕ) : PropPoly58 d k := by
  intro n μ hμ s f0 T
  obtain ⟨Q, hQ, hdeg⟩ := joint_integral58 hμ (fJoint58 (d := d) s k f0 T)
  refine ⟨Q, hdeg.trans (fJoint58_degree s k f0 T), fun Z => ?_⟩
  rw [← hQ Z]
  unfold BofQ
  simp_rw [fJoint58_eval]

end BstLean.Part58
