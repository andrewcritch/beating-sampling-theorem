import BstLean.Part56Orth_Integrability
import BstLean.Part53Wick_Bridge

/-! Translated Wick polynomials and the Gaussian heat mean. -/

namespace BstLean.Part56.Orth

open MeasureTheory
open BstLean.Part29 (stdGauss)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def shiftHom (a : ι → ℝ) : MvPolynomial ι ℝ →+* MvPolynomial ι ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (a i))

omit [Fintype ι] [DecidableEq ι] in
private lemma shiftHom_eval (a z : ι → ℝ) (p : MvPolynomial ι ℝ) :
    MvPolynomial.eval z (shiftHom a p) = MvPolynomial.eval (z + a) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [shiftHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    simp [shiftHom, Pi.add_apply]

omit [Fintype ι] in
private lemma shiftHom_deriv (a : ι → ℝ) (i : ι) (p : MvPolynomial ι ℝ) :
    MvPolynomial.pderiv i (shiftHom a p) = shiftHom a (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [shiftHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.pderiv_mul, hp, map_add]
    by_cases h : i = j
    · subst j; simp [shiftHom, MvPolynomial.pderiv_X]
    · simp [shiftHom, MvPolynomial.pderiv_X, Ne.symm h]

-- The elaborator resolves a finished private declaration. The kernel checks
-- the application, as in Part53Wick_Bridge.
elab "orthSteinImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part43Floor.0.BstLean.Part43.gaussian_polynomial_stein")
    | throwError "Part43Floor.gaussian_polynomial_stein is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

private lemma shifted_raise_mean (a : ι → ℝ) (i : ι) (p : MvPolynomial ι ℝ) :
    (∫ z, MvPolynomial.eval (z + a)
      (MvPolynomial.X i * p - MvPolynomial.pderiv i p) ∂stdGauss ι) =
      a i * ∫ z, MvPolynomial.eval (z + a) p ∂stdGauss ι := by
  have hstein : (∫ z, z i * MvPolynomial.eval z (shiftHom a p) ∂stdGauss ι) =
      ∫ z, MvPolynomial.eval z (MvPolynomial.pderiv i (shiftHom a p)) ∂stdGauss ι :=
    orthSteinImported (shiftHom a p) i
  rw [shiftHom_deriv] at hstein
  simp_rw [shiftHom_eval] at hstein
  have hp := gaussian_eval_integrable (shiftHom a p)
  have hd := gaussian_eval_integrable (shiftHom a (MvPolynomial.pderiv i p))
  have hx := gaussian_eval_integrable (MvPolynomial.X i * shiftHom a p)
  simp only [map_mul, MvPolynomial.eval_X, shiftHom_eval] at hp hd hx
  simp only [map_sub, map_mul, MvPolynomial.eval_X, Pi.add_apply, add_mul]
  rw [integral_sub
      (f := fun z => z i * MvPolynomial.eval (z + a) p + a i * MvPolynomial.eval (z + a) p)
      (g := fun z => MvPolynomial.eval (z + a) (MvPolynomial.pderiv i p))
      (hx.add (hp.const_mul _)) hd,
    integral_add (f := fun z => z i * MvPolynomial.eval (z + a) p)
      (g := fun z => a i * MvPolynomial.eval (z + a) p) hx (hp.const_mul _),
    integral_const_mul, hstein]
  ring

/-- Translation changes the Gaussian mean of a Wick tensor to its plain value. -/
theorem shifted_wick_mean (m : ℕ) (H : List ι → ℝ) (a : ι → ℝ) :
    (∫ z, MvPolynomial.eval (z + a) (BstLean.Part41.wickL m H) ∂stdGauss ι) =
      MvPolynomial.eval a (BstLean.Part41.plainL m H) := by
  classical
  induction m generalizing H with
  | zero => simp [BstLean.Part41.wickL_zero, BstLean.Part41.eval_plainL]
  | succ m ih =>
    rw [BstLean.Part41.wickL_succ]
    change (∫ z, MvPolynomial.eval (z + a)
      (∑ i : ι, (MvPolynomial.X i * BstLean.Part41.wickL m (fun u => H (i :: u)) -
        MvPolynomial.pderiv i (BstLean.Part41.wickL m (fun u => H (i :: u)))))
      ∂stdGauss ι) = _
    simp only [map_sum]
    rw [integral_finsetSum _ (fun i _ => by
      simpa only [shiftHom_eval] using gaussian_eval_integrable
        (shiftHom a (MvPolynomial.X i * BstLean.Part41.wickL m (fun u => H (i :: u)) -
          MvPolynomial.pderiv i (BstLean.Part41.wickL m (fun u => H (i :: u))))))]
    simp_rw [shifted_raise_mean, ih, BstLean.Part41.eval_plainL]
    rw [BstLean.Part41.sum_pi_succ]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [BstLean.Part41.ofFn_cons', Fin.prod_univ_succ, Finset.mul_sum,
      Fin.cons_zero, Fin.cons_succ]
    apply Finset.sum_congr rfl
    intro w hw
    ring

elab "orthFeatureKernelImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part53Wick_Bridge.0.BstLean.Part53.featureKernel53")
    | throwError "Part53Wick_Bridge.featureKernel53 is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

elab "orthFvWickImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part53Wick_Bridge.0.BstLean.Part53.feature_fv_eval53")
    | throwError "Part53Wick_Bridge.feature_fv_eval53 is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

elab "orthFeaturePlainImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part53Wick_Bridge.0.BstLean.Part53.feature_plain_eval53")
    | throwError "Part53Wick_Bridge.feature_plain_eval53 is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono Tens IsSymmT)
open BstLean.Part53 (fvA heatA nsq linZ)

/-- The heat identity for a shifted Gaussian linear field. -/
theorem shifted_linear_heat {n d : ℕ} (k : ℕ) (A : Tens n)
    (hA : ∀ j, IsSymmT (A j)) (ψ : Mono n d → ℝ) (a : CoefIdxD n d → ℝ) :
    (∫ Z, fvA k A (linZ (Z + a) ψ) ∂stdGauss (CoefIdxD n d)) =
      fvA k (heatA k (nsq ψ) A) (linZ a ψ) := by
  classical
  let H := fun c => orthFeatureKernelImported (heatA k (nsq ψ) A) c ψ
  have he (Z : CoefIdxD n d → ℝ) :
      fvA k A (linZ (Z + a) ψ) = MvPolynomial.eval (Z + a)
        (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (H c)) :=
    orthFvWickImported k A ψ hA (Z + a)
  simp_rw [he, map_sum]
  rw [integral_finsetSum _ (fun c hc => by
    simpa only [shiftHom_eval] using gaussian_eval_integrable
      (shiftHom a (BstLean.Part41.wickL c (H c))))]
  simp_rw [shifted_wick_mean]
  unfold fvA
  apply Finset.sum_congr rfl
  intro c hc
  exact orthFeaturePlainImported (heatA k (nsq ψ) A) c ψ a

private lemma heat_zero_at {n : ℕ} (k c : ℕ) (hc : c ≤ k) (A : Tens n) :
    heatA k 0 A c = A c := by
  classical
  funext w
  unfold heatA
  rw [Finset.sum_eq_single 0]
  · simp [BstLean.Part41.trL]
    rw [div_self (by positivity), one_mul]
    congr 1
  · intro i hi hi0
    simp [hi0]
  · simp [hc]

/-- The heat mean identity permits any deterministic mean, including zero residual variance. -/
theorem linear_heat_mean {n d : ℕ} (k : ℕ) (A : Tens n)
    (hA : ∀ j, IsSymmT (A j)) (ψ : Mono n d → ℝ) (y : Fin n → ℝ) :
    (∫ Z, fvA k A (y + linZ Z ψ) ∂stdGauss (CoefIdxD n d)) =
      fvA k (heatA k (nsq ψ) A) y := by
  classical
  by_cases hz : nsq ψ = 0
  · have hψ : ψ = 0 := by
      funext p
      have hle := Finset.single_le_sum (fun q _ => sq_nonneg (ψ q)) (Finset.mem_univ p)
      change ψ p ^ 2 ≤ nsq ψ at hle
      rw [hz] at hle
      simpa only [Pi.zero_apply] using (sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _)))
    have he : fvA k (heatA k 0 A) y = fvA k A y := by
      unfold fvA
      apply Finset.sum_congr rfl
      intro c hc
      rw [heat_zero_at k c (by have := Finset.mem_range.mp hc; omega)]
    rw [hz, he]
    have hl (Z : CoefIdxD n d → ℝ) : linZ Z ψ = 0 := by
      rw [hψ]
      funext i
      simp [linZ]
    simp only [hl, add_zero, integral_const, probReal_univ, one_smul]
  · let a : CoefIdxD n d → ℝ := fun α =>
      y α.2.2 * ψ ⟨α.1, α.2.1⟩ / nsq ψ
    have ha : linZ a ψ = y := by
      funext i
      change (∑ p : Mono n d, (y i * ψ p / nsq ψ) * ψ p) = y i
      simp_rw [show ∀ p : Mono n d,
        (y i * ψ p / nsq ψ) * ψ p = y i * (ψ p ^ 2 / nsq ψ) by intro p; ring]
      rw [← Finset.mul_sum, ← Finset.sum_div]
      change y i * (nsq ψ / nsq ψ) = y i
      rw [div_self hz, mul_one]
    have hadd (Z : CoefIdxD n d → ℝ) : linZ (Z + a) ψ = y + linZ Z ψ := by
      funext i
      have hi := congrFun ha i
      simp only [linZ, BstLean.Part41.colM, Pi.add_apply, add_mul,
        Finset.sum_add_distrib] at hi ⊢
      rw [hi]
      ring
    simpa only [hadd, ha] using shifted_linear_heat k A hA ψ a

end BstLean.Part56.Orth
