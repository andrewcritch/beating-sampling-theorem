import BstLean.Part53Error_Chaos
import BstLean.Part53Error_HeatSum
import BstLean.Part53Floor

namespace BstLean.Part53

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part41 (Mono Tens TSymm IsSymmT phiM colM)

elab "error53FullEval" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part53Floor_Energy.0.BstLean.Part53.FloorEnergy.full_family_eval")
    | throwError "Floor energy declaration unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none
elab "error53FullSymm" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part53Floor_Energy.0.BstLean.Part53.FloorEnergy.full_family_symm")
    | throwError "Floor energy declaration unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none
elab "error53MapScaled" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part53Floor_Energy.0.BstLean.Part53.FloorEnergy.map_scaled_lin")
    | throwError "Floor energy declaration unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

variable {n d : ℕ}

noncomputable def error53_e0 : Mono n d → ℝ := fun p => if p = default then 1 else 0

lemma error53_lin_scale (s : ℝ) (Z : CoefIdxD n d → ℝ) (ψ : Mono n d → ℝ) :
    linZ Z (s • ψ) = s • linZ Z ψ := by
  classical
  funext a
  simp only [linZ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

lemma error53_lin_e0 (Z : CoefIdxD n d → ℝ) : linZ Z error53_e0 = colM Z default := by
  classical
  funext a
  simp [linZ, error53_e0]

lemma error53_nsq_scale (s : ℝ) (ψ : Mono n d → ℝ) :
    nsq (s • ψ) = s ^ 2 * nsq ψ := by
  classical
  simp [nsq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma error53_g0_expansion (hn : 1 ≤ n) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (hT : TSymm k T) (Z : CoefIdxD n d → ℝ) :
    g0 n d k f0 T (sg n d • Z) = MvPolynomial.eval Z
      (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c
        (error53_feature_kernel (Tcirc n d k f0 T) c (sg n d • error53_e0))) := by
  classical
  have hA : ∀ j, IsSymmT (TF k f0 T j) := error53FullSymm k f0 T hT
  have he : nsq (error53_e0 : Mono n d → ℝ) = 1 := by simp [nsq, error53_e0]
  have hs : sg n d ^ 2 = 1 / DD n d := by
    simpa using FloorCorrection.sg_pow_even (d := d) hn 1
  have hcol : colM (sg n d • Z) default =
      linZ Z (sg n d • error53_e0) := by
    rw [error53_lin_scale, error53_lin_e0]
    rfl
  unfold g0
  rw [hcol, error53_feature_expansion k _ _ (fun j =>
    error53_heat_symm (aH n d) (TF k f0 T) hA j),
    error53_nsq_scale, he, mul_one, error53_heat_add]
  have hv : sg n d ^ 2 + aH n d = c0 d / DD n d := by rw [hs]; unfold aH; ring
  rw [hv]
  rfl

lemma error53_fval_expansion (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    BstLean.Part41.fval k f0 T (BstLean.Part36.mapMD (sg n d • Z) x) =
      MvPolynomial.eval Z (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c
        (error53_feature_kernel
          (heatA k (sg n d ^ 2 * nsq (fun p : Mono n d => phiM x p)) (TF k f0 T)) c
          (sg n d • (fun p : Mono n d => phiM x p)))) := by
  rw [← error53FullEval k f0 T, error53MapScaled (sg n d) Z x,
    ← error53_lin_scale]
  rw [error53_feature_expansion k _ _ (error53FullSymm k f0 T hT),
    error53_nsq_scale]


noncomputable def error53_actual_kernel (k : ℕ) (f0 : ℝ) (T : Tens n)
    (x : Fin n → ℝ) (c : ℕ) : List (CoefIdxD n d) → ℝ :=
  error53_feature_kernel
    (heatA k (sg n d ^ 2 * nsq (fun p : Mono n d => phiM x p)) (TF k f0 T)) c
    (sg n d • (fun p : Mono n d => phiM x p))

noncomputable def error53_target_kernel (k : ℕ) (f0 : ℝ) (T : Tens n)
    (c : ℕ) : List (CoefIdxD n d) → ℝ :=
  error53_feature_kernel (Tcirc n d k f0 T) c (sg n d • error53_e0)

lemma error53_actual_continuous (k : ℕ) (f0 : ℝ) (T : Tens n)
    (c : ℕ) (u : List (CoefIdxD n d)) :
    Continuous (fun x => error53_actual_kernel k f0 T x c u) := by
  classical
  have hphi (p : Mono n d) : Continuous (fun x : Fin n → ℝ => phiM x p) :=
    continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)
  have hv : Continuous (fun x : Fin n → ℝ =>
      sg n d ^ 2 * nsq (fun p : Mono n d => phiM x p)) :=
    continuous_const.mul (continuous_finsetSum _ (fun p _ => (hphi p).pow 2))
  have hh (w : Fin c → Fin n) :
      Continuous (fun x : Fin n → ℝ =>
        heatA k (sg n d ^ 2 * nsq (fun p : Mono n d => phiM x p)) (TF k f0 T) c w) := by
    unfold heatA
    apply continuous_finsetSum
    intro i hi
    exact (((hv.div_const 2).pow i).div_const _ |>.mul_const _ |>.mul_const _)
  unfold error53_actual_kernel error53_feature_kernel BstLean.Part41.Tl
  have hp : Continuous (fun x : Fin n → ℝ =>
      (u.map (fun α => (sg n d • (fun p : Mono n d => phiM x p)) (BstLean.Part41.pm α))).prod) := by
    induction u with
    | nil => simpa only [List.map_nil, List.prod_nil] using (continuous_const : Continuous (fun _ : Fin n → ℝ => (1 : ℝ)))
    | cons a u ih =>
      simp only [List.map_cons, List.prod_cons, Pi.smul_apply, smul_eq_mul]
      exact (continuous_const.mul (hphi _)).mul ih
  split_ifs
  · exact (hh _).mul hp
  · exact continuous_const.mul hp

lemma error53_kernel_symm (A : Tens n) (c : ℕ) (ψ : Mono n d → ℝ)
    (hA : IsSymmT (A c)) (u v : List (CoefIdxD n d)) (h : u.Perm v) :
    error53_feature_kernel A c ψ u = error53_feature_kernel A c ψ v := by
  unfold error53_feature_kernel
  rw [BstLean.Part41.Tl_perm A c hA _ _ (h.map _), (h.map _).prod_eq]

lemma error53_wick_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ) (H K : List ι → ℝ) :
    BstLean.Part41.wickL c (fun u => H u - K u) =
      BstLean.Part41.wickL c H - BstLean.Part41.wickL c K := by
  classical
  simp only [BstLean.Part41.wickL, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem error53_error_energy (hn : 1 ≤ n) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (hT : TSymm k T) {μ : Measure (Fin n → ℝ)} (hμ : BstLean.Part40.SphLaw n μ) :
    (∫ Z, (BstLean.Part43.BofQ μ k f0 T (sg n d • Z) -
      g0 n d k f0 T (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d)) =
    ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) *
      ∑ w : Fin c → CoefIdxD n d,
        (∫ x, error53_actual_kernel k f0 T x c (List.ofFn w) -
          error53_target_kernel k f0 T c (List.ofFn w) ∂μ) ^ 2 := by
  classical
  letI := hμ.prob
  let H : (Fin n → ℝ) → ℕ → List (CoefIdxD n d) → ℝ := fun x c u => error53_actual_kernel k f0 T x c u -
    error53_target_kernel k f0 T c u
  have hi c u : Integrable (fun x => H x c u) μ :=
    FloorEnergy.sphere_cont_integrable hμ
      ((error53_actual_continuous k f0 T c u).sub continuous_const)
  have hs x c u v (huv : u.Perm v) : H x c u = H x c v := by
    have hA : ∀ j, IsSymmT (TF k f0 T j) := error53FullSymm k f0 T hT
    dsimp [H, error53_actual_kernel, error53_target_kernel, Tcirc]
    rw [error53_kernel_symm _ c _ (error53_heat_symm _ _ hA c) u v huv,
      error53_kernel_symm _ c _ (error53_heat_symm _ _ hA c) u v huv]
  have he (Z : CoefIdxD n d → ℝ) :
      (∫ x, MvPolynomial.eval Z
        (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (H x c)) ∂μ) =
      BstLean.Part43.BofQ μ k f0 T (sg n d • Z) -
        g0 n d k f0 T (sg n d • Z) := by
    have hp x : MvPolynomial.eval Z
        (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (H x c)) =
      BstLean.Part41.fval k f0 T (BstLean.Part36.mapMD (sg n d • Z) x) -
        g0 n d k f0 T (sg n d • Z) := by
      simp only [H, error53_wick_sub, Finset.sum_sub_distrib, map_sub]
      rw [error53_fval_expansion k f0 T hT Z x, error53_g0_expansion hn k f0 T hT Z]
      rfl
    simp_rw [hp]
    rw [integral_sub]
    · simp [BstLean.Part43.BofQ]
    · simp_rw [error53_fval_expansion k f0 T hT Z]
      simp only [map_sum, BstLean.Part41.wickL, map_mul, MvPolynomial.eval_C]
      exact integrable_finsetSum _ (fun c _ => integrable_finsetSum _ (fun w _ =>
        (FloorEnergy.sphere_cont_integrable hμ
          (error53_actual_continuous k f0 T c (List.ofFn w))).mul_const _))
    · exact integrable_const _
  have hh := error53_integrated_chaos_square μ k H hi hs
  simpa only [he, H] using hh


lemma error53_feature_kernel_ofFn (A : Tens n) (c : ℕ) (ψ : Mono n d → ℝ)
    (w : Fin c → CoefIdxD n d) :
    error53_feature_kernel A c ψ (List.ofFn w) =
      A c (fun t => (w t).2.2) * ∏ t, ψ (BstLean.Part41.pm (w t)) := by
  simp only [error53_feature_kernel, List.map_ofFn, BstLean.Part41.Tl_ofFn,
    List.prod_ofFn, Function.comp_def]

noncomputable def error53_target_energy (s : ℝ) (B : Tens n)
    (c : ℕ) (a : Fin c → Fin n) (p : Fin c → Mono n d) : ℝ :=
  Real.sqrt (c.factorial : ℝ) * s ^ c * B c a * ∏ t, error53_e0 (p t)

theorem error53_error_energy_split (hn : 1 ≤ n) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (hT : TSymm k T) {μ : Measure (Fin n → ℝ)} (hμ : BstLean.Part40.SphLaw n μ) :
    (∫ Z, (BstLean.Part43.BofQ μ k f0 T (sg n d • Z) -
      g0 n d k f0 T (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d)) =
      ∑ c ∈ Finset.range (k + 1), ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
        (∫ x, FloorEnergy.energyKernel k (sg n d) (TF k f0 T) ⟨c, a, p⟩ x -
          error53_target_energy (sg n d) (Tcirc n d k f0 T) c a p ∂μ) ^ 2 := by
  classical
  rw [error53_error_energy hn k f0 T hT hμ]
  apply Finset.sum_congr rfl
  intro c hc
  rw [BstLean.Part41.sum_split]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro p hp
  have hfac := Real.sq_sqrt (Nat.cast_nonneg c.factorial : (0 : ℝ) ≤ c.factorial)
  have he (x : Fin n → ℝ) :
      FloorEnergy.energyKernel k (sg n d) (TF k f0 T) ⟨c, a, p⟩ x -
        error53_target_energy (sg n d) (Tcirc n d k f0 T) c a p =
      Real.sqrt (c.factorial : ℝ) *
        (error53_actual_kernel k f0 T x c
          (List.ofFn (fun t => (⟨(p t).1, ((p t).2, a t)⟩ : CoefIdxD n d))) -
         error53_target_kernel k f0 T c
          (List.ofFn (fun t => (⟨(p t).1, ((p t).2, a t)⟩ : CoefIdxD n d)))) := by
    simp only [error53_actual_kernel, error53_target_kernel, error53_feature_kernel_ofFn,
      Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, BstLean.Part41.pm,
      FloorEnergy.energyKernel, error53_target_energy]
    ring
  simp_rw [he]
  rw [integral_const_mul, mul_pow, hfac]
  rfl

end BstLean.Part53
