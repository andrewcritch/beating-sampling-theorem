import BstLean.Part53Wick

namespace BstLean.Part53

open MeasureTheory BstLean.Part29

noncomputable def error53_feature_kernel {n d : ℕ} (A : BstLean.Part41.Tens n)
    (j : ℕ) (ψ : BstLean.Part41.Mono n d → ℝ)
    (u : List (BstLean.Part36.CoefIdxD n d)) : ℝ :=
  BstLean.Part41.Tl A j (u.map (fun α => α.2.2)) *
    (u.map (fun α => ψ (BstLean.Part41.pm α))).prod

elab "error53FeatureExpansionImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part53Wick_Bridge.0.BstLean.Part53.feature_fv_eval53")
    | throwError "Part53Wick_Bridge.feature_fv_eval53 is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

/-- Feature evaluation is a finite Wick expansion with heated tensor coefficients. -/
theorem error53_feature_expansion {n d : ℕ} (k : ℕ) (A : BstLean.Part41.Tens n)
    (ψ : BstLean.Part41.Mono n d → ℝ)
    (hA : ∀ j, BstLean.Part41.IsSymmT (A j))
    (Z : BstLean.Part36.CoefIdxD n d → ℝ) :
    fvA k A (linZ Z ψ) = MvPolynomial.eval Z
      (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c
        (error53_feature_kernel (heatA k (nsq ψ) A) c ψ)) := by
  exact error53FeatureExpansionImported k A ψ hA Z

-- Reuse the kernel-checked finite chaos identity from the finished Wick bridge.
elab "error53WickPairImported" : term => do
  let env ← Lean.getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString == "_private.BstLean.Part53Wick_Bridge.0.BstLean.Part53.wick_pair_sum53")
    | throwError "Part53Wick_Bridge.wick_pair_sum53 is unavailable"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

/-- The Gaussian square norm of a finite symmetric chaos expansion. -/
theorem error53_chaos_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (H : ℕ → List ι → ℝ)
    (hH : ∀ c u v, u.Perm v → H c u = H c v) :
    (∫ Z, (MvPolynomial.eval Z
      (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (H c))) ^ 2
      ∂stdGauss ι) =
      ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) *
        ∑ w : Fin c → ι, (H c (List.ofFn w)) ^ 2 := by
  simpa only [map_mul, pow_two] using error53WickPairImported k H H hH

/-- The square identity applies to the difference between two symmetric kernels. -/
theorem error53_chaos_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (H K : ℕ → List ι → ℝ)
    (hH : ∀ c u v, u.Perm v → H c u = H c v)
    (hK : ∀ c u v, u.Perm v → K c u = K c v) :
    (∫ Z, (MvPolynomial.eval Z
      (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c
        (fun u => H c u - K c u))) ^ 2 ∂stdGauss ι) =
      ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) *
        ∑ w : Fin c → ι, (H c (List.ofFn w) - K c (List.ofFn w)) ^ 2 := by
  apply error53_chaos_square
  intro c u v huv
  rw [hH c u v huv, hK c u v huv]

/-- Integration commutes with a finite Wick kernel when its coefficients are integrable. -/
theorem error53_integral_wick {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] (μ : Measure X) (c : ℕ) (H : X → List ι → ℝ)
    (hH : ∀ u, Integrable (fun x => H x u) μ) (Z : ι → ℝ) :
    (∫ x, MvPolynomial.eval Z (BstLean.Part41.wickL c (H x)) ∂μ) =
      MvPolynomial.eval Z (BstLean.Part41.wickL c (fun u => ∫ x, H x u ∂μ)) := by
  classical
  simp only [BstLean.Part41.wickL, map_sum, map_mul, MvPolynomial.eval_C]
  rw [integral_finsetSum _ (fun w _ => (hH (List.ofFn w)).mul_const _)]
  apply Finset.sum_congr rfl
  intro w hw
  exact integral_mul_const _ _

/-- Integration commutes with the complete finite chaos expansion. -/
theorem error53_integral_chaos {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] (μ : Measure X) (k : ℕ)
    (H : X → ℕ → List ι → ℝ)
    (hH : ∀ c u, Integrable (fun x => H x c u) μ) (Z : ι → ℝ) :
    (∫ x, MvPolynomial.eval Z
      (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (H x c)) ∂μ) =
      MvPolynomial.eval Z (∑ c ∈ Finset.range (k + 1),
        BstLean.Part41.wickL c (fun u => ∫ x, H x c u ∂μ)) := by
  classical
  have hint c : Integrable (fun x =>
      MvPolynomial.eval Z (BstLean.Part41.wickL c (H x c))) μ := by
    simp only [BstLean.Part41.wickL, map_sum, map_mul, MvPolynomial.eval_C]
    exact integrable_finsetSum _ (fun w _ => (hH c (List.ofFn w)).mul_const _)
  simp only [map_sum]
  rw [integral_finsetSum _ (fun c _ => hint c)]
  apply Finset.sum_congr rfl
  intro c hc
  exact error53_integral_wick μ c (fun x => H x c) (hH c) Z

/-- Gaussian energy of an integrated symmetric chaos kernel. -/
theorem error53_integrated_chaos_square {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] (μ : Measure X) (k : ℕ)
    (H : X → ℕ → List ι → ℝ)
    (hH : ∀ c u, Integrable (fun x => H x c u) μ)
    (hs : ∀ x c u v, u.Perm v → H x c u = H x c v) :
    (∫ Z, (∫ x, MvPolynomial.eval Z
      (∑ c ∈ Finset.range (k + 1), BstLean.Part41.wickL c (H x c)) ∂μ) ^ 2
      ∂stdGauss ι) =
      ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) *
        ∑ w : Fin c → ι, (∫ x, H x c (List.ofFn w) ∂μ) ^ 2 := by
  simp_rw [error53_integral_chaos μ k H hH]
  apply error53_chaos_square
  intro c u v huv
  apply integral_congr_ae
  exact ae_of_all μ (fun x => hs x c u v huv)

end BstLean.Part53
