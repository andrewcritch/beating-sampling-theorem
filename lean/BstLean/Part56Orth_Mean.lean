import BstLean.Part56Orth_Heat
import BstLean.Part56Orth_Residual
import BstLean.Part53Error_Integrability

namespace BstLean.Part56.Orth

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD mapMD)
open BstLean.Part41 (Mono Tens TSymm IsSymmT fval contr)
open BstLean.Part43 (BofQ)
open BstLean.Part40 (SphLaw)
open BstLean.Part53 (sg TF fvA heatA linZ)

variable {n d : ℕ}

private noncomputable def projJoint (v : Fin n → ℝ) (α : CoefIdxD n d) : JointPoly n d :=
  ∑ j ∈ Finset.range (d + 1),
    MvPolynomial.C (ContinuousMap.const _ (phiB d j v ⟨α.1, α.2.1⟩ / kJ d j v v)) *
      ∑ p : Mono n d, MvPolynomial.C (ContinuousMap.const _ (phiB d j v p)) *
        MvPolynomial.X ⟨p.1, (p.2, α.2.2)⟩

private lemma projJoint_eval (v : Fin n → ℝ) (α : CoefIdxD n d)
    (W : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (projJoint v α) W x = projA v W α := by
  classical
  simp [projJoint, jointEval, projA]

private noncomputable def resampleJoint (v : Fin n → ℝ) (Z : CoefIdxD n d → ℝ)
    (p : JointPoly n d) : JointPoly n d :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun α => MvPolynomial.C (ContinuousMap.const _ (projA v Z α)) +
      (MvPolynomial.X α - projJoint v α)) p

private lemma resampleJoint_eval (v : Fin n → ℝ) (Z W : CoefIdxD n d → ℝ)
    (p : JointPoly n d) (x : Fin n → ℝ) :
    jointEval (resampleJoint v Z p) W x =
      jointEval p (projA v Z + (W - projA v W)) x := by
  let E := MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) W
  let Q := fun α : CoefIdxD n d => MvPolynomial.C (ContinuousMap.const _ (projA v Z α)) +
    (MvPolynomial.X α - projJoint v α)
  have hh : E.comp (MvPolynomial.eval₂Hom MvPolynomial.C Q) =
      MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom)
        (projA v Z + (W - projA v W)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [E, RingHom.comp_apply]
    · intro α
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change jointEval (Q α) W x = (projA v Z + (W - projA v W)) α
      simp only [Q, jointEval, map_add, map_sub, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', RingHom.comp_apply, Pi.evalRingHom_apply,
        ContinuousMap.coeFnRingHom_apply, ContinuousMap.const_apply, Pi.add_apply, Pi.sub_apply]
      rw [show MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom)
        W (projJoint v α) = projA v W α from projJoint_eval v α W x]
  exact congrArg (fun f => f p) hh

private lemma full_eval (k : ℕ) (f0 : ℝ) (T : Tens n) (y : Fin n → ℝ) :
    fvA k (TF k f0 T) y = fval k f0 T y := by
  unfold fvA fval
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [contr, TF]
  · rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by rfl, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [add_comm 1 i]
    unfold contr TF
    apply Finset.sum_congr rfl
    intro w hw
    simp only [show i + 1 ≠ 0 by omega, show i + 1 ≤ k by omega, ite_false, ite_true]

private lemma full_symm (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (j : ℕ) :
    IsSymmT (TF k f0 T j) := by
  intro σ w
  unfold TF
  split_ifs with h0 h1
  · rfl
  · exact hT j (by omega) h1 σ w
  · rfl

private lemma mean_at_x (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    (∫ W, fval k f0 T (mapMD (sg n d • (projA v Z + (W - projA v W))) x)
      ∂stdGauss (CoefIdxD n d)) =
      fvA k (heatA k (sg n d ^ 2 * tauR d v x) (TF k f0 T)) (mux (sg n d • Z) v x) := by
  simp_rw [resampled_map, ← full_eval]
  rw [linear_heat_mean k (TF k f0 T) (full_symm k f0 T hT),
    residualFeature_scaled_norm (sg n d) v hv x]

/-- The heat predictor equals the mean over the independently resampled residual. -/
theorem resampled_mean {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) :
    (∫ W, BofQ μ k f0 T (sg n d • (projA v Z + (W - projA v W)))
      ∂stdGauss (CoefIdxD n d)) = gLineH μ k f0 T v (sg n d • Z) := by
  let P := resampleJoint v Z (bJoint (d := d) k f0 T (sg n d))
  have hp (W : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
      jointEval P W x = fval k f0 T (mapMD (sg n d • (projA v Z + (W - projA v W))) x) := by
    dsimp only [P]
    rw [resampleJoint_eval, bJoint_eval]
  have he (W : CoefIdxD n d → ℝ) :
      BofQ μ k f0 T (sg n d • (projA v Z + (W - projA v W))) = ∫ x, jointEval P W x ∂μ := by
    unfold BofQ
    apply integral_congr_ae
    exact ae_of_all _ (fun x => (hp W x).symm)
  simp_rw [he]
  have hex := BstLean.Part53.error53_gaussian_exchange hμ P
  change (∫ W, ∫ x, jointEval P W x ∂μ ∂stdGauss (CoefIdxD n d)) =
    ∫ x, ∫ W, jointEval P W x ∂stdGauss (CoefIdxD n d) ∂μ at hex
  rw [hex]
  change (∫ x, ∫ W, jointEval P W x ∂stdGauss (CoefIdxD n d) ∂μ) = _
  simp_rw [hp]
  unfold gLineH
  apply integral_congr_ae
  exact ae_of_all _ (fun x => mean_at_x k f0 T hT v hv Z x)

/-- The centered independently resampled residual has mean zero. -/
theorem centered_resampled_mean {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T)
    (v : Fin n → ℝ) (hv : UnitV v) (Z : CoefIdxD n d → ℝ) :
    (∫ W, (BofQ μ k f0 T (sg n d • (projA v Z + (W - projA v W))) -
      gLineH μ k f0 T v (sg n d • Z)) ∂stdGauss (CoefIdxD n d)) = 0 := by
  let P := resampleJoint v Z (bJoint (d := d) k f0 T (sg n d))
  have he (W : CoefIdxD n d → ℝ) :
      (∫ x, jointEval P W x ∂μ) = BofQ μ k f0 T (sg n d • (projA v Z + (W - projA v W))) := by
    unfold BofQ
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp only [P]; rw [resampleJoint_eval, bJoint_eval])
  have hi : Integrable (fun W => BofQ μ k f0 T (sg n d • (projA v Z + (W - projA v W))))
      (stdGauss (CoefIdxD n d)) := by
    simpa only [he] using joint_mean_integrable hμ P
  rw [integral_sub hi (integrable_const _), resampled_mean hμ k f0 T hT v hv Z]
  simp

end BstLean.Part56.Orth
