import BstLean.Part53Floor_Covariance

namespace BstLean.Part53.FloorEnergy

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)

variable {n : ℕ}

private abbrev JointPoly (n : ℕ) (κ : Type*) := MvPolynomial κ C((Fin n → ℝ), ℝ)

private noncomputable def jointEval {κ : Type*} (p : JointPoly n κ)
    (Z : κ → ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z p

private lemma joint_separated {κ : Type*} (p : JointPoly n κ) (Z : κ → ℝ) (x : Fin n → ℝ) :
    jointEval p Z x = ∑ e ∈ p.support,
      p.coeff e x * MvPolynomial.eval Z (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  conv_lhs => unfold jointEval; rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
    Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply, MvPolynomial.eval_monomial, one_mul]

private theorem joint_kernel_variance {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    {κ α : Type*} [Fintype κ] (p : JointPoly n κ) (R : Finset α)
    (K : α → (Fin n → ℝ) → ℝ) (hK : ∀ a ∈ R, Continuous (K a))
    (hpair : ∀ x y : Fin n → ℝ,
      (∫ Z, jointEval p Z x * jointEval p Z y ∂stdGauss κ) = ∑ a ∈ R, K a x * K a y) :
    Integrable (fun Z => varU μ (jointEval p Z)) (stdGauss κ) ∧
    (∫ Z, varU μ (jointEval p Z) ∂stdGauss κ) = ∑ a ∈ R, varU μ (K a) := by
  have h := finite_kernel_variance hμ p.support R (fun e x => p.coeff e x)
    (fun e => MvPolynomial.monomial e 1) (fun e _ => (p.coeff e).continuous) K hK
    (by intro x y; simpa only [← joint_separated] using hpair x y)
  simpa only [← joint_separated] using h

open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono Tens phiM colM contr)

variable {d : ℕ}

private lemma continuous_phi (p : Mono n d) : Continuous (fun x : Fin n → ℝ => phiM x p) := by
  exact continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)

private noncomputable def linJoint {d : ℕ} (s : ℝ) (a : Fin n) : JointPoly n (CoefIdxD n d) :=
  ∑ p : Mono n d, MvPolynomial.C ⟨fun x => s * phiM x p, continuous_const.mul (continuous_phi p)⟩ *
    MvPolynomial.X ⟨p.1, (p.2, a)⟩

private lemma linJoint_eval {d : ℕ} (s : ℝ) (a : Fin n) (Z : CoefIdxD n d → ℝ)
    (x : Fin n → ℝ) : jointEval (linJoint s a) Z x = (s • linZ Z (fun p : Mono n d => phiM x p)) a := by
  classical
  simp only [linJoint, jointEval, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', RingHom.comp_apply, Pi.evalRingHom_apply,
    ContinuousMap.coeFnRingHom_apply, linZ, colM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  change (s * phiM x p) * Z ⟨p.1, (p.2, a)⟩ = _
  ring

private noncomputable def fvJoint {d : ℕ} (k : ℕ) (s : ℝ) (A : Tens n) : JointPoly n (CoefIdxD n d) :=
  ∑ c ∈ Finset.range (k + 1), ∑ a : Fin c → Fin n,
    MvPolynomial.C (ContinuousMap.const _ (A c a)) * ∏ t, linJoint s (a t)

private lemma fvJoint_eval {d : ℕ} (k : ℕ) (s : ℝ) (A : Tens n)
    (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    jointEval (fvJoint (d := d) k s A) Z x = fvA k A (s • linZ Z (fun p : Mono n d => phiM x p)) := by
  classical
  simp only [fvJoint, jointEval, map_sum, map_mul, map_prod, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply,
    ContinuousMap.const_apply, fvA, contr]
  have hlin (a : Fin n) :
      MvPolynomial.eval₂Hom ((Pi.evalRingHom _ x).comp ContinuousMap.coeFnRingHom) Z
        (linJoint (d := d) s a) = (s • linZ Z (fun p : Mono n d => phiM x p)) a := linJoint_eval s a Z x
  simp only [hlin]

abbrev EnergyIndex (n d : ℕ) := Σ c : ℕ, (Fin c → Fin n) × (Fin c → Mono n d)

noncomputable def energySet (n d k : ℕ) : Finset (EnergyIndex n d) :=
  (Finset.range (k + 1)).sigma (fun _ => Finset.univ)

noncomputable def energyKernel (k : ℕ) (s : ℝ) (A : Tens n) (i : EnergyIndex n d)
    (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (i.1.factorial : ℝ) * s ^ i.1 *
    heatA k (s ^ 2 * nsq (fun p : Mono n d => phiM x p)) A i.1 i.2.1 *
      ∏ t, phiM x (i.2.2 t)

private lemma dot_power (c : ℕ) (ψ χ : Mono n d → ℝ) :
    (∑ p, ψ p * χ p) ^ c =
      ∑ w : Fin c → Mono n d, (∏ t, ψ (w t)) * (∏ t, χ (w t)) := by
  classical
  calc
    _ = ∏ _t : Fin c, ∑ p, ψ p * χ p := by simp
    _ = ∑ w : Fin c → Mono n d, ∏ t, ψ (w t) * χ (w t) :=
      Fintype.prod_sum (fun (_t : Fin c) (p : Mono n d) => ψ p * χ p)
    _ = _ := by simp only [Finset.prod_mul_distrib]

private lemma wpair_kernel (k : ℕ) (s : ℝ) (A : Tens n) (x y : Fin n → ℝ) :
    wpair k s A A (fun p : Mono n d => phiM x p) (fun p : Mono n d => phiM y p) =
      ∑ i ∈ energySet n d k, energyKernel k s A i x * energyKernel k s A i y := by
  classical
  unfold wpair energySet
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Fintype.sum_prod_type]
  simp only [tinner, dot_power, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro p hp
  have hs : s ^ (2 * c) = (s ^ c) ^ 2 := by rw [mul_comm 2 c, pow_mul]
  have hf : (Real.sqrt (c.factorial : ℝ)) ^ 2 = (c.factorial : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  dsimp only [energyKernel]
  rw [hs]
  ring_nf
  rw [hf]
  ring

private lemma continuous_heat_parameter (k c : ℕ) (A : Tens n) (w : Fin c → Fin n) :
    Continuous (fun v : ℝ => heatA k v A c w) := by
  unfold heatA
  apply continuous_finsetSum
  intro i hi
  exact (((((continuous_id.div_const 2).pow i).div_const (i.factorial : ℝ)).mul_const
    (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ))).mul_const _)

lemma energyKernel_continuous (k : ℕ) (s : ℝ) (A : Tens n) (i : EnergyIndex n d) :
    Continuous (energyKernel k s A i) := by
  have hv : Continuous (fun x : Fin n → ℝ => s ^ 2 * nsq (fun p : Mono n d => phiM x p)) :=
    continuous_const.mul (continuous_finsetSum _ (fun p _ => (continuous_phi p).pow 2))
  have hh := (continuous_heat_parameter k i.1 A i.2.1).comp hv
  have hp : Continuous (fun x : Fin n → ℝ => ∏ t, phiM x (i.2.2 t)) :=
    continuous_finsetProd _ (fun t _ => continuous_phi _)
  exact (continuous_const.mul hh).mul hp

/-- The integrated chaos identity, with integrability, follows from the supplied pair identity. -/
theorem gaussian_variance_energy53 (k : ℕ) (s : ℝ) (A : Tens n)
    (hA : ∀ c, BstLean.Part41.IsSymmT (A c)) (hW : LemmaW53 k)
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) :
    Integrable (fun Z => varU μ (fun x => fvA k A (s • linZ Z (fun p : Mono n d => phiM x p))))
      (stdGauss (CoefIdxD n d)) ∧
    (∫ Z, varU μ (fun x => fvA k A (s • linZ Z (fun p : Mono n d => phiM x p)))
      ∂stdGauss (CoefIdxD n d)) =
      ∑ i ∈ energySet n d k, varU μ (energyKernel k s A i) := by
  have h := joint_kernel_variance hμ (fvJoint (d := d) k s A) (energySet n d k)
    (energyKernel k s A) (fun i _ => energyKernel_continuous k s A i)
    (by
      intro x y
      simp only [fvJoint_eval]
      exact ((hW n d s A A hA hA (fun p : Mono n d => phiM x p) (fun p : Mono n d => phiM y p)).2).trans
        (wpair_kernel k s A x y))
  have he (Z : CoefIdxD n d → ℝ) : jointEval (fvJoint (d := d) k s A) Z =
      fun x => fvA k A (s • linZ Z (fun p : Mono n d => phiM x p)) := by
    funext x
    exact fvJoint_eval k s A Z x
  simpa only [he] using h

private lemma full_family_eval (k : ℕ) (f0 : ℝ) (T : Tens n) (y : Fin n → ℝ) :
    fvA k (TF k f0 T) y = BstLean.Part41.fval k f0 T y := by
  unfold fvA BstLean.Part41.fval
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
    intro w _
    simp only [show i + 1 ≠ 0 by omega, show i + 1 ≤ k by omega, ↓reduceIte]

private lemma full_family_symm (k : ℕ) (f0 : ℝ) (T : Tens n)
    (hT : BstLean.Part41.TSymm k T) (j : ℕ) : BstLean.Part41.IsSymmT (TF k f0 T j) := by
  intro σ w
  unfold TF
  split_ifs with h0 h1
  · rfl
  · exact hT j (by omega) h1 σ w
  · rfl

private lemma map_lin (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    BstLean.Part36.mapMD M x = linZ M (fun p : Mono n d => phiM x p) := by
  classical
  funext a
  unfold BstLean.Part36.mapMD linZ BstLean.Part36.coefD
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun i => ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then M ⟨⟨i, h⟩, (β, a)⟩ else 0) * BstLean.Part36.monoVal x β.1)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  simp [colM, phiM, i.2]

private lemma map_scaled_lin (s : ℝ) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    BstLean.Part36.mapMD (s • Z) x = s • linZ Z (fun p : Mono n d => phiM x p) := by
  rw [map_lin]
  funext a
  simp only [linZ, colM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- W4 in the frozen `varFQ` notation, with all integral exchanges justified. -/
theorem varFQ_energy53 (k : ℕ) (s : ℝ) (f0 : ℝ) (T : Tens n)
    (hT : BstLean.Part41.TSymm k T) (hW : LemmaW53 k)
    {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) :
    Integrable (fun Z => BstLean.Part43.varFQ μ k f0 T (s • Z)) (stdGauss (CoefIdxD n d)) ∧
    (∫ Z, BstLean.Part43.varFQ μ k f0 T (s • Z) ∂stdGauss (CoefIdxD n d)) =
      ∑ i ∈ energySet n d k, varU μ (energyKernel k s (TF k f0 T) i) := by
  have h := gaussian_variance_energy53 (d := d) k s (TF k f0 T)
    (full_family_symm k f0 T hT) hW hμ
  have he (Z : CoefIdxD n d → ℝ) :
      varU μ (fun x => fvA k (TF k f0 T) (s • linZ Z (fun p : Mono n d => phiM x p))) =
        BstLean.Part43.varFQ μ k f0 T (s • Z) := by
    unfold BstLean.Part43.varFQ
    apply congrArg (varU μ)
    funext x
    rw [full_family_eval, map_scaled_lin]
  simpa only [he] using h

end BstLean.Part53.FloorEnergy
