import BstLean.Part229Homogeneous

/-! The projected gradient term is the actual gated tangent Jacobian. -/
namespace BstLean.Part229
open MeasureTheory Real Matrix Filter
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part188
open BstLean.Part151 (JacAt jac lemmaJ_shift)

lemma jacAt_fderiv_apply {n m : ℕ} {A₁ : Matrix (Fin m) (Fin n) ℝ}
    {A₂ : Matrix (Fin m) (Fin m) ℝ} {y : Fin n → ℝ} (hJ : JacAt A₁ A₂ y)
    (j : Fin m) (v : Fin n → ℝ) :
    fderiv ℝ (fun x => hid2 A₁ A₂ x j) y v = (jac A₁ A₂ y *ᵥ v) j := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  simp only [map_smul, (hJ j).2, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma hiddenScalar_homogeneous {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (w : Fin m → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (x : Fin n → ℝ) :
    hiddenScalar A₁ A₂ s w (t • x) = t * hiddenScalar A₁ A₂ s w x := by
  unfold hiddenScalar
  rw [hid2_smul A₁ A₂ ht, smul_comm s t, dotProduct_smul]
  rfl

theorem hiddenScalar_fderiv {n m : ℕ} {A₁ : Matrix (Fin m) (Fin n) ℝ}
    {A₂ : Matrix (Fin m) (Fin m) ℝ} {y : Fin n → ℝ} (hJ : JacAt A₁ A₂ y)
    (s : ℝ) (w : Fin m → ℝ) :
    DifferentiableAt ℝ (hiddenScalar A₁ A₂ s w) y ∧
    ∀ v, fderiv ℝ (hiddenScalar A₁ A₂ s w) y v = s * (w ⬝ᵥ (jac A₁ A₂ y *ᵥ v)) := by
  have he : hiddenScalar A₁ A₂ s w =
      fun x => ∑ j, (w j * s) * hid2 A₁ A₂ x j := by
    funext x
    unfold hiddenScalar dotProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [he]
  have hd := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => ((hJ j).1.hasFDerivAt.const_mul (w j * s)))
  constructor
  · exact hd.differentiableAt
  · intro v
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp_rw [jacAt_fderiv_apply hJ]
    unfold dotProduct
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem hiddenScalar_sphere_derivative {n m : ℕ}
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (s : ℝ) (w : Fin m → ℝ) (c : Fin n → ℝ) (τ : ℝ) {ξ : Fin n → ℝ}
    (hy : normSq (c + τ • ξ) ≠ 0) (hJ : JacAt A₁ A₂ (c + τ • ξ))
    (v : Fin n → ℝ) :
    fderiv ℝ (sphereScalar c τ (hiddenScalar A₁ A₂ s w)) ξ v =
      (s * τ / nrm (c + τ • ξ)) *
        (w ⬝ᵥ (jacT A₁ A₂ (sphPt (c + τ • ξ)) *ᵥ v)) := by
  rw [homogeneous_sphere_derivative (hiddenScalar_homogeneous A₁ A₂ s w)
    c τ hy (hiddenScalar_fderiv hJ s w).1,
    (hiddenScalar_fderiv hJ s w).2]
  have hnrm : 0 < nrm (c + τ • ξ) := Real.sqrt_pos.mpr
    (lt_of_le_of_ne (normSq_nonneg _) hy.symm)
  have he : nrm (c + τ • ξ) • sphPt (c + τ • ξ) = c + τ • ξ := by
    rw [sphPt_eq' hy, one_div]
    change nrm (c + τ • ξ) • ((nrm (c + τ • ξ))⁻¹ • (c + τ • ξ)) = _
    rw [smul_smul, mul_inv_cancel₀ hnrm.ne', one_smul]
  have hj : jac A₁ A₂ (c + τ • ξ) = jac A₁ A₂ (sphPt (c + τ • ξ)) := by
    conv_lhs => rw [← he]
    exact jac_smul A₁ A₂ hnrm _
  rw [hj, Matrix.mulVec_mulVec]
  change _ = _ * (w ⬝ᵥ ((jac A₁ A₂ (sphPt (c + τ • ξ)) *
    projT (sphPt (c + τ • ξ))) *ᵥ v))
  ring

theorem hiddenScalar_sphere_ae_gradient {n m : ℕ} (hn : 1 ≤ n)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (s : ℝ) (w : Fin m → ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      gradientVector (sphereScalar c τ (hiddenScalar A₁ A₂ s w)) ξ =
        (s * τ / nrm (c + τ • ξ)) •
          vecMul w (jacT A₁ A₂ (sphPt (c + τ • ξ))) := by
  filter_upwards [ae_normSq_ne hn c hτ.ne', lemmaJ_shift A₁ A₂ c hτ.ne'] with ξ hy hJ
  funext i
  rw [gradientVector, hiddenScalar_sphere_derivative A₁ A₂ s w c τ hy hJ,
    Matrix.dotProduct_mulVec]
  simp

theorem network_capped_ae_jacobian_split {n m : ℕ} (hn : 1 ≤ n)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    {s : ℝ} (hs : 0 ≤ s) (u b v : Fin m → ℝ) (c : Fin n → ℝ) {τ a d : ℝ}
    (hτ : 0 < τ) (hd : 0 < d) :
    let F := sphereScalar c τ (hiddenScalar A₁ A₂ s u)
    let Z := sphereScalar c τ (hiddenScalar A₁ A₂ s (BstLean.Part134.res b v))
    ∀ᵐ ξ ∂stdGauss (Fin n),
      gradientVector (fun ξ => weight a d (F ξ) * Z ξ) ξ =
        (weight a d (F ξ) * (s * τ / nrm (c + τ • ξ))) •
          vecMul (BstLean.Part134.res b v) (jacT A₁ A₂ (sphPt (c + τ • ξ))) +
        (Z ξ * capSlope a d (F ξ) * (s * τ / nrm (c + τ • ξ))) •
          vecMul u (jacT A₁ A₂ (sphPt (c + τ • ξ))) := by
  dsimp only
  filter_upwards [network_capped_ae_split (a := a) hn A₁ A₂ hs u b v c hτ hd,
    hiddenScalar_sphere_ae_gradient hn A₁ A₂ s u c hτ,
    hiddenScalar_sphere_ae_gradient hn A₁ A₂ s (BstLean.Part134.res b v) c hτ]
    with ξ h hF hZ
  have he : gradientVector (fun ξ =>
      weight a d (sphereScalar c τ (hiddenScalar A₁ A₂ s u) ξ) *
        sphereScalar c τ (hiddenScalar A₁ A₂ s (BstLean.Part134.res b v)) ξ) ξ =
      weight a d (sphereScalar c τ (hiddenScalar A₁ A₂ s u) ξ) •
        gradientVector (sphereScalar c τ (hiddenScalar A₁ A₂ s (BstLean.Part134.res b v))) ξ +
      (sphereScalar c τ (hiddenScalar A₁ A₂ s (BstLean.Part134.res b v)) ξ *
        capSlope a d (sphereScalar c τ (hiddenScalar A₁ A₂ s u) ξ)) •
          gradientVector (sphereScalar c τ (hiddenScalar A₁ A₂ s u)) ξ := by
    funext i
    simp [gradientVector, h]
  rw [he, hF, hZ, smul_smul, smul_smul]

theorem network_projected_energy_formula {n m : ℕ} (hn : 1 ≤ n)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (s : ℝ) (u b v : Fin m → ℝ) (c : Fin n → ℝ) {τ a d : ℝ}
    (hτ : 0 < τ) (hd : 0 < d) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      projectedEnergy a d (sphereScalar c τ (hiddenScalar A₁ A₂ s u))
        (sphereScalar c τ (hiddenScalar A₁ A₂ s (BstLean.Part134.res b v))) ξ =
      weightSq a d (sphereScalar c τ (hiddenScalar A₁ A₂ s u) ξ) *
        (s * τ / nrm (c + τ • ξ)) ^ 2 *
          normSq (vecMul (BstLean.Part134.res b v)
            (jacT A₁ A₂ (sphPt (c + τ • ξ)))) := by
  filter_upwards [hiddenScalar_sphere_ae_gradient hn A₁ A₂ s
    (BstLean.Part134.res b v) c hτ] with ξ h
  rw [(energy_formulas _ _ _ _ _).1, h, normSq_smul, weight_sq hd]
  ring

theorem network_cap_energy_formula {n m : ℕ} (hn : 1 ≤ n)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (s : ℝ) (u b v : Fin m → ℝ) (c : Fin n → ℝ) {τ a d : ℝ} (hτ : 0 < τ) :
    let F := sphereScalar c τ (hiddenScalar A₁ A₂ s u)
    let Z := sphereScalar c τ (hiddenScalar A₁ A₂ s (BstLean.Part134.res b v))
    ∀ᵐ ξ ∂stdGauss (Fin n), capEnergy a d F Z ξ =
      (Z ξ * capSlope a d (F ξ)) ^ 2 * (s * τ / nrm (c + τ • ξ)) ^ 2 *
        normSq (vecMul u (jacT A₁ A₂ (sphPt (c + τ • ξ)))) := by
  dsimp only
  filter_upwards [hiddenScalar_sphere_ae_gradient hn A₁ A₂ s u c hτ] with ξ h
  rw [(energy_formulas _ _ _ _ _).2, h, normSq_smul]
  ring

end BstLean.Part229
