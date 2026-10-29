import BstLean.Part229Covariance

/-! The extension and derivative split for fixed hidden matrices and a fixed computed centre. -/
namespace BstLean.Part229
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part152 BstLean.Part153
open BstLean.Part160 BstLean.Part188
open BstLean.Part148 (EuLip)

noncomputable def hiddenScalar {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (w : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  w ⬝ᵥ (s • hid2 A₁ A₂ x)

noncomputable def hiddenScalarConstant {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (w : Fin m → ℝ) : ℝ :=
  nrm w * s * (opN A₂ * opN A₁)

lemma hiddenScalarConstant_nonneg {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) {s : ℝ} (hs : 0 ≤ s) (w : Fin m → ℝ) :
    0 ≤ hiddenScalarConstant A₁ A₂ s w := by
  exact mul_nonneg (mul_nonneg (nrm_nonneg _) hs)
    (mul_nonneg (opN_nonneg _) (opN_nonneg _))

lemma hiddenScalar_lip {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) {s : ℝ} (hs : 0 ≤ s) (w : Fin m → ℝ) :
    EuLip (hiddenScalar A₁ A₂ s w) (hiddenScalarConstant A₁ A₂ s w) := by
  apply phiq_eulip A₁ A₂ (φ := fun q => w ⬝ᵥ q) (nrm_nonneg w) _ s hs
  intro u v
  rw [← dotProduct_sub]
  exact abs_dot_le_nrm _ _

lemma hiddenScalar_bound {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) {s : ℝ} (hs : 0 ≤ s) (w : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : nrm x ≤ 1) :
    |hiddenScalar A₁ A₂ s w x| ≤ hiddenScalarConstant A₁ A₂ s w := by
  have hop : 0 ≤ opN A₂ * opN A₁ := mul_nonneg (opN_nonneg _) (opN_nonneg _)
  have hq : nrm (hid2 A₁ A₂ x) ≤ opN A₂ * opN A₁ :=
    (nrm_hid2_le_cr A₁ A₂ x).trans (by nlinarith [mul_le_mul_of_nonneg_left hx hop])
  unfold hiddenScalar hiddenScalarConstant
  calc
    _ ≤ nrm w * nrm (s • hid2 A₁ A₂ x) := abs_dot_le_nrm _ _
    _ = nrm w * (s * nrm (hid2 A₁ A₂ x)) := by rw [nrm_smul, abs_of_nonneg hs]
    _ ≤ nrm w * (s * (opN A₂ * opN A₁)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hs) (nrm_nonneg _)
    _ = _ := by ring

lemma hiddenScalar_residual {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (b v : Fin m → ℝ) (x : Fin n → ℝ) :
    hiddenScalar A₁ A₂ s (res b v) x =
      ∑ j, res b (s • hid2 A₁ A₂ x) j * v j := by
  rw [res_symm]
  exact dotProduct_comm _ _

theorem network_capped_extension {n m : ℕ}
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    {s a d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (u b v : Fin m → ℝ) :
    EuLip (cappedExtension a d (hiddenScalar A₁ A₂ s u)
      (hiddenScalar A₁ A₂ s (res b v)))
      (extensionConstant d (hiddenScalarConstant A₁ A₂ s u)
        (hiddenScalarConstant A₁ A₂ s (res b v))
        (hiddenScalarConstant A₁ A₂ s u) (hiddenScalarConstant A₁ A₂ s (res b v))) := by
  exact cappedExtension_lip hd (hiddenScalarConstant_nonneg A₁ A₂ hs u)
    (hiddenScalarConstant_nonneg A₁ A₂ hs (res b v))
    (hiddenScalarConstant_nonneg A₁ A₂ hs u)
    (hiddenScalarConstant_nonneg A₁ A₂ hs (res b v))
    _ _ (hiddenScalar_lip A₁ A₂ hs u) (hiddenScalar_lip A₁ A₂ hs (res b v))
    (hiddenScalar_bound A₁ A₂ hs u) (hiddenScalar_bound A₁ A₂ hs (res b v))

theorem network_capped_ae_split {n m : ℕ} (hn : 1 ≤ n)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    {s : ℝ} (hs : 0 ≤ s) (u b v : Fin m → ℝ) (c : Fin n → ℝ)
    {τ a d : ℝ} (hτ : 0 < τ) (hd : 0 < d) :
    let F := sphereScalar c τ (hiddenScalar A₁ A₂ s u)
    let Z := sphereScalar c τ (hiddenScalar A₁ A₂ s (res b v))
    ∀ᵐ ξ ∂stdGauss (Fin n), fderiv ℝ (fun ξ => weight a d (F ξ) * Z ξ) ξ =
      weight a d (F ξ) • fderiv ℝ Z ξ +
        (Z ξ * capSlope a d (F ξ)) • fderiv ℝ F ξ := by
  exact capped_sphere_ae_split hn c hτ hd (hiddenScalarConstant_nonneg A₁ A₂ hs u)
    (hiddenScalarConstant_nonneg A₁ A₂ hs u)
    (hiddenScalarConstant_nonneg A₁ A₂ hs (res b v)) _ _
    (hiddenScalar_lip A₁ A₂ hs u) (hiddenScalar_lip A₁ A₂ hs (res b v))
    (hiddenScalar_bound A₁ A₂ hs u)

theorem network_capped_covariance {n m : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    {s : ℝ} (hs : 0 ≤ s) (u b v : Fin m → ℝ) (c : Fin n → ℝ)
    {τ a d N C : ℝ} (hτ : 0 < τ) (hd : 0 < d) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hA : ∫ ξ, projectedEnergy a d
      (sphereScalar c τ (hiddenScalar A₁ A₂ s u))
      (sphereScalar c τ (hiddenScalar A₁ A₂ s (res b v))) ξ ∂stdGauss (Fin n) ≤ N)
    (hB : ∫ ξ, capEnergy a d
      (sphereScalar c τ (hiddenScalar A₁ A₂ s u))
      (sphereScalar c τ (hiddenScalar A₁ A₂ s (res b v))) ξ ∂stdGauss (Fin n) ≤ C) :
    let F := sphereScalar c τ (hiddenScalar A₁ A₂ s u)
    let Z := sphereScalar c τ (hiddenScalar A₁ A₂ s (res b v))
    Integrable (fun ξ => (weight a d (F ξ) * Z ξ -
      ∫ ξ', weight a d (F ξ') * Z ξ' ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    (∫ ξ, (weight a d (F ξ) * Z ξ -
      ∫ ξ', weight a d (F ξ') * Z ξ' ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n)) ≤
        (√N + √C) ^ 2 := by
  exact capped_covariance hn c hτ hd
    (hiddenScalarConstant_nonneg A₁ A₂ hs u)
    (hiddenScalarConstant_nonneg A₁ A₂ hs (res b v))
    (hiddenScalarConstant_nonneg A₁ A₂ hs u)
    (hiddenScalarConstant_nonneg A₁ A₂ hs (res b v))
    (hiddenScalar A₁ A₂ s u) (hiddenScalar A₁ A₂ s (res b v))
    (hiddenScalar_lip A₁ A₂ hs u) (hiddenScalar_lip A₁ A₂ hs (res b v))
    (hiddenScalar_bound A₁ A₂ hs u) (hiddenScalar_bound A₁ A₂ hs (res b v)) hN hC hA hB

end BstLean.Part229
