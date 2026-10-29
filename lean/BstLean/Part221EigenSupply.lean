import BstLean.Part221EigenInner
import BstLean.Part212PlaneSupply
import BstLean.Part212Frobenius

/-! Actual order-160 component moments with the active radial majorant. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part160 BstLean.Part157
open BstLean.Part150 (hT sT)
open BstLean.Part151 (mask measurable_mask)
open BstLean.Part161 (Ix uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part166 (winC bhat measurable_bhat)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part167 BstLean.Part168 BstLean.Part212
variable {n : ℕ}

/-- A moment premise under the actual independent Gaussian plane coordinates. -/
def PlaneEigenMoment160 (m : ℕ) (P2 : ℝ) : Prop :=
  (∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (planeEigen ξ₁ ξ₂ ^ 80)
    ∂stdGauss (Fin m) ∂stdGauss (Fin m)) ≤ ENNReal.ofReal (P2 ^ 80)

theorem planeEigenMoment160_old {m : ℕ} (hm : (16000 : ℝ) ≤ m) :
    PlaneEigenMoment160 m (planeEnvelope80 m) := by
  apply le_trans _ (plane_eigenmoment80 hm)
  apply lintegral_mono
  intro ξ₁
  apply lintegral_mono
  intro ξ₂
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (planeEigen_nonneg ξ₁ ξ₂) (planeEigen_le_lamP ξ₁ ξ₂) 80


noncomputable def eigenPlaneSquared160 (n : ℕ) (R2 P2 : ℝ) : ℝ :=
  exactRadius (n - 1 - 1) 80 ^ 2 * R2 *
    (2 / (n : ℝ)) * (2 / (mA n : ℝ)) * P2

lemma eigenPlane_power160 (n : ℕ) (R2 P2 : ℝ) :
    exactRadius (n - 1 - 1) 80 ^ 160 * R2 ^ 80 *
      (2 / (n : ℝ) * (2 / (mA n : ℝ))) ^ 80 * P2 ^ 80 =
        eigenPlaneSquared160 n R2 P2 ^ 80 := by
  unfold eigenPlaneSquared160
  simp only [mul_pow, ← pow_mul]
  ring

theorem plane_frame_eigen160 (hn : 4 ≤ n) {R2 P2 : ℝ} (hR : ActiveRadialMoment160 n R2)
    (hP : PlaneEigenMoment160 (mA n) P2)
    {u w : Fin n → ℝ} {s cs : ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + cs ^ 2 = 1) {c : Fin n → ℝ} {r : ℝ}
    (hcu : c = r • u) (τ : ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2))
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') :
    ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, Xint160 c τ (s • u + cs • w) u w Yf A₁ ξ₁ ξ₂
      ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (eigenPlaneSquared160 n R2 P2 ^ 80) := by
  set x := s • u + cs • w with hx
  have hmeas := measurable_planeIntegrand160 c τ x u w hYm
  -- Tonelli: the plane coordinates outside
  have h3 : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ)) ×
      (Fin (mA n) → ℝ) => Xint160 c τ x u w Yf z.1.1 z.1.2 z.2) := by
    have hg : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ)) ×
        (Fin (mA n) → ℝ) => (z.1.1, z.1.2, z.2)) :=
      (measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h4 := hmeas.comp hg
    exact h4
  have hm1 : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
      ∫⁻ ξ₂, Xint160 c τ x u w Yf z.1 z.2 ξ₂ ∂stdGauss (Fin (mA n))) := h3.lintegral_prod_right'
  rw [lintegral_lintegral_swap hm1.aemeasurable]
  have hsw : ∀ ξ₁ : Fin (mA n) → ℝ,
      ∫⁻ A₁, ∫⁻ ξ₂, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂ ∂stdGauss (Fin (mA n))
        ∂gaussMat (mA n) n (2 / (n : ℝ)) =
      ∫⁻ ξ₂, ∫⁻ A₁, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ))
        ∂stdGauss (Fin (mA n)) := by
    intro ξ₁
    have hg : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (mA n) → ℝ) =>
        (z.1, ξ₁, z.2)) := measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
    have hm2 := hmeas.comp hg
    exact lintegral_lintegral_swap hm2.aemeasurable
  rw [lintegral_congr hsw]
  set Kd : ℝ := exactRadius (n - 1 - 1) 80 ^ 160 * R2 ^ 80 *
      (2 / (n : ℝ) * (2 / (mA n : ℝ))) ^ 80 with hKd
  have hKd0 : 0 ≤ Kd := by
    dsimp only [Kd]
    exact mul_nonneg (mul_nonneg (Even.pow_nonneg (by decide) _)
      (Even.pow_nonneg (by decide) _)) (Even.pow_nonneg (by decide) _)
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ,
      ∫⁻ A₁, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
        ENNReal.ofReal Kd * ENNReal.ofReal (planeEigen ξ₁ ξ₂ ^ 80) := by
    intro ξ₁ ξ₂
    rw [← ENNReal.ofReal_mul hKd0]
    exact inner_frame_eigen160 hn hR hu hw huw hsc hcu τ Yf hY1 hYadm ξ₁ ξ₂
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ A₁, Xint160 c τ x u w Yf A₁ ξ₁ ξ₂
        ∂gaussMat (mA n) n (2 / (n : ℝ)) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal Kd * ENNReal.ofReal (planeEigen ξ₁ ξ₂ ^ 80)
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal Kd * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (planeEigen ξ₁ ξ₂ ^ 80)
        ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal Kd * ENNReal.ofReal (P2 ^ 80) :=
        mul_le_mul_right hP _
    _ = ENNReal.ofReal (eigenPlaneSquared160 n R2 P2 ^ 80) := by
        rw [← ENNReal.ofReal_mul hKd0, hKd, eigenPlane_power160 n R2 P2]

/-- **The plane moment `X_ℓ`** (`planeMoment160`, the remaining sub-lemma 5 of Lemma LJ). -/
theorem planeMoment_eigen160 (hn : 4 ≤ n) {R2 P2 : ℝ} (hR : ActiveRadialMoment160 n R2)
    (hP : PlaneEigenMoment160 (mA n) P2)
    {c : Fin n → ℝ} (hc : c ≠ 0) (τ : ℝ) (a : Ix n) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ)
    (hYm : Measurable (fun z : Matrix (Fin (mA n)) (Fin n) ℝ ×
      ((Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) => Yf z.1 z.2))
    (hY1 : ∀ A p, normSq (Yf A p) ≤ 1)
    (hYadm : ∀ A A', sT n A c τ = sT n A' c τ → Yf A = Yf A') :
    planeMoment160 c τ a v Yf ≤ ENNReal.ofReal (eigenPlaneSquared160 n R2 P2 ^ 80) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hu, hw, huw⟩ := frame_orth hn1 hc hv
  have hs2 : latitude (n := n) (√(normSq c)) τ a ^ 2 ≤ 1 := BstLean.Part162.latitude_sq_le _ _ _
  have hsc : latitude (n := n) (√(normSq c)) τ a ^ 2 +
      √(1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith)]; ring
  have hx := BstLean.Part161.xLat_eq hn1 (c := rc c) hc (latitude (n := n) (√(normSq c)) τ a)
    (unitF53 v)
  have hcu : c = √(normSq c) • uHat (rc c) := by
    have e : (rc c).1.2 = c := rfl
    have hc0 : √(normSq c) ≠ 0 := by
      intro h0
      have hu0 : uHat (rc c) = 0 := by
        unfold uHat; rw [e, h0, _root_.inv_zero, zero_smul]
      rw [hu0] at hu
      simp [normSq] at hu
    unfold uHat
    rw [e, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hX : planeMoment160 c τ a v Yf = ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂,
      Xint160 c τ (latitude (n := n) (√(normSq c)) τ a • uHat (rc c) +
        √(1 - latitude (n := n) (√(normSq c)) τ a ^ 2) • dirW (rc c) (unitF53 v))
        (uHat (rc c)) (dirW (rc c) (unitF53 v)) Yf A₁ ξ₁ ξ₂
      ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
    unfold planeMoment160 Xint160
    rw [hx]
    rfl
  rw [hX]
  exact plane_frame_eigen160 hn hR hP hu hw huw hsc hcu τ Yf hYm hY1 hYadm

theorem planeMoments_eigen160 (hn : 8000 ≤ n) {R2 P2 : ℝ} (hR : ActiveRadialMoment160 n R2)
    (hP : PlaneEigenMoment160 (mA n) P2)
    {c : Fin n → ℝ} {τ : ℝ} (hwin : winC c τ) (a : Ix n)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    planeMoment160 c τ a v (fun A => YF A c τ) ≤
      ENNReal.ofReal (eigenPlaneSquared160 n R2 P2 ^ 80) ∧
    planeMoment160 c τ a v (fun A => YS A c τ) ≤
      ENNReal.ofReal (eigenPlaneSquared160 n R2 P2 ^ 80) := by
  have hc := window_c_ne (by omega) hwin
  constructor
  · exact planeMoment_eigen160 (by omega) hR hP hc τ a hv _ (measurable_YF_joint c τ)
      (fun A p => normSq_bhat_le _) (fun A A' h => YF_adm c τ h)
  · exact planeMoment_eigen160 (by omega) hR hP hc τ a hv _ (measurable_YS_joint c τ)
      (fun A p => normSq_bhat_le _) (fun A A' h => YS_adm c τ h)
lemma eigenPlane_pos160 (hn : 8000 ≤ n) {R2 P2 : ℝ} (hR0 : 0 < R2) (hP0 : 0 < P2) :
    0 < eigenPlaneSquared160 n R2 P2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR : (0 : ℝ) < mA n := by unfold mA; positivity
  have hdR : (2 : ℝ) ≤ (n - 1 - 1 : ℕ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have he : 0 < exactRadius (n - 1 - 1) 80 := by
    unfold exactRadius
    exact div_pos (rpow_pos_of_pos (radialProduct_pos (by omega) 80) _)
      (sqrt_pos.mpr (by linarith))
  unfold eigenPlaneSquared160
  positivity

noncomputable def eigenJacobianSquared160 (n : ℕ) (R2 P2 : ℝ) : ℝ :=
  jacobianConstantSquared160 n (eigenPlaneSquared160 n R2 P2) (frobEnvelopeSquared160 n)

variable (hn : 8000 ≤ n) {R2 P2 : ℝ} (hR0 : 0 < R2) (hR : ActiveRadialMoment160 n R2)
    (hP0 : 0 < P2) (hP : PlaneEigenMoment160 (mA n) P2)

include hn hR hP in
theorem eigenComponentMoments160 :
    ComponentMoments160 n (eigenPlaneSquared160 n R2 P2) (frobEnvelopeSquared160 n) := by
  intro c τ hw a v hv
  have hX := planeMoments_eigen160 hn hR hP hw a hv
  exact ⟨hX.1, hX.2, frobMoment_bound160 hn hw a hv⟩

include hn hR0 hR hP0 hP in
theorem eigenJacobianMoment160 : JacobianMoment160 n (eigenJacobianSquared160 n R2 P2) :=
  assemble_jacobian160 (by omega) (eigenPlane_pos160 hn hR0 hP0)
    (frobEnvelope_pos160 (by omega)) (eigenComponentMoments160 hn hR hP)

include hn hR0 hR hP0 hP in
theorem eigenLatitudeMoment160 : LatitudeMoment160 n (eigenJacobianSquared160 n R2 P2) :=
  latitudeMoment160_of_jacobian (by omega) (eigenJacobianMoment160 hn hR0 hR hP0 hP)

include hn hR0 hP0 in
theorem eigenJacobianSquared_pos160 : 0 < eigenJacobianSquared160 n R2 P2 := by
  have hX := eigenPlane_pos160 hn hR0 hP0
  have hY := frobEnvelope_pos160 (by omega : 2 ≤ n)
  have hZ := operatorEnvelope_pos160 (by omega : 1 ≤ n)
  have hC := transverseConstant_pos160
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR : (0 : ℝ) < mA n := by unfold mA; positivity
  unfold eigenJacobianSquared160 jacobianConstantSquared160
  positivity

end BstLean.Part221
