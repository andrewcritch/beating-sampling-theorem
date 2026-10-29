import BstLean.Part206MA

/-! A finite-difference proof of the sharp MA row Lipschitz bound. The proof
includes ReLU gate boundaries and requires no pointwise derivative of a gate. -/
namespace BstLean.Part206
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part154
open BstLean.Part153 (nrm)

theorem relu_increment (a b : ℝ) :
    min 0 (a - b) ≤ relu a - relu b ∧ relu a - relu b ≤ max 0 (a - b) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> constructor <;> linarith

theorem psi_increment (s a b : ℝ) :
    min 0 (a - b) ≤ BstLean.Part137.psiS s a - BstLean.Part137.psiS s b ∧
    BstLean.Part137.psiS s a - BstLean.Part137.psiS s b ≤ max 0 (a - b) := by
  have hiA := BstLean.Part137.integrable_relu_shift a s
  have hiB := BstLean.Part137.integrable_relu_shift b s
  have he : BstLean.Part137.psiS s a - BstLean.Part137.psiS s b =
      ∫ z, (relu (a + s * z) - relu (b + s * z)) ∂gaussianReal 0 1 := by
    unfold BstLean.Part137.psiS
    rw [integral_sub hiA hiB]
  have hp := fun z : ℝ => relu_increment (a + s * z) (b + s * z)
  have hsub : ∀ z : ℝ, a + s * z - (b + s * z) = a - b := by intro z; ring
  simp_rw [hsub] at hp
  rw [he]
  constructor
  · have h := integral_mono (integrable_const (min 0 (a - b))) (hiA.sub hiB)
      (fun z => (hp z).1)
    simpa using h
  · have h := integral_mono (hiA.sub hiB) (integrable_const (max 0 (a - b)))
      (fun z => (hp z).2)
    simpa using h

/-- Moving an interval by a residual costs only the absolute residual. -/
theorem increment_error {a b v e : ℝ}
    (he : min 0 v ≤ e ∧ e ≤ max 0 v) :
    |(relu a - relu b) - e| ≤ |v| + |(a - b) - v| := by
  obtain ⟨hl, hu⟩ := relu_increment a b
  have hr := abs_le.mp (le_refl (|(a - b) - v|))
  have hv := abs_le.mp (le_refl |v|)
  rw [abs_le]
  rcases le_total 0 v with hv0 | hv0
  · rw [min_eq_left hv0, max_eq_right hv0] at he
    rcases le_total 0 (a - b) with hd | hd
    · simp only [min_eq_left hd, max_eq_right hd] at hl hu
      constructor <;> linarith
    · simp only [min_eq_right hd, max_eq_left hd] at hl hu
      constructor <;> linarith
  · rw [min_eq_right hv0, max_eq_left hv0] at he
    rcases le_total 0 (a - b) with hd | hd
    · simp only [min_eq_left hd, max_eq_right hd] at hl hu
      constructor <;> linarith
    · simp only [min_eq_right hd, max_eq_left hd] at hl hu
      constructor <;> linarith

theorem MF_relu_integrable {d m : ℕ} {f : (Fin d → ℝ) → Fin m → ℝ}
    {L pg : ℝ} (H : MFHyp (BstLean.Part29.stdGauss (Fin d)) f L pg) (z : Fin m → ℝ) :
    Integrable (fun x => relu (z ⬝ᵥ f x)) (BstLean.Part29.stdGauss (Fin d)) := by
  apply (H.int_dot z).1.abs.mono'
    (continuous_relu.measurable.comp (H.meas_dot z)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖relu (z ⬝ᵥ f x)‖ ≤ |z ⬝ᵥ f x|
  rw [Real.norm_eq_abs, abs_of_nonneg (by simp [relu] : 0 ≤ relu (z ⬝ᵥ f x))]
  exact max_le (abs_nonneg _) (le_abs_self _)

/-- The sharp row constant is the mean norm plus the covariance radius. -/
theorem DF_sharp_lipschitz {d m : ℕ} {f : (Fin d → ℝ) → Fin m → ℝ}
    {L pg : ℝ} (H : MFHyp (BstLean.Part29.stdGauss (Fin d)) f L pg)
    (z z' : Fin m → ℝ) :
    |DF (BstLean.Part29.stdGauss (Fin d)) f z -
      DF (BstLean.Part29.stdGauss (Fin d)) f z'| ≤
      (nrm (fbar (BstLean.Part29.stdGauss (Fin d)) f) + L) * nrm (z - z') := by
  let μ := BstLean.Part29.stdGauss (Fin d)
  let v := (z - z') ⬝ᵥ fbar μ f
  let residual := fun x => (z - z') ⬝ᵥ f x - v
  let e := BstLean.Part137.psiS (sF μ f) (z ⬝ᵥ fbar μ f) -
    BstLean.Part137.psiS (sF μ f) (z' ⬝ᵥ fbar μ f)
  have he : min 0 v ≤ e ∧ e ≤ max 0 v := by
    simpa only [v, e, sub_dotProduct] using
      psi_increment (sF μ f) (z ⬝ᵥ fbar μ f) (z' ⬝ᵥ fbar μ f)
  have hrLp : MemLp residual 2 μ := (H.dotL2 (z - z')).sub (memLp_const v)
  have hrI := hrLp.integrable one_le_two
  have hrI2 : Integrable (fun x => |residual x| ^ 2) μ := by
    simp_rw [sq_abs]
    exact (memLp_two_iff_integrable_sq hrLp.aestronglyMeasurable).mp hrLp
  have hrM := H.M1 (z - z')
  change (∫ x, residual x ^ 2 ∂μ) ≤ L ^ 2 * normSq (z - z') at hrM
  have hrJ := mean_sq_le_second hrI.abs hrI2
  simp only [sq_abs] at hrJ
  have hrBound : (∫ x, |residual x| ∂μ) ≤ L * nrm (z - z') := by
    have hnn : 0 ≤ L * nrm (z - z') := mul_nonneg H.hℓ.le
      (BstLean.Part153.nrm_nonneg _)
    have hsq : (L * nrm (z - z')) ^ 2 = L ^ 2 * normSq (z - z') := by
      rw [mul_pow, BstLean.Part153.nrm_sq]
    nlinarith [hrJ.trans hrM]
  have hiZ := MF_relu_integrable H z
  have hiZ' := MF_relu_integrable H z'
  have hBound := fun x : Fin d → ℝ => increment_error
    (a := z ⬝ᵥ f x) (b := z' ⬝ᵥ f x) he
  have hInt : |∫ x, (relu (z ⬝ᵥ f x) - relu (z' ⬝ᵥ f x) - e) ∂μ| ≤
      |v| + ∫ x, |residual x| ∂μ := by
    apply abs_integral_le_integral_abs.trans
    have hPoint : ∀ x, |relu (z ⬝ᵥ f x) - relu (z' ⬝ᵥ f x) - e| ≤
        |v| + |residual x| := by
      intro x
      simpa only [residual, sub_dotProduct] using hBound x
    have h := integral_mono ((hiZ.sub hiZ').sub (integrable_const e)).abs
      ((integrable_const |v|).add hrI.abs) hPoint
    change (∫ x, |relu (z ⬝ᵥ f x) - relu (z' ⬝ᵥ f x) - e| ∂μ) ≤
      ∫ x, (|v| + |residual x|) ∂μ at h
    rw [integral_add (f := fun _ => |v|) (g := fun x => |residual x|)
      (integrable_const |v|) hrI.abs, integral_const] at h
    simpa only [probReal_univ, one_smul] using h
  have heInt : DF μ f z - DF μ f z' =
      ∫ x, (relu (z ⬝ᵥ f x) - relu (z' ⬝ᵥ f x) - e) ∂μ := by
    rw [integral_sub (f := fun x => relu (z ⬝ᵥ f x) - relu (z' ⬝ᵥ f x))
      (g := fun _ => e) (hiZ.sub hiZ') (integrable_const e),
      integral_sub (f := fun x => relu (z ⬝ᵥ f x)) (g := fun x => relu (z' ⬝ᵥ f x)) hiZ hiZ']
    simp only [integral_const, probReal_univ, one_smul, DF, XF, e]
    ring
  rw [heInt]
  have hv := BstLean.Part153.abs_dot_le_nrm (z - z') (fbar μ f)
  change |v| ≤ nrm (z - z') * nrm (fbar μ f) at hv
  calc _ ≤ |v| + ∫ x, |residual x| ∂μ := hInt
    _ ≤ nrm (z - z') * nrm (fbar μ f) + L * nrm (z - z') := add_le_add hv hrBound
    _ = _ := by ring

/-- A scalar row bound gives a Frobenius bound for the norm of all rows. -/
theorem matrix_row_norm_lipschitz {m : ℕ} {φ : (Fin m → ℝ) → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hφ : ∀ z z', |φ z - φ z'| ≤ K * nrm (z - z'))
    (M M' : Matrix (Fin m) (Fin m) ℝ) :
    |nrm (fun i => φ (M i)) - nrm (fun i => φ (M' i))| ≤
      K * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  have hs : normSq ((fun i => φ (M i)) - fun i => φ (M' i)) ≤
      K ^ 2 * ∑ i, ∑ j, (M i j - M' i j) ^ 2 := by
    unfold normSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hφ (M i) (M' i)) 2
    simpa only [sq_abs, mul_pow, BstLean.Part153.nrm_sq, normSq, Pi.sub_apply] using h
  calc _ ≤ nrm ((fun i => φ (M i)) - fun i => φ (M' i)) :=
      BstLean.Part153.abs_nrm_sub_le _ _
    _ ≤ √(K ^ 2 * ∑ i, ∑ j, (M i j - M' i j) ^ 2) := sqrt_le_sqrt hs
    _ = _ := by rw [sqrt_mul (sq_nonneg K), sqrt_sq hK]

/-- The actual MA error has the sharp constant with no gate derivative premise. -/
theorem dC_sharp_lipschitz {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {L pg : ℝ} (H : MFHyp (BstLean.Part29.stdGauss (Fin n)) (fA A c τ) L pg)
    (M M' : Matrix (Fin m) (Fin m) ℝ) :
    |dC A M c τ - dC A M' c τ| ≤
      (√(GamBarF (BstLean.Part29.stdGauss (Fin n)) (fA A c τ)) + L) *
        √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  let s : ℝ := √(2 / (m : ℝ))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < s := sqrt_pos.mpr (by positivity)
  let μ := BstLean.Part29.stdGauss (Fin n)
  let f := fA A c τ
  let K := nrm (fbar μ f) + L
  let φ := fun z : Fin m → ℝ => s * DF μ f (s⁻¹ • z)
  have hK : 0 ≤ K := add_nonneg (BstLean.Part153.nrm_nonneg _) H.hℓ.le
  have hφ : ∀ z z', |φ z - φ z'| ≤ K * nrm (z - z') := by
    intro z z'
    have h := DF_sharp_lipschitz H (s⁻¹ • z) (s⁻¹ • z')
    rw [← smul_sub, BstLean.Part153.nrm_smul, abs_of_pos (inv_pos.mpr hs)] at h
    have h' := mul_le_mul_of_nonneg_left h hs.le
    change s * |DF μ f (s⁻¹ • z) - DF μ f (s⁻¹ • z')| ≤
      s * (K * (s⁻¹ * nrm (z - z'))) at h'
    have he : s * (K * (s⁻¹ * nrm (z - z'))) = K * nrm (z - z') := by
      field_simp
    simpa only [φ, ← mul_sub, abs_mul, abs_of_pos hs, he] using h'
  have he : ∀ M : Matrix (Fin m) (Fin m) ℝ, dC A M c τ = nrm (fun i => φ (M i)) := by
    intro M
    have hv : (fun i => φ (M i)) = s • (hbar2 A M c τ - BstLean.Part150.bO A M c τ) := by
      funext i
      change s * DF μ f (s⁻¹ • M i) = s * _
      rw [DF_row hm A M c τ i]
      rfl
    rw [hv, BstLean.Part153.nrm_smul, abs_of_pos hs]
    rfl
  rw [he M, he M']
  exact matrix_row_norm_lipschitz hK hφ M M'

/-- The sharp MA event has one conditional Gaussian payment. -/
theorem MA_actual_sharp_charge {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {L pg level : ℝ} (H : MFHyp (BstLean.Part29.stdGauss (Fin n)) (fA A c τ) L pg)
    (hl : 0 ≤ level) :
    (gaussMat m m (2 / (m : ℝ))).real
      {M | (∫ M, dC A M c τ ∂gaussMat m m (2 / (m : ℝ))) +
        √(2 * level * (2 / (m : ℝ))) *
          (√(GamBarF (BstLean.Part29.stdGauss (Fin n)) (fA A c τ)) + L) < dC A M c τ}
      ≤ exp (-level) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  exact MA_sharp_charge (by positivity) (add_nonneg (sqrt_nonneg _) H.hℓ.le) hl
    (dC_sharp_lipschitz hm A c τ H)

/-- The sharp MA event implies the source event when the covariance radius fits. -/
theorem MA_actual_event_inclusion {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {L level : ℝ} (hL : L ≤ √(BstLean.Part153.GamS A c τ))
    {M : Matrix (Fin m) (Fin m) ℝ}
    (hEvent : dC A M c τ ≤ (∫ M, dC A M c τ ∂gaussMat m m (2 / (m : ℝ))) +
      √(2 * level * (2 / (m : ℝ))) *
        (√(GamBarF (BstLean.Part29.stdGauss (Fin n)) (fA A c τ)) + L)) :
    M ∉ BadD A c τ level := by
  have hbar : GamBarF (BstLean.Part29.stdGauss (Fin n)) (fA A c τ) ≤
      BstLean.Part153.GamS A c τ := by
    rw [GamBarF_fA, BstLean.Part153.GamS_eq_gO hm]
    exact BstLean.Part153.GamBar_le A c τ
  have hroot := sqrt_le_sqrt hbar
  have hdev := mul_le_mul_of_nonneg_left
    (show √(GamBarF (BstLean.Part29.stdGauss (Fin n)) (fA A c τ)) + L ≤
      2 * √(BstLean.Part153.GamS A c τ) by linarith) (sqrt_nonneg (2 * level * (2 / (m : ℝ))))
  simp only [BadD, mem_setOf_eq, not_lt]
  exact hEvent.trans (add_le_add le_rfl hdev)

#print axioms relu_increment
#print axioms psi_increment
#print axioms increment_error
#print axioms MF_relu_integrable
#print axioms DF_sharp_lipschitz
#print axioms matrix_row_norm_lipschitz
#print axioms dC_sharp_lipschitz
#print axioms MA_actual_sharp_charge
#print axioms MA_actual_event_inclusion
end BstLean.Part206
