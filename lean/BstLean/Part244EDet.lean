import BstLean.Part244Proj

/-! Part 244: the deterministic sharp E-block assembly of Lemma `t7:p04:ti`.
With `S₂A₂L = T + N𝔏`, the main term is centred by `c = t·tr S₂`, and the cross terms pass
through the rank-two projection `Q` onto `S₂A₂(U₂)`. -/
namespace BstLean.Part244
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part152 (opN opN_nonneg)
open BstLean.Part153 (nrm nrm_nonneg nrm_mulVec_le opN_mul_le opN_le_of_bound opN_transpose
  opN_add_le')
open BstLean.Part182 (e4_Q e4_u e4_e2)

lemma opN_smul_le {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) {c : ℝ} (hc : 0 ≤ c) :
    opN (c • M) ≤ c * opN M := by
  refine opN_le_of_bound _ (mul_nonneg hc (opN_nonneg _)) fun w => ?_
  rw [Matrix.smul_mulVec, BstLean.Part153.nrm_smul, abs_of_nonneg hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (nrm_mulVec_le M w) hc

lemma opN_mul3_le {p q r s : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (B : Matrix (Fin q) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin s) ℝ) {a b c : ℝ} (ha : opN A ≤ a) (hb : opN B ≤ b) (hc : opN C ≤ c) :
    opN (A * B * C) ≤ a * b * c := by
  have hb0 : 0 ≤ b := (opN_nonneg _).trans hb
  have ha0 : 0 ≤ a := (opN_nonneg _).trans ha
  refine (opN_mul_le _ _).trans ?_
  refine mul_le_mul ((opN_mul_le _ _).trans (mul_le_mul ha hb (opN_nonneg _) ha0)) hc
    (opN_nonneg _) (mul_nonneg ha0 hb0)

/-- **Deterministic sharp E block.** -/
theorem eb_Eblock_sharp {r a a' D : ℕ} (T : Matrix (Fin r) (Fin a) ℝ)
    (T' : Matrix (Fin r) (Fin a') ℝ) (N : Matrix (Fin r) (Fin D) ℝ)
    (L : Matrix (Fin D) (Fin a) ℝ) (L' : Matrix (Fin D) (Fin a') ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ) (hQs : Qᵀ = Q) (hQT : Q * T = T) (hQT' : Q * T' = T')
    {τ₁ ζ ℓ g c lam : ℝ} (hc : 0 ≤ c)
    (hT : opN T ≤ τ₁) (hT' : opN T' ≤ τ₁) (hQN : opN (Q * N) ≤ ζ)
    (hL : opN L ≤ ℓ) (hL' : opN L' ≤ ℓ)
    (hg : opN (Nᵀ * N - c • (1 : Matrix (Fin D) (Fin D) ℝ)) ≤ g) (hLL : opN (Lᵀ * L') ≤ lam) :
    opN ((T + N * L)ᵀ * (T' + N * L')) ≤ τ₁ ^ 2 + 2 * τ₁ * ζ * ℓ + g * ℓ ^ 2 + c * lam := by
  have e : (T + N * L)ᵀ * (T' + N * L') =
      Tᵀ * T' + Tᵀ * (Q * N) * L' + Lᵀ * (Q * N)ᵀ * T' +
        (Lᵀ * (Nᵀ * N - c • (1 : Matrix (Fin D) (Fin D) ℝ)) * L' + c • (Lᵀ * L')) := by
    have e1 : Tᵀ * (Q * N) * L' = Tᵀ * (N * L') := by
      conv_rhs => rw [← hQT]
      rw [Matrix.transpose_mul, hQs]; simp only [Matrix.mul_assoc]
    have e2 : Lᵀ * (Q * N)ᵀ * T' = (N * L)ᵀ * T' := by
      conv_rhs => rw [← hQT']
      rw [Matrix.transpose_mul, Matrix.transpose_mul, hQs]; simp only [Matrix.mul_assoc]
    have e3 : Lᵀ * (Nᵀ * N - c • (1 : Matrix (Fin D) (Fin D) ℝ)) * L' + c • (Lᵀ * L') =
        (N * L)ᵀ * (N * L') := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      abel
    rw [e1, e2, e3, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  rw [e]
  have hτ0 : 0 ≤ τ₁ := (opN_nonneg _).trans hT
  have hζ0 : 0 ≤ ζ := (opN_nonneg _).trans hQN
  have hℓ0 : 0 ≤ ℓ := (opN_nonneg _).trans hL
  have hTt : opN Tᵀ ≤ τ₁ := by rw [opN_transpose]; exact hT
  have hLt : opN Lᵀ ≤ ℓ := by rw [opN_transpose]; exact hL
  have hQNt : opN (Q * N)ᵀ ≤ ζ := by rw [opN_transpose]; exact hQN
  have h1 : opN (Tᵀ * T') ≤ τ₁ * τ₁ :=
    (opN_mul_le _ _).trans (mul_le_mul hTt hT' (opN_nonneg _) hτ0)
  have h2 : opN (Tᵀ * (Q * N) * L') ≤ τ₁ * ζ * ℓ := opN_mul3_le _ _ _ hTt hQN hL'
  have h3 : opN (Lᵀ * (Q * N)ᵀ * T') ≤ ℓ * ζ * τ₁ := opN_mul3_le _ _ _ hLt hQNt hT'
  have h4 : opN (Lᵀ * (Nᵀ * N - c • (1 : Matrix (Fin D) (Fin D) ℝ)) * L') ≤ ℓ * g * ℓ :=
    opN_mul3_le _ _ _ hLt hg hL'
  have h5 : opN (c • (Lᵀ * L')) ≤ c * lam :=
    (opN_smul_le _ hc).trans (mul_le_mul_of_nonneg_left hLL hc)
  calc _ ≤ opN (Tᵀ * T' + Tᵀ * (Q * N) * L' + Lᵀ * (Q * N)ᵀ * T') +
        opN (Lᵀ * (Nᵀ * N - c • (1 : Matrix (Fin D) (Fin D) ℝ)) * L' + c • (Lᵀ * L')) :=
        opN_add_le' _ _
    _ ≤ (opN (Tᵀ * T') + opN (Tᵀ * (Q * N) * L') + opN (Lᵀ * (Q * N)ᵀ * T')) +
        (opN (Lᵀ * (Nᵀ * N - c • (1 : Matrix (Fin D) (Fin D) ℝ)) * L') + opN (c • (Lᵀ * L'))) :=
        add_le_add ((opN_add_le' _ _).trans (add_le_add (opN_add_le' _ _) le_rfl))
          (opN_add_le' _ _)
    _ ≤ _ := by nlinarith

/-- A `{0,1}` diagonal fixing two vectors fixes the Gram–Schmidt projection onto their span. -/
lemma e4_Q_mul_diag {k : ℕ} (d : Fin k → ℝ) (z₁ z₂ : Fin k → ℝ)
    (h₁ : Matrix.diagonal d *ᵥ z₁ = z₁) (h₂ : Matrix.diagonal d *ᵥ z₂ = z₂) :
    e4_Q z₁ z₂ * Matrix.diagonal d = e4_Q z₁ z₂ := by
  have hu : Matrix.diagonal d *ᵥ e4_u z₁ = e4_u z₁ := by
    unfold e4_u; rw [Matrix.mulVec_smul, h₁]
  have he : Matrix.diagonal d *ᵥ e4_e2 z₁ z₂ = e4_e2 z₁ z₂ := by
    unfold e4_e2 e4_u
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, h₂]
    congr 2
    rw [show e4_u z₁ = (nrm z₁)⁻¹ • z₁ from rfl] at hu
    rw [hu]
  have hfix : ∀ w : Fin k → ℝ, Matrix.diagonal d *ᵥ w = w →
      vecMulVec w w * Matrix.diagonal d = vecMulVec w w := by
    intro w hw
    ext i j
    rw [Matrix.mul_diagonal]
    simp only [vecMulVec_apply]
    rw [mul_assoc]
    congr 1
    have := congrFun hw j
    rw [Matrix.mulVec_diagonal] at this
    rw [mul_comm]; exact this
  unfold e4_Q
  rw [Matrix.add_mul, hfix _ hu, hfix _ he]

end BstLean.Part244
