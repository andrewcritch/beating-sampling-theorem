import BstLean.Part167Conc

/-!
# Part 167 (file `Gam`): the transverse integral of `latSq` (sub-lemma 6 applied)

No proof is left open; no `native_decide` or `axiom` is used.

For an orthonormal pair `(u, w)` of `ℝⁿ`, `Pmat u w = 1 − uuᵀ − wwᵀ` (the paper's `P_lat`):

* **`latSq_eq`**: `latSq g u w = |P_lat g|²`.
* **`gamma_step`**: for a matrix `D` (`m × n`, the paper's `D₁A₁`), vectors `h, r, p` of `ℝ^m` and
  `s ≥ 0`, `E_γ latSq((p + perp h (perp r (sγ)))ᵀD)^{64} ≤
  (√(latSq(pᵀD) + s²‖P_lat Dᵀ‖²_F) + C·s·‖D‖_op)^{128}`, `C = (π/2)(E|g|^{128})^{1/128}`
  (paper: `√(|M₀p|² + s_y²‖M₀‖²_HS) + k_ℓ s_y‖M₀‖_op`).
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm nrm_nonneg nrm_mulVec_le)

variable {n m : ℕ}

/-- `P_lat = 1 − uuᵀ − wwᵀ`. -/
noncomputable def Pmat (u w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - Matrix.vecMulVec u u - Matrix.vecMulVec w w

lemma vmv_mulVec {p q : ℕ} (a : Fin p → ℝ) (b g : Fin q → ℝ) :
    Matrix.vecMulVec a b *ᵥ g = (∑ i, g i * b i) • a := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring

lemma Pmat_mulVec (u w g : Fin n → ℝ) :
    Pmat u w *ᵥ g = g - (∑ i, g i * u i) • u - (∑ i, g i * w i) • w := by
  rw [Pmat, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, vmv_mulVec, vmv_mulVec]

/-- **`latSq g u w = |P_lat g|²`** for an orthonormal pair. -/
theorem latSq_eq {u w : Fin n → ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (g : Fin n → ℝ) :
    latSq g u w = normSq (Pmat u w *ᵥ g) := by
  rw [Pmat_mulVec]
  set a := ∑ i, g i * u i
  set b := ∑ i, g i * w i
  unfold latSq normSq
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have e : ∀ i, (g i - a * u i - b * w i) ^ 2 = g i ^ 2 - 2 * a * (g i * u i) - 2 * b * (g i * w i)
      + a ^ 2 * u i ^ 2 + b ^ 2 * w i ^ 2 + 2 * a * b * (u i * w i) := fun i => by ring
  simp_rw [e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold normSq at hu hw
  rw [hu, hw, huw]
  ring

lemma nrm_Pmat_le {u w : Fin n → ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (g : Fin n → ℝ) : nrm (Pmat u w *ᵥ g) ≤ nrm g := by
  unfold nrm
  apply Real.sqrt_le_sqrt
  rw [← latSq_eq hu hw huw]
  unfold latSq normSq
  nlinarith [sq_nonneg (∑ i, g i * u i), sq_nonneg (∑ i, g i * w i)]

lemma projPerp_mulVec (b z : Fin m → ℝ) : projPerp b *ᵥ z = perp b z := by
  rw [projPerp, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vmv_mulVec,
    smul_smul]
  rfl

lemma perp_smul (b z : Fin m → ℝ) (s : ℝ) : perp b (s • z) = s • perp b z := by
  rw [← projPerp_mulVec, ← projPerp_mulVec, Matrix.mulVec_smul]

lemma normSq_perp_le (b z : Fin m → ℝ) : normSq (perp b z) ≤ normSq z := by
  unfold perp normSq
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  set B := ∑ i, b i ^ 2
  set c := ∑ j, z j * b j
  rcases (show 0 ≤ B from Finset.sum_nonneg fun i _ => sq_nonneg _).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have e : ∀ i, (z i - B⁻¹ * c * b i) ^ 2 = z i ^ 2 - 2 * (B⁻¹ * c) * (z i * b i) +
        (B⁻¹ * c) ^ 2 * b i ^ 2 := fun i => by ring
    simp_rw [e]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : -(2 * (B⁻¹ * c) * c) + (B⁻¹ * c) ^ 2 * B = -(B⁻¹ * c ^ 2) := by
      field_simp; ring
    have h2 : 0 ≤ B⁻¹ * c ^ 2 := by positivity
    linarith

lemma nrm_perp_le (b z : Fin m → ℝ) : nrm (perp b z) ≤ nrm z :=
  Real.sqrt_le_sqrt (normSq_perp_le b z)

/-- `‖M‖²_F`. -/
noncomputable def frobSq {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

lemma frobSq_nonneg {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : 0 ≤ frobSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `‖M Π‖_F ≤ ‖M‖_F` for `Π = P_{h⊥} P_{r⊥}`. -/
lemma frobSq_mul_proj_le {p : ℕ} (M : Matrix (Fin p) (Fin m) ℝ) (h r : Fin m → ℝ) :
    frobSq (M * projPerp h * projPerp r) ≤ frobSq M := by
  unfold frobSq
  refine Finset.sum_le_sum fun i _ => ?_
  have e : (fun j => (M * projPerp h * projPerp r) i j) =
      vecMul (vecMul (M i) (projPerp h)) (projPerp r) := by
    funext j; rw [Matrix.mul_assoc]; simp [Matrix.mul_apply, vecMul, dotProduct]
    simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∀ y : Fin m → ℝ, vecMul y (projPerp h) = perp h y := vecMul_projPerp h
  have h1 : ∑ j, (M * projPerp h * projPerp r) i j ^ 2 =
      normSq (perp r (perp h (M i))) := by
    unfold normSq
    rw [← e2, ← vecMul_projPerp r, ← e]
  rw [h1]
  exact (normSq_perp_le _ _).trans (normSq_perp_le _ _)

/-- **The transverse integral of `latSq`.** -/
theorem gamma_step {u w : Fin n → ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (D : Matrix (Fin m) (Fin n) ℝ) (h r p : Fin m → ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    ∫⁻ γ, ENNReal.ofReal (latSq (vecMul (p + perp h (perp r (s • γ))) D) u w ^ 64)
        ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((√(latSq (vecMul p D) u w + s ^ 2 * frobSq (Pmat u w * Dᵀ)) +
        π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) * (s * opN D)) ^ 128) := by
  set a := Pmat u w *ᵥ vecMul p D
  set B : Matrix (Fin n) (Fin m) ℝ := s • (Pmat u w * Dᵀ * projPerp h * projPerp r) with hB
  have hBv : ∀ γ, B *ᵥ γ = Pmat u w *ᵥ vecMul (perp h (perp r (s • γ))) D := by
    intro γ
    rw [hB, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, projPerp_mulVec, projPerp_mulVec, Matrix.mulVec_transpose,
      perp_smul, perp_smul, Matrix.smul_vecMul, Matrix.mulVec_smul]
  have hpt : ∀ γ, ENNReal.ofReal (latSq (vecMul (p + perp h (perp r (s • γ))) D) u w ^ 64) =
      ENNReal.ofReal (nrm (a + B *ᵥ γ) ^ 128) := by
    intro γ
    rw [Matrix.add_vecMul, latSq_eq hu hw huw, Matrix.mulVec_add, ← hBv]
    unfold nrm
    rw [show (128 : ℕ) = 2 * 64 from rfl, pow_mul, Real.sq_sqrt (normSq_nonneg _)]
  rw [lintegral_congr hpt]
  have hD0 := BstLean.Part152.opN_nonneg D
  have hL : ∀ z, nrm (B *ᵥ z) ≤ (s * opN D) * nrm z := by
    intro z
    rw [hBv]
    refine (nrm_Pmat_le hu hw huw _).trans ?_
    rw [← Matrix.mulVec_transpose]
    refine (nrm_mulVec_le _ _).trans ?_
    rw [BstLean.Part153.opN_transpose]
    have h1 : nrm (perp h (perp r (s • z))) ≤ s * nrm z := by
      refine (nrm_perp_le _ _).trans ((nrm_perp_le _ _).trans (le_of_eq ?_))
      rw [BstLean.Part153.nrm_smul, abs_of_nonneg hs]
    calc opN D * nrm (perp h (perp r (s • z))) ≤ opN D * (s * nrm z) :=
          mul_le_mul_of_nonneg_left h1 hD0
      _ = s * opN D * nrm z := by ring
  refine (trans_mom a B (mul_nonneg hs hD0) hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hV : normSq a + ∑ i, ∑ j, B i j ^ 2 ≤
      latSq (vecMul p D) u w + s ^ 2 * frobSq (Pmat u w * Dᵀ) := by
    rw [latSq_eq hu hw huw]
    have e : ∑ i, ∑ j, B i j ^ 2 = s ^ 2 * frobSq (Pmat u w * Dᵀ * projPerp h * projPerp r) := by
      unfold frobSq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hB, Matrix.smul_apply, smul_eq_mul, mul_pow]
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left (frobSq_mul_proj_le (Pmat u w * Dᵀ) h r) (sq_nonneg s)
    linarith
  have hC0 : 0 ≤ π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) * (s * opN D) :=
    mul_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (BstLean.Part162.gmom_nonneg 128) _)) (mul_nonneg hs hD0)
  exact pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) hC0)
    (by linarith [Real.sqrt_le_sqrt hV]) 128

end BstLean.Part167
