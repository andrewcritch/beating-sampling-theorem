import BstLean.Part71Defs
import BstLean.Part46CharFn_Spectral
import BstLean.Part71QT1_Scalar

/-! Part 71, Theorem QT1, Gaussian pieces: the moment generating function of a Gaussian
quadratic form, and its bound by `exp(8‖B‖_F²/n²)`. -/

namespace BstLean.Part71

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss qformι)

/-- The product formula for a diagonal Gaussian quadratic form. -/
theorem gauss_quad_mgf (n : ℕ) (t : Fin n → ℝ) (ht : ∀ i, t i < 1 / 2) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (∑ i, t i * y i ^ 2)) ∂stdGauss (Fin n) =
      ∏ i, ENNReal.ofReal (Real.sqrt (1 / (1 - 2 * t i))) := by
  have hpt : ∀ y : Fin n → ℝ, ENNReal.ofReal (Real.exp (∑ i, t i * y i ^ 2)) =
      ∏ i, ENNReal.ofReal (Real.exp (t i * y i ^ 2)) := by
    intro y
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  simp_rw [hpt]
  unfold stdGauss
  have hX : ∀ i, Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (t i * y ^ 2))) :=
    fun i => by fun_prop
  have hind := iIndepFun_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (X := fun i (y : ℝ) => ENNReal.ofReal (Real.exp (t i * y ^ 2)))
    (fun i => (hX i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hX i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← gauss1d_mgf (t i) (ht i)]
  exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).lintegral_comp (hX i)

/-- The Gaussian bound: `E_γ exp(2 gᵀBg/n) ≤ exp(8‖B‖_F²/n²)` for a symmetric traceless `B`
with largest eigenvalue at most `n/8`. -/
theorem gauss_quad_bound (n : ℕ) (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (htr : B.trace = 0)
    (hmax : ∀ v : Fin n → ℝ, qf B v ≤ (n : ℝ) / 8 * ∑ i, v i ^ 2) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (2 * qf B g / n)) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (Real.exp (8 * frobM B / (n : ℝ) ^ 2)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set lam := hB.eigenvalues with hlam
  have hl : ∀ i, lam i ≤ n / 8 := by
    intro i
    have h1 := hmax (WithLp.ofLp (hB.eigenvectorBasis i))
    have hq : qf B (WithLp.ofLp (hB.eigenvectorBasis i)) = lam i := by
      rw [show qf B (WithLp.ofLp (hB.eigenvectorBasis i)) =
        qformι B (WithLp.ofLp (hB.eigenvectorBasis i)) from rfl,
        BstLean.Part46.CharFn.qform_eigenbasis B hB]
      simp [hlam]
    have hs : ∑ k, (WithLp.ofLp (hB.eigenvectorBasis i)) k ^ 2 = 1 := by
      rw [← BstLean.Part46.CharFn.linear_norm_eigenbasis hB.eigenvectorBasis]
      simp
    rw [hq, hs, mul_one] at h1
    exact h1
  have hsum : ∑ i, lam i = 0 := by
    have := hB.trace_eq_sum_eigenvalues
    rw [htr] at this
    simpa [hlam] using this.symm
  have hfrob : frobM B = ∑ i, lam i ^ 2 := BstLean.Part46.CharFn.frob_eigenvalues B hB
  let t : Fin n → ℝ := fun i => 2 * lam i / n
  have ht4 : ∀ i, t i ≤ 1 / 4 := by
    intro i
    have := hl i
    simp only [t]
    rw [div_le_iff₀ hnpos]
    nlinarith
  have ht : ∀ i, t i < 1 / 2 := fun i => by linarith [ht4 i]
  have hpt : ∀ g : Fin n → ℝ, ENNReal.ofReal (Real.exp (2 * qf B g / n)) =
      (fun y : Fin n → ℝ => ENNReal.ofReal (Real.exp (∑ i, t i * y i ^ 2)))
        (WithLp.ofLp (hB.eigenvectorBasis.repr (WithLp.toLp 2 g))) := by
    intro g
    simp only
    congr 2
    rw [show qf B g = qformι B g from rfl, BstLean.Part46.CharFn.qform_eigenbasis B hB,
      Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [t, hlam]
    ring
  rw [lintegral_congr hpt]
  rw [(BstLean.Part46.CharFn.gaussian_basis_preserving hB.eigenvectorBasis).lintegral_comp
    (f := fun y : Fin n → ℝ => ENNReal.ofReal (Real.exp (∑ i, t i * y i ^ 2))) (by fun_prop),
    gauss_quad_mgf n t ht]
  calc ∏ i, ENNReal.ofReal (Real.sqrt (1 / (1 - 2 * t i)))
      ≤ ∏ i, ENNReal.ofReal (Real.exp ((2 * t i + (2 * t i) ^ 2) / 2)) := by
        refine Finset.prod_le_prod' (fun i _ => ENNReal.ofReal_le_ofReal ?_)
        apply sqrt_inv_le_exp
        linarith [ht4 i]
    _ = ENNReal.ofReal (Real.exp (∑ i, (2 * t i + (2 * t i) ^ 2) / 2)) := by
        rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    _ = ENNReal.ofReal (Real.exp (8 * frobM B / (n : ℝ) ^ 2)) := by
        congr 2
        have : ∀ i, (2 * t i + (2 * t i) ^ 2) / 2 = 2 / n * lam i + 8 / (n : ℝ) ^ 2 * lam i ^ 2 := by
          intro i; simp only [t]; field_simp; ring
        simp_rw [this]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, hfrob]
        ring

end BstLean.Part71
