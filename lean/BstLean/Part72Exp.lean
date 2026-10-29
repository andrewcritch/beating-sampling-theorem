import BstLean.Part71QT1_Gauss
import BstLean.Part71QT1_Sphere

/-!
# Part 72: the exponential moment of two directions on the sphere

For unit vectors `v, w`, `t, a ≥ 0` and `2(t + a) < n`:
`E_σ exp(t(v·x)² + a(w·x)²) ≤ 1/(1 − 2(t+a)/n)` (`sphere_two_dir`).
Route (omOV-opus Lemma E2): `sphere_le_gauss` (Part 71), the eigenbasis of the rank-two matrix
`B = (t vvᵀ + a wwᵀ)/2` (eigenvalues `λ_i ≥ 0`, `Σ λ_i = (t+a)/2`), the product formula
`gauss_quad_mgf`, `√y ≤ y` for `y ≥ 1`, and `Π(1 − b_i) ≥ 1 − Σ b_i`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere qformι)
open BstLean.Part71 (qf sphere_le_gauss gauss_quad_mgf)

variable {n : ℕ}

/-- The coordinate `v·x`. -/
def dirv (v x : Fin n → ℝ) : ℝ := ∑ i, v i * x i

/-- The rank-two matrix `(t vvᵀ + a wwᵀ)/2`. -/
noncomputable def rk2 (t a : ℝ) (v w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (t * v i * v j + a * w i * w j) / 2

lemma qf_rk2 (t a : ℝ) (v w x : Fin n → ℝ) :
    qf (rk2 t a v w) x = (t * dirv v x ^ 2 + a * dirv w x ^ 2) / 2 := by
  unfold qf rk2 dirv
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (b : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ b i)
    (h1 : ∀ i ∈ s, b i ≤ 1) : 1 - ∑ i ∈ s, b i ≤ ∏ i ∈ s, (1 - b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hb0 := h0 a (Finset.mem_insert_self a s)
    have hb1 := h1 a (Finset.mem_insert_self a s)
    have hS : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 1 - b a)
    nlinarith

/-- **The Gaussian bound for the rank-two form.** -/
theorem gauss_rk2 (hn : 1 ≤ n) (t a : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (v w : Fin n → ℝ)
    (hv : ∑ i, v i ^ 2 = 1) (hw : ∑ i, w i ^ 2 = 1) (hta : 2 * (t + a) < n) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (2 * qf (rk2 t a v w) g / n)) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (1 / (1 - 2 * (t + a) / n)) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set B := rk2 t a v w with hBdef
  have hB : B.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, hBdef, rk2]
    ring
  set lam := hB.eigenvalues with hlam
  have hl0 : ∀ i, 0 ≤ lam i := by
    intro i
    have hq : qf B (WithLp.ofLp (hB.eigenvectorBasis i)) = lam i := by
      rw [show qf B (WithLp.ofLp (hB.eigenvectorBasis i)) =
        qformι B (WithLp.ofLp (hB.eigenvectorBasis i)) from rfl,
        BstLean.Part46.CharFn.qform_eigenbasis B hB]
      simp [hlam]
    rw [← hq]
    have := qf_rk2 t a v w (WithLp.ofLp (hB.eigenvectorBasis i))
    rw [← hBdef] at this
    rw [this]
    positivity
  have hsum : ∑ i, lam i = (t + a) / 2 := by
    have h := hB.trace_eq_sum_eigenvalues
    have htr : B.trace = (t + a) / 2 := by
      simp only [Matrix.trace, Matrix.diag, hBdef, rk2]
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp_rw [mul_assoc, ← sq]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hv, hw]
      ring
    rw [htr] at h
    simpa [hlam] using h.symm
  let s : Fin n → ℝ := fun i => 2 * lam i / n
  have hs0 : ∀ i, 0 ≤ s i := fun i => by simp only [s]; have := hl0 i; positivity
  have hssum : ∑ i, s i = (t + a) / n := by
    simp only [s]
    rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
    ring
  have hsle : ∀ i, s i ≤ ∑ j, s j := fun i =>
    Finset.single_le_sum (fun j _ => hs0 j) (Finset.mem_univ i)
  have hsmall : (t + a) / n < 1 / 2 := by
    rw [div_lt_iff₀ hnpos]; linarith
  have hs2 : ∀ i, s i < 1 / 2 := fun i => by linarith [hsle i, hssum]
  have hpt : ∀ g : Fin n → ℝ, ENNReal.ofReal (Real.exp (2 * qf B g / n)) =
      (fun y : Fin n → ℝ => ENNReal.ofReal (Real.exp (∑ i, s i * y i ^ 2)))
        (WithLp.ofLp (hB.eigenvectorBasis.repr (WithLp.toLp 2 g))) := by
    intro g
    simp only
    congr 2
    rw [show qf B g = qformι B g from rfl, BstLean.Part46.CharFn.qform_eigenbasis B hB,
      Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [s, hlam]
    ring
  rw [lintegral_congr hpt]
  rw [(BstLean.Part46.CharFn.gaussian_basis_preserving hB.eigenvectorBasis).lintegral_comp
    (f := fun y : Fin n → ℝ => ENNReal.ofReal (Real.exp (∑ i, s i * y i ^ 2))) (by fun_prop),
    gauss_quad_mgf n s hs2]
  have hpos : ∀ i, 0 < 1 - 2 * s i := fun i => by linarith [hs2 i]
  calc ∏ i, ENNReal.ofReal (Real.sqrt (1 / (1 - 2 * s i)))
      ≤ ∏ i, ENNReal.ofReal (1 / (1 - 2 * s i)) := by
        refine Finset.prod_le_prod' (fun i _ => ENNReal.ofReal_le_ofReal ?_)
        have h1 : 1 ≤ 1 / (1 - 2 * s i) := by
          rw [le_div_iff₀ (hpos i)]; linarith [hs0 i]
        calc Real.sqrt (1 / (1 - 2 * s i)) ≤ Real.sqrt ((1 / (1 - 2 * s i)) ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith)
          _ = 1 / (1 - 2 * s i) := Real.sqrt_sq (by linarith)
    _ = ENNReal.ofReal (∏ i, (1 / (1 - 2 * s i))) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (div_pos one_pos (hpos i)).le)]
    _ ≤ ENNReal.ofReal (1 / (1 - 2 * (t + a) / n)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.prod_div_distrib, Finset.prod_const_one]
        have hP := prod_one_sub_ge Finset.univ (fun i => 2 * s i) (fun i _ => by linarith [hs0 i])
          (fun i _ => by linarith [hs2 i])
        rw [← Finset.mul_sum, hssum] at hP
        have hk : 0 < 1 - 2 * (t + a) / n := by
          have : 2 * (t + a) / n < 1 := by rw [div_lt_iff₀ hnpos]; linarith
          linarith
        have hP' : 1 - 2 * (t + a) / n ≤ ∏ i, (1 - 2 * s i) := by
          rw [show 2 * (t + a) / (n : ℝ) = 2 * ((t + a) / n) by ring]; exact hP
        exact one_div_le_one_div_of_le hk hP'

/-- **Two directions on the sphere**: `E_σ exp(t(v·x)² + a(w·x)²) ≤ 1/(1 − 2(t+a)/n)`. -/
theorem sphere_two_dir (hn : 1 ≤ n) (t a : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (v w : Fin n → ℝ)
    (hv : ∑ i, v i ^ 2 = 1) (hw : ∑ i, w i ^ 2 = 1) (hta : 2 * (t + a) < n) :
    ∫ x, Real.exp (t * dirv v x ^ 2 + a * dirv w x ^ 2) ∂uniformSphere n ≤
      1 / (1 - 2 * (t + a) / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < 1 - 2 * (t + a) / n := by
    have : 2 * (t + a) / n < 1 := by rw [div_lt_iff₀ hnpos]; linarith
    linarith
  have hl := (sphere_le_gauss n hn (rk2 t a v w)).trans (gauss_rk2 hn t a ht ha v w hv hw hta)
  have he : ∀ x, 2 * qf (rk2 t a v w) x = t * dirv v x ^ 2 + a * dirv w x ^ 2 := by
    intro x; rw [qf_rk2]; ring
  simp_rw [he] at hl
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
    (by unfold dirv; fun_prop)]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hl

end BstLean.Part72
