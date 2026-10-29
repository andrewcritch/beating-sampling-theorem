import BstLean.Part218Covariance

/-! Exact radial factors for the actual angular row kernels. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part29 BstLean.Part36 BstLean.Part73 BstLean.Part80 BstLean.Part105
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137 BstLean.Part214

lemma nrm_smul_nonneg {N : ℕ} {a : ℝ} (ha : 0 ≤ a) (x : Fin N → ℝ) :
    nrm (a • x) = a * nrm x := by
  unfold nrm
  rw [normSq_smul, sqrt_mul (sq_nonneg a), sqrt_sq ha]

lemma rowCos_smul_left {N : ℕ} {a : ℝ} (ha : 0 < a) (x y : Fin N → ℝ) :
    rowCos (a • x) y = rowCos x y := by
  unfold rowCos
  rw [dotp_smul_first, nrm_smul_nonneg ha.le]
  field_simp

lemma sphere_dot_function {N : ℕ} (hN : 1 ≤ N) {y : Fin N → ℝ} (hy : normSq y = 1)
    {F : ℝ → ℝ} (mF : Measurable F) :
    (∫ u, F (dotp y u) ∂uniformSphere N) =
      ∫ u : Fin N → ℝ, F (u ⟨0, hN⟩) ∂uniformSphere N := by
  obtain ⟨O, hO, hOy⟩ := exists_orth_map hN hy (BstLean.Part130.normSq_e0 hN)
  have hmO : Measurable (fun u : Fin N → ℝ => O.transpose.mulVec u) := by fun_prop
  have hm : Measurable (fun u : Fin N → ℝ => F (dotp (BstLean.Part130.e0 N) u)) := by
    apply mF.comp
    unfold dotp
    fun_prop
  have h := integral_map (μ := uniformSphere N) hmO.aemeasurable hm.aestronglyMeasurable
  rw [uniformSphere_orth O.transpose hO.t] at h
  have he : ∀ u : Fin N → ℝ, dotp y u = dotp (BstLean.Part130.e0 N) (O.transpose.mulVec u) := by
    intro u
    rw [← hOy]
    unfold dotp
    have hd := dot_mulVec' O u (BstLean.Part130.e0 N)
    simpa only [mul_comm] using hd
  have hc : ∀ u : Fin N → ℝ, dotp (BstLean.Part130.e0 N) u = u ⟨0, hN⟩ := by
    intro u
    unfold dotp BstLean.Part130.e0
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · simp
    · intro j _ hj
      have hj0 : j.val ≠ 0 := fun he => hj (Fin.ext he)
      simp [hj0]
    · simp
  calc
    _ = ∫ u, F (dotp (BstLean.Part130.e0 N) (O.transpose.mulVec u)) ∂uniformSphere N := by simp_rw [he]
    _ = ∫ u, F (dotp (BstLean.Part130.e0 N) u) ∂uniformSphere N := h.symm
    _ = _ := by simp_rw [hc]

noncomputable def radialAngular {N : ℕ} (k : ℕ) (F : ℝ → ℝ)
    (x y : Fin N → ℝ) : ℝ := normSq x ^ k * normSq y ^ k * F (rowCos x y)

lemma radialAngular_measurable {N : ℕ} (k : ℕ) {F : ℝ → ℝ} (mF : Measurable F) :
    Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => radialAngular k F p.2 p.1) := by
  unfold radialAngular rowCos nrm dotp normSq
  fun_prop

lemma radialAngular_integrable {N : ℕ} (hN : 1 ≤ N) (k : ℕ) {F : ℝ → ℝ}
    (mF : Measurable F) {B : ℝ} (hB : ∀ c : ℝ, |c| ≤ 1 → |F c| ≤ B) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => radialAngular k F p.2 p.1)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N))) := by
  have hi := ((gaussian_normSq_pow_integrable hN k).mul_prod
    (gaussian_normSq_pow_integrable hN k)).mul_const B
  apply hi.mono' (radialAngular_measurable k mF).aestronglyMeasurable
  filter_upwards [] with p
  simp only [radialAngular, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg (normSq_nonneg _) k)]
  have h := mul_le_mul_of_nonneg_left (hB _ (rowCos_abs_le p.2 p.1))
    (mul_nonneg (pow_nonneg (normSq_nonneg p.2) k) (pow_nonneg (normSq_nonneg p.1) k))
  nlinarith [h]

lemma radialAngular_homogeneous {N : ℕ} {k : ℕ} (hk : 1 ≤ k) (F : ℝ → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (x y : Fin N → ℝ) :
    radialAngular k F (a • x) y = a ^ (2 * k) * radialAngular k F x y := by
  rcases ha.eq_or_lt with h0 | ha
  · subst a
    simp [radialAngular, normSq, Nat.ne_of_gt hk, show 2 * k ≠ 0 by omega]
  · unfold radialAngular
    rw [normSq_smul, rowCos_smul_left ha, mul_pow, pow_mul]
    ring

theorem radialAngular_conditional {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {F : ℝ → ℝ} (mF : Measurable F) (y : Fin N → ℝ) :
    (∫ x, radialAngular k F x y ∂stdGauss (Fin N)) =
      rhoD N k * normSq y ^ k * ∫ u : Fin N → ℝ, F (u ⟨0, hN⟩) ∂uniformSphere N := by
  have hm : Measurable (fun x : Fin N → ℝ => radialAngular k F x y) := by
    unfold radialAngular rowCos nrm dotp normSq
    fun_prop
  rw [gaussian_homogeneous hN k hm (fun a ha x => radialAngular_homogeneous hk F a ha x y)]
  by_cases hy0 : normSq y = 0
  · simp [radialAngular, hy0, Nat.ne_of_gt hk]
  have hyp : 0 < nrm y := sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg y) (Ne.symm hy0))
  let z := (nrm y)⁻¹ • y
  have hz : normSq z = 1 := by
    dsimp [z]
    rw [normSq_smul, inv_pow, nrm_sq]
    field_simp
  have he : ∀ᵐ u ∂uniformSphere N,
      radialAngular k F u y = normSq y ^ k * F (dotp z u) := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    change normSq u = 1 at hu
    have hnu : nrm u = 1 := by unfold nrm; rw [hu, sqrt_one]
    have hc : rowCos u y = dotp z u := by
      unfold rowCos z
      rw [hnu, one_mul, dotp_smul_first]
      unfold dotp
      simp only [mul_comm]
      ring
    simp only [radialAngular, hu, one_pow, one_mul, hc]
  rw [integral_congr_ae he, integral_const_mul, sphere_dot_function hN hz mF]
  ring

theorem radialAngular_integral {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {F : ℝ → ℝ} (mF : Measurable F)
    (hi : Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => radialAngular k F p.2 p.1)
      ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) :
    (∫ p : (Fin N → ℝ) × (Fin N → ℝ), radialAngular k F p.2 p.1
      ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) =
      rhoD N k ^ 2 * ∫ u : Fin N → ℝ, F (u ⟨0, hN⟩) ∂uniformSphere N := by
  rw [integral_prod _ hi]
  simp_rw [radialAngular_conditional hN hk mF]
  rw [integral_mul_const, integral_const_mul, gaussian_normSq_pow]
  ring

end BstLean.Part218
#print axioms BstLean.Part218.radialAngular_integral
