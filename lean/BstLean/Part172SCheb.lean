import BstLean.Part172SBnd

/-!
# Part 172 (file `SCheb`): moments of the row statistics and Chebyshev for row sums

No proof is left open; no `native_decide` or `axiom` is used.

For a unit vector `u` and `g ∈ ℝⁿ`: `φ₂(g) = |g|² − (g·u)²`, `φ₁(g) = 1{g·u ≥ 0}φ₂(g)`.
Under the standard Gaussian: `E φ₂ = n − 1`, `E φ₁ ≥ (n − 1)/2`, `E φ_k² ≤ n² + 2n`.
* **`sg_cheb`**: Chebyshev for `Σ_i φ(G_i)`, rows `G_i` independent standard Gaussian:
  `P(|Σ φ(G_i) − m E φ| ≥ t) ≤ m E φ²/t²`.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)

variable {n : ℕ}

/-- `φ₂(g) = |g|² − (g·u)²`. -/
noncomputable def sg_phi2 (u g : Fin n → ℝ) : ℝ := normSq g - sg_z u g ^ 2

/-- `φ₁(g) = 1{g·u ≥ 0}·φ₂(g)`. -/
noncomputable def sg_phi1 (u g : Fin n → ℝ) : ℝ := if 0 ≤ sg_z u g then sg_phi2 u g else 0

lemma sg_z_sq_le {u : Fin n → ℝ} (hu : normSq u = 1) (g : Fin n → ℝ) : sg_z u g ^ 2 ≤ normSq g := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g u
  unfold sg_z normSq at *
  rw [hu, mul_one] at this
  exact this

lemma sg_meas_z (u : Fin n → ℝ) : Measurable (sg_z u) := by
  unfold sg_z; fun_prop

lemma sg_meas_normSq : Measurable (fun g : Fin n → ℝ => normSq g) := by
  unfold normSq; fun_prop

lemma sg_meas_phi2 (u : Fin n → ℝ) : Measurable (sg_phi2 u) :=
  sg_meas_normSq.sub ((sg_meas_z u).pow_const 2)

lemma sg_meas_phi1 (u : Fin n → ℝ) : Measurable (sg_phi1 u) :=
  Measurable.ite (measurableSet_le measurable_const (sg_meas_z u)) (sg_meas_phi2 u) measurable_const

lemma sg_phi2_nonneg {u : Fin n → ℝ} (hu : normSq u = 1) (g : Fin n → ℝ) : 0 ≤ sg_phi2 u g := by
  unfold sg_phi2; linarith [sg_z_sq_le hu g]

lemma sg_phi2_le (u g : Fin n → ℝ) : sg_phi2 u g ≤ normSq g := by
  unfold sg_phi2; linarith [sq_nonneg (sg_z u g)]

lemma sg_phi1_nonneg {u : Fin n → ℝ} (hu : normSq u = 1) (g : Fin n → ℝ) : 0 ≤ sg_phi1 u g := by
  unfold sg_phi1; split_ifs
  · exact sg_phi2_nonneg hu g
  · exact le_rfl

lemma sg_phi1_le {u : Fin n → ℝ} (hu : normSq u = 1) (g : Fin n → ℝ) : sg_phi1 u g ≤ normSq g := by
  unfold sg_phi1; split_ifs
  · exact sg_phi2_le u g
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sg_int_z2 {u : Fin n → ℝ} (hu : normSq u = 1) :
    Integrable (fun g => sg_z u g ^ 2) (stdGauss (Fin n)) ∧
      ∫ g, sg_z u g ^ 2 ∂stdGauss (Fin n) = 1 := by
  classical
  have e : ∀ g : Fin n → ℝ, sg_z u g ^ 2 = ∑ i, ∑ j, (u i * u j) * (g i * g j) := by
    intro g; unfold sg_z; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hi : ∀ i j, Integrable (fun g : Fin n → ℝ => (u i * u j) * (g i * g j)) (stdGauss (Fin n)) :=
    fun i j => (BstLean.Part130.stdGauss_mul_integrable i j).const_mul _
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  simp_rw [integral_finsetSum _ fun j _ => hi _ j, integral_const_mul,
    BstLean.Part130.stdGauss_cov]
  have : ∑ i, ∑ j, u i * u j * (if i = j then (1 : ℝ) else 0) = normSq u := by
    unfold normSq
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [this, hu]

lemma sg_int_normSq : Integrable (fun g : Fin n → ℝ => normSq g) (stdGauss (Fin n)) ∧
    ∫ g, normSq g ∂stdGauss (Fin n) = n := BstLean.Part137.gauss_normSq n

lemma sg_int_normSq2 : Integrable (fun g : Fin n → ℝ => normSq g ^ 2) (stdGauss (Fin n)) ∧
    ∫ g, normSq g ^ 2 ∂stdGauss (Fin n) = (n : ℝ) ^ 2 + 2 * n := BstLean.Part137.gauss_normSq_sq n

lemma sg_int_phi2 {u : Fin n → ℝ} (hu : normSq u = 1) :
    Integrable (sg_phi2 u) (stdGauss (Fin n)) ∧ ∫ g, sg_phi2 u g ∂stdGauss (Fin n) = n - 1 := by
  obtain ⟨i1, e1⟩ := sg_int_normSq (n := n)
  obtain ⟨i2, e2⟩ := sg_int_z2 hu
  refine ⟨i1.sub i2, ?_⟩
  unfold sg_phi2
  rw [integral_sub i1 i2, e1, e2]

lemma sg_int_bdd {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) (h0 : ∀ g, 0 ≤ φ g)
    (h1 : ∀ g, φ g ≤ normSq g) :
    Integrable φ (stdGauss (Fin n)) ∧ Integrable (fun g => φ g ^ 2) (stdGauss (Fin n)) ∧
      ∫ g, φ g ^ 2 ∂stdGauss (Fin n) ≤ (n : ℝ) ^ 2 + 2 * n := by
  obtain ⟨i1, -⟩ := sg_int_normSq (n := n)
  obtain ⟨i2, e2⟩ := sg_int_normSq2 (n := n)
  have hb : ∀ g, φ g ^ 2 ≤ normSq g ^ 2 := fun g => pow_le_pow_left₀ (h0 g) (h1 g) 2
  have j1 : Integrable φ (stdGauss (Fin n)) :=
    Integrable.mono' i1 hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 g)]; exact h1 g)
  have j2 : Integrable (fun g => φ g ^ 2) (stdGauss (Fin n)) :=
    Integrable.mono' i2 (hφ.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb g)
  refine ⟨j1, j2, ?_⟩
  rw [← e2]
  exact integral_mono j2 i2 hb

lemma sg_z_neg (u g : Fin n → ℝ) : sg_z u (-g) = - sg_z u g := by
  unfold sg_z; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by simp

lemma sg_phi2_neg (u g : Fin n → ℝ) : sg_phi2 u (-g) = sg_phi2 u g := by
  unfold sg_phi2; rw [sg_z_neg, neg_sq]; unfold normSq; simp

lemma sg_int_phi1 {u : Fin n → ℝ} (hu : normSq u = 1) :
    ((n : ℝ) - 1) / 2 ≤ ∫ g, sg_phi1 u g ∂stdGauss (Fin n) := by
  obtain ⟨j1, -, -⟩ := sg_int_bdd (sg_meas_phi1 u) (sg_phi1_nonneg hu) (sg_phi1_le hu)
  obtain ⟨i2, e2⟩ := sg_int_phi2 hu
  have hneg := sg_int_neg (d := n) (sg_meas_phi1 u)
  have j1' : Integrable (fun g => sg_phi1 u (-g)) (stdGauss (Fin n)) := by
    refine Integrable.mono' i2 ((sg_meas_phi1 u).comp measurable_neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sg_phi1_nonneg hu _)]
    have := sg_phi1_le hu (-g)
    unfold sg_phi1 at *; split_ifs <;> simp_all [sg_phi2_neg, sg_phi2_nonneg hu]
  have hpt : ∀ g, sg_phi2 u g ≤ sg_phi1 u g + sg_phi1 u (-g) := by
    intro g
    unfold sg_phi1
    rw [sg_z_neg, sg_phi2_neg]
    split_ifs with h1 h2 h2
    · linarith [sg_phi2_nonneg hu g]
    · linarith
    · linarith
    · exfalso; linarith
  have jj : Integrable (fun g => sg_phi1 u g + sg_phi1 u (-g)) (stdGauss (Fin n)) := j1.add j1'
  have := integral_mono i2 jj hpt
  rw [integral_add j1 j1', hneg, e2] at this
  linarith

/-- **Chebyshev for a row sum.** -/
theorem sg_cheb {m : ℕ} {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ)
    (h2 : Integrable (fun g => φ g ^ 2) (stdGauss (Fin n))) {t : ℝ} (ht : 0 < t) :
    (Measure.pi fun _ : Fin m => stdGauss (Fin n))
        {G | t ≤ |∑ i, φ (G i) - m * ∫ g, φ g ∂stdGauss (Fin n)|} ≤
      ENNReal.ofReal (m * (∫ g, φ g ^ 2 ∂stdGauss (Fin n)) / t ^ 2) := by
  set μ := Measure.pi fun _ : Fin m => stdGauss (Fin n)
  have hL : MemLp φ 2 (stdGauss (Fin n)) :=
    (memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).2 h2
  set X : (Fin m → Fin n → ℝ) → ℝ := ∑ i, fun G => φ (G i) with hX
  have hXe : ∀ G, X G = ∑ i, φ (G i) := fun G => by simp [hX]
  have hLi : ∀ i, MemLp (fun G : Fin m → Fin n → ℝ => φ (G i)) 2 μ := fun i =>
    hL.comp_measurePreserving (measurePreserving_eval _ i)
  have hXL : MemLp X 2 μ := memLp_finsetSum' _ fun i _ => hLi i
  have hint : ∀ i, ∫ G, φ (G i) ∂μ = ∫ g, φ g ∂stdGauss (Fin n) := fun i => by
    have h := integral_map (μ := μ) (measurable_pi_apply i).aemeasurable (f := φ)
      (by rw [(measurePreserving_eval _ i).map_eq]; exact hφ.aestronglyMeasurable)
    rw [(measurePreserving_eval _ i).map_eq] at h
    exact h.symm
  have hmean : μ[X] = m * ∫ g, φ g ∂stdGauss (Fin n) := by
    simp_rw [hXe]
    rw [integral_finsetSum _ fun i _ => (hLi i).integrable one_le_two]
    simp_rw [hint]
    simp
  have hvar : variance X μ = m * variance φ (stdGauss (Fin n)) := by
    rw [hX]
    have := variance_sum_pi (μ := fun _ : Fin m => stdGauss (Fin n)) (X := fun _ => φ) (fun _ => hL)
    rw [this]; simp
  have hvle : variance φ (stdGauss (Fin n)) ≤ ∫ g, φ g ^ 2 ∂stdGauss (Fin n) :=
    variance_le_expectation_sq hφ.aestronglyMeasurable
  have hC := meas_ge_le_variance_div_sq hXL ht
  rw [hmean, hvar] at hC
  have hs : {G | t ≤ |∑ i, φ (G i) - m * ∫ g, φ g ∂stdGauss (Fin n)|} =
      {G | t ≤ |X G - m * ∫ g, φ g ∂stdGauss (Fin n)|} := by
    ext G; simp [hXe]
  rw [hs]
  refine hC.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr

end BstLean.Part172
