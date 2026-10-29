import BstLean.Part272Law

/-!
# Part 272 (V3c): closed forms of the sphere moments for even `n`

Paper: `theorem7-01-statement-program.tex`, proof of Lemma `t7:p01:moments`, even case.
`P = (n−4)/2`, `𝒩_P⁻¹ = 2∏_{r=1}^P 2r/(2r+1)`, `J_j(d) = Σ_r (−1)^r C(P,r)(1−d^{2r+j+1})/(2r+j+1)`.

* `JJ_integral`: `J_j(d) = ∫_d^1 z^j(1−z²)^P dz`.
* `NPinv_integral`: `𝒩_P⁻¹ = ∫_{−1}^1 (1−z²)^P dz`.
* `sph_even`: for even `n ≥ 8` and `k ≥ 0`, `E ReLU(m + kT) = sphA n m k` and
  `E ReLU(m + kT)² = sphE n m k`, with `T` the first coordinate of a uniform direction in
  `ℝ^{n−1}`.
-/

namespace BstLean.Part272

open Real MeasureTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part130 (relu measurable_relu continuous_relu)

/-- `J_j(d)` of the even rule. -/
noncomputable def JJ (P j : ℕ) (d : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (P+1), (-1:ℝ)^r * (P.choose r) * (1 - d^(2*r+j+1)) / (2*r+j+1)

/-- `𝒩_P⁻¹ = 2∏_{r=1}^P 2r/(2r+1)`. -/
noncomputable def NPinv (P : ℕ) : ℝ := 2 * ∏ r ∈ Finset.Icc 1 P, (2*(r:ℝ)) / (2*r+1)

/-- The even first-moment rule with its four branches; `P = (n−4)/2`. -/
noncomputable def sphA (n : ℕ) (m k : ℝ) : ℝ :=
  if k = 0 then relu m else if k ≤ m then m else if m ≤ -k then 0 else
    (NPinv ((n-4)/2))⁻¹ * (m * JJ ((n-4)/2) 0 (-m/k) + k * JJ ((n-4)/2) 1 (-m/k))

/-- The even second-moment rule with its four branches; `P = (n−4)/2`. -/
noncomputable def sphE (n : ℕ) (m k : ℝ) : ℝ :=
  if k = 0 then relu m ^ 2 else if k ≤ m then m^2 + k^2/((n:ℝ)-1) else if m ≤ -k then 0 else
    (NPinv ((n-4)/2))⁻¹ * (m^2 * JJ ((n-4)/2) 0 (-m/k) + 2*m*k * JJ ((n-4)/2) 1 (-m/k) +
      k^2 * JJ ((n-4)/2) 2 (-m/k))

theorem binom_expand (P : ℕ) (z : ℝ) :
    (1 - z^2)^P = ∑ r ∈ Finset.range (P+1), (-1:ℝ)^r * (P.choose r) * z^(2*r) := by
  rw [show 1 - z^2 = -z^2 + 1 by ring, add_pow]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [one_pow, mul_one, neg_pow, ← pow_mul]
  ring

theorem JJ_integral (P j : ℕ) (d : ℝ) : JJ P j d = ∫ z in d..1, z^j * (1 - z^2)^P := by
  simp_rw [binom_expand, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum (fun r _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  unfold JJ
  refine Finset.sum_congr rfl fun r _ => ?_
  have h : ∀ z : ℝ, z^j * ((-1:ℝ)^r * (P.choose r) * z^(2*r)) =
      ((-1:ℝ)^r * (P.choose r)) * z^(2*r+j) := by
    intro z; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow]
  push_cast
  ring

theorem Ipow_succ (p : ℕ) :
    ∫ z in (-1:ℝ)..1, (1 - z^2)^(p+1) =
      (2*((p:ℝ)+1))/(2*((p:ℝ)+1)+1) * ∫ z in (-1:ℝ)..1, (1 - z^2)^p := by
  have hd : ∀ z ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun z : ℝ => z * (1 - z^2)^(p+1))
      ((2*(p:ℝ)+3) * (1 - z^2)^(p+1) - (2*(p:ℝ)+2) * (1 - z^2)^p) z := by
    intro z _
    have h := (hasDerivAt_id z).mul
      (((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_pow 2 z)).pow (p+1))
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id, Nat.add_sub_cancel, Nat.reduceSub,
      pow_one, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    ring
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)
  have h0 : (fun z : ℝ => z * (1 - z^2)^(p+1)) 1 - (fun z : ℝ => z * (1 - z^2)^(p+1)) (-1) = 0 := by
    simp
  rw [h0, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hF
  have hb : (2*((p:ℝ)+1)+1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hb]
  linear_combination hF

theorem NPinv_integral (P : ℕ) : NPinv P = ∫ z in (-1:ℝ)..1, (1 - z^2)^P := by
  induction P with
  | zero => simp [NPinv]; norm_num
  | succ p ih =>
    rw [Ipow_succ, ← ih]
    unfold NPinv
    rw [Finset.prod_Icc_succ_top (by omega)]
    push_cast
    ring

/-- The coordinate law in dimension `n − 1` for even `n`, with the natural exponent `P`. -/
theorem coord_law_even {n : ℕ} (hn : 8 ≤ n) (he : Even n) {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∃ M, ∀ z ∈ Icc (-1:ℝ) 1, |g z| ≤ M) :
    ∫ v, g (unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n-1)) =
      (∫ z in (-1:ℝ)..1, g z * (1 - z^2)^((n-4)/2)) / NPinv ((n-4)/2) := by
  have hexp : (((n-1 : ℕ) : ℝ) - 3)/2 = (((n-4)/2 : ℕ) : ℝ) := by
    obtain ⟨q, rfl⟩ := he
    rw [show (q+q-4)/2 = q-2 by omega, Nat.cast_sub (by omega : 2 ≤ q),
      Nat.cast_sub (by omega : 1 ≤ q+q)]
    push_cast
    ring
  rw [coord_law (N := n-1) (by omega) hg hb, hexp, NPinv_integral]
  simp only [rpow_natCast]

/-- Only the active interval `(−m/k, 1]` contributes. -/
theorem active_split {m k : ℝ} (hk : 0 < k) (hm1 : -k < m) (hm2 : m < k) {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hφ0 : ∀ t ≤ 0, φ t = 0) (hφψ : ∀ t, 0 ≤ t → φ t = ψ t) (P : ℕ) :
    ∫ z in (-1:ℝ)..1, φ (m + k*z) * (1 - z^2)^P =
      ∫ z in (-m/k)..1, ψ (m + k*z) * (1 - z^2)^P := by
  have hd1 : -1 ≤ -m/k := by rw [le_div_iff₀ hk]; linarith
  have hd2 : -m/k ≤ 1 := by rw [div_le_iff₀ hk]; linarith
  have hkd : k * (-m/k) = -m := by field_simp
  have hcont : Continuous (fun z => φ (m + k*z) * (1 - z^2)^P) :=
    (hφ.comp (continuous_const.add (continuous_const.mul continuous_id))).mul
      ((continuous_const.sub (continuous_id.pow 2)).pow P)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (-1) (-m/k))
    (hcont.intervalIntegrable (-m/k) 1)]
  have hz1 : ∫ z in (-1:ℝ)..(-m/k), φ (m + k*z) * (1 - z^2)^P = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    intro z hz
    rw [uIcc_of_le hd1] at hz
    have h1 := mul_le_mul_of_nonneg_left hz.2 hk.le
    have h2 : m + k*z ≤ 0 := by linarith
    simp only [hφ0 _ h2, zero_mul]
  rw [hz1, zero_add]
  refine intervalIntegral.integral_congr fun z hz => ?_
  rw [uIcc_of_le hd2] at hz
  have h1 := mul_le_mul_of_nonneg_left hz.1 hk.le
  have h2 : 0 ≤ m + k*z := by linarith
  simp only [hφψ _ h2]

theorem lin_J (P : ℕ) (m k d : ℝ) :
    ∫ z in d..1, (m + k*z) * (1 - z^2)^P = m * JJ P 0 d + k * JJ P 1 d := by
  have h : (fun z : ℝ => (m + k*z) * (1 - z^2)^P) =
      fun z => m * (z^0 * (1 - z^2)^P) + k * (z^1 * (1 - z^2)^P) := by
    funext z; ring
  rw [h, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, JJ_integral, JJ_integral]
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

theorem quad_J (P : ℕ) (m k d : ℝ) :
    ∫ z in d..1, (m + k*z)^2 * (1 - z^2)^P =
      m^2 * JJ P 0 d + 2*m*k * JJ P 1 d + k^2 * JJ P 2 d := by
  have h : (fun z : ℝ => (m + k*z)^2 * (1 - z^2)^P) =
      fun z => m^2 * (z^0 * (1 - z^2)^P) + 2*m*k * (z^1 * (1 - z^2)^P) +
        k^2 * (z^2 * (1 - z^2)^P) := by
    funext z; ring
  rw [h, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, JJ_integral, JJ_integral, JJ_integral]
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

theorem integrable_coord {N : ℕ} (i : Fin N) :
    Integrable (fun v => unitF53 v i) (stdGauss (Fin N)) :=
  integrable_coord_comp i (g := id) measurable_id ⟨1, fun z hz => abs_le.mpr hz⟩

theorem integrable_coord_sq {N : ℕ} (i : Fin N) :
    Integrable (fun v => (unitF53 v i)^2) (stdGauss (Fin N)) :=
  integrable_coord_comp i (g := fun z => z^2) (measurable_id.pow_const 2) ⟨1, fun z hz => by
    rw [abs_of_nonneg (sq_nonneg z)]; nlinarith [hz.1, hz.2]⟩

theorem relu_bound (m k : ℝ) (hk : 0 ≤ k) :
    ∃ M, ∀ z ∈ Icc (-1:ℝ) 1, |relu (m + k*z)| ≤ M := ⟨|m| + k, fun z hz => by
  unfold relu
  rw [abs_of_nonneg (le_max_left _ _)]
  apply max_le (by positivity)
  have : k*z ≤ k := by nlinarith [hz.2]
  linarith [le_abs_self m]⟩

theorem relu_sq_bound (m k : ℝ) (hk : 0 ≤ k) :
    ∃ M, ∀ z ∈ Icc (-1:ℝ) 1, |relu (m + k*z) ^ 2| ≤ M := by
  obtain ⟨M, hM⟩ := relu_bound m k hk
  refine ⟨M^2, fun z hz => ?_⟩
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hM z hz) 2

/-- The first moment for even `n`. -/
theorem sphA_eq {n : ℕ} (hn : 8 ≤ n) (he : Even n) (m : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n-1)) = sphA n m k := by
  have hTm : ∀ v : Fin (n-1) → ℝ, unitF53 v ⟨0, by omega⟩ ∈ Icc (-1:ℝ) 1 :=
    fun v => coord_mem v _
  unfold sphA
  split_ifs with h0 h1 h2
  · subst h0; simp
  · have hr : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) =
        m + k * unitF53 v ⟨0, by omega⟩ := by
      intro v; unfold relu; apply max_eq_right
      nlinarith [mul_nonneg hk (by linarith [(hTm v).1] :
        (0:ℝ) ≤ unitF53 v ⟨0, by omega⟩ + 1)]
    simp_rw [hr]
    rw [integral_add (integrable_const _) ((integrable_coord _).const_mul _),
      integral_const_mul, coord_mean_at]
    simp
  · have hr : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) = 0 := by
      intro v; unfold relu; apply max_eq_left
      nlinarith [mul_nonneg hk (by linarith [(hTm v).2] :
        (0:ℝ) ≤ 1 - unitF53 v ⟨0, by omega⟩)]
    simp_rw [hr]
    simp
  · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm h0)
    have hm1 : -k < m := lt_of_not_ge h2
    have hm2 : m < k := lt_of_not_ge h1
    have h := coord_law_even hn he (g := fun z => relu (m + k*z))
      (measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id)))
      (relu_bound m k hk)
    beta_reduce at h
    have hs := active_split hkp hm1 hm2 (φ := relu) (ψ := fun t => t) continuous_relu
      (fun t ht => max_eq_left ht) (fun t ht => max_eq_right ht) ((n-4)/2)
    beta_reduce at hs
    rw [h, hs, lin_J, div_eq_inv_mul]

/-- The second moment for even `n`. -/
theorem sphE_eq {n : ℕ} (hn : 8 ≤ n) (he : Even n) (m : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2 ∂stdGauss (Fin (n-1)) = sphE n m k := by
  have hTm : ∀ v : Fin (n-1) → ℝ, unitF53 v ⟨0, by omega⟩ ∈ Icc (-1:ℝ) 1 :=
    fun v => coord_mem v _
  unfold sphE
  split_ifs with h0 h1 h2
  · subst h0; simp
  · have hr : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2 =
        m^2 + (2*m*k) * unitF53 v ⟨0, by omega⟩ + k^2 * (unitF53 v ⟨0, by omega⟩)^2 := by
      intro v
      have hp : relu (m + k * unitF53 v ⟨0, by omega⟩) = m + k * unitF53 v ⟨0, by omega⟩ := by
        unfold relu; apply max_eq_right
        nlinarith [mul_nonneg hk (by linarith [(hTm v).1] :
          (0:ℝ) ≤ unitF53 v ⟨0, by omega⟩ + 1)]
      rw [hp]; ring
    simp_rw [hr]
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, coord_mean_at,
      coord_sq_at (by omega), Nat.cast_sub (by omega : 1 ≤ n)]
    · have hc : ∫ _v : Fin (n-1) → ℝ, m^2 ∂stdGauss (Fin (n-1)) = m^2 := by simp
      rw [hc]
      push_cast
      ring
    all_goals first
      | exact integrable_const _
      | exact (integrable_coord _).const_mul _
      | exact (integrable_coord_sq _).const_mul _
      | exact (integrable_const _).add ((integrable_coord _).const_mul _)
  · have hr : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2 = 0 := by
      intro v
      have hp : relu (m + k * unitF53 v ⟨0, by omega⟩) = 0 := by
        unfold relu; apply max_eq_left
        nlinarith [mul_nonneg hk (by linarith [(hTm v).2] :
          (0:ℝ) ≤ 1 - unitF53 v ⟨0, by omega⟩)]
      rw [hp]; ring
    simp_rw [hr]
    simp
  · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm h0)
    have hm1 : -k < m := lt_of_not_ge h2
    have hm2 : m < k := lt_of_not_ge h1
    have h := coord_law_even hn he (g := fun z => relu (m + k*z) ^ 2)
      ((measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id))).pow_const 2)
      (relu_sq_bound m k hk)
    beta_reduce at h
    have hs := active_split hkp hm1 hm2 (φ := fun t => relu t ^ 2) (ψ := fun t => t^2)
      (continuous_relu.pow 2)
      (fun t ht => by simp only [relu, max_eq_left ht]; ring)
      (fun t ht => by simp only [relu, max_eq_right ht]) ((n-4)/2)
    beta_reduce at hs
    rw [h, hs, quad_J, div_eq_inv_mul]

/-- **V3c.** The even closed forms are the exact sphere moments. -/
theorem sph_even {n : ℕ} (hn : 8 ≤ n) (he : Even n) (m : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n-1)) = sphA n m k ∧
    ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2 ∂stdGauss (Fin (n-1)) = sphE n m k :=
  ⟨sphA_eq hn he m hk, sphE_eq hn he m hk⟩

end BstLean.Part272

#print axioms BstLean.Part272.sph_even
