import BstLean.Part173Def

/-!
# Part 173 (file `Cov`): the latitude factor `1 − s²` in the covariance and the fluctuations

No proof is left open; no `native_decide` or `axiom` is used.

* `grad_lat`: a positively 1-homogeneous `F` on `ℝ^k` with
  `|F w − F w'| ≤ L·√(s²(|w| − |w'|)² + (1 − s²)|w − w'|²)` has
  `|∇F(v)|² ≤ (1 − s²)L² + (F(v)/|v|)²` at every `v` (Euler's identity for the radial part, a
  one-sided slope bound for the tangential part; `v = 0` by the odd symmetry of the derivative).
* **`tanSq_le_lat`**: `tanSq Φ c s v ≤ (1 − s²)L²` for `Φ` `L`-Lipschitz and 1-homogeneous
  (Part 162's `abs_tanSq_le` has `2L²`, and Part 170's `cov_bound` uses `L²`).
* **`cov_bound_lat`**: `E_v ⟨e, aLat − ā⟩² ≤ (1 − s²)·O²/(n − 2)·|e|²`.
* **`exFn_mom_q`**, **`exWn_mom_q`**: Part 170's `exFn_mom`, `exWn_mom` with `F_fl`, `W_fl`
  computed from the covariance `q·O²/(n − 2)`, for any `q ≥ 1 − s_g²` (`FflQ`, `WflQ`).
-/

namespace BstLean.Part173

open MeasureTheory ProbabilityTheory Filter Topology Real
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq)
open BstLean.Part53 (unitF53 radF53)

section abs
variable {ι : Type} [Fintype ι]

lemma fd_lin [DecidableEq ι] (h : (ι → ℝ) → ℝ) (x w : ι → ℝ) :
    fderiv ℝ h x w = w ⬝ᵥ (fun i => fderiv ℝ h x (Pi.single i 1)) := by
  have h' := (fderiv ℝ h x).toLinearMap.pi_apply_eq_sum_univ w
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h'
  rw [h']
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

lemma gradSq_eq_dot [DecidableEq ι] (h : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    gradSq h x = (fun i => fderiv ℝ h x (Pi.single i 1)) ⬝ᵥ
      (fun i => fderiv ℝ h x (Pi.single i 1)) := by
  unfold gradSq; simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => by ring

lemma hasDerivAt_line {h : (ι → ℝ) → ℝ} {x : ι → ℝ} (hd : DifferentiableAt ℝ h x)
    (u : ι → ℝ) : HasDerivAt (fun t : ℝ => h (x + t • u)) (fderiv ℝ h x u) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
    simpa using this
  have h2 : HasFDerivAt h (fderiv ℝ h x) (x + (0 : ℝ) • u) := by
    simpa using hd.hasFDerivAt
  exact h2.comp_hasDerivAt (0 : ℝ) h1

lemma slope_bound {h : (ι → ℝ) → ℝ} {x u : ι → ℝ} (hd : DifferentiableAt ℝ h x) {a b : ℝ}
    (hb : ∀ t : ℝ, 0 < t → h (x + t • u) - h x ≤ a * t + b * t ^ 2) :
    fderiv ℝ h x u ≤ a := by
  have ht := (hasDerivAt_line hd u).tendsto_slope_zero_right
  have h2 : Tendsto (fun t : ℝ => a + b * t) (𝓝[>] 0) (𝓝 a) := by
    have : Tendsto (fun t : ℝ => a + b * t) (𝓝 0) (𝓝 (a + b * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    simpa using this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto ht h2 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have ht0' : (0 : ℝ) < t := ht0
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  rw [inv_mul_le_iff₀ ht0']
  have := hb t ht0'
  have e : t * (a + b * t) = a * t + b * t ^ 2 := by ring
  linarith

lemma radF_sq (v : ι → ℝ) : radF53 v ^ 2 = v ⬝ᵥ v := by
  unfold radF53
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => by ring

lemma radF_nonneg' (v : ι → ℝ) : 0 ≤ radF53 v := Real.sqrt_nonneg _

/-- **The gradient of a 1-homogeneous function with a latitude Lipschitz bound.** -/
theorem grad_lat [DecidableEq ι] {F : (ι → ℝ) → ℝ} {L s : ℝ} (hL0 : 0 ≤ L) (hs : s ^ 2 ≤ 1)
    (hhom : ∀ (t : ℝ) (w : ι → ℝ), 0 < t → F (t • w) = t * F w)
    (hlip : ∀ w w', |F w - F w'| ≤
      L * √(s ^ 2 * (radF53 w - radF53 w') ^ 2 + (1 - s ^ 2) * ∑ i, (w i - w' i) ^ 2))
    (v : ι → ℝ) : gradSq F v ≤ (1 - s ^ 2) * L ^ 2 + (F v / radF53 v) ^ 2 := by
  have hq0 : 0 ≤ 1 - s ^ 2 := by linarith
  by_cases hd : DifferentiableAt ℝ F v
  swap
  · unfold gradSq
    rw [fderiv_zero_of_not_differentiableAt hd]
    simp only [ContinuousLinearMap.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
    positivity
  set g : ι → ℝ := fun i => fderiv ℝ F v (Pi.single i 1) with hg
  have hlin : ∀ w, fderiv ℝ F v w = w ⬝ᵥ g := fun w => fd_lin F v w
  rw [gradSq_eq_dot]
  rw [← hg]
  set S := g ⬝ᵥ g with hS
  have hS0 : 0 ≤ S := by rw [hS]; simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsq : ∀ {X a : ℝ}, 0 ≤ X → 0 ≤ a → X ≤ a * √X → X ≤ a ^ 2 := by
    intro X a hX ha h
    have hr := Real.sqrt_nonneg X
    have hX' : √X ^ 2 = X := Real.sq_sqrt hX
    by_cases h0 : √X = 0
    · have hX0 : X = 0 := by rw [← hX', h0]; ring
      rw [hX0]; positivity
    have hpos : 0 < √X := lt_of_le_of_ne hr (Ne.symm h0)
    have : √X ≤ a := by nlinarith
    nlinarith
  by_cases hv : v = 0
  · -- the point `0`
    subst hv
    have hF0 : F 0 = 0 := by
      have := hhom 2 0 (by norm_num)
      rw [smul_zero] at this
      linarith
    have key : ∀ w, fderiv ℝ F 0 w = F w := by
      intro w
      have ht := (hasDerivAt_line hd w).tendsto_slope_zero_right
      have hc : Tendsto (fun t : ℝ => t⁻¹ • (F (0 + (0 + t) • w) - F (0 + (0 : ℝ) • w)))
          (𝓝[>] 0) (𝓝 (F w)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht0
        have ht0' : (0 : ℝ) < t := ht0
        simp only [zero_add, zero_smul, smul_eq_mul, hF0, sub_zero]
        rw [hhom t w ht0', ← mul_assoc, inv_mul_cancel₀ ht0'.ne', one_mul]
      exact tendsto_nhds_unique ht hc
    have h1 : S = F g := by rw [hS, ← key, hlin]
    have h2 : F (-g) = -F g := by rw [← key, ← key, map_neg]
    have hb := hlip g (-g)
    have er : radF53 (-g) = radF53 g := by unfold radF53; simp
    rw [er, h2, sub_self] at hb
    have es : ∑ i, (g i - (-g) i) ^ 2 = 4 * S := by
      rw [hS]; simp only [dotProduct, Pi.neg_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [es] at hb
    have e2 : √(s ^ 2 * 0 ^ 2 + (1 - s ^ 2) * (4 * S)) = 2 * (√(1 - s ^ 2) * √S) := by
      rw [show s ^ 2 * 0 ^ 2 + (1 - s ^ 2) * (4 * S) = 2 ^ 2 * ((1 - s ^ 2) * S) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num), Real.sqrt_mul hq0]
    rw [e2] at hb
    have h3 : S ≤ (L * √(1 - s ^ 2)) * √S := by
      have : |F g - -F g| = 2 * |F g| := by
        rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_two]
      rw [this] at hb
      have := le_abs_self (F g)
      nlinarith
    have h4 := hsq hS0 (by positivity) h3
    rw [mul_pow, Real.sq_sqrt hq0] at h4
    have : 0 ≤ (F 0 / radF53 (0 : ι → ℝ)) ^ 2 := sq_nonneg _
    nlinarith
  -- `v ≠ 0`
  have hr := BstLean.Part162.radF_pos hv
  set V := v ⬝ᵥ v with hV
  have hV' : radF53 v ^ 2 = V := radF_sq v
  have hV0 : 0 < V := by rw [← hV']; positivity
  -- Euler
  have hE : fderiv ℝ F v v = F v := by
    have h2 : HasDerivAt (fun t : ℝ => F (v + t • v)) (F v) 0 := by
      have h3 : HasDerivAt (fun t : ℝ => (1 + t) * F v) (F v) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const (F v)
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
      have ht' : (0 : ℝ) < 1 + t := by simp only [Set.mem_Ioi] at ht; linarith
      rw [show v + t • v = (1 + t) • v by rw [add_smul, one_smul], hhom _ _ ht']
    exact (hasDerivAt_line hd v).unique h2
  have hgv : g ⬝ᵥ v = F v := by rw [dotProduct_comm, ← hlin, hE]
  set p := (g ⬝ᵥ v) / V with hp
  set u := g - p • v with hu
  have huv : u ⬝ᵥ v = 0 := by
    rw [hu, sub_dotProduct, smul_dotProduct, smul_eq_mul, hp, ← hV]
    field_simp; ring
  set U := u ⬝ᵥ u with hU
  have hU0 : 0 ≤ U := by rw [hU]; simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hgu : g = u + p • v := by rw [hu]; abel
  have hDu : fderiv ℝ F v u = U := by
    rw [hlin, hgu, dotProduct_add, dotProduct_smul, huv, smul_zero, add_zero]
  have hSU : S = U + p ^ 2 * V := by
    rw [hS, hgu, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, smul_dotProduct, dotProduct_comm v u, huv, ← hU, ← hV]
    simp only [smul_eq_mul]; ring
  -- the line bound
  have hb : ∀ t : ℝ, 0 < t → F (v + t • u) - F v ≤
      (L * √(1 - s ^ 2) * √U) * t + (L * U / radF53 v) * t ^ 2 := by
    intro t ht
    have h0 := (le_abs_self _).trans (hlip (v + t • u) v)
    set δ := radF53 (v + t • u) - radF53 v with hδ
    have hR2 : radF53 (v + t • u) ^ 2 = V + t ^ 2 * U := by
      rw [radF_sq, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
        dotProduct_smul, dotProduct_smul, smul_dotProduct, dotProduct_comm v u, huv, ← hU, ← hV]
      simp only [smul_eq_mul]; ring
    have hR0 := radF_nonneg' (v + t • u)
    have hδ0 : 0 ≤ δ := by
      rw [hδ]
      have : radF53 v ^ 2 ≤ radF53 (v + t • u) ^ 2 := by rw [hR2, hV']; nlinarith
      nlinarith
    have hδ1 : δ ≤ t ^ 2 * U / radF53 v := by
      rw [le_div_iff₀ hr]
      have : δ * (radF53 (v + t • u) + radF53 v) = t ^ 2 * U := by
        rw [hδ]; nlinarith [hR2, hV']
      nlinarith
    have es : ∑ i, ((v + t • u) i - v i) ^ 2 = t ^ 2 * U := by
      rw [hU]; simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [es] at h0
    have hc : √(s ^ 2 * δ ^ 2 + (1 - s ^ 2) * (t ^ 2 * U)) ≤ δ + √(1 - s ^ 2) * t * √U := by
      have hcc : (√(1 - s ^ 2) * t * √U) ^ 2 = (1 - s ^ 2) * (t ^ 2 * U) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt hU0]; ring
      have hc0 : 0 ≤ √(1 - s ^ 2) * t * √U := by positivity
      rw [← Real.sqrt_sq (add_nonneg hδ0 hc0)]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg s, mul_nonneg hδ0 hc0]
    have := mul_le_mul_of_nonneg_left hc hL0
    have h5 : L * δ ≤ L * (t ^ 2 * U / radF53 v) := mul_le_mul_of_nonneg_left hδ1 hL0
    have e6 : L * (t ^ 2 * U / radF53 v) = (L * U / radF53 v) * t ^ 2 := by ring
    have e8 : L * (δ + √(1 - s ^ 2) * t * √U) = L * δ + (L * √(1 - s ^ 2) * √U) * t := by ring
    linarith
  have hD := slope_bound hd hb
  rw [hDu] at hD
  have h4 := hsq hU0 (by positivity) hD
  rw [mul_pow, Real.sq_sqrt hq0] at h4
  rw [hSU]
  have e7 : p ^ 2 * V = (F v / radF53 v) ^ 2 := by
    rw [hp, hgv, div_pow, div_pow, hV']; field_simp
  rw [e7]; nlinarith

end abs

section lat
open BstLean.Part161 (xLat hhMat uHat consV hh_normSq normSq_consV)
open BstLean.Part130 (normSq)
open BstLean.Part157 (Ret)
open BstLean.Part162 (xLatH xLatH_eq xLatH_smul consV_sub tanSq)

variable {n : ℕ}

/-- The exact distance of the 1-homogeneous latitude lift (the equality behind `xLatH_dist`). -/
lemma xLatH_distSq (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) (v w : Fin (n - 1) → ℝ) :
    ∑ i, (xLatH c s v i - xLatH c s w i) ^ 2 =
      s ^ 2 * (radF53 v - radF53 w) ^ 2 + (1 - s ^ 2) * ∑ i, (v i - w i) ^ 2 := by
  have e : (fun i => xLatH c s v i - xLatH c s w i) =
      (hhMat (uHat c)).mulVec (consV (s * (radF53 v - radF53 w)) (√(1 - s ^ 2) • (v - w))) := by
    funext i
    unfold xLatH
    rw [← Pi.sub_apply, ← Matrix.mulVec_sub, consV_sub, smul_sub, mul_sub]
  have h1 : ∑ i, (xLatH c s v i - xLatH c s w i) ^ 2 =
      normSq (fun i => xLatH c s v i - xLatH c s w i) := rfl
  rw [h1, e, hh_normSq, normSq_consV hn]
  have h2 : normSq (√(1 - s ^ 2) • (v - w)) = (1 - s ^ 2) * ∑ i, (v i - w i) ^ 2 := by
    unfold normSq
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_pow]
    rw [Real.sq_sqrt (by linarith), Finset.mul_sum]
  rw [h2]; ring

/-- **The tangential gradient on a latitude sphere carries the factor `1 − s²`**: for `Φ`
Lipschitz (constant `L`) and positively 1-homogeneous, `tanSq Φ c s v ≤ (1 − s²)L²` at every `v`.
(Part 162's `abs_tanSq_le` has `2L²`, Part 170's `cov_bound` uses `L²`.) -/
theorem tanSq_le_lat (hn : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {Φ : (Fin n → ℝ) → ℝ}
    {L : ℝ} (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) (v : Fin (n - 1) → ℝ) :
    tanSq Φ c s v ≤ (1 - s ^ 2) * L ^ 2 := by
  set F : (Fin (n - 1) → ℝ) → ℝ := fun w => Φ (xLatH c s w) with hF
  have hhomF : ∀ (t : ℝ) (w : Fin (n - 1) → ℝ), 0 < t → F (t • w) = t * F w := by
    intro t w ht; simp only [hF]; rw [xLatH_smul c s ht, hhom t _ ht]
  have hlip : ∀ w w', |F w - F w'| ≤
      L * √(s ^ 2 * (radF53 w - radF53 w') ^ 2 + (1 - s ^ 2) * ∑ i, (w i - w' i) ^ 2) := by
    intro w w'
    rw [← xLatH_distSq (by omega) c hs]
    exact hL _ _
  have hg := grad_lat hL0 hs hhomF hlip v
  have hval : (F v / radF53 v) ^ 2 ≤ Φ (xLat c s (unitF53 v)) ^ 2 := by
    by_cases hv : v = 0
    · subst hv
      have : radF53 (0 : Fin (n - 1) → ℝ) = 0 := by unfold radF53; simp
      rw [this, div_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
    · have hr := BstLean.Part162.radF_pos hv
      have : F v = radF53 v * Φ (xLat c s (unitF53 v)) := by
        simp only [hF]; rw [xLatH_eq, hhom _ _ hr]
      rw [this, mul_div_cancel_left₀ _ hr.ne']
  unfold tanSq
  linarith

end lat

section cov
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part148 (EuLip)

variable {n : ℕ}

/-- **Part 170's `cov_bound` with the latitude factor**:
`E_v ⟨e, aLat − ā⟩² ≤ (1 − s²)·O²/(n − 2)·|e|²`. -/
theorem cov_bound_lat (hn : 3 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) (e : Fin (mA n) → ℝ) :
    ∫ v, (e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2
        ∂stdGauss (Fin (n - 1)) ≤ (1 - s ^ 2) * O ^ 2 / ((n : ℝ) - 2) * normSq e := by
  have hn1 : 1 ≤ n := by omega
  set Φ : (Fin n → ℝ) → ℝ := fun x => e ⬝ᵥ reluV ((A1 c) *ᵥ x) with hΦ
  set L := √(normSq e) * O with hLd
  have hL0 : 0 ≤ L := by positivity
  have hL : EuLip Φ L := by
    intro x y
    simp only [hΦ]
    rw [← dotProduct_sub]
    refine (abs_dot_le _ _).trans ?_
    rw [hLd, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h2 := normSq_reluV_sub ((A1 c) *ᵥ x) ((A1 c) *ᵥ y)
    rw [← Matrix.mulVec_sub] at h2
    have h3 := h1 (x - y)
    have e4 : normSq (x - y) = ∑ i, (x i - y i) ^ 2 := rfl
    rw [← e4, ← Real.sqrt_sq hO, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (h2.trans h3)
  have hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x := by
    intro t x ht
    simp only [hΦ]
    rw [Matrix.mulVec_smul, BstLean.Part130.reluV_smul_of_nonneg ht.le, dotProduct_smul,
      smul_eq_mul]
  have hls := BstLean.Part162.ls_lat (by omega) c hs hL0 hL hhom
  have hc := hL.continuous hL0
  have bT : ∀ v, |BstLean.Part162.tanSq Φ c s v| ≤ 2 * L ^ 2 := fun v =>
    BstLean.Part162.abs_tanSq_le (by omega) c hs hL0 hL hhom v
  have bT1 : ∀ v, BstLean.Part162.tanSq Φ c s v ≤ (1 - s ^ 2) * L ^ 2 := fun v =>
    tanSq_le_lat (by omega) c hs hL0 hL hhom v
  have mT := BstLean.Part162.measurable_tanSq_left hc c s
  have hT : ∫ v, (BstLean.Part151.gradSq (fun w => Φ (BstLean.Part162.xLatH c s w)) v -
      Φ (xLat c s (unitF53 v)) ^ 2) ∂stdGauss (Fin (n - 1)) ≤ (1 - s ^ 2) * L ^ 2 := by
    calc _ = ∫ v, BstLean.Part162.tanSq Φ c s v ∂stdGauss (Fin (n - 1)) := rfl
      _ ≤ ∫ _v, (1 - s ^ 2) * L ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mT.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact bT v))
            (integrable_const _) bT1
      _ = (1 - s ^ 2) * L ^ 2 := by simp
  have hK := aLat_bdd hn1 c hs hO h1
  have hmean : ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1)) =
      e ⬝ᵥ vmean (stdGauss (Fin (n - 1))) (aLat c s) :=
    int_dot (measurable_aLat c s) hK e
  have heq : ∀ v, Φ (xLat c s (unitF53 v)) - ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))
      = e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s)) := by
    intro v; rw [hmean, dotProduct_sub]; rfl
  simp_rw [heq] at hls
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hL2 : L ^ 2 = normSq e * O ^ 2 := by
    rw [hLd, mul_pow, Real.sq_sqrt (by unfold normSq; positivity)]
  have e9 : (1 - s ^ 2) * O ^ 2 / ((n : ℝ) - 2) * normSq e = (1 - s ^ 2) * L ^ 2 / ((n : ℝ) - 2) := by
    rw [hL2]; ring
  rw [e9, le_div_iff₀ h2n]
  nlinarith [hls, hT]



end cov

section momF
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part134 (res lam projPerp glue)
open BstLean.Part167 (perp)
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part157 (cOf reb)
open BstLean.Part150 (hT sT)
open BstLean.Part136 (HidParam)
variable {n : ℕ}

/-- **Part 170's `exFn_mom` with the latitude factor**: the same bound with `F_fl` computed from
the covariance `q·O²/(n − 2)`, for any `q ≥ 1 − s_g²`. -/
theorem exFn_mom_q (hn : 3 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 < O)
    (h1 : OpB (A1 c) O) {q : ℝ} (hq0 : 0 < q) (hq : 1 - nodeS c g ^ 2 ≤ q) {B : ℝ}
    (hB0 : 0 < B)
    (hBias : ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ M, ENNReal.ofReal (exFn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((FflQ n O q + B) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  set s := nodeS c g with hsd
  set h := hB c
  set r := res h (a1Bar c s)
  set Λ := q * O ^ 2 / ((n : ℝ) - 2) with hΛd
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hΛ0 : 0 ≤ Λ := by positivity
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ Λ * normSq e := fun e =>
    (cov_bound_lat hn c hs hO.le h1 e).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq (sq_nonneg O)) h2n.le)
      (normSq_nonneg e))
  set A := FflQ n O q with hAd
  have hA : 0 < A := by
    rw [hAd]; unfold FflQ
    have : 0 < √(tA n * (q * O ^ 2 / ((n : ℝ) - 2))) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    positivity
  set k₁ := (A + B) ^ 7 / A ^ 7
  set k₂ := (A + B) ^ 7 / B ^ 7
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  -- the plane split
  have mF : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (exFn (withA2 c p.2.2) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exFn_comp ((measurable_withA2 c).comp
      (measurable_snd.comp measurable_snd)) measurable_const).pow_const 8)
  have hps := BstLean.Part167.plane_split (q := mA n) (tA n) h (a1Bar c s) mF
  have e0 : ∫⁻ M, ENNReal.ofReal (exFn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) =
      ∫⁻ M, (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (exFn (withA2 c p.2.2) g ^ 8)) (M *ᵥ h, M *ᵥ a1Bar c s, M)
        ∂gaussMat (mA n) (mA n) (tA n) := rfl
  rw [e0, hps]
  simp only
  -- the inner bound at fixed plane coordinates
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ, ∫⁻ N, ENNReal.ofReal (exFn (withA2 c
      (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) := by
    intro ξ₁ ξ₂
    set c₁ := cOf (tA n) h ξ₁
    set c₂ := cOf (tA n) r ξ₂
    set M₀ := Mpl h r c₁ c₂ 0
    set b₀ := bOfY c (M₀ *ᵥ h)
    set ψ₀ : Fin (mA n) → ℝ := fun j => BstLean.Part137.psiS √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)
    set κ₀ := (n : ℝ) / (√(n : ℝ) * √(normSq b₀))
    set E := flE (stdGauss (Fin (n - 1))) (aLat c s) h M₀ b₀ ψ₀ κ₀
    have hE : ∀ N, exFn (withA2 c (reb h c₁ (reb r c₂ N))) g = E N := fun N =>
      exFn_Mpl hn1 c g hK c₁ c₂ N
    have hmE : ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) = biasF c g ξ₁ ξ₂ := by
      unfold biasF
      exact integral_congr_ae (Filter.Eventually.of_forall fun N => (hE N).symm)
    simp_rw [hE]
    have hc := continuous_flE (measurable_aLat c s) hK hΛ0 hΛ h M₀ b₀ ψ₀ κ₀
    have hpt : ∀ N, ENNReal.ofReal (E N ^ 8) ≤ ENNReal.ofReal k₁ *
        ENNReal.ofReal (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8) +
        ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
      intro N
      rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hk₂ (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow8_split (E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n))
        (∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)) hA hB0
      rw [sub_add_cancel, hmE] at this
      have e8 : |biasF c g ξ₁ ξ₂| ^ 8 = biasF c g ξ₁ ξ₂ ^ 8 := (by decide : Even 8).pow_abs _
      rw [e8] at this
      rw [hmE]
      exact this
    have mfl : Measurable (fun N => ENNReal.ofReal
        (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8)) :=
      ENNReal.measurable_ofReal.comp (((hc.measurable.sub_const _).abs).pow_const 8)
    have hfl := fl_mom (measurable_aLat c s) hK hΛ0 hΛ h M₀ b₀ ψ₀ κ₀ htA.le
    have hfl' : (π / 2) ^ 8 * (gmom 8 * (|κ₀| * √(normSq b₀) * √(tA n * Λ) / 2) ^ 8) ≤ A ^ 8 := by
      have h1' : |κ₀| * √(normSq b₀) * √(tA n * Λ) / 2 ≤ √(n : ℝ) * √(tA n * Λ) / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (kappa_b_le n b₀)
          (Real.sqrt_nonneg _)) (by norm_num)
      have h2' := gmom8_le
      have h3 : (|κ₀| * √(normSq b₀) * √(tA n * Λ) / 2) ^ 8 ≤ (√(n : ℝ) * √(tA n * Λ) / 2) ^ 8 :=
        pow_le_pow_left₀ (by positivity) h1' 8
      have h4 : gmom 8 * (|κ₀| * √(normSq b₀) * √(tA n * Λ) / 2) ^ 8 ≤
          (18 / 10) ^ 8 * (√(n : ℝ) * √(tA n * Λ) / 2) ^ 8 :=
        mul_le_mul h2' h3 (by positivity) (by positivity)
      have e : A ^ 8 = (π / 2) ^ 8 * ((18 / 10) ^ 8 * (√(n : ℝ) * √(tA n * Λ) / 2) ^ 8) := by
        rw [hAd]; unfold FflQ; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    calc ∫⁻ N, ENNReal.ofReal (E N ^ 8) ∂gaussMat (mA n) (mA n) (tA n)
        ≤ ∫⁻ N, (ENNReal.ofReal k₁ *
          ENNReal.ofReal (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8) +
          ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8)) ∂gaussMat (mA n) (mA n) (tA n) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal k₁ * ∫⁻ N, ENNReal.ofReal
            (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8)
            ∂gaussMat (mA n) (mA n) (tA n) + ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ mfl]
      _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (A ^ 8) +
            ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
          gcongr
          exact hfl.trans (ENNReal.ofReal_le_ofReal hfl')
      _ = _ := by
          rw [← ENNReal.ofReal_mul hk₁, ENNReal.ofReal_mul hk₂]
  -- the outer integrals
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (exFn (withA2 c
        (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ *
          ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ * ∫⁻ ξ₁, ∫⁻ ξ₂,
          ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        have e1 : ∀ ξ₁ : Fin (mA n) → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ *
            ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n)) =
            ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ * ∫⁻ ξ₂,
              ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n)) := by
          intro ξ₁
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        gcongr
    _ = ENNReal.ofReal ((A + B) ^ 8) := by
        rw [← ENNReal.ofReal_mul hk₂, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hA7 : A ^ 7 ≠ 0 := by positivity
        have hB7 : B ^ 7 ≠ 0 := by positivity
        simp only [k₁, k₂]
        field_simp

end momF

section momW
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part134 (res lam projPerp glue)
open BstLean.Part167 (perp normSq_perp_le)
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part157 (cOf reb)
variable {n : ℕ}

/-- **Part 170's `exWn_mom` with the latitude factor**: the same bound with `W_fl` computed from
the covariance `q·O²/(n − 2)`, for any `q ≥ 1 − s_g²`. -/
theorem exWn_mom_q (hn : 3 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 < O)
    (h1 : OpB (A1 c) O) {q : ℝ} (hq0 : 0 < q) (hq : 1 - nodeS c g ^ 2 ≤ q) {B : ℝ}
    (hB0 : 0 < B)
    (hBias : ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((WflQ n O q + B) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  set s := nodeS c g with hsd
  set h := hB c
  set r := res h (a1Bar c s)
  set Λ := q * O ^ 2 / ((n : ℝ) - 2) with hΛd
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hΛ0 : 0 < Λ := by positivity
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hK2 : ∀ v, normSq (aLat c s v) ≤ O ^ 2 := aLat_normSq_le hn1 c hs h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ Λ * normSq e := fun e =>
    (cov_bound_lat hn c hs hO.le h1 e).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq (sq_nonneg O)) h2n.le)
      (normSq_nonneg e))
  set L := √(tA n * Λ) with hLd
  have hL : 0 < L := Real.sqrt_pos.mpr (mul_pos htA hΛ0)
  set a₁ := (π / 2 * (25 / 10) * L) ^ 2 + 2 * (π / 2 * (18 / 10) * L) + (π / 2 * L) ^ 2
  set b₁ := 2 * (π / 2 * (18 / 10) * L) * √(tA n * O ^ 2)
  have ha₁ : 0 < a₁ := by positivity
  have hb₁ : 0 < b₁ := by
    have : 0 < √(tA n * O ^ 2) := Real.sqrt_pos.mpr (by positivity)
    positivity
  set A := WflQ n O q with hAd
  have hAe : A = a₁ + b₁ * (√3 * √((mA n : ℝ) + 8)) := by rw [hAd]; unfold WflQ; rfl
  have hA : 0 < A := by rw [hAe]; positivity
  set k₁ := (A + B) ^ 7 / A ^ 7
  set k₂ := (A + B) ^ 7 / B ^ 7
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  -- the plane split
  have mF : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exWn_comp ((measurable_withA2 c).comp
      (measurable_snd.comp measurable_snd)) measurable_const).pow_const 8)
  have hps := BstLean.Part167.plane_split (q := mA n) (tA n) h (a1Bar c s) mF
  have e0 : ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) =
      ∫⁻ M, (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (exWn (withA2 c p.2.2) g ^ 8)) (M *ᵥ h, M *ᵥ a1Bar c s, M)
        ∂gaussMat (mA n) (mA n) (tA n) := rfl
  rw [e0, hps]
  simp only
  -- the inner bound at fixed plane coordinates
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
      (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ))) ^ 8) +
        ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) := by
    intro ξ₁ ξ₂
    set c₁ := cOf (tA n) h ξ₁
    set c₂ := cOf (tA n) r ξ₂
    set M₀ := Mpl h r c₁ c₂ 0
    set C₀ := ∑ j, G2 √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)
    set E : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ := fun N =>
      exWn (withA2 c (reb h c₁ (reb r c₂ N))) g
    have mE : Measurable E :=
      measurable_exWn_comp ((measurable_withA2 c).comp (BstLean.Part157.measurable_reb_comp
        measurable_const measurable_const (BstLean.Part157.measurable_reb_comp measurable_const
          measurable_const measurable_id))) measurable_const
    have hE : ∀ N, E N = flQ (stdGauss (Fin (n - 1))) (aLat c s) h M₀ N - C₀ := fun N =>
      exWn_Mpl hn1 c g hK c₁ c₂ N
    set F : (Fin (mA n) × Fin (mA n) → ℝ) → ℝ := fun ζ =>
      flQ (stdGauss (Fin (n - 1))) (aLat c s) h M₀ (matOf (tA n) ζ)
    have hS := sqrtQ_euLip (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
    have iF : Integrable F (stdGauss (Fin (mA n) × Fin (mA n))) := by
      have := euLip_sq_integrable (Real.sqrt_nonneg _) hS
      refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
      exact Real.sq_sqrt (flQ_nonneg _ _ _ _)
    set qb := ∫ ζ, F ζ ∂stdGauss (Fin (mA n) × Fin (mA n))
    have hmE : biasW c g ξ₁ ξ₂ = qb - C₀ := by
      have e0 : biasW c g ξ₁ ξ₂ = ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) := rfl
      rw [e0, gaussMat_eq, integral_map (measurable_matOf _).aemeasurable mE.aestronglyMeasurable]
      have : (fun ζ => E (matOf (tA n) ζ)) = fun ζ => F ζ - C₀ := funext fun ζ => hE _
      rw [this]
      rw [integral_sub iF (integrable_const _)]
      simp
      rfl
    -- `qb ≤ tO²(X + m)`
    have hqb : qb ≤ tA n * O ^ 2 * (normSq ξ₁ + normSq ξ₂ + (mA n : ℝ)) := by
      have hα : ∀ v, normSq (M₀ *ᵥ aLat c s v) ≤ tA n * O ^ 2 * (normSq ξ₁ + normSq ξ₂) := fun v =>
        (M0_bound htA.le h (a1Bar c s) ξ₁ ξ₂ (aLat c s v)).trans (by
          have hX : 0 ≤ normSq ξ₁ + normSq ξ₂ := by unfold normSq; positivity
          have := mul_le_mul_of_nonneg_left (hK2 v) htA.le
          nlinarith)
      have := flQ_mean_le (measurable_aLat c s) hK hΛ0.le hΛ h M₀ htA.le
        (by unfold normSq; positivity) (sq_nonneg O) hα hK2
      calc qb ≤ _ := this
        _ = _ := by ring
    have hfl := flQ_conc (measurable_aLat c s) hK hΛ0 hΛ h M₀ htA
    have hFl : (π / 2 * (25 / 10) * L) ^ 2 + 2 * (√qb + 1) * (π / 2 * (18 / 10) * L) +
        (π / 2 * L) ^ 2 ≤ a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ)) := by
      have h1' : √qb ≤ √(tA n * O ^ 2) * √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt hqb
      have hc8 : 0 ≤ π / 2 * (18 / 10) * L := by positivity
      have := mul_le_mul_of_nonneg_left h1' (by positivity : (0:ℝ) ≤ 2 * (π / 2 * (18 / 10) * L))
      simp only [a₁, b₁]
      nlinarith
    have hpt : ∀ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ≤ ENNReal.ofReal k₁ *
        ENNReal.ofReal (|F ζ - qb| ^ 8) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
      intro ζ
      rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hk₂ (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow8_split (F ζ - qb) (biasW c g ξ₁ ξ₂) hA hB0
      have e8 : |biasW c g ξ₁ ξ₂| ^ 8 = biasW c g ξ₁ ξ₂ ^ 8 := (by decide : Even 8).pow_abs _
      rw [e8] at this
      have e : E (matOf (tA n) ζ) = F ζ - qb + biasW c g ξ₁ ξ₂ := by rw [hE, hmE]; ring
      rw [e]; exact this
    have cF : Continuous F :=
      ((hS.continuous (Real.sqrt_nonneg _)).pow 2).congr fun ζ => Real.sq_sqrt (flQ_nonneg _ _ _ _)
    have mfl : Measurable (fun ζ => ENNReal.ofReal (|F ζ - qb| ^ 8)) :=
      ENNReal.measurable_ofReal.comp (((cF.measurable.sub_const _).abs).pow_const 8)
    rw [gaussMat_eq, lintegral_map (f := fun N => ENNReal.ofReal (E N ^ 8))
      (ENNReal.measurable_ofReal.comp (mE.pow_const 8)) (measurable_matOf _)]
    calc ∫⁻ ζ, ENNReal.ofReal (E (matOf (tA n) ζ) ^ 8) ∂stdGauss (Fin (mA n) × Fin (mA n))
        ≤ ∫⁻ ζ, (ENNReal.ofReal k₁ * ENNReal.ofReal (|F ζ - qb| ^ 8) +
          ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n) × Fin (mA n)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal k₁ * ∫⁻ ζ, ENNReal.ofReal (|F ζ - qb| ^ 8)
            ∂stdGauss (Fin (mA n) × Fin (mA n)) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ mfl]
      _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
            (mA n : ℝ))) ^ 8) + ENNReal.ofReal (k₂ * biasW c g ξ₁ ξ₂ ^ 8) := by
          gcongr
          refine hfl.trans (ENNReal.ofReal_le_ofReal ?_)
          exact pow_le_pow_left₀ (by positivity) hFl 8
      _ = _ := by rw [ENNReal.ofReal_mul hk₂]
  -- the outer integrals
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (exWn (withA2 c
        (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
          (mA n : ℝ))) ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8))
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal k₁ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
          (mA n : ℝ))) ^ 8) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) +
          ENNReal.ofReal k₂ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        have mI : ∀ ξ₁ : Fin (mA n) → ℝ, Measurable (fun ξ₂ : Fin (mA n) → ℝ =>
            ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
              (mA n : ℝ))) ^ 8)) := fun ξ₁ =>
          measurable_const.mul (ENNReal.measurable_ofReal.comp ((measurable_const.add
            (measurable_const.mul (((measurable_const.add continuous_normSq.measurable).add
              measurable_const).sqrt))).pow_const 8))
        have e1 : ∀ ξ₁ : Fin (mA n) → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * ENNReal.ofReal ((a₁ + b₁ *
            √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ))) ^ 8) + ENNReal.ofReal k₂ *
            ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n)) =
            ENNReal.ofReal k₁ * ∫⁻ ξ₂, ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ +
              (mA n : ℝ))) ^ 8) ∂stdGauss (Fin (mA n)) + ENNReal.ofReal k₂ *
            ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n)) := fun ξ₁ => by
          rw [lintegral_add_left (mI ξ₁), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        have mJ : Measurable (fun ξ₁ : Fin (mA n) → ℝ => ENNReal.ofReal k₁ * ∫⁻ ξ₂,
            ENNReal.ofReal ((a₁ + b₁ * √(normSq ξ₁ + normSq ξ₂ + (mA n : ℝ))) ^ 8)
            ∂stdGauss (Fin (mA n))) := by
          refine measurable_const.mul ?_
          exact (ENNReal.measurable_ofReal.comp ((measurable_const.add
            (measurable_const.mul ((((continuous_normSq.measurable.comp measurable_fst).add
              (continuous_normSq.measurable.comp measurable_snd)).add
              measurable_const).sqrt))).pow_const 8) : Measurable (fun p :
            (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => ENNReal.ofReal ((a₁ + b₁ * √(normSq p.1 +
              normSq p.2 + (mA n : ℝ))) ^ 8))).lintegral_prod_right'
        rw [lintegral_add_left mJ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        gcongr
        rw [hAe]; exact outer_mom (mA n) ha₁ hb₁
    _ = ENNReal.ofReal ((A + B) ^ 8) := by
        rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_mul hk₂,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hA7 : A ^ 7 ≠ 0 := by positivity
        have hB7 : B ^ 7 ≠ 0 := by positivity
        simp only [k₁, k₂]
        field_simp

end momW

end BstLean.Part173
