import BstLean.Part171Op

/-!
# Part 171 (file `Red`): two deterministic steps toward the charge (Part F1, first half)

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `E_v(v_v − ς²) = −h_U` and the first line of
`t7:p08:statistics` (`h_U` by LS).

* `pyth`: `t_A|y|² = q₁(y)² + q₂(y)² + t_A|perp r (perp h y)|²` (Pythagoras in the plane `U`).
* `vsig2_eq`: `ς² = t_A E_v|a − ā|²` (the clipping `max 0` is not active).
* **`hUN_eq_DstN`**: on `‖A₁‖_op ≤ O`, `hUN = DstN` (the two forms of the paper's `h_U` agree).
* `q1_eq_dot`, `q2_eq_dot`: `q₁(y) = e₁·y`, `q₂(y) = e₂·y` with `|e₁|², |e₂|² ≤ t_A`.
* **`DstN_le_tan`**: on `‖A₁‖_op ≤ O`, `(n − 2)·DstN ≤ E_v tanSq Φ_{e₁} + E_v tanSq Φ_{e₂}`,
  `Φ_e(x) = e·ReLU(A₁x)`: the LS step, with Lean's constant `1/(n − 2)` (Part 162's `ls_lat`).
  `tanSq` is the squared tangential gradient (the paper's `(1 − s²)Ψ_e`).
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part134 (res lam)
open BstLean.Part167 (perp)
open BstLean.Part170 (hB tA aLat vmean vmean_aLat aLat_normSq_le measurable_aLat aLat_bdd)
open BstLean.Part53 (unitF53)
open BstLean.Part161 (xLat)

variable {n : ℕ}

lemma perp_sub' {m : ℕ} (b x y : Fin m → ℝ) : perp b (x - y) = perp b x - perp b y := by
  unfold perp
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  ring

lemma sum_comm_dot {m : ℕ} (x y : Fin m → ℝ) : ∑ j, x j * y j = y ⬝ᵥ x := by
  unfold dotProduct; exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma sq_q_aux (B d t : ℝ) (hB : 0 ≤ B) (ht : 0 ≤ t) :
    (B⁻¹ * d * (√t * √B)) ^ 2 = t * (B⁻¹ * d ^ 2) := by
  rcases hB.lt_or_eq with h | h
  · rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hB]; field_simp
  · rw [← h]; simp

/-- **Pythagoras in the plane**: `t_A|y|² = q₁(y)² + q₂(y)² + t_A|perp r (perp h y)|²`. -/
lemma pyth (c : Ret n) (g : ℕ) (y : Fin (mA n) → ℝ) :
    tA n * normSq y = q1 c y ^ 2 + q2 c g y ^ 2 +
      tA n * normSq (perp (res (hB c) (a1Bar c (nodeS c g))) (perp (hB c) y)) := by
  set h := hB c
  set r := res h (a1Bar c (nodeS c g))
  have ht := tA_nonneg n
  have e1 := BstLean.Part170.normSq_perp_eq (n := n) r (perp h y)
  have e2 := BstLean.Part170.normSq_perp_eq (n := n) h y
  have hq1 : q1 c y ^ 2 = tA n * ((normSq h)⁻¹ * (∑ j, y j * h j) ^ 2) := by
    unfold q1; rw [sq_q_aux _ _ _ (normSq_nonneg' _) ht, sum_comm_dot]
  have hq2 : q2 c g y ^ 2 = tA n * ((normSq r)⁻¹ * (∑ j, perp h y j * r j) ^ 2) := by
    unfold q2
    rw [sq_q_aux _ _ _ (normSq_nonneg' _) ht, sum_comm_dot, ← BstLean.Part170.perp_eq_res (hB c) y]
  rw [hq1, hq2, e1, e2]
  ring

lemma int_normSq_bdd {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
    {m : ℕ} {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (i : Fin m) :
    Integrable (fun v => a v i) μ :=
  bdd_int ((measurable_pi_apply i).comp ha) (C := K) fun v => (norm_le_pi_norm (a v) i).trans (hK v)

/-- `ς² = t_A E_v|a − ā|²`. -/
lemma vsig2_eq (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) :
    vsig2 c s = tA n * ∫ v, normSq (aLat c s v - a1Bar c s) ∂stdGauss (Fin (n - 1)) := by
  have ha := measurable_aLat c s
  have hK := aLat_bdd hn c hs hO h1
  have hi : ∀ i, Integrable (fun v => aLat c s v i) (stdGauss (Fin (n - 1))) :=
    fun i => int_normSq_bdd ha hK i
  have hi2 : ∀ i, Integrable (fun v => aLat c s v i ^ 2) (stdGauss (Fin (n - 1))) := fun i =>
    bdd_int (((measurable_pi_apply i).comp ha).pow_const 2) (C := O ^ 2) fun v =>
      sq_abs_le ((norm_le_pi_norm (aLat c s v) i).trans (hK v))
  have hmean : ∀ i, ∫ v, aLat c s v i ∂stdGauss (Fin (n - 1)) = a1Bar c s i := fun i => rfl
  have hj : ∀ i, Integrable (fun v => (aLat c s v i - a1Bar c s i) ^ 2) (stdGauss (Fin (n - 1))) := by
    intro i
    have := ((hi2 i).sub ((hi i).const_mul (2 * a1Bar c s i))).add (integrable_const (a1Bar c s i ^ 2))
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  have hvar : ∀ i, ∫ v, (aLat c s v i - a1Bar c s i) ^ 2 ∂stdGauss (Fin (n - 1)) =
      e1Bar c s i - a1Bar c s i ^ 2 := by
    intro i
    have e : ∀ v, (aLat c s v i - a1Bar c s i) ^ 2 =
        aLat c s v i ^ 2 - 2 * a1Bar c s i * aLat c s v i + a1Bar c s i ^ 2 := fun v => by ring
    simp_rw [e]
    have j1 : Integrable (fun v => aLat c s v i ^ 2 - 2 * a1Bar c s i * aLat c s v i)
        (stdGauss (Fin (n - 1))) := (hi2 i).sub ((hi i).const_mul _)
    rw [integral_add j1 (integrable_const _), integral_sub (hi2 i) ((hi i).const_mul _),
      integral_const_mul, hmean]
    simp only [integral_const, probReal_univ, one_smul]
    have : e1Bar c s i = ∫ v, aLat c s v i ^ 2 ∂stdGauss (Fin (n - 1)) := rfl
    rw [this]; ring
  have hsum : ∫ v, normSq (aLat c s v - a1Bar c s) ∂stdGauss (Fin (n - 1)) =
      ∑ i, e1Bar c s i - normSq (a1Bar c s) := by
    unfold normSq
    simp only [Pi.sub_apply]
    rw [integral_finsetSum _ fun i _ => hj i]
    simp_rw [hvar]; rw [Finset.sum_sub_distrib]
  have hnn : 0 ≤ ∑ i, e1Bar c s i - normSq (a1Bar c s) := by
    rw [← hsum]; exact integral_nonneg fun v => normSq_nonneg' _
  unfold vsig2
  rw [max_eq_right (mul_nonneg (by positivity) hnn), hsum]
  rfl

lemma int_normSq_dev (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) :
    Integrable (fun v => normSq (aLat c s v - a1Bar c s)) (stdGauss (Fin (n - 1))) := by
  have ha := measurable_aLat c s
  have hK := aLat_bdd hn c hs hO h1
  have hi : ∀ i, Integrable (fun v => aLat c s v i) (stdGauss (Fin (n - 1))) :=
    fun i => int_normSq_bdd ha hK i
  have hi2 : ∀ i, Integrable (fun v => aLat c s v i ^ 2) (stdGauss (Fin (n - 1))) := fun i =>
    bdd_int (((measurable_pi_apply i).comp ha).pow_const 2) (C := O ^ 2) fun v =>
      sq_abs_le ((norm_le_pi_norm (aLat c s v) i).trans (hK v))
  have hj : ∀ i, Integrable (fun v => (aLat c s v i - a1Bar c s i) ^ 2) (stdGauss (Fin (n - 1))) := by
    intro i
    have := ((hi2 i).sub ((hi i).const_mul (2 * a1Bar c s i))).add (integrable_const (a1Bar c s i ^ 2))
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  unfold normSq
  simp only [Pi.sub_apply]
  exact integrable_finsetSum _ fun i _ => hj i

lemma measurable_wT (c : Ret n) (g : ℕ) : Measurable (wT c g) := by
  unfold wT
  exact measurable_const.mul (BstLean.Part130.continuous_normSq.measurable.comp
    ((BstLean.Part167.measurable_perp _).comp ((BstLean.Part167.measurable_perp _).comp
      (measurable_aLat c (nodeS c g)))))

/-- **`hUN = DstN`**: the two forms of the paper's `h_U` agree (on `‖A₁‖_op ≤ O`). -/
theorem hUN_eq_DstN (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) : hUN c g = DstN c g := by
  set s := nodeS c g
  set y : (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ := fun v => aLat c s v - a1Bar c s with hy
  have hpt : ∀ v, q1 c (y v) ^ 2 + q2 c g (y v) ^ 2 = tA n * normSq (y v) - wT c g v := by
    intro v
    have hp := pyth c g (y v)
    have e : perp (res (hB c) (a1Bar c s)) (perp (hB c) (y v)) =
        perp (res (hB c) (a1Bar c s)) (perp (hB c) (aLat c s v)) := by
      simp only [hy]
      rw [perp_sub', perp_sub', BstLean.Part170.perp_perp_res, sub_zero]
    rw [e] at hp
    unfold wT; linarith
  have iy := int_normSq_dev hn c hs hO h1
  have iw : Integrable (wT c g) (stdGauss (Fin (n - 1))) :=
    bdd_int (measurable_wT c g) (C := tA n * O ^ 2) fun v => by
      rw [abs_of_nonneg (by unfold wT; exact mul_nonneg (tA_nonneg n) (normSq_nonneg' _))]
      unfold wT
      exact mul_le_mul_of_nonneg_left ((BstLean.Part167.normSq_perp_le _ _).trans
        ((BstLean.Part167.normSq_perp_le _ _).trans (aLat_normSq_le hn c hs h1 v))) (tA_nonneg n)
  have hD : DstN c g = tA n * ∫ v, normSq (y v) ∂stdGauss (Fin (n - 1)) -
      ∫ v, wT c g v ∂stdGauss (Fin (n - 1)) := by
    unfold DstN
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub (iy.const_mul _) iw,
      integral_const_mul]
  have hv := vsig2_eq hn c hs hO h1
  unfold hUN
  rw [integral_sub iw (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  rw [hv, show tA n * ∫ v, normSq (aLat c s v - a1Bar c s) ∂stdGauss (Fin (n - 1)) =
    tA n * ∫ v, normSq (y v) ∂stdGauss (Fin (n - 1)) from rfl]
  rw [abs_sub_comm, abs_of_nonneg (by rw [← hD]; exact BstLean.Part171.DstN_nonneg c g), hD]

/-- `e₁ = (|h|⁻²√t_A|h|)·h`: `q₁(y) = e₁·y`. -/
noncomputable def e1v (c : Ret n) : Fin (mA n) → ℝ :=
  ((normSq (hB c))⁻¹ * (√(tA n) * √(normSq (hB c)))) • hB c

/-- `e₂ = (|r|⁻²√t_A|r|)·r`, `r = res h ā`: `q₂(y) = e₂·y`. -/
noncomputable def e2v (c : Ret n) (g : ℕ) : Fin (mA n) → ℝ :=
  ((normSq (res (hB c) (a1Bar c (nodeS c g))))⁻¹ *
    (√(tA n) * √(normSq (res (hB c) (a1Bar c (nodeS c g)))))) • res (hB c) (a1Bar c (nodeS c g))

lemma q1_eq_dot (c : Ret n) (y : Fin (mA n) → ℝ) : q1 c y = e1v c ⬝ᵥ y := by
  unfold q1 e1v; rw [smul_dotProduct, smul_eq_mul]; ring

lemma q2_eq_dot (c : Ret n) (g : ℕ) (y : Fin (mA n) → ℝ) : q2 c g y = e2v c g ⬝ᵥ y := by
  unfold q2 e2v
  rw [smul_dotProduct, smul_eq_mul, ← BstLean.Part170.perp_eq_res (hB c) y,
    ← BstLean.Part170.perp_dot, BstLean.Part167.perp_res]
  ring

/-- **The LS step for one direction**: `(n − 2)·E_v(e·(a − ā))² ≤ E_v tanSq Φ_e`,
`Φ_e(x) = e·ReLU(A₁x)` (on `‖A₁‖_op ≤ O`). -/
theorem ls_dot (hn : 3 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) (e : Fin (mA n) → ℝ) :
    ((n : ℝ) - 2) * ∫ v, (e ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2 ∂stdGauss (Fin (n - 1)) ≤
      ∫ v, BstLean.Part162.tanSq (fun x => e ⬝ᵥ reluV ((A1 c) *ᵥ x)) c s v
        ∂stdGauss (Fin (n - 1)) := by
  have hn1 : 1 ≤ n := by omega
  set Φ : (Fin n → ℝ) → ℝ := fun x => e ⬝ᵥ reluV ((A1 c) *ᵥ x) with hΦ
  set L := √(normSq e) * O with hLd
  have hL0 : 0 ≤ L := by positivity
  have hL : BstLean.Part148.EuLip Φ L := by
    intro x y
    simp only [hΦ]
    rw [← dotProduct_sub]
    refine (BstLean.Part170.abs_dot_le _ _).trans ?_
    rw [hLd, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have h2 := BstLean.Part169.normSq_reluV_sub ((A1 c) *ᵥ x) ((A1 c) *ᵥ y)
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
  have hK := aLat_bdd hn1 c hs hO h1
  have hmean : ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1)) =
      e ⬝ᵥ vmean (stdGauss (Fin (n - 1))) (aLat c s) :=
    BstLean.Part170.int_dot (measurable_aLat c s) hK e
  have heq : ∀ v, Φ (xLat c s (unitF53 v)) - ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))
      = e ⬝ᵥ (aLat c s v - a1Bar c s) := by
    intro v; rw [hmean, dotProduct_sub, vmean_aLat]; rfl
  simp_rw [heq] at hls
  exact hls

/-- **The LS step for `h_U`** (paper `t7:p08:statistics`, first line, Lean's constant):
`(n − 2)·DstN ≤ E_v tanSq Φ_{e₁} + E_v tanSq Φ_{e₂}` on `‖A₁‖_op ≤ O`. -/
theorem DstN_le_tan (hn : 3 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) :
    ((n : ℝ) - 2) * DstN c g ≤
      ∫ v, BstLean.Part162.tanSq (fun x => e1v c ⬝ᵥ reluV ((A1 c) *ᵥ x)) c (nodeS c g) v
        ∂stdGauss (Fin (n - 1)) +
      ∫ v, BstLean.Part162.tanSq (fun x => e2v c g ⬝ᵥ reluV ((A1 c) *ᵥ x)) c (nodeS c g) v
        ∂stdGauss (Fin (n - 1)) := by
  have hn1 : 1 ≤ n := by omega
  set s := nodeS c g
  have iy := int_normSq_dev hn1 c hs hO h1
  have hmeas : ∀ e : Fin (mA n) → ℝ, Measurable (fun v => (e ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2) :=
    fun e => ((continuous_const.dotProduct continuous_id).measurable.comp
      ((measurable_aLat c s).sub_const _)).pow_const 2
  have hint : ∀ e : Fin (mA n) → ℝ, Integrable (fun v => (e ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2)
      (stdGauss (Fin (n - 1))) := by
    intro e
    refine Integrable.mono' (iy.const_mul (normSq e)) (hmeas e).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := BstLean.Part170.abs_dot_le e (aLat c s v - a1Bar c s)
    have h2 : (e ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2 ≤ (√(normSq e) * √(normSq (aLat c s v - a1Bar c s))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rwa [mul_pow, Real.sq_sqrt (normSq_nonneg' _), Real.sq_sqrt (normSq_nonneg' _)] at h2
  have hD : DstN c g = ∫ v, (e1v c ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2 ∂stdGauss (Fin (n - 1)) +
      ∫ v, (e2v c g ⬝ᵥ (aLat c s v - a1Bar c s)) ^ 2 ∂stdGauss (Fin (n - 1)) := by
    unfold DstN
    simp_rw [q1_eq_dot, q2_eq_dot]
    exact integral_add (hint _) (hint _)
  rw [hD, mul_add]
  exact add_le_add (ls_dot hn c hs hO h1 _) (ls_dot hn c hs hO h1 _)

end BstLean.Part171
