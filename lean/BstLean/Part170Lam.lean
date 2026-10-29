import BstLean.Part170Fl

/-!
# Part 170 (file `Lam`): the covariance bound of the first-layer field on a latitude

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, formula `t7:p08:cov`: `‖H_s‖_op ≤ ℓ_s²`, by sphere Poincaré.
Lean's form (Part 162's `ls_lat`; the tangential term is at most the full squared gradient of
the lift, which is at most `L²`): for every `e ∈ ℝ^m`,
`E_v ⟨e, a₁(x_v) − ā⟩² ≤ (O₁²/(n − 2))·|e|²` on `‖A₁‖_op ≤ O₁`, at every latitude `s² ≤ 1`.
The paper has `(1 − s²)O₁²/(n − 2)`; Lean's constant is larger by `1/(1 − s²)`.

* `aLat c s v = ReLU(A₁ x_s(v))`: the first-layer field on the latitude sphere.
* `aLat_bdd`: `‖aLat c s v‖ ≤ O₁` (sup norm).
* **`cov_bound`**: `E_v ⟨e, aLat − ā⟩² ≤ O₁²/(n − 2)·|e|²`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part148 (EuLip)

variable {n : ℕ}

/-- The first-layer field `ReLU(A₁ x_s(v))` on the latitude sphere. -/
noncomputable def aLat (c : Ret n) (s : ℝ) (v : Fin (n - 1) → ℝ) : Fin (mA n) → ℝ :=
  reluV ((A1 c) *ᵥ xLat c s (unitF53 v))

lemma measurable_aLat (c : Ret n) (s : ℝ) : Measurable (aLat c s) := by
  unfold aLat
  have hx := measurable_xLat_joint (C := fun _ : Fin (n - 1) → ℝ => c) (f := fun _ => s)
    measurable_const measurable_const measurable_unitF
  exact measurable_pi_iff.mpr fun i => measurable_relu.comp ((measurable_pi_apply i).comp
    (BstLean.Part149.measurable_mulVec_joint.comp (measurable_const.prodMk hx)))

lemma abs_le_sqrt_normSq {ι : Type*} [Fintype ι] (y : ι → ℝ) (i : ι) : |y i| ≤ √(normSq y) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => y j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

lemma aLat_bdd (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) (v : Fin (n - 1) → ℝ) : ‖aLat c s v‖ ≤ O := by
  refine (pi_norm_le_iff_of_nonneg hO).mpr fun i => ?_
  unfold aLat reluV
  rw [Real.norm_eq_abs]
  have hx := normSq_xLat_le' hn c hs v
  have h2 : normSq ((A1 c) *ᵥ xLat c s (unitF53 v)) ≤ O ^ 2 :=
    (h1 _).trans (by nlinarith [sq_nonneg O])
  have hr : |relu (((A1 c) *ᵥ xLat c s (unitF53 v)) i)| ≤ |((A1 c) *ᵥ xLat c s (unitF53 v)) i| := by
    unfold relu
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (abs_nonneg _) (le_abs_self _)
  refine hr.trans ((abs_le_sqrt_normSq _ i).trans ?_)
  rw [Real.sqrt_le_left hO]; exact h2

lemma abs_dot_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) : |x ⬝ᵥ y| ≤ √(normSq x) * √(normSq y) := by
  unfold dotProduct normSq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |x i|) (fun i => |y i|)
  simp only [sq_abs] at this
  simpa only [abs_mul] using this

/-- **The covariance bound** (paper `t7:p08:cov`, Lean's constant): on `‖A₁‖_op ≤ O`, at every
latitude with `s² ≤ 1`, `E_v ⟨e, a₁(x_v) − ā⟩² ≤ (O²/(n − 2))·|e|²`. -/
theorem cov_bound (hn : 3 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) (e : Fin (mA n) → ℝ) :
    ∫ v, (e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2
        ∂stdGauss (Fin (n - 1)) ≤ O ^ 2 / ((n : ℝ) - 2) * normSq e := by
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
  have bT1 : ∀ v, BstLean.Part162.tanSq Φ c s v ≤ L ^ 2 := fun v => by
    unfold BstLean.Part162.tanSq
    have := BstLean.Part151.gradSq_le hL0 (BstLean.Part162.lift_euLip (by omega) c hs hL0 hL) v
    nlinarith [sq_nonneg (Φ (xLat c s (unitF53 v)))]
  have mT := BstLean.Part162.measurable_tanSq_left hc c s
  have hT : ∫ v, (BstLean.Part151.gradSq (fun w => Φ (BstLean.Part162.xLatH c s w)) v -
      Φ (xLat c s (unitF53 v)) ^ 2) ∂stdGauss (Fin (n - 1)) ≤ L ^ 2 := by
    calc _ = ∫ v, BstLean.Part162.tanSq Φ c s v ∂stdGauss (Fin (n - 1)) := rfl
      _ ≤ ∫ _v, L ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mT.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact bT v))
            (integrable_const _) bT1
      _ = L ^ 2 := by simp
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
  rw [div_mul_eq_mul_div, le_div_iff₀ h2n]
  nlinarith [hls, hT]

end BstLean.Part170
