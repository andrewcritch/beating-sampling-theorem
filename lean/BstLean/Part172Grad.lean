import BstLean.Part171All

/-!
# Part 172 (file `Grad`): the tangential gradients of the first-layer fields

No proof is left open; no `native_decide` or `axiom` is used.

Setting: `x = xLat c s (unitF53 v)`, `u = uHat c`, `w = dirW c (unitF53 v)`, a matrix `A`.

* **`tan_dot`**: for `Φ_e(y) = e·ReLU(Ay)`, at a point with no zero preactivation,
  `tanSq Φ_e c s v = (1 − s²)·latSq((D₁A)ᵀe, u, w)`.
* **`tan_sqrtw`**: for `S(y) = √t·|perp r (perp h (ReLU(Ay)))|` with `r ⊥ h`, at a point with no
  zero preactivation, `tanSq S c s v ≤ (1 − s²)·latSq((D₁A)ᵀ(√t·ĉ'), u, w)`, `ĉ' = P/|P|`
  (`0` if `P = 0`), `P = perp r (perp h (ReLU(Ax)))`.
* `S_hom`, `S_lip`: `S` is positively 1-homogeneous and `√t·O`-Lipschitz on `‖A‖_op ≤ O`.
* **`kink_null`**, **`kink_ae`**: the kink set `{(A, v) | ∃ i, (A x_v)_i = 0}` is measurable and
  null under `gaussMat ⊗ stdGauss`; so for a.e. `A`, for a.e. `v`, there is no kink.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Set Filter Matrix Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part134 (projPerp projPerp_mulVec res)
open BstLean.Part151 (mask mask_of_pos mask_of_nonpos gradSq)
open BstLean.Part161 (xLat uHat)
open BstLean.Part162 (xLatH tanSq xLatH_eq dirW radF_pos)
open BstLean.Part167 (perp latSq D1A1 tanSq_of_hasFDerivAt relu1_eventually
  hasFDerivAt_nrm_mulVec normSq_perp_le perp_smul vecMul_projPerp)
open BstLean.Part166 (bhat)
open BstLean.Part53 (unitF53 radF53)

variable {n : ℕ}

/-! ## §1 Algebra of `perp` -/

lemma gr_perp_orth {m : ℕ} (b z : Fin m → ℝ) : ∑ j, perp b z j * b j = 0 := by
  by_cases hb : b = 0
  · subst hb; simp
  · rw [BstLean.Part170.perp_eq_res]; exact BstLean.Part134.res_orth hb z

lemma gr_perp_of_orth {m : ℕ} {b z : Fin m → ℝ} (hz : ∑ j, z j * b j = 0) : perp b z = z := by
  unfold perp; rw [hz]; simp

/-- `P = perp r (perp h a)` is fixed by `perp r` and by `perp h` when `r ⊥ h`. -/
lemma gr_perp_fix {m : ℕ} {h r : Fin m → ℝ} (hrh : ∑ j, r j * h j = 0) (a : Fin m → ℝ) :
    perp h (perp r (perp r (perp h a))) = perp r (perp h a) := by
  set X := perp h a
  have h1 : perp r (perp r X) = perp r X := gr_perp_of_orth (gr_perp_orth r X)
  rw [h1]
  apply gr_perp_of_orth
  have hX : ∑ j, X j * h j = 0 := gr_perp_orth h a
  set k := (normSq r)⁻¹ * ∑ i, X i * r i
  show ∑ j, (X j - k * r j) * h j = 0
  have e : ∀ j, (X j - k * r j) * h j = X j * h j - k * (r j * h j) := fun j => by ring
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, ← Finset.mul_sum, hX, hrh]
  ring

lemma gr_mulVec_perp {m : ℕ} (b z : Fin m → ℝ) : projPerp b *ᵥ z = perp b z := by
  rw [projPerp_mulVec, BstLean.Part170.perp_eq_res]

lemma gr_normSq_smul {m : ℕ} (k : ℝ) (z : Fin m → ℝ) : normSq (k • z) = k ^ 2 * normSq z := by
  unfold normSq
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]

lemma gr_bhat_smul {m : ℕ} {k : ℝ} (hk : 0 < k) (z : Fin m → ℝ) : bhat (k • z) = bhat z := by
  unfold bhat
  rw [gr_normSq_smul, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le, smul_smul, mul_inv]
  congr 1
  field_simp

/-! ## §2 The point of the lift and the local linearity -/

lemma gr_mask_smul {k t : ℝ} (hk : 0 < k) : mask (k * t) = mask t := by
  unfold mask
  by_cases h : 0 < t
  · simp [h, mul_pos hk h]
  · have : ¬ 0 < k * t := by
      intro h'; exact h (pos_of_mul_pos_right h' hk.le)
    simp [h, this]

lemma gr_mulVec_H (c : Ret n) (s : ℝ) (v : Fin (n - 1) → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    A *ᵥ xLatH c s v = radF53 v • (A *ᵥ xLat c s (unitF53 v)) := by
  rw [xLatH_eq, Matrix.mulVec_smul]

lemma gr_D1A1_mulVec {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (x z : Fin k → ℝ) (i : Fin m) :
    (D1A1 A x *ᵥ z) i = mask ((A *ᵥ x) i) * (A *ᵥ z) i := by
  simp only [D1A1, mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Near `xLatH c s v` (no kink at `x`), `ReLU(Az) = (D₁A)z` with the gates of `x`. -/
lemma gr_relu_loc {c : Ret n} {s : ℝ} {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ} (hK : ∀ i, (A *ᵥ xLat c s (unitF53 v)) i ≠ 0) :
    ∀ᶠ z in 𝓝 (xLatH c s v), reluV (A *ᵥ z) = D1A1 A (xLat c s (unitF53 v)) *ᵥ z := by
  have hr := radF_pos hv
  have hK' : ∀ i, (A *ᵥ xLatH c s v) i ≠ 0 := by
    intro i; rw [gr_mulVec_H, Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero hr.ne' (hK i)
  filter_upwards [relu1_eventually hK'] with z hz
  funext i
  rw [hz i, gr_D1A1_mulVec, gr_mulVec_H, Pi.smul_apply, smul_eq_mul, gr_mask_smul hr]

/-! ## §3 `tan_dot` -/

/-- **The tangential gradient of `Φ_e(y) = e·ReLU(Ay)`** at a point with no kink. -/
theorem tan_dot (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (e : Fin (mA n) → ℝ) (hK : ∀ i, (A *ᵥ xLat c s (unitF53 v)) i ≠ 0) :
    tanSq (fun y => e ⬝ᵥ reluV (A *ᵥ y)) c s v =
      (1 - s ^ 2) * latSq (vecMul e (D1A1 A (xLat c s (unitF53 v)))) (uHat c)
        (dirW c (unitF53 v)) := by
  set x := xLat c s (unitF53 v)
  set g := vecMul e (D1A1 A x) with hg
  set Lc : (Fin n → ℝ) →L[ℝ] ℝ := ∑ l, g l • (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ)
    with hLc
  have hLa : ∀ d, Lc d = 1 * ∑ l, g l * d l := by intro d; simp [hLc]
  have hloc : (fun y => e ⬝ᵥ reluV (A *ᵥ y)) =ᶠ[𝓝 (xLatH c s v)] fun z => Lc z := by
    filter_upwards [gr_relu_loc hv hK] with z hz
    show e ⬝ᵥ reluV (A *ᵥ z) = Lc z
    rw [hz, hLa, one_mul, Matrix.dotProduct_mulVec]
    rfl
  have hd : HasFDerivAt (fun y => e ⬝ᵥ reluV (A *ᵥ y)) Lc (xLatH c s v) :=
    Lc.hasFDerivAt.congr_of_eventuallyEq hloc
  have hhom : ∀ (t : ℝ) (y : Fin n → ℝ), 0 < t →
      e ⬝ᵥ reluV (A *ᵥ (t • y)) = t * (e ⬝ᵥ reluV (A *ᵥ y)) := by
    intro t y ht
    rw [Matrix.mulVec_smul, reluV_smul_of_nonneg ht.le, dotProduct_smul, smul_eq_mul]
  rw [tanSq_of_hasFDerivAt hn hc hs hhom hv hd hLa]
  ring

/-! ## §4 `S = √t·|P(ReLU(Ay))|` -/

/-- The field `S(y) = √t·|perp r (perp h (ReLU(Ay)))|` (the paper's `√(v_v)`). -/
noncomputable def Sfld (t : ℝ) (h r : Fin (mA n) → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (y : Fin n → ℝ) : ℝ :=
  √t * √(normSq (perp r (perp h (reluV (A *ᵥ y)))))

/-- The unit direction `ĉ' = P/|P|` (`0` if `P = 0`) at the point `x`. -/
noncomputable def cdir (h r : Fin (mA n) → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (x : Fin n → ℝ) : Fin (mA n) → ℝ :=
  bhat (perp r (perp h (reluV (A *ᵥ x))))

lemma S_hom (t : ℝ) (h r : Fin (mA n) → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) (k : ℝ)
    (y : Fin n → ℝ) (hk : 0 < k) : Sfld t h r A (k • y) = k * Sfld t h r A y := by
  unfold Sfld
  rw [Matrix.mulVec_smul, reluV_smul_of_nonneg hk.le, perp_smul, perp_smul, gr_normSq_smul,
    Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le]
  ring

lemma gr_sqrt_sub_le {m : ℕ} (a b : Fin m → ℝ) :
    |√(normSq a) - √(normSq b)| ≤ √(normSq (a - b)) := by
  have key : ∀ a b : Fin m → ℝ, √(normSq a) ≤ √(normSq (a - b)) + √(normSq b) := by
    intro a b
    have h := abs_dot_le' (a - b) b
    have e : a = (a - b) + b := by abel
    have h2 : normSq ((a - b) + b) ≤ (√(normSq (a - b)) + √(normSq b)) ^ 2 := by
      have hu : 0 ≤ normSq (a - b) := by unfold normSq; positivity
      have hw : 0 ≤ normSq b := by unfold normSq; positivity
      have ex : normSq ((a - b) + b) = normSq (a - b) + 2 * ((a - b) ⬝ᵥ b) + normSq b := by
        unfold normSq dotProduct
        simp only [Pi.add_apply]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [ex, add_sq, Real.sq_sqrt hu, Real.sq_sqrt hw]
      have := (abs_le.mp h).2
      nlinarith [Real.sqrt_nonneg (normSq (a - b)), Real.sqrt_nonneg (normSq b)]
    rw [← e] at h2
    calc √(normSq a) ≤ √((√(normSq (a - b)) + √(normSq b)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = _ := Real.sqrt_sq (by positivity)
  rw [abs_le]
  constructor
  · have h1 := key b a
    have e : normSq (b - a) = normSq (a - b) := by
      unfold normSq; exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
    rw [e] at h1; linarith
  · linarith [key a b]
where
  abs_dot_le' {m : ℕ} (x y : Fin m → ℝ) : |x ⬝ᵥ y| ≤ √(normSq x) * √(normSq y) :=
    BstLean.Part170.abs_dot_le x y

lemma S_lip (t : ℝ) (h r : Fin (mA n) → ℝ) {A : Matrix (Fin (mA n)) (Fin n) ℝ}
    {O : ℝ} (hO : 0 ≤ O) (h1 : BstLean.Part169.OpB A O) :
    BstLean.Part148.EuLip (Sfld t h r A) (√t * O) := by
  intro x y
  unfold Sfld
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg t)
  refine (gr_sqrt_sub_le _ _).trans ?_
  rw [← BstLean.Part171.perp_sub', ← BstLean.Part171.perp_sub']
  have e4 : normSq (x - y) = ∑ i, (x i - y i) ^ 2 := rfl
  rw [← e4, ← Real.sqrt_sq hO, ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  refine (normSq_perp_le _ _).trans ((normSq_perp_le _ _).trans ?_)
  have h2 := BstLean.Part169.normSq_reluV_sub (A *ᵥ x) (A *ᵥ y)
  rw [← Matrix.mulVec_sub] at h2
  exact h2.trans (h1 _)

/-- **The tangential gradient of `S`** at a point with no kink. -/
theorem tan_sqrtw (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (t : ℝ) (h r : Fin (mA n) → ℝ) (hrh : ∑ j, r j * h j = 0)
    (hK : ∀ i, (A *ᵥ xLat c s (unitF53 v)) i ≠ 0) :
    tanSq (Sfld t h r A) c s v ≤
      (1 - s ^ 2) * latSq (vecMul (√t • cdir h r A (xLat c s (unitF53 v)))
        (D1A1 A (xLat c s (unitF53 v)))) (uHat c) (dirW c (unitF53 v)) := by
  set x := xLat c s (unitF53 v) with hx
  set y0 := xLatH c s v with hy0
  set D := D1A1 A x with hD
  set P := perp r (perp h (reluV (A *ᵥ x))) with hP
  have hr0 := radF_pos hv
  have hy0x : y0 = radF53 v • x := xLatH_eq c s v
  have hSy : Sfld t h r A y0 = radF53 v * Sfld t h r A x := by
    rw [hy0x]; exact S_hom t h r A _ x hr0
  by_cases hP0 : normSq P = 0
  · -- `P = 0`: a minimum
    have hSx : Sfld t h r A x = 0 := by unfold Sfld; rw [← hP, hP0]; simp
    have hmin : IsLocalMin (fun w => Sfld t h r A (xLatH c s w)) v := by
      refine Filter.Eventually.of_forall fun w => ?_
      show Sfld t h r A y0 ≤ Sfld t h r A (xLatH c s w)
      rw [hSy, hSx, mul_zero]; unfold Sfld; positivity
    have hT : tanSq (Sfld t h r A) c s v = 0 := by
      unfold tanSq gradSq
      rw [hmin.fderiv_eq_zero, ← hx, hSx]; simp
    have hcd : cdir h r A x = 0 := by
      unfold cdir bhat; rw [← hP, hP0]; simp
    rw [hT, hcd, smul_zero]
    have : vecMul (0 : Fin (mA n) → ℝ) D = 0 := by funext l; simp [vecMul]
    rw [this]; unfold latSq; simp
  · -- `P ≠ 0`: differentiable
    set R : Matrix (Fin (mA n)) (Fin n) ℝ := projPerp r * projPerp h * D with hR
    have hRz : ∀ z, R *ᵥ z = perp r (perp h (D *ᵥ z)) := by
      intro z
      rw [hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gr_mulVec_perp, gr_mulVec_perp]
    have hloc : Sfld t h r A =ᶠ[𝓝 y0] fun z => √t * √(normSq (R *ᵥ z)) := by
      filter_upwards [gr_relu_loc hv hK] with z hz
      unfold Sfld; rw [hz, hRz]
    have hDx : D *ᵥ x = reluV (A *ᵥ x) := by
      funext i
      rw [hD, gr_D1A1_mulVec]
      rcases lt_or_gt_of_ne (hK i) with hneg | hpos
      · simp [mask_of_nonpos hneg.le, reluV, relu_of_nonpos hneg.le]
      · simp [mask_of_pos hpos, reluV, relu_of_nonneg hpos.le]
    have hRy : R *ᵥ y0 = radF53 v • P := by
      rw [hy0x, Matrix.mulVec_smul, hRz, hDx]
    have hRy0 : normSq (R *ᵥ y0) ≠ 0 := by
      rw [hRy, gr_normSq_smul]; exact mul_ne_zero (pow_ne_zero 2 hr0.ne') hP0
    obtain ⟨L0, hL0, hL0a⟩ := hasFDerivAt_nrm_mulVec R hRy0
    have hd : HasFDerivAt (Sfld t h r A) (√t • L0) y0 :=
      (hL0.const_mul √t).congr_of_eventuallyEq hloc
    have hg : vecMul (bhat (R *ᵥ y0)) R = vecMul (cdir h r A x) D := by
      rw [hRy, gr_bhat_smul hr0, hR, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
        vecMul_projPerp, vecMul_projPerp]
      congr 1
      show perp h (perp r (bhat P)) = bhat P
      unfold bhat
      rw [perp_smul, perp_smul, hP, gr_perp_fix hrh]
    have hLa : ∀ d, (√t • L0) d =
        1 * ∑ l, vecMul (√t • cdir h r A x) D l * d l := by
      intro d
      rw [_root_.smul_apply, hL0a, hg, smul_eq_mul, one_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]; ring
    have hhom : ∀ (k : ℝ) (y : Fin n → ℝ), 0 < k → Sfld t h r A (k • y) = k * Sfld t h r A y :=
      fun k y hk => S_hom t h r A k y hk
    rw [tanSq_of_hasFDerivAt hn hc hs hhom hv hd hLa]
    ring_nf; exact le_rfl

/-! ## §5 The kink set is null -/

/-- The kink set of the first layer on the latitude sphere. -/
def kinkSet (c : Ret n) (s : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ)) :=
  {p | ∃ i, (p.1 *ᵥ xLat c s (unitF53 p.2)) i = 0}

lemma gr_meas_coord (c : Ret n) (s : ℝ) (i : Fin (mA n)) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      (p.1 *ᵥ xLat c s (unitF53 p.2)) i) :=
  (measurable_pi_apply i).comp (BstLean.Part149.measurable_mulVec_joint.comp
    (measurable_fst.prodMk (BstLean.Part161.measurable_xLat_comp c measurable_const
      (BstLean.Part53.measurable_unitF.comp measurable_snd))))

lemma gr_xLat_ne (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {v : Fin (n - 1) → ℝ}
    (hv : v ≠ 0) : xLat c s (unitF53 v) ≠ 0 := by
  intro h0
  have h1 : normSq (xLat c s (unitF53 v)) = 1 := by
    unfold xLat
    rw [BstLean.Part161.hh_normSq, BstLean.Part161.normSq_consV hn, gr_normSq_smul,
      Real.sq_sqrt (by linarith)]
    have : normSq (unitF53 v) = 1 := by
      rw [show normSq (unitF53 v) = radF53 (unitF53 v) ^ 2 from (BstLean.Part162.radF_sq _).symm,
        BstLean.Part162.radF_unitF hv]; norm_num
    rw [this]; ring
  rw [h0] at h1; simp [normSq] at h1

/-- **The kink set is measurable and null.** -/
theorem kink_null (hn2 : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    MeasurableSet (kinkSet c s) ∧
      ((gaussMat (mA n) n (2 / (n : ℝ))).prod (stdGauss (Fin (n - 1)))) (kinkSet c s) = 0 := by
  have hM : MeasurableSet (kinkSet c s) := by
    have e : kinkSet c s = ⋃ i, (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
        (p.1 *ᵥ xLat c s (unitF53 p.2)) i) ⁻¹' {0} := by
      ext p; simp [kinkSet]
    rw [e]
    exact MeasurableSet.iUnion fun i => (gr_meas_coord c s i) (measurableSet_singleton 0)
  refine ⟨hM, ?_⟩
  have hn : 1 ≤ n := by omega
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  have hn0 : (0 : ℝ) < 2 / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton (μ := (volume : Measure (Fin (n - 1) → ℝ)))
        (0 : Fin (n - 1) → ℝ))
    rw [ae_iff]; simpa using h0
  have hcomp : MeasurableSet {p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) |
      ∀ i, (p.1 *ᵥ xLat c s (unitF53 p.2)) i ≠ 0} := by
    have e : {p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) |
        ∀ i, (p.1 *ᵥ xLat c s (unitF53 p.2)) i ≠ 0} = (kinkSet c s)ᶜ := by
      ext p; simp [kinkSet]
    rw [e]; exact hM.compl
  have hv : ∀ᵐ v ∂stdGauss (Fin (n - 1)), ∀ᵐ A ∂gaussMat (mA n) n (2 / (n : ℝ)),
      ∀ i, (A *ᵥ xLat c s (unitF53 v)) i ≠ 0 := by
    filter_upwards [hnz] with v hv
    rw [ae_all_iff]
    intro i
    exact BstLean.Part167.gaussMat_row_ne hn0 (gr_xLat_ne hn c hs hv) i
  have hA := (Measure.ae_ae_comm (μ := gaussMat (mA n) n (2 / (n : ℝ))) (ν := stdGauss (Fin (n - 1)))
    (p := fun A v => ∀ i, (A *ᵥ xLat c s (unitF53 v)) i ≠ 0) hcomp).mpr hv
  have hP := (Measure.ae_prod_iff_ae_ae hcomp).mpr hA
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hP] with p hp
  simp only [kinkSet, mem_ofPred_eq, not_exists]
  exact hp

/-- **No kink for a.e. `A`, a.e. `v`.** -/
theorem kink_ae (hn : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    ∀ᵐ A ∂gaussMat (mA n) n (2 / (n : ℝ)), ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ i, (A *ᵥ xLat c s (unitF53 v)) i ≠ 0 := by
  obtain ⟨hM, h0⟩ := kink_null hn c hs
  have hcomp : MeasurableSet {p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) |
      ∀ i, (p.1 *ᵥ xLat c s (unitF53 p.2)) i ≠ 0} := by
    have e : {p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) |
        ∀ i, (p.1 *ᵥ xLat c s (unitF53 p.2)) i ≠ 0} = (kinkSet c s)ᶜ := by
      ext p; simp [kinkSet]
    rw [e]; exact hM.compl
  refine (Measure.ae_prod_iff_ae_ae hcomp).mp ?_
  rw [measure_eq_zero_iff_ae_notMem] at h0
  filter_upwards [h0] with p hp
  simpa [kinkSet] using hp

end BstLean.Part172
