import BstLean.Part143LinC
import BstLean.Part145C2

/-!
# Part 145 (K8): the second-order term `δ(Mh, Mh′)` of a Gaussian linear layer, sharper

`M` is a Gaussian matrix with `m` rows and entry variance `v`, `s = m·v`. For unit `h, h′`,
`x = |Mh|²/s − 1`, `y = |Mh′|²/s − 1`, `a = √(1 + x)`, `b = √(1 + y)`, `D = (a − b)²/2 =
δ(Mh, Mh′)/s`, `V = (x − y)²/8`, `u = (x + y)/2`, `mm = max(|x|, |y|)`:
`D = V·(1 − u) + D·u² + D²·(1 − u)/2`, so `D ≤ (x² + y²)/4 + mm³/8 + 2·mm⁴` (`dlt_ptX`).

* `dX m = K4 m/(2m) + (1/8)·√(√2·(K4 m/m)·(√2·qCos m)) + 2·√2·qCos m`, `cDx m = m·dX m`,
  `kX m = cDx m/2` (`kX` is in the place of `K4` of Part 142: `2·K4 m` becomes `cDx m`).
* **`lin_dlt_unit_x`**: unit `h, h′`: `‖δ(Mh, Mh′)‖₂ ≤ cDx m·v` (Part 142: `2·K4 m·v`).
* **`linDltX`**: all `h, h′`: `‖δ(Mh, Mh′) − m·v·δ(h, h′)‖₂ ≤
    m·v·(cDx m/(2m)·(|h|² + |h′|²) + (1/√(2m))·||h|² − |h′|²|)`.
* `remUnit_L2x`, **`linRem_L2x`**: the copies of `remUnit_L2`, `linRem_L2` of `Part143LinC`
  with `kX` in the place of `K4`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142
open BstLean.Part143

/-! ## The pointwise bound -/

/-- `D ≤ (x² + y²)/4 + mm³/8 + 2·mm⁴` for `D = (a − b)²/2`, `x = a² − 1`, `y = b² − 1`. -/
lemma dlt_ptX {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 / 2 ≤ ((a ^ 2 - 1) ^ 2 + (b ^ 2 - 1) ^ 2) / 4 +
      1 / 8 * max |a ^ 2 - 1| |b ^ 2 - 1| ^ 3 + 2 * max |a ^ 2 - 1| |b ^ 2 - 1| ^ 4 := by
  obtain ⟨x, hx⟩ : ∃ x, x = a ^ 2 - 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = b ^ 2 - 1 := ⟨_, rfl⟩
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = max |x| |y| := ⟨_, rfl⟩
  have hu : |x| ≤ mm := hmm ▸ le_max_left _ _
  have hw : |y| ≤ mm := hmm ▸ le_max_right _ _
  have hm0 : 0 ≤ mm := (abs_nonneg _).trans hu
  obtain ⟨D, hD⟩ : ∃ D, D = (a - b) ^ 2 / 2 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = (x - y) ^ 2 / 8 := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u, u = (x + y) / 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  have hDm2 : D ≤ mm ^ 2 := by
    rw [hD]
    exact half_sq_sub_le_sq ha hb (hx ▸ hu) (hy ▸ hw)
  have hVu : V * |u| ≤ mm ^ 3 / 8 := by
    rw [hV, hud]
    exact ptC_Vu hu hw
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  have hum : |u| ≤ mm := by
    rw [hud, abs_le]
    constructor <;> linarith
  have hum' := abs_le.mp hum
  have hu1 : -1 ≤ u := by
    rw [hud, hx, hy]
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hu2 : u ^ 2 ≤ mm ^ 2 := sq_le_sq' hum'.1 hum'.2
  have hVx : V ≤ (x ^ 2 + y ^ 2) / 4 := by
    rw [hV]
    nlinarith [sq_nonneg (x + y)]
  have hid : D = V * (1 - u) + D * u ^ 2 + D ^ 2 * (1 - u) / 2 := by
    rw [hD, hV, hud, hx, hy]
    ring
  have b1 : V * (1 - u) ≤ V + mm ^ 3 / 8 := by
    have : V * (-u) ≤ V * |u| := mul_le_mul_of_nonneg_left (neg_le_abs u) hV0
    linarith
  have b2 : D * u ^ 2 ≤ mm ^ 4 := by
    have := mul_le_mul hDm2 hu2 (sq_nonneg u) (sq_nonneg mm)
    calc D * u ^ 2 ≤ mm ^ 2 * mm ^ 2 := this
      _ = mm ^ 4 := by ring
  have b3 : D ^ 2 * (1 - u) / 2 ≤ mm ^ 4 := by
    have h1 : D ^ 2 ≤ mm ^ 4 := by
      calc D ^ 2 = D * D := by ring
        _ ≤ mm ^ 2 * mm ^ 2 := mul_le_mul hDm2 hDm2 hD0 (sq_nonneg mm)
        _ = mm ^ 4 := by ring
    have h2 : D ^ 2 * ((1 - u) / 2) ≤ D ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg D)
    linarith
  rw [← hx, ← hy, ← hmm, ← hD]
  linarith

variable {m k : ℕ}

/-! ## The constant -/

/-- The bound of `δ(Mh, Mh′)/(m·v)` for unit `h, h′`. -/
noncomputable def dX (m : ℕ) : ℝ :=
  K4 m / (2 * (m : ℝ)) + 1 / 8 * √(√2 * (K4 m / (m : ℝ)) * (√2 * qCos m)) +
    2 * (√2 * qCos m)

/-- `‖δ(Mh, Mh′)‖₂ ≤ cDx m·v` for unit `h, h′` (in the place of `2·K4 m`). -/
noncomputable def cDx (m : ℕ) : ℝ := (m : ℝ) * dX m

/-- `kX m = cDx m/2`: in the place of `K4 m` in the bounds of Part 142 and Part 143. -/
noncomputable def kX (m : ℕ) : ℝ := cDx m / 2

lemma dX_nonneg (m : ℕ) : 0 ≤ dX m := by
  have := K4_nonneg m
  have := qCos_nonneg m
  unfold dX
  positivity

lemma cDx_nonneg (m : ℕ) : 0 ≤ cDx m := by
  have := dX_nonneg m
  unfold cDx
  positivity

lemma kX_nonneg (m : ℕ) : 0 ≤ kX m := by
  have := cDx_nonneg m
  unfold kX
  positivity

lemma kX_eq (m : ℕ) : kX m = cDx m / 2 := rfl

lemma two_kX (m : ℕ) : 2 * kX m = cDx m := by unfold kX; ring

/-! ## Unit vectors -/

/-- **The second-order term at unit vectors**: `‖δ(Mh, Mh′)‖₂ ≤ cDx m·v`. -/
theorem lin_dlt_unit_x {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => dlt (M.mulVec h) (M.mulVec h')) (cDx m * v) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set s := (m : ℝ) * v with hs
  have hs0 : 0 < s := mul_pos hm0 hv
  set K := √(12 + 48 / (m : ℝ)) / (m : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hQ0 := qCos_nonneg m
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hA : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h) / s - 1) ^ 2) K := by
    have := dev_sq_L2 hv hm h
    rw [hh, one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hB : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h') / s - 1) ^ 2) K := by
    have := dev_sq_L2 hv hm h'
    rw [hh', one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hA4 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h) / s - 1) ^ 4) (qCos m) := by
    have := dev_four_L2 hv hm h
    rw [hh, one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hB4 : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h') / s - 1) ^ 4) (qCos m) := by
    have := dev_four_L2 hv hm h'
    rw [hh', one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hXm : AEStronglyMeasurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (M.mulVec h) / s - 1) (gaussMat m k v) :=
    (((measurable_normSq_mulVec h).div_const _).sub_const _).aestronglyMeasurable
  have hYm : AEStronglyMeasurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (M.mulVec h') / s - 1) (gaussMat m k v) :=
    (((measurable_normSq_mulVec h').div_const _).sub_const _).aestronglyMeasurable
  have hmm : AEStronglyMeasurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      max |normSq (M.mulVec h) / s - 1| |normSq (M.mulVec h') / s - 1|) (gaussMat m k v) :=
    (continuous_abs.comp_aestronglyMeasurable hXm).sup
      (continuous_abs.comp_aestronglyMeasurable hYm)
  have hM2 := l2_max_pow 2 hXm hYm hA hB
  have hM4 := l2_max_pow 4 hXm hYm hA4 hB4
  have hM4' : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (max |normSq (M.mulVec h) / s - 1| |normSq (M.mulVec h') / s - 1| ^ 2) ^ 2)
      (√2 * qCos m) := hM4.congr_fun fun M => by ring
  have t1 := (hA.add' hB hK0 hK0).const_mul_nonneg (c := 1 / 4) (by norm_num)
  have hm2m : AEStronglyMeasurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      max |normSq (M.mulVec h) / s - 1| |normSq (M.mulVec h') / s - 1| ^ 2)
      (gaussMat m k v) := hmm.pow 2
  have t5 := (l2_abs_mul_of_sq (mul_nonneg hs2 hK0) (mul_nonneg hs2 hQ0) hmm hm2m hM2
    hM4').const_mul_nonneg (c := 1 / 8) (by norm_num)
  have t6 := hM4.const_mul_nonneg (c := 2) (by norm_num)
  have htot := (((t1.add' t5 (by positivity) (by positivity)).add' t6 (by positivity)
    (by positivity)).const_mul_nonneg hs0.le)
  refine (L2le.of_abs_le (measurable_dlt_lin h h').aestronglyMeasurable htot
    (fun M => ?_)).congr_bound ?_
  · have hX0 : 0 ≤ normSq (M.mulVec h) := normSq_nonneg _
    have hY0 : 0 ≤ normSq (M.mulVec h') := normSq_nonneg _
    have hr0 : 0 ≤ √s := Real.sqrt_nonneg _
    have hrr : √s ^ 2 = s := Real.sq_sqrt hs0.le
    have ea : nrm (M.mulVec h) = √s * √(normSq (M.mulVec h) / s) := by
      unfold nrm
      rw [← Real.sqrt_mul hs0.le]
      congr 1
      field_simp
    have eb : nrm (M.mulVec h') = √s * √(normSq (M.mulVec h') / s) := by
      unfold nrm
      rw [← Real.sqrt_mul hs0.le]
      congr 1
      field_simp
    have hpt := dlt_ptX (Real.sqrt_nonneg (normSq (M.mulVec h) / s))
      (Real.sqrt_nonneg (normSq (M.mulVec h') / s))
    rw [Real.sq_sqrt (div_nonneg hX0 hs0.le), Real.sq_sqrt (div_nonneg hY0 hs0.le)] at hpt
    have hm0' : 0 ≤ max |normSq (M.mulVec h) / s - 1| |normSq (M.mulVec h') / s - 1| :=
      le_max_of_le_left (abs_nonneg _)
    have e : dlt (M.mulVec h) (M.mulVec h') =
        s * ((√(normSq (M.mulVec h) / s) - √(normSq (M.mulVec h') / s)) ^ 2 / 2) := by
      rw [dlt_eq, ea, eb]
      linear_combination ((√(normSq (M.mulVec h) / s) -
        √(normSq (M.mulVec h') / s)) ^ 2 / 2) * hrr
    rw [abs_of_nonneg (dlt_nonneg _ _), e]
    refine le_trans ?_ (le_abs_self _)
    refine mul_le_mul_of_nonneg_left ?_ hs0.le
    rw [abs_of_nonneg (pow_nonneg hm0' 2), abs_of_nonneg hm0']
    refine hpt.trans (le_of_eq ?_)
    ring
  · rw [hK]
    unfold cDx dX K4
    rw [hs]
    ring

/-- The same with `2·kX m` (the shape of the fourth component of `unit_four`). -/
lemma lin_dlt_unit_k {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => dlt (M.mulVec h) (M.mulVec h')) (2 * kX m * v) :=
  (lin_dlt_unit_x hv hm hh hh').congr_bound (by rw [two_kX])

/-! ## All vectors -/

lemma dlt_smul_smul {ι : Type*} [Fintype ι] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (y y' : ι → ℝ) :
    dlt (a • y) (b • y') = a * b * dlt y y' + (a - b) * (a * normSq y - b * normSq y') / 2 := by
  unfold dlt
  rw [normSq_smul, normSq_smul, BstLean.Part135.nrm_smul_of_nonneg ha,
    BstLean.Part135.nrm_smul_of_nonneg hb]
  ring

/-- **The second-order term of a linear layer, all vectors**, with the product `|h||h′|`. -/
theorem linDltX0 {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        dlt (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * dlt h h')
      ((m : ℝ) * v * (cDx m / (m : ℝ) * (nrm h * nrm h') +
        1 / √(2 * (m : ℝ)) * |normSq h - normSq h'|)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := cDx_nonneg m
  have hs2m : 0 < √(2 * (m : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hs2m2 : √(2 * (m : ℝ)) * √(2 * (m : ℝ)) = 2 * m := Real.mul_self_sqrt (by positivity)
  have hhalf : 1 / 2 * √(2 * (m : ℝ)) = (m : ℝ) / √(2 * (m : ℝ)) := by
    rw [eq_div_iff hs2m.ne']
    calc 1 / 2 * √(2 * (m : ℝ)) * √(2 * (m : ℝ))
        = 1 / 2 * (√(2 * (m : ℝ)) * √(2 * (m : ℝ))) := by ring
      _ = m := by rw [hs2m2]; ring
  have h0 : normSq (0 : Fin k → ℝ) = 0 := by simp [normSq]
  have deg : ∀ g : Fin k → ℝ, L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => (normSq (M.mulVec g) - (m : ℝ) * (v * normSq g)) / 2)
      ((m : ℝ) * v * (1 / √(2 * (m : ℝ)) * normSq g)) := by
    intro g
    have a := (lin_c2 (m := m) hv.le g).const_mul_nonneg (c := 1 / 2) (by norm_num)
    refine (a.congr_fun fun M => by ring).congr_bound ?_
    calc 1 / 2 * (√(2 * (m : ℝ)) * (v * normSq g))
        = 1 / 2 * √(2 * (m : ℝ)) * (v * normSq g) := by ring
      _ = _ := by rw [hhalf]; ring
  by_cases hz : normSq h = 0
  · have : h = 0 := normSq_eq_zero hz
    subst this
    refine ((deg h').congr_fun fun M => ?_).congr_bound ?_
    · rw [Matrix.mulVec_zero, dlt_zero_leftL, dlt_zero_leftL]; ring
    · rw [nrm_zero_of h0, h0, zero_sub, abs_neg, abs_of_nonneg (normSq_nonneg h')]
      ring
  by_cases hz' : normSq h' = 0
  · have : h' = 0 := normSq_eq_zero hz'
    subst this
    refine ((deg h).congr_fun fun M => ?_).congr_bound ?_
    · rw [Matrix.mulVec_zero, dlt_comm (M.mulVec h), dlt_comm h, dlt_zero_leftL,
        dlt_zero_leftL]
      ring
    · rw [nrm_zero_of h0, h0, sub_zero, abs_of_nonneg (normSq_nonneg h)]
      ring
  -- the main case
  set a := nrm h with ha
  set b := nrm h' with hb
  have ha0 : 0 < a := nrm_pos_of_ne hz
  have hb0 : 0 < b := nrm_pos_of_ne hz'
  have eN : normSq h = a ^ 2 := (nrm_sq h).symm
  have eN' : normSq h' = b ^ 2 := (nrm_sq h').symm
  set g : Fin k → ℝ := a⁻¹ • h with hg
  set g' : Fin k → ℝ := b⁻¹ • h' with hg'
  have hgu : normSq g = 1 := normed_unit hz
  have hgu' : normSq g' = 1 := normed_unit hz'
  have ehg : h = a • g := by rw [hg, smul_smul, mul_inv_cancel₀ ha0.ne', one_smul]
  have ehg' : h' = b • g' := by rw [hg', smul_smul, mul_inv_cancel₀ hb0.ne', one_smul]
  have hunit := lin_dlt_unit_x (m := m) hv hm hgu hgu'
  have c2 := lin_c2 (m := m) hv.le g
  have c2' := lin_c2 (m := m) hv.le g'
  rw [hgu, mul_one] at c2
  rw [hgu', mul_one] at c2'
  have p1 := hunit.const_mul_nonneg (c := a * b) (by positivity)
  have p2 := c2.const_mul ((a - b) / 2 * a)
  have p3 := c2'.const_mul (-((a - b) / 2 * b))
  have s12 := p1.add0 p2 (by positivity) (by positivity)
  have s123 := s12.add0 p3 (by positivity) (by positivity)
  have ed : dlt h h' = (a - b) ^ 2 / 2 := dlt_eq h h'
  refine (s123.congr_fun fun M => ?_).congr_bound ?_
  · have e1 : M.mulVec h = a • M.mulVec g := by
      conv_lhs => rw [ehg]
      exact Matrix.mulVec_smul M a g
    have e2 : M.mulVec h' = b • M.mulVec g' := by
      conv_lhs => rw [ehg']
      exact Matrix.mulVec_smul M b g'
    rw [e1, e2, dlt_smul_smul ha0.le hb0.le, ed]
    ring
  · have e5 : |normSq h - normSq h'| = |a - b| * (a + b) := by
      rw [eN, eN', show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
        abs_of_pos (by linarith : 0 < a + b)]
    have e6 : |(a - b) / 2 * a| = |a - b| / 2 * a := by
      rw [abs_mul, abs_div, abs_of_pos ha0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have e7 : |(-((a - b) / 2 * b))| = |a - b| / 2 * b := by
      rw [abs_neg, abs_mul, abs_div, abs_of_pos hb0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [e5, e6, e7]
    have e8 : |a - b| * (a + b) / 2 * v * √(2 * (m : ℝ)) =
        (m : ℝ) * v * (1 / √(2 * (m : ℝ)) * (|a - b| * (a + b))) := by
      calc |a - b| * (a + b) / 2 * v * √(2 * (m : ℝ))
          = |a - b| * (a + b) * v * (1 / 2 * √(2 * (m : ℝ))) := by ring
        _ = |a - b| * (a + b) * v * ((m : ℝ) / √(2 * (m : ℝ))) := by rw [hhalf]
        _ = _ := by ring
    have e9 : (m : ℝ) * v * (cDx m / (m : ℝ) * (a * b)) = a * b * (cDx m * v) := by
      field_simp
    rw [mul_add, e9, ← e8]
    ring

/-- **`linDltX`: the second-order term of a linear layer**, in the shape of `LinDltStmt`,
with `cDx m/(2m)` in the place of `K4 m/m` and `1/√(2m)` in the place of `√2/√m`. -/
theorem linDltX {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        dlt (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * dlt h h')
      ((m : ℝ) * v * (cDx m / (2 * (m : ℝ)) * (normSq h + normSq h') +
        1 / √(2 * (m : ℝ)) * |normSq h - normSq h'|)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := cDx_nonneg m
  have hnn := nrm_mul_nonneg h h'
  have hle := nrm_mul_le h h'
  refine (linDltX0 hv hm h h').mono (by positivity) ?_
  have h1 : cDx m / (m : ℝ) * (nrm h * nrm h') ≤
      cDx m / (2 * (m : ℝ)) * (normSq h + normSq h') := by
    have e : cDx m / (2 * (m : ℝ)) * (normSq h + normSq h') =
        cDx m / (m : ℝ) * ((normSq h + normSq h') / 2) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-! ## The remainder of the link of one linear layer, with `kX` -/

section unit

variable {G : ℝ → ℝ} {v : ℝ} {h h' : Fin k → ℝ}

/-- **The remainder at unit vectors, in `L²`**, with `kX` in the place of `K4`. -/
lemma remUnit_L2x (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (hh : normSq h = 1)
    (hh' : normSq h' = 1) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * (1 - G (dotp h h')) -
          cUnit G ((m : ℝ) * v) (dotp h h') (M.mulVec h) (M.mulVec h'))
      ((m : ℝ) * v * (((1 - G (dotp h h')) - (1 - G (-1)) / 2 * (1 - dotp h h')) /
        √(m : ℝ) + 2 * kX m / (m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := kX_nonneg m
  obtain ⟨hτ1, eDh, enh⟩ := unit_facts hh hh'
  obtain ⟨-, -, hC, -⟩ := unit_four (m := m) hv hm hh hh'
  have hD := lin_dlt_unit_k (m := m) hv hm hh hh'
  set τ := dotp h h' with hτ
  set q := √(m : ℝ) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hm'
  have hqq : q * q = m := Real.mul_self_sqrt hm'.le
  have hmq : (m : ℝ) / q = q := by rw [div_eq_iff hq0.ne']; exact hqq.symm
  rcases eq_or_lt_of_le hτ1 with h1 | h1
  · have hz : normSq (h - h') = 0 := by rw [enh, h1]; ring
    have he : h = h' := sub_eq_zero.mp (normSq_eq_zero hz)
    have hb0 : 0 ≤ (m : ℝ) * v * (((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) / q +
        2 * kX m / (m : ℝ)) := by
      rw [h1, hG.one]
      have : (m : ℝ) * v * (((1 - 1) - (1 - G (-1)) / 2 * (1 - 1)) / q +
          2 * kX m / (m : ℝ)) = 2 * kX m * v := by
        field_simp
        ring
      rw [this]
      positivity
    refine (L2le_zero (μ := gaussMat m k v) hb0).congr_fun fun M => ?_
    unfold cUnit
    rw [he, phiD_self hG, eD_eq, sub_self, h1, hG.one]
    simp [normSq]
  have hHi := sHi_mul (G := G) h1
  have hLo := sLo_mul (G := G) hd
  have hLo0 := sLo_nonneg hG hd h1
  have hHi1 := sHi_le_one hG hd h1
  have hLH : sLo G τ ≤ sHi G τ := by
    obtain ⟨s, a, b, -⟩ := secant_mem hG hd h1 (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from
      ⟨by norm_num, by norm_num⟩)
    linarith
  have hr0 : 0 ≤ rS G τ := by unfold rS; linarith
  have b3 := (L2le.abs' hC).const_mul_nonneg hr0
  have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have s34 := b3.add0 hD (by positivity) (by positivity)
  have hmeasΦ := ((measurable_phiD_lin (m := m) hG.cont h h').sub
    (measurable_const (a := (m : ℝ) * v * (1 - G τ)))).sub
    (measurable_cUnit_lin (m := m) G ((m : ℝ) * v) τ h h')
  refine (L2le.of_abs_le hmeasΦ.aestronglyMeasurable s34 (fun M => ?_)).congr_bound ?_
  · exact (phiD_secant_rem hG (M.mulVec h) (M.mulVec h') ((m : ℝ) * v) hd h1).trans
      (le_abs_self _)
  · have eR : (m : ℝ) * v * (((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) / q +
        2 * kX m / (m : ℝ)) =
        q * v * ((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) + 2 * kX m * v := by
      calc _ = v * ((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) * ((m : ℝ) / q) +
            2 * kX m * v * ((m : ℝ) / m) := by ring
        _ = _ := by rw [hmq, div_self hm'.ne']; ring
    rw [eR]
    simp only [rS]
    linear_combination (q * v * (1 + τ) / 2) * hHi - (q * v * (1 - τ) / 2) * hLo

end unit

section gen

variable {G : ℝ → ℝ} {v : ℝ}

/-- **The remainder of the linear layer after the centred part, in `L²`**: the copy of
`linRem_L2` with `kX` in the place of `K4`. -/
theorem linRem_L2x (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ)
    (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * phiD G h h' - cLin G m v M h h')
      ((m : ℝ) * v * (((phiD G h h' - dlt h h') -
          (1 - G (-1)) / 2 * (eD h h' - dlt h h')) / √(m : ℝ) +
        2 * kX m / (m : ℝ) * (nrm h * nrm h') + |normSq h - normSq h'| / √(2 * (m : ℝ)))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := kX_nonneg m
  have hs2m : 0 < √(2 * (m : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hs2m2 : √(2 * (m : ℝ)) * √(2 * (m : ℝ)) = 2 * m := Real.mul_self_sqrt (by positivity)
  have hhalf : 1 / 2 * √(2 * (m : ℝ)) = (m : ℝ) / √(2 * (m : ℝ)) := by
    rw [eq_div_iff hs2m.ne']
    calc 1 / 2 * √(2 * (m : ℝ)) * √(2 * (m : ℝ))
        = 1 / 2 * (√(2 * (m : ℝ)) * √(2 * (m : ℝ))) := by ring
      _ = m := by rw [hs2m2]; ring
  have h0 : normSq (0 : Fin k → ℝ) = 0 := by simp [normSq]
  have deg : ∀ g : Fin k → ℝ, L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ => (normSq (M.mulVec g) - (m : ℝ) * (v * normSq g)) / 2)
      ((m : ℝ) * v * (normSq g / √(2 * (m : ℝ)))) := by
    intro g
    have a := (lin_c2 (m := m) hv.le g).const_mul_nonneg (c := 1 / 2) (by norm_num)
    refine (a.congr_fun fun M => by ring).congr_bound ?_
    calc 1 / 2 * (√(2 * (m : ℝ)) * (v * normSq g))
        = 1 / 2 * √(2 * (m : ℝ)) * (v * normSq g) := by ring
      _ = _ := by rw [hhalf]; ring
  by_cases hz : normSq h = 0
  · have : h = 0 := normSq_eq_zero hz
    subst this
    refine ((deg h').congr_fun fun M => ?_).congr_bound ?_
    · rw [cLin_zero_left G v M h0 h', Matrix.mulVec_zero, phiD_zero_left, phiD_zero_left]; ring
    · have e1 : phiD G (0 : Fin k → ℝ) h' - dlt 0 h' = 0 := by
        rw [phiD_zero_left, dlt_zero_leftL]; ring
      have e2 : eD (0 : Fin k → ℝ) h' - dlt 0 h' = 0 := by
        rw [dlt_zero_leftL]; unfold eD dotp; simp [h0]
      rw [e1, e2, nrm_zero_of h0, h0]
      simp only [zero_sub, abs_neg]
      rw [abs_of_nonneg (normSq_nonneg h')]
      ring
  by_cases hz' : normSq h' = 0
  · have : h' = 0 := normSq_eq_zero hz'
    subst this
    refine ((deg h).congr_fun fun M => ?_).congr_bound ?_
    · rw [cLin_zero_right G v M h h0, Matrix.mulVec_zero, phiD_zero_right, phiD_zero_right]; ring
    · have e1 : phiD G h (0 : Fin k → ℝ) - dlt h 0 = 0 := by
        rw [phiD_zero_right, dlt_comm, dlt_zero_leftL]; ring
      have e2 : eD h (0 : Fin k → ℝ) - dlt h 0 = 0 := by
        rw [dlt_comm, dlt_zero_leftL]; unfold eD dotp; simp [h0]
      rw [e1, e2, nrm_zero_of h0, h0]
      simp only [sub_zero]
      rw [abs_of_nonneg (normSq_nonneg h)]
      ring
  -- the main case
  have hcl := cLin_eq (m := m) G v (h := h) (h' := h')
  set a := nrm h with ha
  set b := nrm h' with hb
  have ha0 : 0 < a := nrm_pos_of_ne hz
  have hb0 : 0 < b := nrm_pos_of_ne hz'
  have eN : normSq h = a ^ 2 := (nrm_sq h).symm
  have eN' : normSq h' = b ^ 2 := (nrm_sq h').symm
  set g : Fin k → ℝ := a⁻¹ • h with hg
  set g' : Fin k → ℝ := b⁻¹ • h' with hg'
  have hgu : normSq g = 1 := normed_unit hz
  have hgu' : normSq g' = 1 := normed_unit hz'
  have ehg : h = a • g := by rw [hg, smul_smul, mul_inv_cancel₀ ha0.ne', one_smul]
  have ehg' : h' = b • g' := by rw [hg', smul_smul, mul_inv_cancel₀ hb0.ne', one_smul]
  set τ := dotp g g' with hτ
  have edot : dotp h h' = a * b * τ := by
    rw [hτ]
    conv_lhs => rw [ehg, ehg']
    exact dotp_smul_smul a b g g'
  have hτ0 : 0 ≤ τ := by
    have h1 : 0 ≤ a * b * τ := by rw [← edot]; exact hd
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos ha0 hb0]
  have hτ1 : τ ≤ 1 := by
    have := abs_dotp_le_nrm g g'
    rw [nrm_of_normSq_one hgu, nrm_of_normSq_one hgu', mul_one] at this
    exact (le_abs_self _).trans this
  have hunit := remUnit_L2x (m := m) hG hv hm hgu hgu' hτ0
  rw [← hτ] at hunit
  have hX := secX_nonneg hG hτ0 hτ1
  have hub : 0 ≤ (m : ℝ) * v * (((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) /
      √(m : ℝ) + 2 * kX m / (m : ℝ)) := by positivity
  have c2 := lin_c2 (m := m) hv.le g
  have c2' := lin_c2 (m := m) hv.le g'
  rw [hgu, mul_one] at c2
  rw [hgu', mul_one] at c2'
  have p1 := hunit.const_mul_nonneg (c := a * b) (by positivity)
  have p2 := c2.const_mul ((a - b) / 2 * a)
  have p3 := c2'.const_mul (-((a - b) / 2 * b))
  have s12 := p1.add0 p2 (by positivity) (by positivity)
  have s123 := s12.add0 p3 (by positivity) (by positivity)
  have e3' : phiD G h h' = a * b * (1 - G τ) + (a - b) * (a - b) / 2 := by
    conv_lhs => rw [ehg, ehg']
    rw [phiD_smul_smul G ha0 hb0, phiD_unit G hgu hgu', hgu, hgu']
    ring
  refine (s123.congr_fun fun M => ?_).congr_bound ?_
  · have e1 : M.mulVec h = a • M.mulVec g := by
      conv_lhs => rw [ehg]
      exact Matrix.mulVec_smul M a g
    have e2 : M.mulVec h' = b • M.mulVec g' := by
      conv_lhs => rw [ehg']
      exact Matrix.mulVec_smul M b g'
    rw [hcl M, e1, e2, phiD_smul_smul G ha0 hb0, e3']
    ring
  · have e3 : phiD G h h' - dlt h h' = a * b * (1 - G τ) := by
      rw [e3', dlt_eq]; ring
    have e4 : eD h h' - dlt h h' = a * b * (1 - τ) := by
      unfold eD dlt; rw [edot]; ring
    have e5 : |normSq h - normSq h'| = |a - b| * (a + b) := by
      rw [eN, eN', show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
        abs_of_pos (by linarith : 0 < a + b)]
    have e6 : |(a - b) / 2 * a| = |a - b| / 2 * a := by
      rw [abs_mul, abs_div, abs_of_pos ha0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have e7 : |(-((a - b) / 2 * b))| = |a - b| / 2 * b := by
      rw [abs_neg, abs_mul, abs_div, abs_of_pos hb0, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [e3, e4, e5, e6, e7]
    have e8 : |a - b| * (a + b) / 2 * v * √(2 * (m : ℝ)) =
        (m : ℝ) * v * (|a - b| * (a + b) / √(2 * (m : ℝ))) := by
      calc |a - b| * (a + b) / 2 * v * √(2 * (m : ℝ))
          = |a - b| * (a + b) * v * (1 / 2 * √(2 * (m : ℝ))) := by ring
        _ = |a - b| * (a + b) * v * ((m : ℝ) / √(2 * (m : ℝ))) := by rw [hhalf]
        _ = _ := by ring
    calc a * b * ((m : ℝ) * v * (((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) /
            √(m : ℝ) + 2 * kX m / (m : ℝ))) + |a - b| / 2 * a * (√(2 * (m : ℝ)) * v) +
          |a - b| / 2 * b * (√(2 * (m : ℝ)) * v)
        = (m : ℝ) * v * (((a * b * (1 - G τ)) - (1 - G (-1)) / 2 * (a * b * (1 - τ))) /
            √(m : ℝ) + 2 * kX m / (m : ℝ) * (a * b)) +
            |a - b| * (a + b) / 2 * v * √(2 * (m : ℝ)) := by ring
      _ = _ := by rw [e8]; ring

end gen

end BstLean.Part145

open BstLean.Part145 in
#print axioms lin_dlt_unit_x
open BstLean.Part145 in
#print axioms linDltX
open BstLean.Part145 in
#print axioms linRem_L2x
