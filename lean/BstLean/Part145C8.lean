import BstLean.Part145C7

/-!
# Part 145, helper `C8`: the fourth moment of `⟨x(u), x(u′)⟩ − κ(κ(0))`

`tX z = ⟨x(u), x(u′)⟩`, `q = κ(κ(0))`. The three steps of `world_cos_L2g`, in `L⁴`:
the last matrix (`lin_cos_M4`), the hidden layers (bounded, with the `L²` bound `eHid`; they
enter through `M4le.perturb`), the inputs (`sphere_kk_M4`). The event that a hidden vector is
zero has probability at most `2·epsW m`; it adds `32·epsW m` to the fourth moment.

* `gS4 n m c = (1 − c²)·√(kEC n) + j4C n + 2·√(kEC n)·√(2·eHid m)`; `aW4`, `world_a_M4`.
* `wS4`, `world_sec_M4`: the fourth moment over `W` for fixed unit inputs.
* `a1G`, `aL4G`, `m4G`, `tX_L4_gen` (all widths); `m4C n = m4G (2n) n (m_W)`;
  **`tX_L4_145C`**: `‖(tX − q)²‖₂ ≤ m4C n` at the widths of the Focus, `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142 BstLean.Part143

section World

variable {N m n : ℕ}

/-- The `L⁴` bound of the last matrix after the average over the hidden layers, as a function of
`c = κ(κ(⟨u, u′⟩))`. -/
noncomputable def gS4 (n m : ℕ) (c : ℝ) : ℝ :=
  (1 - c ^ 2) * √(kEC n) + j4C n + 2 * √(kEC n) * √(2 * eHid m)

/-- The part of the last matrix, set to `0` if a hidden vector is zero. -/
noncomputable def aW4 (u u' : Fin N → ℝ)
    (z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  if normSq (hid2 z.1.1 z.1.2 u) = 0 ∨ normSq (hid2 z.1.1 z.1.2 u') = 0 then 0 else
    dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
      cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')

lemma measurable_aW4 (u u' : Fin N → ℝ) : Measurable (aW4 (m := m) (n := n) u u') := by
  have hmeasC : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) := measurable_cosv_hid2 u u'
  have h1 : ∀ w : Fin N → ℝ, MeasurableSet {z : (Matrix (Fin m) (Fin N) ℝ ×
      Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin n) (Fin m) ℝ | normSq (hid2 z.1.1 z.1.2 w) = 0} :=
    fun w => measurableSet_eq_fun
      ((continuous_normSq.comp (continuous_hid2_param w)).measurable.comp measurable_fst)
      measurable_const
  unfold aW4
  exact Measurable.ite ((h1 u).union (h1 u')) measurable_const
    ((measurable_lastStep u u').sub (hmeasC.comp measurable_fst))

lemma abs_aW4_le (hn : 1 ≤ n) (u u' : Fin N → ℝ)
    (z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) × Matrix (Fin n) (Fin m) ℝ) :
    |aW4 u u' z| ≤ 2 := by
  unfold aW4
  split_ifs
  · simp
  · have hc := cosv_mem (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')
    have h1 := dotp_sphPt_ge hn (z.2.mulVec (hid2 z.1.1 z.1.2 u))
      (z.2.mulVec (hid2 z.1.1 z.1.2 u'))
    have h2 := dotp_sphPt_le hn (z.2.mulVec (hid2 z.1.1 z.1.2 u))
      (z.2.mulVec (hid2 z.1.1 z.1.2 u'))
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]

/-- The fourth moment of the part of the last matrix, for unit inputs. -/
lemma world_a_M4 (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {u u' : Fin N → ℝ}
    (hu : normSq u = 1) (hu' : normSq u' = 1) :
    M4le (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
      (gaussMat n m (2 / (m : ℝ)))) (aW4 u u')
      (gS4 n m (kappa (kappa (dotp u u'))) ^ 4 + t4C n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = kappa (kappa (dotp u u')) := ⟨_, rfl⟩
  have h23 := hid_cos_L2 (m := m) hN hm hu hu'
  rw [← hcdef] at h23 ⊢
  have hcm : 0 ≤ c ∧ c ≤ 1 := hcdef ▸ kk_mem (unit_dot_mem hu hu')
  have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith [hcm.1, hcm.2]
  have hk := kEC_nonneg n
  have hj := j4C_nonneg n
  have heH := eHid_nonneg m
  have hmeasC : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) := measurable_cosv_hid2 u u'
  have hb2 : ∀ θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      |cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') - c| ≤ 2 := fun θ => by
    have hc := cosv_mem (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, hcm.1, hcm.2]
  have tX2 : M4le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
      (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
        |cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') - c|) (√(2 * eHid m) ^ 4) := by
    have h0 := M4le.of_bound_l2 hb2 h23
    refine M4le.of_abs_le (hmeasC.sub measurable_const).abs.aestronglyMeasurable
      (h0.mono (le_of_eq ?_)) (fun θ => by rw [abs_abs])
    have : √(2 * eHid m) ^ 4 = (√(2 * eHid m) ^ 2) ^ 2 := by ring
    rw [this, Real.sq_sqrt (by positivity)]
    ring
  have hg := (M4le.const (μ := (gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
    ((1 - c ^ 2) * √(kEC n) + j4C n)).add (tX2.const_mul (c := 2 * √(kEC n)) (by positivity))
    (by positivity) (by positivity)
  refine (M4le.prod (t4C_nonneg n) (measurable_aW4 u u').aestronglyMeasurable hg
    (Filter.Eventually.of_forall fun θ => ?_)).mono (le_of_eq (by unfold gS4; ring))
  by_cases hz : normSq (hid2 θ.1 θ.2 u) = 0 ∨ normSq (hid2 θ.1 θ.2 u') = 0
  · have e0 : ∀ M : Matrix (Fin n) (Fin m) ℝ, aW4 u u' (θ, M) = 0 := fun M =>
      ite_eq_left_of_eq_true _ _ (eq_true hz)
    simp only [e0]
    refine ⟨by simp, ?_⟩
    have := t4C_nonneg n
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    positivity
  · have e1 : ∀ M : Matrix (Fin n) (Fin m) ℝ, aW4 u u' (θ, M) =
        dotp (sphPt (M.mulVec (hid2 θ.1 θ.2 u))) (sphPt (M.mulVec (hid2 θ.1 θ.2 u'))) -
          cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') := fun M =>
      ite_eq_right_of_eq_false _ _ (eq_false hz)
    simp only [e1]
    have hz' : normSq (hid2 θ.1 θ.2 u) ≠ 0 ∧ normSq (hid2 θ.1 θ.2 u') ≠ 0 :=
      ⟨fun h => hz (Or.inl h), fun h => hz (Or.inr h)⟩
    have hb := lin_cos_M4 (n := n) (v := 2 / (m : ℝ)) (by positivity) hn
      (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') hz'.1 hz'.2
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u') := ⟨_, rfl⟩
    have hc := cosv_mem (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')
    rw [← hτ] at hb hc ⊢
    have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith [hc.1, hc.2]
    have hkey : 1 - τ ^ 2 ≤ (1 - c ^ 2) + 2 * |τ - c| := by
      have e : c ^ 2 - τ ^ 2 = (c + τ) * (c - τ) := by ring
      have h1 : |(c + τ) * (c - τ)| ≤ 2 * |τ - c| := by
        rw [abs_mul, abs_sub_comm c τ]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [hc.1, hc.2, hcm.1, hcm.2]
      have := le_abs_self ((c + τ) * (c - τ))
      linarith
    have hle : (1 - τ ^ 2) * √(kEC n) + j4C n ≤
        (1 - c ^ 2) * √(kEC n) + j4C n + 2 * √(kEC n) * |τ - c| := by
      have := mul_le_mul_of_nonneg_right hkey (Real.sqrt_nonneg (kEC n))
      linarith
    have h4 := pow_le_pow_left₀ (by positivity) hle 4
    refine ⟨hb.2.1, hb.2.2.trans ?_⟩
    have e4 : (((1 - c ^ 2) * √(kEC n) + j4C n + 2 * √(kEC n) * |τ - c|) ^ 2) ^ 2 =
        ((1 - c ^ 2) * √(kEC n) + j4C n + 2 * √(kEC n) * |τ - c|) ^ 4 := by ring
    rw [e4]
    linarith

/-- The bound of the `L⁴` norm over `W`, for fixed inputs, as a function of
`c = κ(κ(⟨u, u′⟩))`. -/
noncomputable def wS4 (n m : ℕ) (c : ℝ) : ℝ :=
  √(√(gS4 n m c ^ 4 + t4C n)) + |c - kappa (kappa 0)|

lemma sqrt_sqrt_pow4 {x : ℝ} (hx : 0 ≤ x) : √(√x) ^ 4 = x := by
  have : √(√x) ^ 4 = (√(√x) ^ 2) ^ 2 := by ring
  rw [this, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hx]

/-- **The fourth moment over `W` for fixed unit inputs.** -/
theorem world_sec_M4 (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {u u' : Fin N → ℝ}
    (hu : normSq u = 1) (hu' : normSq u' = 1) :
    ∫ W : MlpParam N m n, ((dotp (xW W u) (xW W u') - kappa (kappa 0)) ^ 2) ^ 2
      ∂mlpGauss N m n ≤
      (wS4 n m (kappa (kappa (dotp u u'))) ^ 2) ^ 2 +
        24 * eHid m * wS4 n m (kappa (kappa (dotp u u'))) ^ 2 +
        (28 * eHid m ^ 2 + 32 * epsW m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have heps := epsW_pos hm
  have heH := eHid_nonneg m
  have hA := world_a_M4 (n := n) hN hm hn hu hu'
  have h23 := hid_cos_L2 (m := m) hN hm hu hu'
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = kappa (kappa (dotp u u')) := ⟨_, rfl⟩
  rw [← hcdef] at hA h23 ⊢
  have hcm : 0 ≤ c ∧ c ≤ 1 := hcdef ▸ kk_mem (unit_dot_mem hu hu')
  have hq := q_mem
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = c - kappa (kappa 0) := ⟨_, rfl⟩
  have hδ1 : |δ| ≤ 1 := by
    rw [hδ, abs_le]
    constructor <;> linarith [hcm.1, hcm.2, hq.1, hq.2]
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = √(√(gS4 n m c ^ 4 + t4C n)) := ⟨_, rfl⟩
  have hx0 : 0 ≤ gS4 n m c ^ 4 + t4C n := by
    have := t4C_nonneg n
    positivity
  have hH0 : 0 ≤ H := hH ▸ Real.sqrt_nonneg _
  have hH4 : H ^ 4 = gS4 n m c ^ 4 + t4C n := by rw [hH]; exact sqrt_sqrt_pow4 hx0
  have hw : wS4 n m c = H + |δ| := by unfold wS4; rw [hH, hδ]
  rw [hw]
  have hmeasC : Measurable (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      cosv (hid2 θ.1 θ.2 u) (hid2 θ.1 θ.2 u')) := measurable_cosv_hid2 u u'
  -- the main part and the constant
  have h1 : M4le (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
      (gaussMat n m (2 / (m : ℝ)))) (aW4 u u') (H ^ 4) := hA.mono (le_of_eq hH4.symm)
  have h2 := h1.add ((M4le.const (μ := ((gaussMat m N (2 / (N : ℝ))).prod
    (gaussMat m m (2 / (m : ℝ)))).prod (gaussMat n m (2 / (m : ℝ)))) δ).mono
    (le_of_eq (Even.pow_abs ⟨2, rfl⟩ δ).symm)) hH0 (abs_nonneg δ)
  -- the hidden layers
  have hb := h23.comp_fst (ν := gaussMat n m (2 / (m : ℝ)))
  have h3 := h2.perturb hb heH (fun z => by
      have := abs_aW4_le hn u u' z
      have := abs_add_le (aW4 u u' z) δ
      linarith) (fun z => by
      have hc := cosv_mem (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u')
      rw [abs_le]
      constructor <;> linarith [hc.1, hc.2, hcm.1, hcm.2])
  -- the zero events
  have hind : ∀ w : Fin N → ℝ, normSq w = 1 →
      L2le ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ))))
        (fun θ : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
          if normSq (hid2 θ.1 θ.2 w) = 0 then (1 : ℝ) else 0) (√(epsW m)) := by
    intro w hw
    refine L2le.of_sq_le (measurable_zero_ind w).aestronglyMeasurable (integrable_zero_ind w)
      (fun θ => by split_ifs <;> simp) ?_
    rw [Real.sq_sqrt heps.le]
    exact hid2_zero hN hm hw
  have hIu := (hind u hu).comp_fst (ν := gaussMat n m (2 / (m : ℝ)))
  have hIu' := (hind u' hu').comp_fst (ν := gaussMat n m (2 / (m : ℝ)))
  have bIu := hIu.le
  have bIu' := hIu'.le
  rw [Real.sq_sqrt heps.le] at bIu bIu'
  -- the pointwise bound
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      Matrix (Fin n) (Fin m) ℝ → ℝ, Φ = fun z =>
      dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u))) (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
        kappa (kappa 0) := ⟨_, rfl⟩
  have hΦm : Measurable Φ := by
    rw [hΦ]; exact (measurable_lastStep u u').sub measurable_const
  have hpt : ∀ z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      Matrix (Fin n) (Fin m) ℝ, (Φ z ^ 2) ^ 2 ≤
      ((aW4 u u' z + δ + (cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u') - c)) ^ 2) ^ 2 +
        16 * ((if normSq (hid2 z.1.1 z.1.2 u) = 0 then (1 : ℝ) else 0) ^ 2 +
          (if normSq (hid2 z.1.1 z.1.2 u') = 0 then (1 : ℝ) else 0) ^ 2) := by
    intro z
    obtain ⟨I1, hI1⟩ : ∃ I1 : ℝ, I1 = if normSq (hid2 z.1.1 z.1.2 u) = 0 then (1 : ℝ) else 0 :=
      ⟨_, rfl⟩
    obtain ⟨I2, hI2⟩ : ∃ I2 : ℝ, I2 = if normSq (hid2 z.1.1 z.1.2 u') = 0 then (1 : ℝ) else 0 :=
      ⟨_, rfl⟩
    rw [← hI1, ← hI2]
    have i1 : 0 ≤ I1 ^ 2 := sq_nonneg _
    have i2 : 0 ≤ I2 ^ 2 := sq_nonneg _
    by_cases hz : normSq (hid2 z.1.1 z.1.2 u) = 0 ∨ normSq (hid2 z.1.1 z.1.2 u') = 0
    · have h1 := dotp_sphPt_ge hn (z.2.mulVec (hid2 z.1.1 z.1.2 u))
        (z.2.mulVec (hid2 z.1.1 z.1.2 u'))
      have h2 := dotp_sphPt_le hn (z.2.mulVec (hid2 z.1.1 z.1.2 u))
        (z.2.mulVec (hid2 z.1.1 z.1.2 u'))
      have hΦ2 : |Φ z| ≤ 2 := by
        rw [hΦ, abs_le]
        constructor <;> linarith [hq.1, hq.2]
      have hs1 : Φ z ^ 2 ≤ 2 ^ 2 := by
        rw [← sq_abs (Φ z)]
        exact pow_le_pow_left₀ (abs_nonneg _) hΦ2 2
      have hs2 : (Φ z ^ 2) ^ 2 ≤ (2 ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hs1 2
      have e16 : ((2 : ℝ) ^ 2) ^ 2 = 16 := by norm_num
      have h0 : 0 ≤ ((aW4 u u' z + δ +
          (cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u') - c)) ^ 2) ^ 2 := by positivity
      rcases hz with hz | hz
      · have e : I1 ^ 2 = 1 := by
          rw [hI1, ite_eq_left_of_eq_true _ _ (eq_true hz)]; norm_num
        linarith
      · have e : I2 ^ 2 = 1 := by
          rw [hI2, ite_eq_left_of_eq_true _ _ (eq_true hz)]; norm_num
        linarith
    · have e1 : aW4 u u' z =
          dotp (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u)))
            (sphPt (z.2.mulVec (hid2 z.1.1 z.1.2 u'))) -
            cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u') :=
        ite_eq_right_of_eq_false _ _ (eq_false hz)
      have e2 : aW4 u u' z + δ + (cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u') - c) =
          Φ z := by rw [e1, hδ, hΦ]; ring
      rw [e2]
      linarith
  have iI : Integrable (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      Matrix (Fin n) (Fin m) ℝ =>
      16 * ((if normSq (hid2 z.1.1 z.1.2 u) = 0 then (1 : ℝ) else 0) ^ 2 +
        (if normSq (hid2 z.1.1 z.1.2 u') = 0 then (1 : ℝ) else 0) ^ 2))
      (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ)))) := (hIu.int_sq.add hIu'.int_sq).const_mul 16
  have iA : Integrable (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      Matrix (Fin n) (Fin m) ℝ =>
      ((aW4 u u' z + δ + (cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u') - c)) ^ 2) ^ 2)
      (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ)))) := h3.2.1
  have bA : ∫ z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      Matrix (Fin n) (Fin m) ℝ,
      ((aW4 u u' z + δ + (cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u') - c)) ^ 2) ^ 2
      ∂(((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ)))) ≤
      (H + |δ|) ^ 4 + 24 * (H + |δ|) ^ 2 * eHid m + 28 * eHid m ^ 2 := h3.2.2
  have iG : Integrable (fun z : (Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      Matrix (Fin n) (Fin m) ℝ =>
      ((aW4 u u' z + δ + (cosv (hid2 z.1.1 z.1.2 u) (hid2 z.1.1 z.1.2 u') - c)) ^ 2) ^ 2 +
        16 * ((if normSq (hid2 z.1.1 z.1.2 u) = 0 then (1 : ℝ) else 0) ^ 2 +
          (if normSq (hid2 z.1.1 z.1.2 u') = 0 then (1 : ℝ) else 0) ^ 2))
      (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ)))) := iA.add iI
  have iΦ : Integrable (fun z => (Φ z ^ 2) ^ 2)
      (((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ)))) := by
    refine Integrable.mono' iG ((hΦm.pow_const 2).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt z
  have hmain := integral_mono iΦ iG hpt
  rw [integral_add iA iI, integral_const_mul, integral_add hIu.int_sq hIu'.int_sq] at hmain
  -- the change of variables
  have hmap : (mlpGauss N m n).map (MeasurableEquiv.prodAssoc (α := Matrix (Fin m) (Fin N) ℝ)
      (β := Matrix (Fin m) (Fin m) ℝ) (γ := Matrix (Fin n) (Fin m) ℝ)).symm =
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
        (gaussMat n m (2 / (m : ℝ))) := by
    unfold mlpGauss
    rw [← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]
  have hint : ∫ W : MlpParam N m n, ((dotp (xW W u) (xW W u') - kappa (kappa 0)) ^ 2) ^ 2
      ∂mlpGauss N m n = ∫ z, (Φ z ^ 2) ^ 2
        ∂(((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))).prod
          (gaussMat n m (2 / (m : ℝ)))) := by
    rw [← hmap, integral_map_equiv, hΦ]
    rfl
  rw [hint]
  have e4 : ((H + |δ|) ^ 2) ^ 2 = (H + |δ|) ^ 4 := by ring
  rw [e4]
  linarith

end World

/-! ## All widths -/

/-- The `L⁴` bound of the last matrix after the average over the hidden layers and the
inputs. -/
noncomputable def a1G (N n m : ℕ) : ℝ :=
  √(kEC n) * (1 - kappa (kappa 0) ^ 2 + 2 * sU4 N) + j4C n + 2 * √(kEC n) * √(2 * eHid m)

/-- The `L⁴` bound of the last matrix and the inputs. -/
noncomputable def aL4G (N n m : ℕ) : ℝ := √(√(a1G N n m ^ 4 + t4C n)) + sU4 N

/-- The bound of `‖(tX − κ(κ(0)))²‖₂`, all widths. -/
noncomputable def m4G (N n m : ℕ) : ℝ :=
  √(aL4G N n m ^ 4 + 24 * aL4G N n m ^ 2 * eHid m + 28 * eHid m ^ 2 + 32 * epsW m)

lemma a1G_nonneg (N n m : ℕ) : 0 ≤ a1G N n m := by
  have hq := q_mem
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have := sU4_nonneg N
  have := j4C_nonneg n
  unfold a1G
  positivity

lemma aL4G_nonneg (N n m : ℕ) : 0 ≤ aL4G N n m := by
  have := sU4_nonneg N
  unfold aL4G
  positivity

lemma m4G_nonneg (N n m : ℕ) : 0 ≤ m4G N n m := Real.sqrt_nonneg _

/-- The `L⁴` norm over the inputs of the bound `wS4` of the sections. -/
lemma wS4_M4 {N mW n : ℕ} (hN : 1 ≤ N) :
    M4le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      wS4 n mW (kappa (kappa (dotp uu.1 uu.2)))) (aL4G N n mW ^ 4) := by
  have := lawU2_prob hN
  have hq := q_mem
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hk := kEC_nonneg n
  have hj := j4C_nonneg n
  have ht := t4C_nonneg n
  have heH := eHid_nonneg mW
  have hsU := sU4_nonneg N
  have ha1 := a1G_nonneg N n mW
  have hmk : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2))) :=
    (continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable
  have hgc : Continuous (gS4 n mW) := by unfold gS4; fun_prop
  have hwc : Continuous (wS4 n mW) := by unfold wS4; fun_prop
  have hX3 := sphere_kk_M4 hN
  have hG : M4le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      gS4 n mW (kappa (kappa (dotp uu.1 uu.2)))) (a1G N n mW ^ 4) := by
    have h0 := (M4le.const (μ := lawU2 N) ((1 - kappa (kappa 0) ^ 2) * √(kEC n) + j4C n +
      2 * √(kEC n) * √(2 * eHid mW))).add (hX3.const_mul (c := 2 * √(kEC n)) (by positivity))
      (by positivity) (by positivity)
    refine M4le.of_abs_le_ae (hgc.measurable.comp hmk).aestronglyMeasurable
      (h0.mono (le_of_eq (by unfold a1G; ring))) ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = kappa (kappa (dotp uu.1 uu.2)) := ⟨_, rfl⟩
    have hcm : 0 ≤ c ∧ c ≤ 1 := hc ▸ kk_mem (unit_dot_mem huu.1 huu.2)
    rw [← hc]
    have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith [hcm.1, hcm.2]
    have hkey : 1 - c ^ 2 ≤ (1 - kappa (kappa 0) ^ 2) + 2 * |c - kappa (kappa 0)| := by
      have e : kappa (kappa 0) ^ 2 - c ^ 2 = (kappa (kappa 0) + c) * (kappa (kappa 0) - c) := by
        ring
      have h1 : |(kappa (kappa 0) + c) * (kappa (kappa 0) - c)| ≤
          2 * |c - kappa (kappa 0)| := by
        rw [abs_mul, abs_sub_comm (kappa (kappa 0)) c]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [hcm.1, hcm.2, hq.1, hq.2]
      have := le_abs_self ((kappa (kappa 0) + c) * (kappa (kappa 0) - c))
      linarith
    have h0g : 0 ≤ gS4 n mW c := by unfold gS4; positivity
    rw [abs_of_nonneg h0g, abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_right hkey (Real.sqrt_nonneg (kEC n))
    unfold gS4
    linarith
  have e4 : ∀ uu : (Fin N → ℝ) × (Fin N → ℝ),
      (gS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) ^ 2 =
        gS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 4 := fun _ => by ring
  have iG4 : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      gS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 4) (lawU2 N) := by
    simpa only [e4] using hG.2.1
  have bG4 : ∫ uu : (Fin N → ℝ) × (Fin N → ℝ),
      gS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 4 ∂lawU2 N ≤ a1G N n mW ^ 4 := by
    simpa only [e4] using hG.2.2
  have hH : M4le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      √(√(gS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 4 + t4C n)))
      (√(√(a1G N n mW ^ 4 + t4C n)) ^ 4) := by
    have ex : ∀ uu : (Fin N → ℝ) × (Fin N → ℝ),
        (√(√(gS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 4 + t4C n)) ^ 2) ^ 2 =
          gS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 4 + t4C n := fun uu => by
      rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
    refine ⟨(((hgc.measurable.comp hmk).pow_const 4).add_const _).sqrt.sqrt.aestronglyMeasurable,
      ?_, ?_⟩
    · simp only [ex]
      exact iG4.add (integrable_const _)
    · simp only [ex]
      rw [integral_add iG4 (integrable_const _), sqrt_sqrt_pow4 (by positivity)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      linarith
  exact hH.add hX3 (Real.sqrt_nonneg _) hsU

lemma tX_F4_integrable {N mW n : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) :
    Integrable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      ((tX z - kappa (kappa 0)) ^ 2) ^ 2) ((lawU2 N).prod (mlpGauss N mW n)) := by
  have := lawU2_prob hN
  have hq := q_mem
  have hmF : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      tX z - kappa (kappa 0)) := measurable_tX.sub measurable_const
  have hbd : ∀ z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n,
      ((tX z - kappa (kappa 0)) ^ 2) ^ 2 ≤ 16 := by
    intro z
    have h := tX_mem hn z
    have h1 : |tX z - kappa (kappa 0)| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [h.1, h.2, hq.1, hq.2]
    have h2 : (tX z - kappa (kappa 0)) ^ 2 ≤ 2 ^ 2 := by
      rw [← sq_abs (tX z - kappa (kappa 0))]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 := pow_le_pow_left₀ (sq_nonneg _) h2 2
    have e16 : ((2 : ℝ) ^ 2) ^ 2 = 16 := by norm_num
    linarith
  refine Integrable.mono' (integrable_const (16 : ℝ))
    ((hmF.pow_const 2).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hbd z

/-- The integral over the inputs of the bound of the sections. -/
lemma wS4_int {N mW n : ℕ} (hN : 1 ≤ N) :
    Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) ^ 2 +
        24 * eHid mW * wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2 +
        (28 * eHid mW ^ 2 + 32 * epsW mW)) (lawU2 N) ∧
    ∫ uu : (Fin N → ℝ) × (Fin N → ℝ),
      ((wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) ^ 2 +
        24 * eHid mW * wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2 +
        (28 * eHid mW ^ 2 + 32 * epsW mW)) ∂lawU2 N ≤
      aL4G N n mW ^ 4 + 24 * aL4G N n mW ^ 2 * eHid mW + 28 * eHid mW ^ 2 + 32 * epsW mW := by
  have := lawU2_prob hN
  have heH := eHid_nonneg mW
  have hw : M4le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      wS4 n mW (kappa (kappa (dotp uu.1 uu.2)))) (aL4G N n mW ^ 4) := wS4_M4 hN
  have iw4 : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) ^ 2) (lawU2 N) := hw.2.1
  have bw4 : ∫ uu : (Fin N → ℝ) × (Fin N → ℝ),
      (wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) ^ 2 ∂lawU2 N ≤ aL4G N n mW ^ 4 := hw.2.2
  have iw2 : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) (lawU2 N) := l2_integrable hw.l2sq
  have bw2 : ∫ uu : (Fin N → ℝ) × (Fin N → ℝ),
      wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2 ∂lawU2 N ≤ aL4G N n mW ^ 2 :=
    (le_abs_self _).trans (l2_abs_integral_le (sq_nonneg _) hw.l2sq)
  have iw2c : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      24 * eHid mW * wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) (lawU2 N) :=
    iw2.const_mul _
  have i12 : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) ^ 2 +
        24 * eHid mW * wS4 n mW (kappa (kappa (dotp uu.1 uu.2))) ^ 2) (lawU2 N) := iw4.add iw2c
  refine ⟨i12.add (integrable_const _), ?_⟩
  rw [integral_add i12 (integrable_const _), integral_add iw4 iw2c, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have := mul_le_mul_of_nonneg_left bw2 (by positivity : (0 : ℝ) ≤ 24 * eHid mW)
  linarith

/-- **`‖(⟨x(u), x(u′)⟩ − κ(κ(0)))²‖₂ ≤ m4G N n m`**, all widths. -/
theorem tX_L4_gen {N mW n : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => (tX z - kappa (kappa 0)) ^ 2)
      (m4G N n mW) := by
  have := lawU2_prob hN
  have heH := eHid_nonneg mW
  have heps := epsW_nonneg mW
  have haL := aL4G_nonneg N n mW
  have hmF : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      tX z - kappa (kappa 0)) := measurable_tX.sub measurable_const
  have iF := tX_F4_integrable (mW := mW) hn hN
  obtain ⟨iR, bR⟩ := wS4_int (mW := mW) (n := n) hN
  refine ⟨(hmF.pow_const 2).aestronglyMeasurable, iF, ?_⟩
  unfold m4G
  rw [Real.sq_sqrt (by positivity), integral_prod _ iF]
  refine le_trans (integral_mono_ae iF.integral_prod_left iR ?_) bR
  filter_upwards [lawU2_ae_unit hN] with uu huu
  have h := world_sec_M4 (n := n) hN hmW hn huu.1 huu.2
  have e : ∀ W : MlpParam N mW n, tX (uu, W) = dotp (xW W uu.1) (xW W uu.2) := fun W => rfl
  simp only [e]
  exact h

/-! ## The widths of the Focus -/

/-- **The bound of `‖(⟨x(u), x(u′)⟩ − κ(κ(0)))²‖₂`** at the widths of the Focus, `r = 2`. -/
noncomputable def m4C (n : ℕ) : ℝ := m4G (2 * n) n (mW n)

lemma m4C_nonneg (n : ℕ) : 0 ≤ m4C n := m4G_nonneg _ _ _

/-- **`‖(⟨x(u), x(u′)⟩ − κ(κ(0)))²‖₂ ≤ m4C n`** at the widths of the Focus, `n ≥ 4096`. -/
theorem tX_L4_145C {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        (tX z - kappa (kappa 0)) ^ 2) (m4C n) := by
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  exact tX_L4_gen (by omega) (by omega) hmW

end BstLean.Part145

open BstLean.Part145 in
#print axioms world_sec_M4
open BstLean.Part145 in
#print axioms tX_L4_145C
