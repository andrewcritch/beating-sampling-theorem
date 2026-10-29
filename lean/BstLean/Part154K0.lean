import BstLean.Part154Defs

/-!
# Part 154: the constant of Lemma PR (i): `U(a) ≤ K₀`

`U(a) = Φ(a)Φ(−a) − ψ₁(a)ψ₁(−a) = Var relu(a + Z) − Φ(a)²`. Proved here: `0 ≤ U ≤ 1/4`,
and the sharp bound `U(a) ≤ U(0) = K₀ = (π − 2)/(4π)`.

Proof of the sharp bound: `U` is even and `U′ = −2G` with
`G = φ(2Φ − 1) − aΦ(1 − Φ)`, `G′ = P = 2φ² − Φ(1 − Φ)`, `P′ = φ·Q`, `Q = (2Φ − 1) − 4aφ`,
`Q′ = φ(4a² − 2)`. `Q` has one sign change (`−` to `+`) on `[0, ∞)`, so has `P` (`+` to `−`,
because `P → 0`), hence `G ≥ 0` on `[0, ∞)` (because `G(0) = 0` and `G → 0`).
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130 (relu reluV normSq relu_of_nonneg relu_of_nonpos integrable_pow_gauss)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm phiG_pos phiG_neg PhiG_pos PhiG_le_one int_z int_z2
  psiS_one psiG_nonneg hasDerivAt_phiG hasDerivAt_PhiG hasDerivAt_psiG tendsto_mul_exp psiS_neg)

/-! ## Integrals of a quadratic polynomial against the standard Gaussian law -/

lemma int_one_gauss : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
  simpa using integrable_pow_gauss 1

lemma quad_integrable (c0 c1 c2 : ℝ) :
    Integrable (fun z : ℝ => c0 + c1 * z + c2 * z ^ 2) (gaussianReal 0 1) :=
  ((integrable_const c0).add (int_one_gauss.const_mul c1)).add
    ((integrable_pow_gauss 2).const_mul c2)

lemma quad_intK (c0 c1 c2 : ℝ) :
    ∫ z, (c0 + c1 * z + c2 * z ^ 2) ∂gaussianReal 0 1 = c0 + c2 := by
  have i0 : Integrable (fun _ : ℝ => c0) (gaussianReal 0 1) := integrable_const _
  have i1 : Integrable (fun z : ℝ => c1 * z) (gaussianReal 0 1) := int_one_gauss.const_mul _
  have i2 : Integrable (fun z : ℝ => c2 * z ^ 2) (gaussianReal 0 1) :=
    (integrable_pow_gauss 2).const_mul _
  have i01 : Integrable (fun z : ℝ => c0 + c1 * z) (gaussianReal 0 1) := i0.add i1
  rw [integral_add i01 i2, integral_add i0 i1, integral_const_mul, integral_const_mul,
    integral_id_gaussianReal, gaussMom_eq 2]
  norm_num [gaussMom]

lemma quad_setInt (v c0 c1 c2 : ℝ) :
    ∫ z in Ioi (-v), (c0 + c1 * z + c2 * z ^ 2) ∂gaussianReal 0 1 =
      c0 * PhiG v + c1 * phiG v + c2 * (PhiG v - v * phiG v) := by
  have i0 : IntegrableOn (fun _ : ℝ => c0) (Ioi (-v)) (gaussianReal 0 1) :=
    (integrable_const c0).integrableOn
  have i1 : IntegrableOn (fun z : ℝ => c1 * z) (Ioi (-v)) (gaussianReal 0 1) :=
    (int_one_gauss.const_mul c1).integrableOn
  have i2 : IntegrableOn (fun z : ℝ => c2 * z ^ 2) (Ioi (-v)) (gaussianReal 0 1) :=
    ((integrable_pow_gauss 2).const_mul c2).integrableOn
  have i01 : IntegrableOn (fun z : ℝ => c0 + c1 * z) (Ioi (-v)) (gaussianReal 0 1) := i0.add i1
  rw [integral_add i01 i2, integral_add i0 i1, integral_const_mul, integral_const_mul,
    setIntegral_const, int_z, int_z2]
  simp only [smul_eq_mul, PhiG]
  ring

/-! ## Symmetry -/

/-- `ψ₁(−a) = ψ₁(a) − a`. -/
lemma psiG_neg_eq (a : ℝ) : psiG (-a) = psiG a - a := by
  rw [← psiS_one, ← psiS_one]; exact psiS_neg 1 a

/-- `Φ(a) + Φ(−a) = 1`. -/
lemma PhiG_add_neg (a : ℝ) : PhiG a + PhiG (-a) = 1 := by
  have hd : ∀ x, HasDerivAt (fun x => PhiG x + PhiG (-x)) (phiG x + phiG (-x) * -1) x := by
    intro x
    have h1 : HasDerivAt (fun x => PhiG (-x)) (phiG (-x) * -1) x :=
      (hasDerivAt_PhiG (-x)).comp x (hasDerivAt_neg x)
    exact (hasDerivAt_PhiG x).add h1
  have hc := is_const_of_deriv_eq_zero (f := fun x => PhiG x + PhiG (-x))
    (fun x => (hd x).differentiableAt) (fun x => by rw [(hd x).deriv, phiG_neg]; ring) a 1
  have h1 := psiG_neg_eq 1
  unfold psiG at h1
  rw [phiG_neg] at h1
  have hc' : PhiG a + PhiG (-a) = PhiG 1 + PhiG (-1) := hc
  linarith

lemma PhiG_neg_eq (a : ℝ) : PhiG (-a) = 1 - PhiG a := by
  have := PhiG_add_neg a; linarith

lemma PhiG_zero : PhiG 0 = 1 / 2 := by
  have := PhiG_add_neg 0
  simp only [neg_zero] at this
  linarith

/-- `E relu(a + Z)² = (a² + 1)Φ(a) + aφ(a)`. -/
lemma relu_sq_int (a : ℝ) :
    ∫ z, relu (a + z) ^ 2 ∂gaussianReal 0 1 = (a ^ 2 + 1) * PhiG a + a * phiG a := by
  have e : (fun z : ℝ => relu (a + z) ^ 2) =
      (Ioi (-a)).indicator (fun z => a ^ 2 + (2 * a) * z + 1 * z ^ 2) := by
    funext z
    by_cases hz : z ∈ Ioi (-a)
    · have := mem_Ioi.mp hz
      rw [indicator_of_mem hz, relu_of_nonneg (by linarith)]; ring
    · have := not_lt.mp (fun h => hz (mem_Ioi.mpr h))
      rw [indicator_of_notMem hz, relu_of_nonpos (by linarith)]; ring
  rw [e, integral_indicator measurableSet_Ioi, quad_setInt]
  ring

lemma relu_int (a : ℝ) : ∫ z, relu (a + z) ∂gaussianReal 0 1 = psiG a := by
  rw [← psiS_one]; unfold psiS; simp only [one_mul]

/-- The closed form of `U`. -/
lemma Ures_closed (a : ℝ) :
    Ures a = (a ^ 2 + 1) * PhiG a + a * phiG a - psiG a ^ 2 - PhiG a ^ 2 := by
  unfold Ures
  rw [psiG_neg_eq, PhiG_neg_eq]
  unfold psiG; ring

/-- `U(a) = Var relu(a + Z) − Φ(a)²`. -/
theorem Ures_eq (a : ℝ) : BstLean.Part153.Vr a - PhiG a ^ 2 = Ures a := by
  rw [Ures_closed]
  unfold BstLean.Part153.Vr
  rw [relu_sq_int, relu_int]

theorem Ures_nonneg (a : ℝ) : 0 ≤ Ures a := by
  have hnn : 0 ≤ ∫ z, (relu (a + z) - psiG a - PhiG a * z) ^ 2 ∂gaussianReal 0 1 :=
    integral_nonneg fun z => sq_nonneg _
  have e : (fun z : ℝ => (relu (a + z) - psiG a - PhiG a * z) ^ 2) = fun z =>
      (Ioi (-a)).indicator (fun z => (a ^ 2 - 2 * a * psiG a) +
        (2 * a - 2 * psiG a - 2 * a * PhiG a) * z + (1 - 2 * PhiG a) * z ^ 2) z +
      (psiG a ^ 2 + (2 * psiG a * PhiG a) * z + PhiG a ^ 2 * z ^ 2) := by
    funext z
    by_cases hz : z ∈ Ioi (-a)
    · have := mem_Ioi.mp hz
      rw [indicator_of_mem hz, relu_of_nonneg (by linarith)]; ring
    · have := not_lt.mp (fun h => hz (mem_Ioi.mpr h))
      rw [indicator_of_notMem hz, relu_of_nonpos (by linarith)]; ring
  rw [e, integral_add ((quad_integrable _ _ _).indicator measurableSet_Ioi)
    (quad_integrable _ _ _), integral_indicator measurableSet_Ioi, quad_setInt, quad_intK] at hnn
  rw [Ures_closed]
  unfold psiG at hnn ⊢
  nlinarith [hnn]

lemma Ures_neg (a : ℝ) : Ures (-a) = Ures a := by
  unfold Ures; rw [neg_neg]; ring

theorem Ures_le_quarter (a : ℝ) : Ures a ≤ 1 / 4 := by
  have h := mul_nonneg (psiG_nonneg a) (psiG_nonneg (-a))
  unfold Ures
  rw [PhiG_neg_eq]
  nlinarith [sq_nonneg (PhiG a - 1 / 2)]

theorem K0_pos : 0 < K0 := by
  unfold K0
  have := Real.pi_gt_three
  exact div_pos (by linarith) (by linarith)

theorem K0_lt : K0 < 1 / 8 := by
  unfold K0
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_lt_d2
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-! ## The sharp constant -/

/-- `G = φ(2Φ − 1) − aΦ(1 − Φ)`; `U′ = −2G`. -/
noncomputable def GG (a : ℝ) : ℝ := phiG a * (2 * PhiG a - 1) - a * PhiG a * (1 - PhiG a)

/-- `P = 2φ² − Φ(1 − Φ) = G′`. -/
noncomputable def PP (a : ℝ) : ℝ := 2 * (phiG a * phiG a) - PhiG a * (1 - PhiG a)

/-- `Q = (2Φ − 1) − 4aφ`; `P′ = φ·Q`. -/
noncomputable def QQ (a : ℝ) : ℝ := (2 * PhiG a - 1) - 4 * a * phiG a

lemma hasDerivAt_GG (a : ℝ) : HasDerivAt GG (PP a) a := by
  have hφ := hasDerivAt_phiG a
  have hΦ := hasDerivAt_PhiG a
  have h := (hφ.mul ((hΦ.const_mul 2).sub_const 1)).sub
    (((hasDerivAt_id a).mul hΦ).mul (hΦ.const_sub 1))
  refine HasDerivAt.congr_deriv (show HasDerivAt GG _ a from h) ?_
  unfold PP
  simp only [id, Pi.mul_apply]
  ring

lemma hasDerivAt_PP (a : ℝ) : HasDerivAt PP (phiG a * QQ a) a := by
  have hφ := hasDerivAt_phiG a
  have hΦ := hasDerivAt_PhiG a
  have h := ((hφ.mul hφ).const_mul 2).sub (hΦ.mul (hΦ.const_sub 1))
  refine HasDerivAt.congr_deriv (show HasDerivAt PP _ a from h) ?_
  unfold QQ
  ring

lemma hasDerivAt_QQ (a : ℝ) : HasDerivAt QQ (phiG a * (4 * a ^ 2 - 2)) a := by
  have hφ := hasDerivAt_phiG a
  have hΦ := hasDerivAt_PhiG a
  have h := ((hΦ.const_mul 2).sub_const 1).sub (((hasDerivAt_id a).const_mul 4).mul hφ)
  refine HasDerivAt.congr_deriv (show HasDerivAt QQ _ a from h) ?_
  simp only [id]
  ring

/-- Mills: `a(1 − Φ(a)) ≤ φ(a)`. -/
lemma mul_tail_le (a : ℝ) : a * (1 - PhiG a) ≤ phiG a := by
  have h := psiG_nonneg (-a)
  unfold psiG at h
  rw [phiG_neg, PhiG_neg_eq] at h
  linarith

lemma tendsto_phiG : Tendsto phiG atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t * rexp (-(t ^ 2 / 2))) atTop (𝓝 0) := by
    simpa using tendsto_mul_exp.neg
  have h1 : Tendsto (fun t : ℝ => t * phiG t) atTop (𝓝 0) := by
    have := h0.const_mul (√(2 * π))⁻¹
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    unfold phiG; ring
  refine squeeze_zero' (Eventually.of_forall fun t => (phiG_pos t).le) ?_ h1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  nlinarith [phiG_pos t]

lemma tendsto_tail : Tendsto (fun a => 1 - PhiG a) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun t => by have := PhiG_le_one t; linarith) ?_
    tendsto_phiG
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have h1 := mul_tail_le t
  have h2 := PhiG_le_one t
  nlinarith

lemma tendsto_mul_tail : Tendsto (fun a => a * (1 - PhiG a)) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ (Eventually.of_forall mul_tail_le) tendsto_phiG
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h2 := PhiG_le_one t
  exact mul_nonneg ht (by linarith)

lemma tendsto_PhiG : Tendsto PhiG atTop (𝓝 1) := by
  have h := tendsto_tail.const_sub 1
  rw [sub_zero] at h
  refine h.congr fun t => ?_
  ring

lemma tendsto_GG : Tendsto GG atTop (𝓝 0) := by
  have h := (tendsto_phiG.mul ((tendsto_PhiG.const_mul 2).sub_const 1)).sub
    (tendsto_mul_tail.mul tendsto_PhiG)
  rw [show (0 * (2 * 1 - 1) - 0 * 1 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  unfold GG; ring

lemma tendsto_PP : Tendsto PP atTop (𝓝 0) := by
  have h := ((tendsto_phiG.mul tendsto_phiG).const_mul 2).sub (tendsto_PhiG.mul tendsto_tail)
  rw [show (2 * (0 * 0) - 1 * 0 : ℝ) = 0 by norm_num] at h
  exact h

lemma QQ_zero : QQ 0 = 0 := by
  unfold QQ; rw [PhiG_zero]; ring

lemma GG_zero : GG 0 = 0 := by
  unfold GG; rw [PhiG_zero]; ring

/-- `Q` has one sign change on `[0, ∞)`: after it is positive, it stays positive. -/
lemma QQ_pos_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (h : 0 < QQ x) : 0 < QQ y := by
  have hcont : Continuous QQ :=
    continuous_iff_continuousAt.mpr fun a => (hasDerivAt_QQ a).continuousAt
  have hs0 : 0 < √(1 / 2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hanti : AntitoneOn QQ (Icc 0 (√(1 / 2 : ℝ))) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont.continuousOn
      (fun a _ => (hasDerivAt_QQ a).differentiableAt.differentiableWithinAt) fun z hz => ?_
    rw [interior_Icc] at hz
    rw [(hasDerivAt_QQ z).deriv]
    have h1 : z ^ 2 ≤ 1 / 2 := by nlinarith [hz.1, hz.2]
    exact mul_nonpos_of_nonneg_of_nonpos (phiG_pos z).le (by linarith)
  have hmono : MonotoneOn QQ (Ici (√(1 / 2 : ℝ))) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) hcont.continuousOn
      (fun a _ => (hasDerivAt_QQ a).differentiableAt.differentiableWithinAt) fun z hz => ?_
    rw [interior_Ici] at hz
    rw [(hasDerivAt_QQ z).deriv]
    have hz' := mem_Ioi.mp hz
    have h1 : 1 / 2 ≤ z ^ 2 := by nlinarith
    exact mul_nonneg (phiG_pos z).le (by linarith)
  by_cases hxs : x ≤ √(1 / 2 : ℝ)
  · have := hanti (left_mem_Icc.mpr hs0.le) ⟨hx, hxs⟩ hx
    rw [QQ_zero] at this
    linarith
  · rw [not_le] at hxs
    have := hmono (mem_Ici.mpr hxs.le) (mem_Ici.mpr (hxs.le.trans hxy)) hxy
    linarith

/-- `P` has one sign change on `[0, ∞)`: after it is nonpositive, it stays nonpositive. -/
lemma PP_nonpos_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (h : PP x ≤ 0) : PP y ≤ 0 := by
  have hcont : Continuous PP :=
    continuous_iff_continuousAt.mpr fun a => (hasDerivAt_PP a).continuousAt
  by_cases hQ : QQ y ≤ 0
  · have hanti : AntitoneOn PP (Icc 0 y) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont.continuousOn
        (fun a _ => (hasDerivAt_PP a).differentiableAt.differentiableWithinAt) fun z hz => ?_
      rw [interior_Icc] at hz
      rw [(hasDerivAt_PP z).deriv]
      have hz0 : QQ z ≤ 0 := by
        by_contra hc
        rw [not_le] at hc
        have := QQ_pos_mono hz.1.le hz.2.le hc
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (phiG_pos z).le hz0
    have := hanti ⟨hx, hxy⟩ ⟨hx.trans hxy, le_rfl⟩ hxy
    linarith
  · rw [not_le] at hQ
    have hmono : MonotoneOn PP (Ici y) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici _) hcont.continuousOn
        (fun a _ => (hasDerivAt_PP a).differentiableAt.differentiableWithinAt) fun z hz => ?_
      rw [interior_Ici] at hz
      rw [(hasDerivAt_PP z).deriv]
      have hz' := mem_Ioi.mp hz
      exact mul_nonneg (phiG_pos z).le (QQ_pos_mono (hx.trans hxy) hz'.le hQ).le
    refine ge_of_tendsto tendsto_PP ?_
    filter_upwards [eventually_ge_atTop y] with z hz
    exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz

/-- `G ≥ 0` on `[0, ∞)`. -/
lemma GG_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ GG a := by
  have hcont : Continuous GG :=
    continuous_iff_continuousAt.mpr fun a => (hasDerivAt_GG a).continuousAt
  by_cases h : PP a ≤ 0
  · have hanti : AntitoneOn GG (Ici a) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
        (fun a _ => (hasDerivAt_GG a).differentiableAt.differentiableWithinAt) fun z hz => ?_
      rw [interior_Ici] at hz
      rw [(hasDerivAt_GG z).deriv]
      exact PP_nonpos_mono ha (mem_Ioi.mp hz).le h
    refine le_of_tendsto tendsto_GG ?_
    filter_upwards [eventually_ge_atTop a] with z hz
    exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  · rw [not_le] at h
    have hmono : MonotoneOn GG (Icc 0 a) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn
        (fun a _ => (hasDerivAt_GG a).differentiableAt.differentiableWithinAt) fun z hz => ?_
      rw [interior_Icc] at hz
      rw [(hasDerivAt_GG z).deriv]
      by_contra hc
      rw [not_le] at hc
      have := PP_nonpos_mono hz.1.le hz.2.le hc.le
      linarith
    have := hmono (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha) ha
    rw [GG_zero] at this
    exact this

lemma hasDerivAt_Ures (a : ℝ) : HasDerivAt Ures (-2 * GG a) a := by
  have h1 : HasDerivAt (fun a => PhiG (-a)) (phiG (-a) * -1) a :=
    (hasDerivAt_PhiG (-a)).comp a (hasDerivAt_neg a)
  have h2 : HasDerivAt (fun a => psiG (-a)) (PhiG (-a) * -1) a :=
    (hasDerivAt_psiG (-a)).comp a (hasDerivAt_neg a)
  have h := ((hasDerivAt_PhiG a).mul h1).sub ((hasDerivAt_psiG a).mul h2)
  refine HasDerivAt.congr_deriv (show HasDerivAt Ures _ a from h) ?_
  rw [phiG_neg, PhiG_neg_eq, psiG_neg_eq]
  unfold GG psiG
  ring

lemma Ures_zero : Ures 0 = K0 := by
  have hπ := Real.pi_pos
  have h0 : phiG 0 = (√(2 * π))⁻¹ := by unfold phiG; norm_num
  have h1 : phiG 0 * phiG 0 = (2 * π)⁻¹ := by
    rw [h0, ← mul_inv, Real.mul_self_sqrt (by positivity)]
  unfold Ures psiG
  simp only [neg_zero, zero_mul, zero_add]
  rw [PhiG_zero, h1]
  unfold K0
  field_simp
  ring

/-- **The sharp constant**: `U(a) ≤ U(0) = K₀ = (π − 2)/(4π)`. -/
theorem Ures_le_K0 (a : ℝ) : Ures a ≤ K0 := by
  have hcont : Continuous Ures :=
    continuous_iff_continuousAt.mpr fun a => (hasDerivAt_Ures a).continuousAt
  have hanti : AntitoneOn Ures (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
      (fun a _ => (hasDerivAt_Ures a).differentiableAt.differentiableWithinAt) fun z hz => ?_
    rw [interior_Ici] at hz
    rw [(hasDerivAt_Ures z).deriv]
    have := GG_nonneg (mem_Ioi.mp hz).le
    linarith
  have key : ∀ b : ℝ, 0 ≤ b → Ures b ≤ K0 := fun b hb => by
    have := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hb) hb
    rwa [Ures_zero] at this
  rcases le_total 0 a with ha | ha
  · exact key a ha
  · rw [← Ures_neg]; exact key (-a) (by linarith)

end BstLean.Part154
