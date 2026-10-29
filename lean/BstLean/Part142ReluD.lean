import BstLean.Part142Stmt

/-!
# Part 142: one ReLU layer for the distance form

Role: `delegations/statements/p142-spec.md`, item 2. This file proves the four statements
`ReluSqStmt`, `ReluEDStmt`, `ReluDltStmt`, `ReluPhiStmt` of `Part142Stmt`, for a Gaussian matrix
`M` with `m` rows and entry variance `v`, and fixed `h, h′` (`s = (m/2)·v`):

* `reluSqStmt`: `‖|ReLU(Mh)|² − s|h|²‖₂ ≤ (√5/2)√m·v|h|²` and
  `‖(|ReLU(Mh)|² − s|h|²)²‖₂ ≤ m·K_r(m)·(v|h|²)²` (the fourth central moment of a sum of `m`
  independent terms `ReLU(g)²`: `m·(633/16) + 3m(m − 1)·(5/4)²`).
* `reluEDStmt`: `‖e(ReLU(Mh), ReLU(Mh′)) − s·Φ_κ(h, h′)‖₂ ≤ (√3/2)√m·v·|h − h′|²`.
* `reluDltStmt`: the term `δ = (|y| − |y′|)²/2`.
* `reluPhiStmt`: the distance form `Φ_G`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

/-! ## The moments of `ReLU(x)² − 1/2` -/

lemma relu_csq_moments :
    ∫ x : ℝ, (relu x ^ 2 - 1 / 2) ∂gaussianReal 0 1 = 0 ∧
    ∫ x : ℝ, (relu x ^ 2 - 1 / 2) ^ 2 ∂gaussianReal 0 1 = 5 / 4 ∧
    Integrable (fun x : ℝ => (relu x ^ 2 - 1 / 2) ^ 4) (gaussianReal 0 1) ∧
    ∫ x : ℝ, (relu x ^ 2 - 1 / 2) ^ 4 ∂gaussianReal 0 1 = 633 / 16 := by
  obtain ⟨g2, g4, g6, g8⟩ := gaussMom_vals
  have p := integrable_relu_pow
  have r2 : ∫ x, relu x ^ 2 ∂gaussianReal 0 1 = 1 / 2 := by
    rw [int_relu_pow_even (by norm_num) (by decide), g2]
  have r4 : ∫ x, relu x ^ 4 ∂gaussianReal 0 1 = 3 / 2 := by
    rw [int_relu_pow_even (by norm_num) (by decide), g4]
  have r6 : ∫ x, relu x ^ 6 ∂gaussianReal 0 1 = 15 / 2 := by
    rw [int_relu_pow_even (by norm_num) (by decide), g6]
  have r8 : ∫ x, relu x ^ 8 ∂gaussianReal 0 1 = 105 / 2 := by
    rw [int_relu_pow_even (by norm_num) (by decide), g8]
  obtain ⟨-, e1⟩ := integral_lin4 (μ := gaussianReal 0 1) (p 2) (p 2) (p 2) (p 2) (-(1 / 2)) 1 0 0 0
  obtain ⟨-, e2⟩ := integral_lin4 (μ := gaussianReal 0 1) (p 4) (p 2) (p 2) (p 2) (1 / 4) 1 1 0 0
  obtain ⟨i4, e4⟩ := integral_lin4 (μ := gaussianReal 0 1) (p 8) (p 6) (p 4) (p 2) (1 / 16) 1 2
    (-(3 / 2)) (1 / 2)
  have f1 : (fun x : ℝ => relu x ^ 2 - 1 / 2) =
      fun x => 1 * relu x ^ 2 + -(1 / 2) - 0 * relu x ^ 2 - 0 * relu x ^ 2 - 0 * relu x ^ 2 := by
    funext x; ring
  have f2 : (fun x : ℝ => (relu x ^ 2 - 1 / 2) ^ 2) =
      fun x => 1 * relu x ^ 4 + 1 / 4 - 1 * relu x ^ 2 - 0 * relu x ^ 2 - 0 * relu x ^ 2 := by
    funext x; ring
  have f4 : (fun x : ℝ => (relu x ^ 2 - 1 / 2) ^ 4) =
      fun x => 1 * relu x ^ 8 + 1 / 16 - 2 * relu x ^ 6 - -(3 / 2) * relu x ^ 4 -
        1 / 2 * relu x ^ 2 := by
    funext x; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [f1, e1, r2]; ring
  · rw [f2, e2, r4, r2]; ring
  · rw [f4]; exact i4
  · rw [f4, e4, r8, r6, r4, r2]; ring

lemma integral_quad3 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (c d : ℝ) :
    ∫ ω, (f ω - c * g ω + d) ∂μ = ∫ ω, f ω ∂μ - c * ∫ ω, g ω ∂μ + d := by
  obtain ⟨-, e⟩ := integral_lin4 hf hg hg hg d 1 c 0 0
  have : (fun ω => f ω - c * g ω + d) =
      fun ω => 1 * f ω + d - c * g ω - 0 * g ω - 0 * g ω := by
    funext ω; ring
  rw [this, e]; ring

variable {m k : ℕ}

lemma measurable_normSq_relu (h : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (reluV (M.mulVec h))) :=
  measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right h))

lemma Kr_sq (m : ℕ) : Kr m ^ 2 = 75 / 16 + 35 / (m : ℝ) := Real.sq_sqrt (by positivity)

/-! ## The squared norm of one ReLU layer -/

theorem reluSqStmt : ReluSqStmt := by
  intro m k v hv0 hm h
  have hv : 0 ≤ v := hv0.le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℝ := v * normSq h with ha
  have ha0 : 0 ≤ a := mul_nonneg hv (normSq_nonneg h)
  have hmeas := measurable_normSq_relu (m := m) h
  constructor
  · obtain ⟨i1, e1⟩ := layer_relu_sq (m := m) hv h
    obtain ⟨i2, e2⟩ := layer_relu_four (m := m) hv h
    have hG : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
        normSq (reluV (M.mulVec h)) ^ 2 - 2 * ((m : ℝ) / 2 * a) * normSq (reluV (M.mulVec h)) +
          ((m : ℝ) / 2 * a) ^ 2) (gaussMat m k v) :=
      (i2.sub (i1.const_mul _)).add (integrable_const _)
    refine L2le.of_sq_le (hmeas.sub measurable_const).aestronglyMeasurable hG
      (fun M => le_of_eq (by ring)) ?_
    rw [integral_quad3 i2 i1, e1, e2]
    have e : (√5 / 2 * √(m : ℝ) * a) ^ 2 = 5 / 4 * (m : ℝ) * a ^ 2 := by
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hm'.le, Real.sq_sqrt (by norm_num)]
      ring
    rw [e]
    apply le_of_eq
    ring
  · classical
    obtain ⟨c1, c2, ci4, c4⟩ := relu_csq_moments
    have hg : Measurable (fun y : Fin m → ℝ => (normSq (reluV y) - (m : ℝ) / 2 * a) ^ 4) :=
      ((measurable_normSq.comp measurable_reluV).sub measurable_const).pow_const 4
    have e : ∀ ξ : Fin m → ℝ,
        (normSq (reluV ((Real.sqrt v * Real.sqrt (normSq h)) • ξ)) - (m : ℝ) / 2 * a) ^ 4 =
        a ^ 4 * (∑ i, (relu (ξ i) ^ 2 - 1 / 2)) ^ 4 := by
      intro ξ
      have hn : normSq (reluV ξ) = ∑ i, relu (ξ i) ^ 2 := rfl
      rw [reluV_smul_of_nonneg (scale_nonneg v h), normSq_smul, sq_scale hv, Finset.sum_sub_distrib,
        hn]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hf : Measurable (fun x : ℝ => relu x ^ 2 - 1 / 2) :=
      (measurable_relu.pow_const 2).sub measurable_const
    obtain ⟨pi4, -, -, pe4⟩ := pi_sum_four_finset (ι := Fin m) (μ := gaussianReal 0 1) hf ci4 c1
      Finset.univ
    have I4 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
        (normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * a) ^ 4) (gaussMat m k v) := by
      refine layer_transfer_integrable v h hg ?_
      simp_rw [e]
      exact pi4.const_mul _
    have E4 : ∫ M : Matrix (Fin m) (Fin k) ℝ,
        (normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * a) ^ 4 ∂gaussMat m k v =
        a ^ 4 * ((m : ℝ) * (633 / 16) + 3 * (m : ℝ) * ((m : ℝ) - 1) * (5 / 4) ^ 2) := by
      rw [layer_transfer v h hg]
      simp_rw [e]
      rw [integral_const_mul]
      unfold stdGauss
      rw [pe4, c2, c4, Finset.card_univ, Fintype.card_fin]
    have e4 : (fun M : Matrix (Fin m) (Fin k) ℝ =>
        ((normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * a) ^ 2) ^ 2) =
        fun M => (normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * a) ^ 4 := by
      funext M; ring
    refine L2le.mk' ((hmeas.sub measurable_const).pow_const 2).aestronglyMeasurable ?_ ?_
    · rw [e4]; exact I4
    · rw [e4, E4]
      have eb : ((m : ℝ) * Kr m * a ^ 2) ^ 2 = (75 / 16 * (m : ℝ) ^ 2 + 35 * m) * a ^ 4 := by
        rw [mul_pow, mul_pow, Kr_sq]
        field_simp
      rw [eb]
      have h0 : 0 ≤ a ^ 4 * (m : ℝ) := by positivity
      nlinarith

/-! ## The squared distance of the two outputs -/

lemma abs_relu_sub_le (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  rw [max_comm 0 a, max_comm 0 b]
  exact abs_max_sub_max_le_abs a b 0

theorem reluEDStmt : ReluEDStmt := by
  intro m k v hv0 hm h h'
  classical
  have hv : 0 ≤ v := hv0.le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set f : (Fin k → ℝ) → ℝ := fun w => (relu (dotp w h) - relu (dotp w h')) ^ 2 / 2 with hfdef
  have hf : Measurable f :=
    (((measurable_relu.comp (measurable_dotp_left h)).sub
      (measurable_relu.comp (measurable_dotp_left h'))).pow_const 2).div_const 2
  have hfs : Measurable (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ)) :=
    hf.comp (measurable_const_smul _)
  obtain ⟨i4, e4⟩ := row_four hv (h - h')
  -- the pointwise bound of `f²`
  have hpt : ∀ w : Fin k → ℝ, f w ^ 2 ≤ dotp w (h - h') ^ 4 / 4 := by
    intro w
    have h1 := abs_relu_sub_le (dotp w h) (dotp w h')
    rw [← dotp_sub_right] at h1
    have h2 : (relu (dotp w h) - relu (dotp w h')) ^ 2 ≤ dotp w (h - h') ^ 2 := by
      rw [← sq_abs (relu (dotp w h) - relu (dotp w h')), ← sq_abs (dotp w (h - h'))]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : 0 ≤ (relu (dotp w h) - relu (dotp w h')) ^ 2 := sq_nonneg _
    rw [hfdef]
    simp only
    nlinarith
  have hf2 : Integrable (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin k)) := by
    refine Integrable.mono' (i4.div_const 4) (hfs.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt _
  have I2 : ∫ ξ : Fin k → ℝ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      3 * (v * normSq (h - h')) ^ 2 / 4 := by
    have := integral_mono hf2 (i4.div_const 4) (fun ξ => hpt _)
    rw [integral_div, e4] at this
    exact this
  have hf1 : Integrable (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ)) (stdGauss (Fin k)) :=
    ((memLp_two_iff_integrable_sq hfs.aestronglyMeasurable).mpr hf2).integrable one_le_two
  set μ₀ : ℝ := ∫ ξ : Fin k → ℝ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) with hμ₀
  have hprob : IsProbabilityMeasure (stdGauss (Fin k)) := by unfold stdGauss; infer_instance
  -- the centred row function
  set ft : (Fin k → ℝ) → ℝ := fun w => f w - μ₀ with hftdef
  have hft : Measurable ft := hf.sub measurable_const
  have eft : (fun ξ : Fin k → ℝ => ft (Real.sqrt v • ξ) ^ 2) =
      fun ξ => f (Real.sqrt v • ξ) ^ 2 - 2 * μ₀ * f (Real.sqrt v • ξ) + μ₀ ^ 2 := by
    funext ξ; simp only [hftdef]; ring
  have hft2 : Integrable (fun ξ : Fin k → ℝ => ft (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin k)) := by
    rw [eft]
    exact (hf2.sub (hf1.const_mul _)).add (integrable_const _)
  have Eft1 : ∫ ξ : Fin k → ℝ, ft (Real.sqrt v • ξ) ∂stdGauss (Fin k) = 0 := by
    simp only [hftdef]
    rw [integral_sub hf1 (integrable_const _)]
    simp [hμ₀]
  have Eft2 : ∫ ξ : Fin k → ℝ, ft (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      3 * (v * normSq (h - h')) ^ 2 / 4 := by
    rw [eft, integral_quad3 hf2 hf1, ← hμ₀]
    nlinarith [sq_nonneg μ₀]
  obtain ⟨iS, eS⟩ := rows_sum_sq (m := m) v ft hft hft2
  rw [Eft1] at eS
  -- `e` as a sum over the rows
  have heD : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      eD (reluV (M.mulVec h)) (reluV (M.mulVec h')) = ∑ i, f (rowOf i M) := by
    intro M
    rw [eD_eq]
    unfold normSq
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => rfl
  -- the mean
  have hmean : (m : ℝ) * μ₀ = (m : ℝ) / 2 * v * phiD kappa h h' := by
    have hi : ∀ i : Fin m, Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => f (rowOf i M))
        (gaussMat m k v) := fun i => (row_integrable_iff v i hf).mpr hf1
    have e1 : ∫ M : Matrix (Fin m) (Fin k) ℝ, eD (reluV (M.mulVec h)) (reluV (M.mulVec h'))
        ∂gaussMat m k v = (m : ℝ) * μ₀ := by
      simp_rw [heD]
      rw [integral_finsetSum _ fun i _ => hi i]
      simp_rw [row_integral v _ hf]
      simp [hμ₀]
    obtain ⟨ip, ep⟩ := layer_relu_sq (m := m) hv h
    obtain ⟨ip', ep'⟩ := layer_relu_sq (m := m) hv h'
    obtain ⟨ic, ec⟩ := layer_dot_relu (m := m) hv h h'
    have e2 : ∫ M : Matrix (Fin m) (Fin k) ℝ, eD (reluV (M.mulVec h)) (reluV (M.mulVec h'))
        ∂gaussMat m k v =
        ((m : ℝ) / 2 * (v * normSq h) + (m : ℝ) / 2 * (v * normSq h')) / 2 -
          (m : ℝ) / 2 * (v * kernelPhi h h') := by
      have hpp : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
          (normSq (reluV (M.mulVec h)) + normSq (reluV (M.mulVec h'))) / 2) (gaussMat m k v) :=
        (ip.add ip').div_const 2
      have epp : ∫ M : Matrix (Fin m) (Fin k) ℝ,
          (normSq (reluV (M.mulVec h)) + normSq (reluV (M.mulVec h'))) / 2 ∂gaussMat m k v =
          ((m : ℝ) / 2 * (v * normSq h) + (m : ℝ) / 2 * (v * normSq h')) / 2 := by
        rw [integral_div, integral_add ip ip', ep, ep']
      unfold eD
      rw [integral_sub hpp ic, epp, ec]
    rw [← e1, e2, kernelPhi_eq_psi]
    unfold phiD
    ring
  have hfun : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      eD (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * v * phiD kappa h h' =
        ∑ i, ft (rowOf i M) := by
    intro M
    rw [heD, ← hmean]
    simp only [hftdef, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hmeasS : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => ∑ i, ft (rowOf i M)) :=
    Finset.measurable_sum _ fun i _ => hft.comp (measurable_rowOf i)
  have key : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ => ∑ i, ft (rowOf i M))
      (√3 / 2 * √(m : ℝ) * v * normSq (h - h')) := by
    refine L2le.mk' hmeasS.aestronglyMeasurable iS ?_
    rw [eS]
    have e : (√3 / 2 * √(m : ℝ) * v * normSq (h - h')) ^ 2 =
        (m : ℝ) * (3 * (v * normSq (h - h')) ^ 2 / 4) := by
      rw [mul_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt hm'.le, Real.sq_sqrt (by norm_num)]
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left Eft2 hm'.le
    linarith
  exact key.congr_fun fun M => (hfun M).symm

/-! ## The term `δ` -/

section zero

variable {ι : Type*} [Fintype ι]

lemma normSq_zero' : normSq (0 : ι → ℝ) = 0 := by simp [normSq]

lemma nrm_zero' : nrm (0 : ι → ℝ) = 0 := by unfold nrm; rw [normSq_zero', Real.sqrt_zero]

lemma dlt_zero_left (y : ι → ℝ) : dlt (0 : ι → ℝ) y = normSq y / 2 := by
  unfold dlt; rw [normSq_zero', nrm_zero']; ring

lemma dlt_zero_right (y : ι → ℝ) : dlt y (0 : ι → ℝ) = normSq y / 2 := by
  unfold dlt; rw [normSq_zero', nrm_zero']; ring

lemma reluV_zero' : reluV (0 : ι → ℝ) = 0 := by
  funext i
  simp [reluV, relu]

end zero

lemma measurable_dlt_relu (h h' : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dlt (reluV (M.mulVec h)) (reluV (M.mulVec h'))) := by
  unfold dlt
  exact (((measurable_normSq_relu h).add (measurable_normSq_relu h')).div_const 2).sub
    ((continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h))).mul
      (continuous_nrm.measurable.comp (measurable_reluV.comp (measurable_mulVec_right h'))))

/-- The degenerate case of `reluDltStmt`: one of the two vectors is `0`. -/
lemma dlt_half_bound {v : ℝ} (hv0 : 0 < v) (hm : 1 ≤ m) (g : Fin k → ℝ) :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        normSq (reluV (M.mulVec g)) / 2 - (m : ℝ) / 2 * v * (normSq g / 2))
      ((m : ℝ) / 2 * v * (4 * Kr m / (m : ℝ) * normSq g + √5 / √(m : ℝ) * normSq g)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn := normSq_nonneg g
  have hK := Kr_nonneg m
  obtain ⟨q, hq0, hqm, hqs⟩ : ∃ q : ℝ, 0 < q ∧ (m : ℝ) = q ^ 2 ∧ √(m : ℝ) = q :=
    ⟨√(m : ℝ), Real.sqrt_pos.mpr hm', (Real.sq_sqrt hm'.le).symm, rfl⟩
  have h1 := ((reluSqStmt hv0 hm g).1.const_mul_nonneg (c := 1 / 2) (by norm_num))
  have h5 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg _
  refine (h1.congr_fun fun M => by ring).mono (by positivity) ?_
  rw [hqs, hqm]
  have e : q ^ 2 / 2 * v * (4 * Kr m / q ^ 2 * normSq g + √5 / q * normSq g) =
      2 * Kr m * v * normSq g + √5 / 2 * q * v * normSq g := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ 2 * Kr m * v * normSq g := by positivity
  have : 0 ≤ √5 / 2 * q * v * normSq g := by positivity
  nlinarith

theorem reluDltStmt : ReluDltStmt := by
  intro m k v hv0 hm h h'
  have hv : 0 ≤ v := hv0.le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hz : normSq h = 0
  · have h0 : h = 0 := normSq_eq_zero hz
    subst h0
    have hb := dlt_half_bound hv0 hm h'
    refine (hb.congr_fun fun M => ?_).congr_bound ?_
    · rw [Matrix.mulVec_zero, reluV_zero', dlt_zero_left, dlt_zero_left]
    · rw [normSq_zero', zero_add, zero_sub, abs_neg, abs_of_nonneg (normSq_nonneg h')]
  by_cases hz' : normSq h' = 0
  · have h0 : h' = 0 := normSq_eq_zero hz'
    subst h0
    have hb := dlt_half_bound hv0 hm h
    refine (hb.congr_fun fun M => ?_).congr_bound ?_
    · rw [Matrix.mulVec_zero, reluV_zero', dlt_zero_right, dlt_zero_right]
    · rw [normSq_zero', add_zero, sub_zero, abs_of_nonneg (normSq_nonneg h)]
  -- the general case
  have hN : 0 < normSq h := lt_of_le_of_ne (normSq_nonneg h) (Ne.symm hz)
  have hN' : 0 < normSq h' := lt_of_le_of_ne (normSq_nonneg h') (Ne.symm hz')
  set x := nrm h with hx
  set x' := nrm h' with hx'
  have hx0 : 0 < x := Real.sqrt_pos.mpr hN
  have hx0' : 0 < x' := Real.sqrt_pos.mpr hN'
  have ex : normSq h = x ^ 2 := (nrm_sq h).symm
  have ex' : normSq h' = x' ^ 2 := (nrm_sq h').symm
  have hs0 : 0 < (m : ℝ) / 2 * v := by positivity
  obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = (m : ℝ) / 2 * v :=
    ⟨√((m : ℝ) / 2 * v), Real.sqrt_pos.mpr hs0, Real.sq_sqrt hs0.le⟩
  obtain ⟨q, hq0, hqm, hqs⟩ : ∃ q : ℝ, 0 < q ∧ (m : ℝ) = q ^ 2 ∧ √(m : ℝ) = q :=
    ⟨√(m : ℝ), Real.sqrt_pos.mpr hm', (Real.sq_sqrt hm'.le).symm, rfl⟩
  obtain ⟨s2, s4⟩ := reluSqStmt hv0 hm h
  obtain ⟨s2', s4'⟩ := reluSqStmt hv0 hm h'
  have ea : (r * x) ^ 2 = (m : ℝ) / 2 * (v * normSq h) := by rw [mul_pow, hr2, ex]; ring
  have ea' : (r * x') ^ 2 = (m : ℝ) / 2 * (v * normSq h') := by rw [mul_pow, hr2, ex']; ring
  have hK := Kr_nonneg m
  have h5 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg _
  have key := delta_L2_core (μ := gaussMat m k v)
    (Y := fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h))
    (Y' := fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h'))
    (measurable_dlt_relu h h').aestronglyMeasurable (a₀ := r * x) (b₀ := r * x')
    (mul_pos hr0 hx0) (mul_pos hr0 hx0')
    (s2.congr_fun fun M => by rw [ea]) (s2'.congr_fun fun M => by rw [ea'])
    (s4.congr_fun fun M => by rw [ea]) (s4'.congr_fun fun M => by rw [ea'])
    (by positivity) (by positivity) (by positivity) (by positivity)
  refine (key.congr_fun fun M => ?_).congr_bound ?_
  · have : (r * x - r * x') ^ 2 / 2 = (m : ℝ) / 2 * v * dlt h h' := by
      rw [dlt_eq, ← hr2]; ring
    rw [this]
  · have habs1 : |r * x - r * x'| = r * |x - x'| := by
      rw [← mul_sub, abs_mul, abs_of_pos hr0]
    have habs2 : |x ^ 2 - x' ^ 2| = |x - x'| * (x + x') := by
      rw [show x ^ 2 - x' ^ 2 = (x - x') * (x + x') by ring, abs_mul,
        abs_of_pos (by linarith : 0 < x + x')]
    have hv_eq : v = 2 * r ^ 2 / q ^ 2 := by
      rw [hr2, hqm]; field_simp
    rw [habs1, hqs, ex, ex', habs2, hqm, hv_eq]
    field_simp
    ring

/-! ## The distance form -/

theorem reluPhiStmt : ReluPhiStmt := by
  intro m k G hG v hv0 hm h h'
  have hv : 0 ≤ v := hv0.le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hbb := bG_nonneg hG
  have hK := Kr_nonneg m
  have h5 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg _
  have hn := normSq_nonneg h
  have hn' := normSq_nonneg h'
  have hnd := normSq_nonneg (h - h')
  have hd0 := dlt_nonneg h h'
  obtain ⟨q, hq0, hqm, hqs⟩ : ∃ q : ℝ, 0 < q ∧ (m : ℝ) = q ^ 2 ∧ √(m : ℝ) = q :=
    ⟨√(m : ℝ), Real.sqrt_pos.mpr hm', (Real.sq_sqrt hm'.le).symm, rfl⟩
  set s : ℝ := (m : ℝ) / 2 * v with hs
  have hs0 : 0 ≤ s := by positivity
  set P : ℝ := s * ((normSq h + normSq h') / 2) with hP
  set pb : ℝ := s * (nrm h * nrm h') with hpb
  set t : ℝ := kappa (cosv h h') with ht
  have ht01 := kappa_mem (cosv_mem h h').1 (cosv_mem h h').2
  have hpb0 : 0 ≤ pb := mul_nonneg hs0 (nrm_mul_nonneg h h')
  have hPb : pb ≤ P := mul_le_mul_of_nonneg_left (nrm_mul_le h h') hs0
  have hPpb : P - pb = s * dlt h h' := by rw [hP, hpb]; unfold dlt; ring
  have hEref : P - pb * t = s * phiD kappa h h' := by
    rw [hP, hpb, ht]; unfold phiD psi; ring
  have href : P - pb * G t = s * phiD (G ∘ kappa) h h' := by
    rw [hP, hpb, ht]; unfold phiD psi; simp only [Function.comp_apply]; ring
  obtain ⟨s2, -⟩ := reluSqStmt hv0 hm h
  obtain ⟨s2', -⟩ := reluSqStmt hv0 hm h'
  have hE : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      eD (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (P - pb * t))
      (√3 / 2 * √(m : ℝ) * v * normSq (h - h')) :=
    (reluEDStmt hv0 hm h h').congr_fun fun M => by rw [hEref]
  have hPl : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (reluV (M.mulVec h)) + normSq (reluV (M.mulVec h'))) / 2 - P)
      (1 / 2 * (√5 / 2 * √(m : ℝ) * (v * normSq h) + √5 / 2 * √(m : ℝ) * (v * normSq h'))) :=
    ((s2.add0 s2' (by positivity) (by positivity)).const_mul_nonneg (c := 1 / 2)
      (by norm_num)).congr_fun fun M => by rw [hP, hs]; ring
  have hD : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dlt (reluV (M.mulVec h)) (reluV (M.mulVec h')) + (P - pb))
      ((m : ℝ) / 2 * v * (4 * Kr m / (m : ℝ) * (normSq h + normSq h') +
        √5 / √(m : ℝ) * |normSq h - normSq h'|) + |2 * (s * dlt h h')|) :=
    ((reluDltStmt hv0 hm h h').add0 (L2le.const (μ := gaussMat m k v) (2 * (s * dlt h h')))
      (by positivity) (abs_nonneg _)).congr_fun fun M => by rw [hPpb, hs]; ring
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      phiD G (reluV (M.mulVec h)) (reluV (M.mulVec h'))) := by
    unfold phiD
    exact (((measurable_normSq_relu h).add (measurable_normSq_relu h')).div_const 2).sub
      (measurable_psi_relu hG.cont h h')
  have key := phiD_L2_core2 (μ := gaussMat m k v) hG
    (Y := fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h))
    (Y' := fun M : Matrix (Fin m) (Fin k) ℝ => reluV (M.mulVec h'))
    hmeas.aestronglyMeasurable hpb0 hPb ht01.1 ht01.2 hE hPl hD
    (by positivity) (by positivity) (by positivity)
  refine (key.congr_fun fun M => by rw [href]).congr_bound ?_
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (s * dlt h h')), hs, hqs, hqm]
  field_simp

end BstLean.Part142

open BstLean.Part142 in
#print axioms reluSqStmt
open BstLean.Part142 in
#print axioms reluEDStmt
open BstLean.Part142 in
#print axioms reluDltStmt
open BstLean.Part142 in
#print axioms reluPhiStmt
