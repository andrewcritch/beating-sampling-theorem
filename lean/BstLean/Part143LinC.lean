import BstLean.Part142LinS

/-!
# Part 143: the centred part of the link of one linear Gaussian layer for the distance form

The bound of `phi_lin_S` (file `Part142LinS`) is split into an explicit centred function `cLin`
and a remainder. `M` is a Gaussian matrix with `m` rows and entry variance `v`, `s₀ = m·v`.

* `cUnit G s₀ τ y y′ = (1 − τ)·r_S(τ)·((|y|² + |y′|²)/2 − s₀) + c_S(τ)·(e(y, y′) − s₀(1 − τ))`.
* `cLin G m v M h h′ = |h||h′|·cUnit G (m·v) (cos(h, h′)) (M ĥ) (M ĥ′)`, `ĥ = h/|h|`.
* `measurable_cLin`: `cLin` is measurable in `(M, h, h′)`.
* **`cLin_integral`**: `cLin` is integrable in `M` and `∫ cLin dM = 0` (all `h, h′`).
* **`cLin_L2`**: `⟨h, h′⟩ ≥ 0`: `‖cLin‖₂ ≤ m·v·√2·(Φ_G(h, h′) − δ(h, h′))/√m`.
* **`linRem_L2`**: `⟨h, h′⟩ ≥ 0`:
  `‖Φ_G(Mh, Mh′) − m·v·Φ_G(h, h′) − cLin‖₂ ≤ m·v·(((Φ_G − δ) − ((1 − G(−1))/2)(e − δ))/√m +
    (2K₄(m)/m)·|h||h′| + ||h|² − |h′|²|/√(2m))`: the bound of `phi_lin_S` with `1` in the place
  of `1 + √2`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142

section pt

variable {ι : Type*} [Fintype ι]

/-- The centred part of the link at unit reference vectors with cosine `τ`. -/
noncomputable def cUnit (G : ℝ → ℝ) (s₀ τ : ℝ) (y y' : ι → ℝ) : ℝ :=
  (1 - τ) * rS G τ * ((normSq y + normSq y') / 2 - s₀) + cS G τ * (eD y y' - s₀ * (1 - τ))

/-- The remainder of `phiD_secant` after the centred part. -/
lemma phiD_secant_rem {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) (s₀ : ℝ) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    |phiD G y y' - s₀ * (1 - G τ) - cUnit G s₀ τ y y'| ≤
      rS G τ * |τ * ((normSq y + normSq y') / 2) - dotp y y'| + dlt y y' := by
  have hτm : τ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hτ1.le⟩
  obtain ⟨s, hs1, hs2, hs⟩ := secant_mem hG hτ0 hτ1 (cosv_mem y y')
  have hHi := sHi_mul (G := G) hτ1
  have hLo0 := sLo_nonneg hG hτ0 hτ1
  have hHi1 := sHi_le_one hG hτ0 hτ1
  have hγτ := hG.self_le hτm
  have hγ1 := hG.le_one hτm
  have hdl := dlt_nonneg y y'
  set pp := (normSq y + normSq y') / 2 with hpp
  set Pi0 := nrm y * nrm y' with hPi0
  have hc : dotp y y' = cosv y y' * Pi0 := dotp_eq_cosv_mul y y'
  have hr0 : 0 ≤ rS G τ := by unfold rS; linarith
  have key : phiD G y y' - s₀ * (1 - G τ) - cUnit G s₀ τ y y' =
      (s - cS G τ) * (τ * pp - dotp y y') + (G τ - s * τ) * dlt y y' := by
    unfold cUnit phiD psi eD dlt
    rw [hc]
    simp only [cS, rS, ← hpp, ← hPi0]
    linear_combination (s₀ - pp) * hHi + Pi0 * hs
  have hsc : |s - cS G τ| ≤ rS G τ := by
    rw [abs_le]; unfold cS rS; constructor <;> linarith
  have hd0 : 0 ≤ G τ - s * τ := by
    have e : (G τ - sHi G τ * τ) * (1 - τ) = G τ - τ := by linear_combination (-τ) * hHi
    have h1 : 0 ≤ G τ - sHi G τ * τ := by
      by_contra hneg
      push Not at hneg
      nlinarith
    nlinarith
  have hd1 : G τ - s * τ ≤ 1 := by nlinarith
  rw [key]
  have a3 : |(s - cS G τ) * (τ * pp - dotp y y')| ≤ rS G τ * |τ * pp - dotp y y'| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hsc (abs_nonneg _)
  have a4 : |(G τ - s * τ) * dlt y y'| ≤ dlt y y' := by
    rw [abs_mul, abs_of_nonneg hd0, abs_of_nonneg hdl]
    nlinarith
  have t1 := abs_add_le ((s - cS G τ) * (τ * pp - dotp y y')) ((G τ - s * τ) * dlt y y')
  linarith

lemma phiD_sub_dlt (G : ℝ → ℝ) (y y' : ι → ℝ) :
    phiD G y y' - dlt y y' = nrm y * nrm y' * (1 - G (cosv y y')) := by
  unfold phiD psi dlt
  ring

lemma phiD_sub_dlt_nonneg {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) :
    0 ≤ phiD G y y' - dlt y y' := by
  rw [phiD_sub_dlt]
  have := hG.le_one (cosv_mem y y')
  exact mul_nonneg (nrm_mul_nonneg y y') (by linarith)

/-- The cosine is the inner product of the normalized vectors. -/
lemma dotp_normed (y y' : ι → ℝ) :
    dotp ((nrm y)⁻¹ • y) ((nrm y')⁻¹ • y') = cosv y y' := by
  rw [dotp_smul_smul]
  unfold cosv
  rw [div_eq_mul_inv, mul_inv]
  ring

end pt

section tools

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma L2le_zero [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) :
    L2le μ (fun _ : Ω => (0 : ℝ)) a := by
  have := L2le.const (μ := μ) (0 : ℝ)
  rw [abs_zero] at this
  exact this.mono (le_refl _) ha

end tools

variable {m k : ℕ}

/-- The centred part of the link of the matrix `M` at `(h, h′)`. -/
noncomputable def cLin (G : ℝ → ℝ) (m : ℕ) (v : ℝ) (M : Matrix (Fin m) (Fin k) ℝ)
    (h h' : Fin k → ℝ) : ℝ :=
  nrm h * nrm h' * cUnit G ((m : ℝ) * v) (cosv h h') (M.mulVec ((nrm h)⁻¹ • h))
    (M.mulVec ((nrm h')⁻¹ • h'))

lemma cLin_eq (G : ℝ → ℝ) (v : ℝ) (M : Matrix (Fin m) (Fin k) ℝ) (h h' : Fin k → ℝ) :
    cLin G m v M h h' = nrm h * nrm h' * cUnit G ((m : ℝ) * v)
      (dotp ((nrm h)⁻¹ • h) ((nrm h')⁻¹ • h')) (M.mulVec ((nrm h)⁻¹ • h))
      (M.mulVec ((nrm h')⁻¹ • h')) := by
  rw [dotp_normed]
  rfl

lemma cLin_zero_left (G : ℝ → ℝ) (v : ℝ) (M : Matrix (Fin m) (Fin k) ℝ) {h : Fin k → ℝ}
    (hz : normSq h = 0) (h' : Fin k → ℝ) : cLin G m v M h h' = 0 := by
  unfold cLin
  rw [nrm_zero_of hz]
  ring

lemma cLin_zero_right (G : ℝ → ℝ) (v : ℝ) (M : Matrix (Fin m) (Fin k) ℝ) (h : Fin k → ℝ)
    {h' : Fin k → ℝ} (hz : normSq h' = 0) : cLin G m v M h h' = 0 := by
  unfold cLin
  rw [nrm_zero_of hz]
  ring

lemma normed_unit {h : Fin k → ℝ} (hz : normSq h ≠ 0) : normSq ((nrm h)⁻¹ • h) = 1 := by
  have ha0 : 0 < nrm h := nrm_pos_of_ne hz
  rw [normSq_smul, ← nrm_sq h]
  field_simp

/-! ## Measurability -/

lemma measurable_sLo {G : ℝ → ℝ} (hG : Continuous G) : Measurable (sLo G) := by
  show Measurable (fun τ : ℝ => (G τ - G (-1)) / (1 + τ))
  exact (hG.measurable.sub measurable_const).div (measurable_const.add measurable_id)

lemma measurable_sHi {G : ℝ → ℝ} (hG : Continuous G) : Measurable (sHi G) := by
  show Measurable (fun τ : ℝ => (1 - G τ) / (1 - τ))
  exact (measurable_const.sub hG.measurable).div (measurable_const.sub measurable_id)

lemma measurable_cS {G : ℝ → ℝ} (hG : Continuous G) : Measurable (cS G) := by
  show Measurable (fun τ : ℝ => (sLo G τ + sHi G τ) / 2)
  exact ((measurable_sLo hG).add (measurable_sHi hG)).div_const 2

lemma measurable_rS {G : ℝ → ℝ} (hG : Continuous G) : Measurable (rS G) := by
  show Measurable (fun τ : ℝ => (sHi G τ - sLo G τ) / 2)
  exact ((measurable_sHi hG).sub (measurable_sLo hG)).div_const 2

/-- `cLin` is measurable in `(M, h, h′)`. -/
lemma measurable_cLin {G : ℝ → ℝ} (hG : Continuous G) (v : ℝ) :
    Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      cLin G m v p.1 p.2.1 p.2.2) := by
  have h1 : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      p.2.1) := measurable_fst.comp measurable_snd
  have h2 : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      p.2.2) := measurable_snd.comp measurable_snd
  have ha : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      nrm p.2.1) := continuous_nrm.measurable.comp h1
  have hb : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      nrm p.2.2) := continuous_nrm.measurable.comp h2
  have hτ : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      cosv p.2.1 p.2.2) := measurable_cosv.comp measurable_snd
  have hmv : Measurable (fun q : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) => q.1.mulVec q.2) :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable
  have hg : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      p.1.mulVec ((nrm p.2.1)⁻¹ • p.2.1)) :=
    hmv.comp (measurable_fst.prodMk (ha.inv.smul h1))
  have hg' : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      p.1.mulVec ((nrm p.2.2)⁻¹ • p.2.2)) :=
    hmv.comp (measurable_fst.prodMk (hb.inv.smul h2))
  have hpp := ((measurable_normSq.comp hg).add (measurable_normSq.comp hg')).div_const 2
  have hdot := measurable_dotp_comp hg hg'
  have hr := (measurable_rS hG).comp hτ
  have hc := (measurable_cS hG).comp hτ
  have hτ1 : Measurable (fun p : Matrix (Fin m) (Fin k) ℝ × (Fin k → ℝ) × (Fin k → ℝ) =>
      1 - cosv p.2.1 p.2.2) := measurable_const.sub hτ
  unfold cLin cUnit eD
  exact (ha.mul hb).mul ((((hτ1.mul hr).mul (hpp.sub measurable_const))).add
    (hc.mul ((hpp.sub hdot).sub (measurable_const.mul hτ1))))

lemma measurable_cUnit_lin (G : ℝ → ℝ) (s₀ τ : ℝ) (h h' : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      cUnit G s₀ τ (M.mulVec h) (M.mulVec h')) := by
  have hpp := ((measurable_normSq.comp (measurable_mulVec_right (m := m) h)).add
    (measurable_normSq.comp (measurable_mulVec_right (m := m) h'))).div_const 2
  have hdot := measurable_dotp_comp (measurable_mulVec_right (m := m) h)
    (measurable_mulVec_right (m := m) h')
  unfold cUnit eD
  exact ((hpp.sub measurable_const).const_mul _).add
    (((hpp.sub hdot).sub measurable_const).const_mul _)

/-! ## Unit vectors -/

section unit

variable {G : ℝ → ℝ} {v : ℝ} {h h' : Fin k → ℝ}

lemma unit_facts (hh : normSq h = 1) (hh' : normSq h' = 1) :
    dotp h h' ≤ 1 ∧ eD h h' = 1 - dotp h h' ∧ normSq (h - h') = 2 * (1 - dotp h h') := by
  have hτ1 : dotp h h' ≤ 1 := by
    have := abs_dotp_le_nrm h h'
    rw [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one] at this
    exact (le_abs_self _).trans this
  have eDh : eD h h' = 1 - dotp h h' := by unfold eD; rw [hh, hh']; ring
  refine ⟨hτ1, eDh, ?_⟩
  have := eD_eq h h'
  rw [eDh] at this
  linarith

/-- The four ingredients of `phi_lin_unit_L2`. -/
lemma unit_four (hv : 0 < v) (hm : 1 ≤ m) (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h) + normSq (M.mulVec h')) / 2 - (m : ℝ) * v) (√2 * √(m : ℝ) * v) ∧
    L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      eD (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * (1 - dotp h h'))
      (√2 * √(m : ℝ) * v * (1 - dotp h h')) ∧
    L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2) -
        dotp (M.mulVec h) (M.mulVec h')) (√(m : ℝ) * v * (1 - dotp h h' ^ 2)) ∧
    L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dlt (M.mulVec h) (M.mulVec h')) (2 * K4 m * v) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K4_nonneg m
  obtain ⟨hτ1, eDh, enh⟩ := unit_facts hh hh'
  set τ := dotp h h' with hτ
  set q := √(m : ℝ) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hm'
  have hqq : q * q = m := Real.mul_self_sqrt hm'.le
  have h22 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : (0 : ℝ) < √2 := by positivity
  have hsq : √(2 * (m : ℝ)) = √2 * q := Real.sqrt_mul (by norm_num) _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have a1 := (lin_c2 (m := m) hv.le h).const_mul_nonneg (c := 1 / 2) (by norm_num)
    have a2 := (lin_c2 (m := m) hv.le h').const_mul_nonneg (c := 1 / 2) (by norm_num)
    refine ((a1.add0 a2 (by positivity) (by positivity)).congr_fun fun M => ?_).congr_bound ?_
    · rw [hh, hh']; ring
    · rw [hh, hh', hsq]; ring
  · refine ((linEDStmt hv hm h h').congr_fun fun M => ?_).congr_bound ?_
    · rw [eDh]
    · rw [enh]
      have u : q / √2 * 2 = √2 * q := by
        rw [div_mul_eq_mul_div, div_eq_iff h2p.ne']
        linear_combination (-q) * h22
      calc q / √2 * v * (2 * (1 - τ)) = q / √2 * 2 * v * (1 - τ) := by ring
        _ = _ := by rw [u]
  · obtain ⟨i, e⟩ := lin_ctp_var (m := m) hv.le hh hh'
    have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
        dotp (M.mulVec h) (M.mulVec h') -
          τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) :=
      (measurable_dotp_comp (measurable_mulVec_right h) (measurable_mulVec_right h')).sub
        ((((measurable_normSq.comp (measurable_mulVec_right h)).add
          (measurable_normSq.comp (measurable_mulVec_right h'))).div_const 2).const_mul _)
    have base : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
        dotp (M.mulVec h) (M.mulVec h') -
          τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) (q * v * (1 - τ ^ 2)) := by
      refine L2le.mk' hmeas.aestronglyMeasurable i ?_
      rw [e]
      apply le_of_eq
      rw [mul_pow, mul_pow, sq q, hqq]
    exact base.neg.congr_fun fun M => by ring
  · have hd0 : dlt h h' = 0 := by
      unfold dlt
      rw [hh, hh', nrm_of_normSq_one hh, nrm_of_normSq_one hh']; ring
    refine ((linDltStmt hv hm h h').congr_fun fun M => ?_).congr_bound ?_
    · rw [hd0]; ring
    · rw [hh, hh']
      simp only [sub_self, abs_zero, mul_zero, add_zero]
      field_simp
      ring

/-- The centred part at unit vectors has mean zero. -/
lemma cUnit_integral (G : ℝ → ℝ) (hv : 0 ≤ v) (hh : normSq h = 1) (hh' : normSq h' = 1) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      cUnit G ((m : ℝ) * v) (dotp h h') (M.mulVec h) (M.mulVec h')) (gaussMat m k v) ∧
    ∫ M, cUnit G ((m : ℝ) * v) (dotp h h') (M.mulVec h) (M.mulVec h') ∂gaussMat m k v = 0 := by
  obtain ⟨-, -, enh⟩ := unit_facts hh hh'
  obtain ⟨i1, e1⟩ := layer_lin_sq (m := m) hv h
  obtain ⟨i2, e2⟩ := layer_lin_sq (m := m) hv h'
  obtain ⟨i3, e3⟩ := layer_lin_sq (m := m) hv (h - h')
  set τ := dotp h h' with hτ
  set a : ℝ := (1 - τ) * rS G τ with ha
  set b : ℝ := cS G τ with hb
  have hf : (fun M : Matrix (Fin m) (Fin k) ℝ =>
      cUnit G ((m : ℝ) * v) τ (M.mulVec h) (M.mulVec h')) =
      fun M : Matrix (Fin m) (Fin k) ℝ => (a / 2 * normSq (M.mulVec h) +
        a / 2 * normSq (M.mulVec h')) + (b / 2 * normSq (M.mulVec (h - h')) +
        (-(a * ((m : ℝ) * v)) - b * ((m : ℝ) * v * (1 - τ)))) := by
    funext M
    unfold cUnit
    rw [eD_eq, mulVec_sub']
    ring
  rw [hf]
  have j1 := i1.const_mul (a / 2)
  have j2 := i2.const_mul (a / 2)
  have j3 := i3.const_mul (b / 2)
  have jc : Integrable (fun _ : Matrix (Fin m) (Fin k) ℝ =>
      (-(a * ((m : ℝ) * v)) - b * ((m : ℝ) * v * (1 - τ)))) (gaussMat m k v) :=
    integrable_const _
  have j12 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => a / 2 * normSq (M.mulVec h) +
      a / 2 * normSq (M.mulVec h')) (gaussMat m k v) := j1.add j2
  have j3c : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      b / 2 * normSq (M.mulVec (h - h')) +
        (-(a * ((m : ℝ) * v)) - b * ((m : ℝ) * v * (1 - τ)))) (gaussMat m k v) := j3.add jc
  refine ⟨j12.add j3c, ?_⟩
  rw [integral_add j12 j3c, integral_add j1 j2, integral_add j3 jc,
    integral_const_mul, integral_const_mul, integral_const_mul, e1, e2, e3, hh, hh', enh]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **The centred part at unit vectors, in `L²`.** -/
lemma cUnit_L2 (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (hh : normSq h = 1)
    (hh' : normSq h' = 1) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        cUnit G ((m : ℝ) * v) (dotp h h') (M.mulVec h) (M.mulVec h'))
      (√2 * √(m : ℝ) * v * (1 - G (dotp h h'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hτ1, eDh, enh⟩ := unit_facts hh hh'
  obtain ⟨hP, hE, -, -⟩ := unit_four (m := m) hv hm hh hh'
  set τ := dotp h h' with hτ
  rcases eq_or_lt_of_le hτ1 with h1 | h1
  · have hz : normSq (h - h') = 0 := by rw [enh, h1]; ring
    have he : h = h' := sub_eq_zero.mp (normSq_eq_zero hz)
    refine ((L2le_zero (μ := gaussMat m k v) (le_refl 0)).congr_fun fun M => ?_).congr_bound ?_
    · unfold cUnit
      rw [he, eD_eq, sub_self, h1]
      simp [normSq]
    · rw [h1, hG.one]; ring
  have hHi := sHi_mul (G := G) h1
  have hLo0 := sLo_nonneg hG hd h1
  have hHi1 := sHi_le_one hG hd h1
  have hLH : sLo G τ ≤ sHi G τ := by
    obtain ⟨s, a, b, -⟩ := secant_mem hG hd h1 (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from
      ⟨by norm_num, by norm_num⟩)
    linarith
  have hr0 : 0 ≤ rS G τ := by unfold rS; linarith
  have hc0 : 0 ≤ cS G τ := by unfold cS; linarith
  have b1 := hP.const_mul_nonneg (c := (1 - τ) * rS G τ) (mul_nonneg (by linarith) hr0)
  have b2 := hE.const_mul_nonneg hc0
  have s12 := b1.add0 b2 (by positivity)
    (mul_nonneg hc0 (mul_nonneg (by positivity) (by linarith)))
  refine (s12.congr_fun fun M => rfl).congr_bound ?_
  simp only [cS, rS]
  linear_combination (√2 * √(m : ℝ) * v) * hHi

/-- **The remainder at unit vectors, in `L²`.** -/
lemma remUnit_L2 (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (hh : normSq h = 1)
    (hh' : normSq h' = 1) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * (1 - G (dotp h h')) -
          cUnit G ((m : ℝ) * v) (dotp h h') (M.mulVec h) (M.mulVec h'))
      ((m : ℝ) * v * (((1 - G (dotp h h')) - (1 - G (-1)) / 2 * (1 - dotp h h')) /
        √(m : ℝ) + 2 * K4 m / (m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K4_nonneg m
  obtain ⟨hτ1, eDh, enh⟩ := unit_facts hh hh'
  obtain ⟨-, -, hC, hD⟩ := unit_four (m := m) hv hm hh hh'
  set τ := dotp h h' with hτ
  set q := √(m : ℝ) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hm'
  have hqq : q * q = m := Real.mul_self_sqrt hm'.le
  have hmq : (m : ℝ) / q = q := by rw [div_eq_iff hq0.ne']; exact hqq.symm
  rcases eq_or_lt_of_le hτ1 with h1 | h1
  · have hz : normSq (h - h') = 0 := by rw [enh, h1]; ring
    have he : h = h' := sub_eq_zero.mp (normSq_eq_zero hz)
    have hb0 : 0 ≤ (m : ℝ) * v * (((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) / q +
        2 * K4 m / (m : ℝ)) := by
      rw [h1, hG.one]
      have : (m : ℝ) * v * (((1 - 1) - (1 - G (-1)) / 2 * (1 - 1)) / q +
          2 * K4 m / (m : ℝ)) = 2 * K4 m * v := by
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
        2 * K4 m / (m : ℝ)) =
        q * v * ((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) + 2 * K4 m * v := by
      calc _ = v * ((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) * ((m : ℝ) / q) +
            2 * K4 m * v * ((m : ℝ) / m) := by ring
        _ = _ := by rw [hmq, div_self hm'.ne']; ring
    rw [eR]
    simp only [rS]
    linear_combination (q * v * (1 + τ) / 2) * hHi - (q * v * (1 - τ) / 2) * hLo

end unit

/-! ## All vectors -/

section gen

variable {G : ℝ → ℝ} {v : ℝ}

/-- **The centred part has mean zero.** -/
theorem cLin_integral (G : ℝ → ℝ) (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => cLin G m v M h h') (gaussMat m k v) ∧
      ∫ M, cLin G m v M h h' ∂gaussMat m k v = 0 := by
  by_cases hz : normSq h = 0
  · simp only [cLin_zero_left G v _ hz h']
    exact ⟨integrable_const _, by simp⟩
  by_cases hz' : normSq h' = 0
  · simp only [cLin_zero_right G v _ h hz']
    exact ⟨integrable_const _, by simp⟩
  obtain ⟨i, e⟩ := cUnit_integral (m := m) G hv (normed_unit hz) (normed_unit hz')
  simp only [cLin_eq]
  exact ⟨i.const_mul _, by rw [integral_const_mul, e, mul_zero]⟩

/-- **The centred part, in `L²`.** -/
theorem cLin_L2 (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ)
    (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ => cLin G m v M h h')
      ((m : ℝ) * v * (√2 * (phiD G h h' - dlt h h') / √(m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpd := phiD_sub_dlt_nonneg hG h h'
  have hb0 : 0 ≤ (m : ℝ) * v * (√2 * (phiD G h h' - dlt h h') / √(m : ℝ)) := by positivity
  by_cases hz : normSq h = 0
  · simp only [cLin_zero_left G v _ hz h']
    exact L2le_zero hb0
  by_cases hz' : normSq h' = 0
  · simp only [cLin_zero_right G v _ h hz']
    exact L2le_zero hb0
  have ha0 : 0 < nrm h := nrm_pos_of_ne hz
  have hb0' : 0 < nrm h' := nrm_pos_of_ne hz'
  have hτ0 : 0 ≤ dotp ((nrm h)⁻¹ • h) ((nrm h')⁻¹ • h') := by
    rw [dotp_smul_smul]
    positivity
  have hu := (cUnit_L2 (m := m) hG hv hm (normed_unit hz) (normed_unit hz') hτ0).const_mul_nonneg
    (c := nrm h * nrm h') (by positivity)
  simp only [cLin_eq]
  refine hu.congr_bound ?_
  rw [phiD_sub_dlt, dotp_normed]
  have hq0 : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hm'
  have hqq : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm'.le
  have hmq : (m : ℝ) / √(m : ℝ) = √(m : ℝ) := by rw [div_eq_iff hq0.ne']; exact hqq.symm
  calc nrm h * nrm h' * (√2 * √(m : ℝ) * v * (1 - G (cosv h h')))
      = v * (√2 * (nrm h * nrm h' * (1 - G (cosv h h')))) * √(m : ℝ) := by ring
    _ = v * (√2 * (nrm h * nrm h' * (1 - G (cosv h h')))) * ((m : ℝ) / √(m : ℝ)) := by
        rw [hmq]
    _ = _ := by ring

/-- **The remainder of the linear layer after the centred part, in `L²`**: the bound of
`phi_lin_S` with `1` in the place of `1 + √2`. -/
theorem linRem_L2 (hG : KGood G) (hv : 0 < v) (hm : 1 ≤ m) (h h' : Fin k → ℝ)
    (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * phiD G h h' - cLin G m v M h h')
      ((m : ℝ) * v * (((phiD G h h' - dlt h h') -
          (1 - G (-1)) / 2 * (eD h h' - dlt h h')) / √(m : ℝ) +
        2 * K4 m / (m : ℝ) * (nrm h * nrm h') + |normSq h - normSq h'| / √(2 * (m : ℝ)))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K4_nonneg m
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
  have hunit := remUnit_L2 (m := m) hG hv hm hgu hgu' hτ0
  rw [← hτ] at hunit
  have hX := secX_nonneg hG hτ0 hτ1
  have hub : 0 ≤ (m : ℝ) * v * (((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) /
      √(m : ℝ) + 2 * K4 m / (m : ℝ)) := by positivity
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
            √(m : ℝ) + 2 * K4 m / (m : ℝ))) + |a - b| / 2 * a * (√(2 * (m : ℝ)) * v) +
          |a - b| / 2 * b * (√(2 * (m : ℝ)) * v)
        = (m : ℝ) * v * (((a * b * (1 - G τ)) - (1 - G (-1)) / 2 * (a * b * (1 - τ))) /
            √(m : ℝ) + 2 * K4 m / (m : ℝ) * (a * b)) +
            |a - b| * (a + b) / 2 * v * √(2 * (m : ℝ)) := by ring
      _ = _ := by rw [e8]; ring

end gen

end BstLean.Part143

open BstLean.Part143 in
#print axioms measurable_cLin
open BstLean.Part143 in
#print axioms cLin_integral
open BstLean.Part143 in
#print axioms cLin_L2
open BstLean.Part143 in
#print axioms linRem_L2
