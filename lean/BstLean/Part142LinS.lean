import BstLean.Part142LinD
import BstLean.Part135Upper

/-!
# Part 142: one linear Gaussian layer for the distance form, with the secant of `G` at the
reference cosine

Role: `delegations/statements/p142-spec.md`, item 2. A sharper form of `linPhiStmt` (file
`Part142LinD`): the slope of `G` between the reference cosine `τ` and the random cosine is in
`[s_lo, s_hi]`, `s_lo = (G τ − G(−1))/(1 + τ)`, `s_hi = (1 − G τ)/(1 − τ)` (convexity).

* `secant_mem`: for `0 ≤ τ < 1`, `t′ ∈ [−1, 1]`: `G τ − G t′ = s·(τ − t′)` with `s_lo ≤ s ≤ s_hi`.
* `phiD_secant`: pointwise, `|Φ_G(y, y′) − s₀(1 − G τ)| ≤ (1 − τ)r|p⁺ − s₀| +
    s_c|e − s₀(1 − τ)| + r|τp⁺ − ⟨y, y′⟩| + δ`, `s_c = (s_lo + s_hi)/2`, `r = (s_hi − s_lo)/2`.
* **`phi_lin_unit_L2`**: unit `h, h′`, `τ = ⟨h, h′⟩ ≥ 0`:
  `‖Φ_G(Mh, Mh′) − m·v·(1 − G τ)‖₂ ≤
    m·v·(((1 + √2)(1 − G τ) − ((1 − G(−1))/2)(1 − τ))/√m + 2K₄(m)/m)`.
* **`phi_lin_S`**: all `h, h′` with `⟨h, h′⟩ ≥ 0`:
  `‖Φ_G(Mh, Mh′) − m·v·Φ_G(h, h′)‖₂ ≤ m·v·(((1 + √2)(Φ_G − δ) − ((1 − G(−1))/2)(e − δ))/√m +
    (2K₄(m)/m)·|h||h′| + ||h|² − |h′|²|/√(2m))` (`Φ_G`, `e`, `δ` at `(h, h′)`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

/-- The slope of `G` between `−1` and `τ`. -/
noncomputable def sLo (G : ℝ → ℝ) (τ : ℝ) : ℝ := (G τ - G (-1)) / (1 + τ)

/-- The slope of `G` between `τ` and `1` (for `G 1 = 1`). -/
noncomputable def sHi (G : ℝ → ℝ) (τ : ℝ) : ℝ := (1 - G τ) / (1 - τ)

/-- The centre of the slope interval. -/
noncomputable def cS (G : ℝ → ℝ) (τ : ℝ) : ℝ := (sLo G τ + sHi G τ) / 2

/-- The radius of the slope interval. -/
noncomputable def rS (G : ℝ → ℝ) (τ : ℝ) : ℝ := (sHi G τ - sLo G τ) / 2

section secant

variable {G : ℝ → ℝ} {τ : ℝ}

lemma sHi_mul (hτ1 : τ < 1) : sHi G τ * (1 - τ) = 1 - G τ := by
  unfold sHi
  rw [div_mul_cancel₀ _ (by linarith : (1 : ℝ) - τ ≠ 0)]

lemma sLo_mul (hτ0 : 0 ≤ τ) : sLo G τ * (1 + τ) = G τ - G (-1) := by
  unfold sLo
  rw [div_mul_cancel₀ _ (by linarith : (1 : ℝ) + τ ≠ 0)]

lemma sLo_nonneg (hG : KGood G) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) : 0 ≤ sLo G τ := by
  have h := hG.mono (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨le_refl _, by norm_num⟩)
    (show τ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, hτ1.le⟩) (by linarith)
  unfold sLo
  exact div_nonneg (by linarith) (by linarith)

lemma sHi_le_one (hG : KGood G) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) : sHi G τ ≤ 1 := by
  have h := hG.lip (t := τ) (s := 1) (by linarith) hτ1.le (le_refl _)
  rw [hG.one] at h
  unfold sHi
  rw [div_le_one (by linarith)]
  exact h

/-- **The secant of `G` at `τ`.** -/
lemma secant_mem (hG : KGood G) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {t' : ℝ}
    (ht' : t' ∈ Icc (-1 : ℝ) 1) :
    ∃ s : ℝ, sLo G τ ≤ s ∧ s ≤ sHi G τ ∧ G τ - G t' = s * (τ - t') := by
  have hτm : τ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hτ1.le⟩
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have eLo : sLo G τ = (G (-1) - G τ) / (-1 - τ) := by
    unfold sLo
    rw [← neg_sub (G τ) (G (-1)), show (-1 : ℝ) - τ = -(1 + τ) by ring, neg_div_neg_eq]
  have eHi : sHi G τ = (G 1 - G τ) / (1 - τ) := by unfold sHi; rw [hG.one]
  rcases eq_or_ne t' τ with h | h
  · refine ⟨sLo G τ, le_refl _, ?_, by rw [h]; ring⟩
    rw [eLo, eHi]
    exact hG.conv.secant_mono hτm hm1 h1 (by linarith) (by linarith) (by norm_num)
  · refine ⟨(G t' - G τ) / (t' - τ), ?_, ?_, ?_⟩
    · rw [eLo]
      exact hG.conv.secant_mono hτm hm1 ht' (by linarith) h ht'.1
    · rw [eHi]
      exact hG.conv.secant_mono hτm ht' h1 h (by linarith) ht'.2
    · have hne : t' - τ ≠ 0 := sub_ne_zero.mpr h
      field_simp
      ring

end secant

/-- `(1 − G τ) − ((1 − G(−1))/2)(1 − τ) ≥ 0` for `0 ≤ τ ≤ 1` (convexity). -/
lemma secX_nonneg {G : ℝ → ℝ} (hG : KGood G) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ (1 - G τ) - (1 - G (-1)) / 2 * (1 - τ) := by
  rcases eq_or_lt_of_le hτ1 with h1 | h1
  · rw [h1, hG.one]; simp
  · have hHi := sHi_mul (G := G) h1
    have hLo := sLo_mul (G := G) hτ0
    obtain ⟨s, a, b, -⟩ := secant_mem hG hτ0 h1 (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from
      ⟨by norm_num, by norm_num⟩)
    have hLH : sLo G τ ≤ sHi G τ := a.trans b
    have h2 := mul_le_mul_of_nonneg_right hLH
      (show (0 : ℝ) ≤ (1 + τ) * (1 - τ) from mul_nonneg (by linarith) (by linarith))
    have e1 : sLo G τ * ((1 + τ) * (1 - τ)) = (G τ - G (-1)) * (1 - τ) := by
      linear_combination (1 - τ) * hLo
    have e2 : sHi G τ * ((1 + τ) * (1 - τ)) = (1 - G τ) * (1 + τ) := by
      linear_combination (1 + τ) * hHi
    have e3 : (1 - G τ) * (1 + τ) - (G τ - G (-1)) * (1 - τ) =
        2 * ((1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) := by ring
    linarith

variable {ι : Type*} [Fintype ι]

/-- **The distance form with the secant of `G` at the reference cosine `τ`**, `0 ≤ τ < 1`,
against the reference `s₀·(1 − G τ)`. -/
lemma phiD_secant {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) (s₀ : ℝ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) :
    |phiD G y y' - s₀ * (1 - G τ)| ≤
      (1 - τ) * rS G τ * |(normSq y + normSq y') / 2 - s₀| +
        cS G τ * |eD y y' - s₀ * (1 - τ)| +
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
  have hc0 : 0 ≤ cS G τ := by unfold cS; linarith
  have key : phiD G y y' - s₀ * (1 - G τ) =
      (1 - τ) * rS G τ * (pp - s₀) + cS G τ * (eD y y' - s₀ * (1 - τ)) +
        (s - cS G τ) * (τ * pp - dotp y y') + (G τ - s * τ) * dlt y y' := by
    unfold phiD psi eD dlt
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
  have a1 : |(1 - τ) * rS G τ * (pp - s₀)| = (1 - τ) * rS G τ * |pp - s₀| := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by linarith) hr0)]
  have a2 : |cS G τ * (eD y y' - s₀ * (1 - τ))| = cS G τ * |eD y y' - s₀ * (1 - τ)| := by
    rw [abs_mul, abs_of_nonneg hc0]
  have a3 : |(s - cS G τ) * (τ * pp - dotp y y')| ≤ rS G τ * |τ * pp - dotp y y'| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hsc (abs_nonneg _)
  have a4 : |(G τ - s * τ) * dlt y y'| ≤ dlt y y' := by
    rw [abs_mul, abs_of_nonneg hd0, abs_of_nonneg hdl]
    nlinarith
  have t1 := abs_add_le ((1 - τ) * rS G τ * (pp - s₀) + cS G τ * (eD y y' - s₀ * (1 - τ)) +
    (s - cS G τ) * (τ * pp - dotp y y')) ((G τ - s * τ) * dlt y y')
  have t2 := abs_add_le ((1 - τ) * rS G τ * (pp - s₀) + cS G τ * (eD y y' - s₀ * (1 - τ)))
    ((s - cS G τ) * (τ * pp - dotp y y'))
  have t3 := abs_add_le ((1 - τ) * rS G τ * (pp - s₀)) (cS G τ * (eD y y' - s₀ * (1 - τ)))
  linarith

lemma phiD_self {G : ℝ → ℝ} (hG : KGood G) (y : ι → ℝ) : phiD G y y = 0 := by
  unfold phiD
  by_cases hz : normSq y = 0
  · rw [psi_zero_left G hz, hz]; ring
  · have hp := nrm_pos_of_ne hz
    have hc : cosv y y = 1 := by
      unfold cosv dotp
      have : ∑ i, y i * y i = normSq y := by
        unfold normSq; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, nrm_mul_self]
      exact div_self hz
    unfold psi
    rw [hc, hG.one, mul_one, nrm_mul_self]
    ring

lemma phiD_zero_left (G : ℝ → ℝ) (y' : ι → ℝ) : phiD G (0 : ι → ℝ) y' = normSq y' / 2 := by
  have h0 : normSq (0 : ι → ℝ) = 0 := by simp [normSq]
  unfold phiD
  rw [psi_zero_left G h0, h0]; ring

lemma phiD_zero_right (G : ℝ → ℝ) (y : ι → ℝ) : phiD G y (0 : ι → ℝ) = normSq y / 2 := by
  have h0 : normSq (0 : ι → ℝ) = 0 := by simp [normSq]
  unfold phiD
  rw [psi_zero_right G y h0, h0]; ring

/-- The scaling identity of the distance form. -/
lemma phiD_smul_smul (G : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y y' : ι → ℝ) :
    phiD G (a • y) (b • y') =
      a * b * phiD G y y' + (a - b) * (a * normSq y - b * normSq y') / 2 := by
  unfold phiD
  rw [BstLean.Part135.psi_smul_smul G ha hb, normSq_smul, normSq_smul]
  ring

variable {m k : ℕ}

/-- **The linear layer for unit vectors, with the secant of `G`.** -/
theorem phi_lin_unit_L2 {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m)
    {h h' : Fin k → ℝ} (hh : normSq h = 1) (hh' : normSq h' = 1) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * (1 - G (dotp h h')))
      ((m : ℝ) * v * (((1 + √2) * (1 - G (dotp h h')) - (1 - G (-1)) / 2 * (1 - dotp h h')) /
        √(m : ℝ) + 2 * K4 m / (m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := K4_nonneg m
  set τ := dotp h h' with hτ
  have hτ1 : τ ≤ 1 := by
    have := abs_dotp_le_nrm h h'
    rw [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one] at this
    exact (le_abs_self _).trans this
  have eDh : eD h h' = 1 - τ := by unfold eD; rw [hh, hh']; ring
  have enh : normSq (h - h') = 2 * (1 - τ) := by
    have := eD_eq h h'
    rw [eDh] at this
    linarith
  set q := √(m : ℝ) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hm'
  have hqq : q * q = m := Real.mul_self_sqrt hm'.le
  have hmq : (m : ℝ) / q = q := by rw [div_eq_iff hq0.ne']; exact hqq.symm
  have h22 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : (0 : ℝ) < √2 := by positivity
  have hsq : √(2 * (m : ℝ)) = √2 * q := Real.sqrt_mul (by norm_num) _
  rcases eq_or_lt_of_le hτ1 with h1 | h1
  · -- `τ = 1`: `h = h′`
    have hz : normSq (h - h') = 0 := by rw [enh, h1]; ring
    have he : h = h' := sub_eq_zero.mp (normSq_eq_zero hz)
    subst he
    have hz0 : L2le (gaussMat m k v) (fun _ : Matrix (Fin m) (Fin k) ℝ => (0 : ℝ)) 0 := by
      have := L2le.const (μ := gaussMat m k v) (0 : ℝ)
      rwa [abs_zero] at this
    refine (hz0.congr_fun fun M => ?_).mono (le_refl _) ?_
    · rw [phiD_self hG, h1, hG.one]; ring
    · rw [h1, hG.one]
      have : (m : ℝ) * v * (((1 + √2) * (1 - 1) - (1 - G (-1)) / 2 * (1 - 1)) / q +
          2 * K4 m / (m : ℝ)) = 2 * K4 m * v := by
        field_simp
        ring
      rw [this]
      positivity
  -- the main case
  have hHi := sHi_mul (G := G) h1
  have hLo := sLo_mul (G := G) hd
  have hLo0 := sLo_nonneg hG hd h1
  have hHi1 := sHi_le_one hG hd h1
  have hLH : sLo G τ ≤ sHi G τ := by
    obtain ⟨s, a, b, -⟩ := secant_mem hG hd h1 (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from
      ⟨by norm_num, by norm_num⟩)
    linarith
  have hr0 : 0 ≤ rS G τ := by unfold rS; linarith
  have hc0 : 0 ≤ cS G τ := by unfold cS; linarith
  set s₀ : ℝ := (m : ℝ) * v with hs₀
  -- the four ingredients
  have hP : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec h) + normSq (M.mulVec h')) / 2 - s₀) (√2 * q * v) := by
    have a1 := (lin_c2 (m := m) hv.le h).const_mul_nonneg (c := 1 / 2) (by norm_num)
    have a2 := (lin_c2 (m := m) hv.le h').const_mul_nonneg (c := 1 / 2) (by norm_num)
    refine ((a1.add0 a2 (by positivity) (by positivity)).congr_fun fun M => ?_).congr_bound ?_
    · rw [hh, hh', hs₀]; ring
    · rw [hh, hh', hsq]; ring
  have hE : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      eD (M.mulVec h) (M.mulVec h') - s₀ * (1 - τ)) (√2 * q * v * (1 - τ)) := by
    refine ((linEDStmt hv hm h h').congr_fun fun M => ?_).congr_bound ?_
    · rw [eDh]
    · rw [enh]
      have u : q / √2 * 2 = √2 * q := by
        rw [div_mul_eq_mul_div, div_eq_iff h2p.ne']
        linear_combination (-q) * h22
      calc q / √2 * v * (2 * (1 - τ)) = q / √2 * 2 * v * (1 - τ) := by ring
        _ = _ := by rw [u]
  have hC : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      τ * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2) - dotp (M.mulVec h) (M.mulVec h'))
      (q * v * (1 - τ ^ 2)) := by
    obtain ⟨i, e⟩ := lin_ctp_var (m := m) hv.le hh hh'
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
  have hD : L2le (gaussMat m k v) (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dlt (M.mulVec h) (M.mulVec h')) (2 * K4 m * v) := by
    have hd0 : dlt h h' = 0 := by
      unfold dlt
      rw [hh, hh', nrm_of_normSq_one hh, nrm_of_normSq_one hh']; ring
    refine ((linDltStmt hv hm h h').congr_fun fun M => ?_).congr_bound ?_
    · rw [hd0]; ring
    · rw [hh, hh']
      simp only [sub_self, abs_zero, mul_zero, add_zero]
      field_simp
      ring
  -- the sum
  have b1 := (L2le.abs' hP).const_mul_nonneg (c := (1 - τ) * rS G τ)
    (mul_nonneg (by linarith) hr0)
  have b2 := (L2le.abs' hE).const_mul_nonneg hc0
  have b3 := (L2le.abs' hC).const_mul_nonneg hr0
  have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have s12 := b1.add0 b2 (by positivity)
    (mul_nonneg hc0 (mul_nonneg (by positivity) (by linarith)))
  have s123 := s12.add0 b3 (add_nonneg (by positivity)
    (mul_nonneg hc0 (mul_nonneg (by positivity) (by linarith)))) (by positivity)
  have s1234 := s123.add0 hD (add_nonneg (add_nonneg (by positivity)
    (mul_nonneg hc0 (mul_nonneg (by positivity) (by linarith)))) (by positivity))
    (by positivity)
  have hmeasΦ := (measurable_phiD_lin (m := m) hG.cont h h').sub
    (measurable_const (a := s₀ * (1 - G τ)))
  refine (L2le.of_abs_le hmeasΦ.aestronglyMeasurable s1234 (fun M => ?_)).congr_bound ?_
  · exact (phiD_secant hG (M.mulVec h) (M.mulVec h') s₀ hd h1).trans (le_abs_self _)
  · have eR : (m : ℝ) * v * (((1 + √2) * (1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) / q +
        2 * K4 m / (m : ℝ)) =
        q * v * ((1 + √2) * (1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) + 2 * K4 m * v := by
      calc _ = v * ((1 + √2) * (1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) * ((m : ℝ) / q) +
            2 * K4 m * v * ((m : ℝ) / m) := by ring
        _ = _ := by rw [hmq, div_self hm'.ne']; ring
    rw [eR]
    simp only [cS, rS]
    linear_combination (√2 * q * v + q * v * (1 + τ) / 2) * hHi - (q * v * (1 - τ) / 2) * hLo

/-- **The linear layer for the distance form, with the secant of `G`** (all `h, h′` with
`⟨h, h′⟩ ≥ 0`). -/
theorem phi_lin_S {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 < v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) (hd : 0 ≤ dotp h h') :
    L2le (gaussMat m k v)
      (fun M : Matrix (Fin m) (Fin k) ℝ =>
        phiD G (M.mulVec h) (M.mulVec h') - (m : ℝ) * v * phiD G h h')
      ((m : ℝ) * v * (((1 + √2) * (phiD G h h' - dlt h h') -
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
  -- a degenerate case, as a general fact
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
    · rw [Matrix.mulVec_zero, phiD_zero_left, phiD_zero_left]; ring
    · have e1 : phiD G (0 : Fin k → ℝ) h' - dlt 0 h' = 0 := by
        rw [phiD_zero_left, dlt_zero_leftL]; ring
      have e2 : eD (0 : Fin k → ℝ) h' - dlt 0 h' = 0 := by
        rw [dlt_zero_leftL]; unfold eD dotp; simp [h0]
      rw [e1, e2, nrm_zero_of h0, h0, zero_sub, abs_neg, abs_of_nonneg (normSq_nonneg h')]
      ring
  by_cases hz' : normSq h' = 0
  · have : h' = 0 := normSq_eq_zero hz'
    subst this
    refine ((deg h).congr_fun fun M => ?_).congr_bound ?_
    · rw [Matrix.mulVec_zero, phiD_zero_right, phiD_zero_right]; ring
    · have e1 : phiD G h (0 : Fin k → ℝ) - dlt h 0 = 0 := by
        rw [phiD_zero_right, dlt_comm, dlt_zero_leftL]; ring
      have e2 : eD h (0 : Fin k → ℝ) - dlt h 0 = 0 := by
        rw [dlt_comm, dlt_zero_leftL]; unfold eD dotp; simp [h0]
      rw [e1, e2, nrm_zero_of h0, h0, sub_zero, abs_of_nonneg (normSq_nonneg h)]
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
  have hgu : normSq g = 1 := by
    rw [hg, normSq_smul, eN]; field_simp
  have hgu' : normSq g' = 1 := by
    rw [hg', normSq_smul, eN']; field_simp
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
  have hunit := phi_lin_unit_L2 (m := m) hG hv hm hgu hgu' hτ0
  rw [← hτ] at hunit
  have hX := secX_nonneg hG hτ0 hτ1
  have hγ1 : 0 ≤ 1 - G τ := by
    have := hG.le_one (show τ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, hτ1⟩)
    linarith
  have hXX : 0 ≤ (1 + √2) * (1 - G τ) - (1 - G (-1)) / 2 * (1 - τ) := by
    have : 0 ≤ √2 * (1 - G τ) := by positivity
    linarith
  have hub : 0 ≤ (m : ℝ) * v * (((1 + √2) * (1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) /
      √(m : ℝ) + 2 * K4 m / (m : ℝ)) := by positivity
  have c2 := lin_c2 (m := m) hv.le g
  have c2' := lin_c2 (m := m) hv.le g'
  rw [hgu, mul_one] at c2
  rw [hgu', mul_one] at c2'
  -- the pieces
  have p1 := hunit.const_mul_nonneg (c := a * b) (by positivity)
  have p2 := c2.const_mul ((a - b) / 2 * a)
  have p3 := c2'.const_mul (-((a - b) / 2 * b))
  have s12 := p1.add0 p2 (by positivity) (by positivity)
  have s123 := s12.add0 p3 (by positivity) (by positivity)
  refine (s123.congr_fun fun M => ?_).congr_bound ?_
  · have e1 : M.mulVec h = a • M.mulVec g := by
      conv_lhs => rw [ehg]
      exact Matrix.mulVec_smul M a g
    have e2 : M.mulVec h' = b • M.mulVec g' := by
      conv_lhs => rw [ehg']
      exact Matrix.mulVec_smul M b g'
    have e3 : phiD G h h' = a * b * (1 - G τ) + (a - b) * (a - b) / 2 := by
      conv_lhs => rw [ehg, ehg']
      rw [phiD_smul_smul G ha0 hb0, phiD_unit G hgu hgu', hgu, hgu']
      ring
    rw [e1, e2, phiD_smul_smul G ha0 hb0, e3]
    ring
  · have e3 : phiD G h h' - dlt h h' = a * b * (1 - G τ) := by
      have e3' : phiD G h h' = a * b * (1 - G τ) + (a - b) * (a - b) / 2 := by
        conv_lhs => rw [ehg, ehg']
        rw [phiD_smul_smul G ha0 hb0, phiD_unit G hgu hgu', hgu, hgu']
        ring
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
    calc a * b * ((m : ℝ) * v * (((1 + √2) * (1 - G τ) - (1 - G (-1)) / 2 * (1 - τ)) /
            √(m : ℝ) + 2 * K4 m / (m : ℝ))) + |a - b| / 2 * a * (√(2 * (m : ℝ)) * v) +
          |a - b| / 2 * b * (√(2 * (m : ℝ)) * v)
        = (m : ℝ) * v * (((1 + √2) * (a * b * (1 - G τ)) - (1 - G (-1)) / 2 * (a * b * (1 - τ))) /
            √(m : ℝ) + 2 * K4 m / (m : ℝ) * (a * b)) +
            |a - b| * (a + b) / 2 * v * √(2 * (m : ℝ)) := by ring
      _ = _ := by rw [e8]; ring

end BstLean.Part142

open BstLean.Part142 in
#print axioms phi_lin_unit_L2
open BstLean.Part142 in
#print axioms phi_lin_S
