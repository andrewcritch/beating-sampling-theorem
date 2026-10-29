import BstLean.Part169Red

/-!
# Part 169 (file `In`): the inputs of Part 08 that hold on the good set

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, formula `t7:p08:inputs`: `S̄(s) ≥ γ_A d_*` on kept latitudes
(`d_* = (1 − η)d_low`) and `|c_A|² ≤ γ_A e_b n χ_A⁺`, `χ_A⁺ = 1 + 2√(12/n) + 24/n`.

* `sA_le`: `S(x) ≤ (2/m_A)·‖A₂‖_F²·‖A₁‖_F²` on the latitude points (so `S` is integrable in `v`).
* **`Sb_lower`**: on a kept index of the paper's program, `S̄ ≥ γ_A·dStar`,
  `dStar = (1 − 10⁻⁴)·0.4691² ≈ 0.220028 > 1/5`. Lean's good slice asks `σ ≥ √γ_A·0.4691`
  pointwise and the kept slice has mass at least `1 − η`, `η = 10⁻⁴`; the paper's argument
  ("nonnegative omitted energy and kept mass at least `1 − η`").
* **`cA_input`**: on `goodD`, `e_b > 0` and `|c_A|² ≤ γ_A e_b n χ_A⁺` (from Part 164's event
  `EcA` and `cA_of_good`).
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (keptIx latC muI xLat Ix sA lamX sigX)
open BstLean.Part162 (sgA latC_sq_le normSq_xLat_le)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- `dStar = (1 − 10⁻⁴)·0.4691²`, the floor `d_*` of the kept full means. -/
noncomputable def dStar : ℝ := (1 - 1 / 10000) * (4691 / 10000) ^ 2

lemma dStar_ge : (1 : ℝ) / 5 ≤ dStar := by unfold dStar; norm_num

/-- `S(x) ≤ (2/m_A)·‖A₂‖_F²·‖A₁‖_F²` at the latitude points. -/
lemma sA_le (hn : 1 ≤ n) (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    sA D c a v ≤ 2 / (mA n : ℝ) * (BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)) := by
  have hm : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  show sigX D c (xLat c (latC D c a) (unitF53 v)) ^ 2 ≤ _
  unfold sigX sig
  set h := hid2 c.2.1.1.1 c.2.1.1.2 (xLat c (latC D c a) (unitF53 v))
  set b := D.bA c.1 c.2.1.1
  rw [mul_pow, Real.sq_sqrt hm, Real.sq_sqrt (normSq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ hm
  have hres : normSq (res b h) ≤ normSq h := by
    by_cases hb : b = 0
    · have : res b h = h := by unfold res; rw [hb, smul_zero, sub_zero]
      rw [this]
    · exact BstLean.Part149.normSq_res_le hb h
  refine hres.trans ((BstLean.Part131.normSq_hid2_le _ _ _).trans ?_)
  have hx := normSq_xLat_le hn c (latC_sq_le D c a) v
  have h1 := BstLean.Part131.frob_nonneg (A1 c)
  have h2 := BstLean.Part131.frob_nonneg (A2 c)
  calc BstLean.Part131.frob c.2.1.1.2 * (BstLean.Part131.frob c.2.1.1.1 *
        normSq (xLat c (latC D c a) (unitF53 v)))
      ≤ BstLean.Part131.frob c.2.1.1.2 * (BstLean.Part131.frob c.2.1.1.1 * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx h1) h2
    _ = BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c) := by ring

lemma integrable_sA (hn : 1 ≤ n) (D : Design n) (c : Ret n) (a : Ix n) :
    Integrable (sA D c a) (stdGauss (Fin (n - 1))) := by
  refine Integrable.mono' (integrable_const (2 / (mA n : ℝ) *
    (BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c))))
    (BstLean.Part161.measurable_sA_left D c a).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by show 0 ≤ sgA D c a v ^ 2; positivity)]
  exact sA_le hn D c a v

/-- **The floor of the kept full means** (paper `t7:p08:inputs`, first inequality):
`S̄(a) ≥ γ_A·dStar` on the kept indices of the paper's program. -/
theorem Sb_lower (hn : 1 ≤ n) (c : Ret n) {a : Ix n} (ha : a ∈ KR c) :
    2 / (n : ℝ) * dStar ≤ (dP c).Sb a := by
  set D := paperDesignP n
  have hk := BstLean.Part162.kept_facts hn D c (by norm_num : (0:ℝ) < 1 / 10000)
    (by norm_num : (1:ℝ) / 10000 < 1) ha
  obtain ⟨-, hm1, -, -, hsl, -⟩ := hk
  set σl : ℝ := √(2 / (n : ℝ)) * (4691 / 10000) with hσl
  set sl := BstLean.Part161.slice (dP c) a with hsl_def
  have msl : MeasurableSet sl := BstLean.Part161.measurableSet_slice _ a
  have hσ0 : 0 ≤ σl := by positivity
  have hpt : ∀ v, sl.indicator (fun _ => σl ^ 2) v ≤ sA D c a v := by
    intro v
    by_cases hv : v ∈ sl
    · rw [Set.indicator_of_mem hv]
      have h1 := (hsl v hv).2
      show σl ^ 2 ≤ sgA D c a v ^ 2
      exact pow_le_pow_left₀ hσ0 h1 2
    · rw [Set.indicator_of_notMem hv]
      show 0 ≤ sgA D c a v ^ 2
      positivity
  have hint := integral_mono ((integrable_const (σl ^ 2)).indicator msl) (integrable_sA hn D c a)
    hpt
  rw [integral_indicator msl, integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hint
  have hS : (dP c).Sb a = ∫ v, sA D c a v ∂stdGauss (Fin (n - 1)) := rfl
  rw [hS]
  refine le_trans ?_ hint
  have hσ2 : σl ^ 2 = 2 / (n : ℝ) * (4691 / 10000) ^ 2 := by
    rw [hσl, mul_pow, Real.sq_sqrt (by positivity)]
  rw [hσ2]
  unfold dStar
  have h0 : (0 : ℝ) ≤ 2 / (n : ℝ) * (4691 / 10000) ^ 2 := by positivity
  have hm1' : 1 - 1 / 10000 ≤ (stdGauss (Fin (n - 1))).real sl := hm1
  have := mul_le_mul_of_nonneg_right hm1' h0
  linarith

/-- **`|c_A|²` on the good set** (paper `t7:p08:inputs`): `e_b > 0` and
`|c_A|² ≤ γ_A e_b n χ_A⁺` with `χ_A⁺ = chiUp n / n = 1 + 2√(12/n) + 24/n`. -/
theorem cA_input (hn : 16384 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) :
    0 < eR c ∧ normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * (BstLean.Part164.chiUp n / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hE : c ∈ BstLean.Part164.EcA (paperCentres n) := hc.2.1.2.1.2
  have hpos := (BstLean.Part164.cA_of_good hn passF passW measurable_passF measurable_passW
    hc).1
  obtain ⟨h1, -⟩ := hE
  have hb : normSq ((paperCentres n).bA c.1 c.2.1.1) = normSq (bR c) := rfl
  rw [hb] at h1
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm] at h1
  have hup : 0 < BstLean.Part164.chiUp n := by unfold BstLean.Part164.chiUp; positivity
  constructor
  · unfold eR
    have : 0 < normSq (bR c) := by
      by_contra hneg
      have h0 : normSq (bR c) = 0 := le_antisymm (le_of_not_gt hneg) (normSq_nonneg _)
      rw [h0] at h1; simp at h1; linarith
    positivity
  · refine h1.trans (le_of_eq ?_)
    unfold eR
    field_simp

end BstLean.Part169
