import BstLean.Part201All
import BstLean.Part159PaperD

/-! S06: smoothing precision from 4096. -/

namespace BstLean.Part204

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part133 (L2le)
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN sS h1bar GamS GamS_L2x GamS_nonneg psiS mW_ge_pow42)
open BstLean.Part141 (aOf sOf rowS rowS_nonneg aOf_mul aOf_cN sOf_cN sOf_sq cN_nonneg cN_sq_le
  cN_le_half GamS_rowS psiS_lip_x psiS_lip_s aOne_mean GamS_mean measurable_aOf)
open BstLean.Part150 (binMean lemmaBF1_paper c1F kappa4 c1F_kappa4_le c1F_nonneg kappa4_nonneg)
open BstLean.Part157

open BstLean.Part159

variable {n : ℕ}

theorem sWp_sub_sq (hn : 4096 ≤ n) (hm : 1 ≤ mW n) (θ : WHid n) (hS1 : 1998 / 1000 ≤ SWp θ)
    (hS2 : SWp θ ≤ 2002 / 1000) (hd1 : |cNt n - cN (2 * n)| ≤ cN (2 * n) / 100) :
    (sWp θ - sS θ.1) ^ 2 ≤ 9 * (cNt n - cN (2 * n)) ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨-, hcw⟩ := BstLean.Part201.cN_even_window hn
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = cN (2 * n) := ⟨_, rfl⟩
  rw [← hc] at hd1 hcw ⊢
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = cNt n - c := ⟨_, rfl⟩
  rw [← hd] at hd1 ⊢
  have hc0 : 0 ≤ c := by rw [hc]; exact cN_nonneg _
  have hct : cNt n = c + d := by rw [hd]; ring
  obtain ⟨hda, hdb⟩ := abs_le.mp hd1
  -- `c̃² ≤ 1.0201·c²`, `(2c + d)² ≤ 4.0401·c²`
  have hct2 : cNt n ^ 2 ≤ (101 / 100 * c) ^ 2 := by
    rw [hct]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2cd : (2 * c + d) ^ 2 ≤ (201 / 100 * c) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hX : c ^ 2 * (n : ℝ) ≤ 8 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hcw
    linarith
  -- `dNt ≥ 0.33/n`
  have hdN : 33 / 100 / (n : ℝ) ≤ dNt n := by
    unfold dNt
    rw [div_le_iff₀ hnpos]
    have e : (1 / (2 * (n : ℝ)) - 2 * cNt n ^ 2) * (n : ℝ) = 1 / 2 - 2 * (cNt n ^ 2 * (n : ℝ)) := by
      field_simp
    rw [e]
    have h1 : cNt n ^ 2 * (n : ℝ) ≤ (101 / 100 * c) ^ 2 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hct2 hnpos.le
    nlinarith
  have hdN0 : 0 ≤ dNt n := le_trans (by positivity) hdN
  have hSpos : 0 < SWp θ := by linarith
  have hst2 : sWp θ ^ 2 = SWp θ * dNt n := by
    unfold sWp
    exact Real.sq_sqrt (mul_nonneg hSpos.le hdN0)
  have hst0 : 0 ≤ sWp θ := sWp_nonneg θ
  have hs0 : 0 ≤ sS θ.1 := Real.sqrt_nonneg _
  have hs2 : sS θ.1 ^ 2 = SWp θ * (1 / (2 * (n : ℝ)) - 2 * c ^ 2) := by
    have h := sOf_sq (N := 2 * n) (m := mW n) hN hm (cN_nonneg _) le_rfl θ
    rw [sOf_cN hN hm] at h
    rw [h, hNcast, hc]
    unfold SWp
    field_simp
  have hlow : 65 / 100 / (n : ℝ) ≤ sWp θ ^ 2 := by
    rw [hst2]
    have h1 : 1998 / 1000 * (33 / 100 / (n : ℝ)) ≤ SWp θ * dNt n :=
      mul_le_mul hS1 hdN (by positivity) hSpos.le
    have h0 : 65 / 100 / (n : ℝ) ≤ 1998 / 1000 * (33 / 100 / (n : ℝ)) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by norm_num) hnpos.le
    exact h0.trans h1
  have hdiff : sWp θ ^ 2 - sS θ.1 ^ 2 = -(2 * SWp θ * d * (2 * c + d)) := by
    rw [hst2, hs2]
    unfold dNt
    rw [hct]
    ring
  have hkey : (sWp θ - sS θ.1) ^ 2 * sWp θ ^ 2 ≤ (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 := by
    have e : (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 = (sWp θ - sS θ.1) ^ 2 * (sWp θ + sS θ.1) ^ 2 := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact pow_le_pow_left₀ hst0 (by linarith) 2
  have hsq : (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 * (n : ℝ) ≤ 53 / 10 * d ^ 2 := by
    rw [hdiff, neg_sq]
    have e : (2 * SWp θ * d * (2 * c + d)) ^ 2 * (n : ℝ) =
        4 * SWp θ ^ 2 * ((2 * c + d) ^ 2 * (n : ℝ)) * d ^ 2 := by ring
    rw [e]
    have h1 : SWp θ ^ 2 ≤ (2002 / 1000) ^ 2 := pow_le_pow_left₀ hSpos.le hS2 2
    have h2 : (2 * c + d) ^ 2 * (n : ℝ) ≤ (201 / 100) ^ 2 * (8 / 100) := by
      have h3 := mul_le_mul_of_nonneg_right h2cd hnpos.le
      nlinarith
    have h4 : 4 * SWp θ ^ 2 * ((2 * c + d) ^ 2 * (n : ℝ)) ≤
        4 * (2002 / 1000) ^ 2 * ((201 / 100) ^ 2 * (8 / 100)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity) (by norm_num)
    have h5 : (4 * (2002 / 1000) ^ 2 * ((201 / 100) ^ 2 * (8 / 100)) : ℝ) ≤ 53 / 10 := by norm_num
    exact mul_le_mul_of_nonneg_right (h4.trans h5) (sq_nonneg _)
  -- conclude
  have h6 : (sWp θ - sS θ.1) ^ 2 * (65 / 100 / (n : ℝ)) ≤ (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 :=
    (mul_le_mul_of_nonneg_left hlow (sq_nonneg _)).trans hkey
  have h7 : (sWp θ - sS θ.1) ^ 2 * (65 / 100) ≤ (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 * (n : ℝ) := by
    have h8 := mul_le_mul_of_nonneg_right h6 hnpos.le
    have e : (sWp θ - sS θ.1) ^ 2 * (65 / 100 / (n : ℝ)) * (n : ℝ) =
        (sWp θ - sS θ.1) ^ 2 * (65 / 100) := by field_simp
    rw [e] at h8
    exact h8
  nlinarith [sq_nonneg d, sq_nonneg (sWp θ - sS θ.1)]


end BstLean.Part204

#print axioms BstLean.Part204.sWp_sub_sq
