import BstLean.Part204Smoothing

/-! S06: computed-centre distance from 4096. -/

namespace BstLean.Part204

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN sS)
open BstLean.Part141 (aOf)
open BstLean.Part150 (c1F kappa4 c1F_kappa4_le c1F_nonneg kappa4_nonneg)
open BstLean.Part157

open BstLean.Part159

variable {n : ℕ}

theorem bWp_dist (hn : 4096 ≤ n) (hC : ConstC n) {θ : WHid n} (hS : θ ∈ goodS n)
    (hA : θ ∈ goodAo n) :
    2 / (mW n : ℝ) * normSq (bWp θ - bhat θ) ≤
      2 / ((2 * n : ℕ) : ℝ) * (645 / 10 ^ 4 / (mW n : ℝ)) := by
  have hn4 : 4096 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
  have hmpos : (0 : ℝ) < mW n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨hJ1, hJ2⟩ := JW_ge hn4
  have hJpos : (0 : ℝ) < (JW n : ℝ) := by
    have : (1000 : ℝ) ≤ (JW n : ℝ) := by exact_mod_cast hJ2
    linarith
  set X : ℝ := 1 / ((n : ℝ) * (mW n : ℝ)) with hX
  have hXpos : 0 < X := by positivity
  set d := cNt n - cN (2 * n) with hd
  -- the constant
  have hC' : d ^ 2 * (n : ℝ) * (mW n : ℝ) ≤ 1 / 10 ^ 17 := hC
  have hdX : d ^ 2 ≤ 1 / 10 ^ 17 * X := by
    rw [hX]
    have e : 1 / 10 ^ 17 * (1 / ((n : ℝ) * (mW n : ℝ))) =
        1 / 10 ^ 17 / ((n : ℝ) * (mW n : ℝ)) := by ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨hcw, -⟩ := BstLean.Part201.cN_even_window hn
  have hc0 : 0 ≤ cN (2 * n) := BstLean.Part141.cN_nonneg _
  have hd1 : |d| ≤ cN (2 * n) / 100 := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    have h1 : 1 / 10 ^ 17 * X ≤ (1 / (13 * (n : ℝ))) / 10 ^ 4 := by
      rw [hX]
      rw [div_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : (cN (2 * n) / 100) ^ 2 = cN (2 * n) ^ 2 / 10 ^ 4 := by ring
    rw [h2]
    have h3 : (1 / (13 * (n : ℝ))) / 10 ^ 4 ≤ cN (2 * n) ^ 2 / 10 ^ 4 :=
      div_le_div_of_nonneg_right hcw (by norm_num)
    linarith
  -- `S_W`
  have hS' : |SWp θ / 2 - 1| ≤ 1 / 1000 := hS
  obtain ⟨hSa, hSb⟩ := abs_le.mp hS'
  have hS1 : 1998 / 1000 ≤ SWp θ := by linarith
  have hS2 : SWp θ ≤ 2002 / 1000 := by linarith
  -- the three pieces
  set c1 := c1F kappa4 (JW n) with hc1
  have hc1le : c1 ≤ 1792 / 10000 := c1F_kappa4_le hJ2
  have hc10 : 0 ≤ c1 := c1F_nonneg kappa4_nonneg _
  set A := c1 * sWp θ / (JW n) with hAdef
  have hst := sWp_sq_le hn1 θ
  have hJm : (mW n : ℝ) ≤ (JW n : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hJ1 2
    rwa [Real.sq_sqrt hmpos.le] at this
  have hA2 : A ^ 2 ≤ 3212 / 100000 * (1001 / 1000) * X := by
    rw [hAdef, div_pow, mul_pow, div_le_iff₀ (by positivity)]
    have h1 : c1 ^ 2 ≤ 3212 / 100000 := by nlinarith
    have h2 : sWp θ ^ 2 ≤ 1001 / 1000 / (n : ℝ) := by
      refine hst.trans ?_
      rw [div_le_div_iff₀ (by positivity) hnpos]
      nlinarith
    have h3 : c1 ^ 2 * sWp θ ^ 2 ≤ 3212 / 100000 * (1001 / 1000 / (n : ℝ)) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by norm_num)
    have h4 : 3212 / 100000 * (1001 / 1000 / (n : ℝ)) =
        3212 / 100000 * (1001 / 1000) * X * (mW n : ℝ) := by
      rw [hX]; field_simp
    have h5 : 3212 / 100000 * (1001 / 1000) * X * (mW n : ℝ) ≤
        3212 / 100000 * (1001 / 1000) * X * (JW n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hJm (by positivity)
    linarith
  have hCs := BstLean.Part204.sWp_sub_sq hn hm θ hS1 hS2 hd1
  set Cs := |sWp θ - sS θ.1| with hCsdef
  have hCs2 : Cs ^ 2 ≤ 9 * d ^ 2 := by
    rw [hCsdef, sq_abs]
    exact hCs
  have hTa : 2 / (mW n : ℝ) * normSq (aOf 1 θ) ≤ 10 ^ 8 := hA
  -- coordinates
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (mW n) → ℝ, δ = bWp θ - bhat θ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; exact div_nonneg (mul_nonneg hc10 (sWp_nonneg θ)) hJpos.le
  have hcoord : ∀ i : Fin (mW n), δ i ^ 2 ≤
      (1 + 1 / 1000) * A ^ 2 +
        (1 + 1 / (1 / 1000 : ℝ)) * (2 * (d ^ 2 * aOf 1 θ i ^ 2) + 2 * Cs ^ 2) := by
    intro i
    have h1 := bWp_coord hn1 (by omega : 1 ≤ JW n) θ i
    have h2 : |δ i| ≤ A + (|d| * |aOf 1 θ i| + Cs) := by
      rw [hδ]
      simp only [Pi.sub_apply]
      linarith
    have hB0 : 0 ≤ |d| * |aOf 1 θ i| + Cs := by positivity
    have h3 : δ i ^ 2 ≤ (A + (|d| * |aOf 1 θ i| + Cs)) ^ 2 := by
      rw [← sq_abs (δ i)]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h4 := sq_add_eta (η := 1 / 1000) (by norm_num) A (|d| * |aOf 1 θ i| + Cs)
    have h5 : (|d| * |aOf 1 θ i| + Cs) ^ 2 ≤ 2 * (d ^ 2 * aOf 1 θ i ^ 2) + 2 * Cs ^ 2 := by
      have e : d ^ 2 * aOf 1 θ i ^ 2 = (|d| * |aOf 1 θ i|) ^ 2 := by
        rw [mul_pow, sq_abs, sq_abs]
      rw [e]
      exact sq_add_two _ _
    have h6 := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 1 + 1 / (1 / 1000 : ℝ))
    exact h3.trans (h4.trans (add_le_add le_rfl h6))
  have h7 := dist_assembly hm δ (aOf 1 θ) hcoord
  rw [← hδ]
  have h9 : d ^ 2 * (2 / (mW n : ℝ) * normSq (aOf 1 θ)) ≤ d ^ 2 * 10 ^ 8 :=
    mul_le_mul_of_nonneg_left hTa (sq_nonneg _)
  have e10 : 2 / ((2 * n : ℕ) : ℝ) * (645 / 10 ^ 4 / (mW n : ℝ)) = 645 / 10 ^ 4 * X := by
    rw [hNcast, hX]
    field_simp
  rw [e10]
  have h11 : d ^ 2 * 10 ^ 8 ≤ 1 / 10 ^ 17 * X * 10 ^ 8 :=
    mul_le_mul_of_nonneg_right hdX (by norm_num)
  have h12 : Cs ^ 2 ≤ 9 * (1 / 10 ^ 17 * X) :=
    hCs2.trans (mul_le_mul_of_nonneg_left hdX (by norm_num))
  have h13 : (1 + 1 / (1 / 1000 : ℝ)) = 1001 := by norm_num
  rw [h13] at h7
  linarith


end BstLean.Part204

#print axioms BstLean.Part204.bWp_dist
