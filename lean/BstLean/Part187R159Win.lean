import BstLean.Part159Win
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R159Hat

/-! Part 187 (file `Part187R159Win`): copy of `Part159Win` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part159.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat Bn136)
open BstLean.Part140
open BstLean.Part152 (chiSq_upper_LM chiSq_lower_LM)
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}


/-- The window of `t_W|b̂|²` for `n ≥ 16 384`: `0.48688·γ ≤ t_W|b̂|² ≤ 0.50077·γ`
(Part 140 has `0.48`, `0.508` for `n ≥ 4096`). -/
theorem Bh_window_16 (hn : 16250 ≤ n) {θ : WHid n} (hθ : θ ∈ goodHat n) :
    2 / ((2 * n : ℕ) : ℝ) * (48686 / 100000) ≤ Bh (2 * n) (mW n) θ ∧
      Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (50080 / 100000) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn4; omega
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by rw [hNcast]; linarith
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  obtain ⟨hB1, hB2⟩ := Bn136 hn4 hθ.1.1
  have hHB : Hh (2 * n) (mW n) θ = 2 / ((2 * n : ℕ) : ℝ) * BstLean.Part137.Bn (2 * n) (mW n) θ := by
    unfold Hh BstLean.Part137.Bn
    field_simp
  have hL : 2 / ((2 * n : ℕ) : ℝ) * (4936 / 10000) ≤ Hh (2 * n) (mW n) θ := by
    rw [hHB]; exact mul_le_mul_of_nonneg_left hB1 hγ.le
  have hU : Hh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (494 / 1000) := by
    rw [hHB]; exact mul_le_mul_of_nonneg_left hB2 hγ.le
  have hd : dist2 (2 * n) (mW n) θ ≤
      2 / ((2 * n : ℕ) : ℝ) * (3 / 4 / ((2 * n : ℕ) : ℝ)) := hθ.1.2
  have hξ : (3 / 4 / ((2 * n : ℕ) : ℝ) : ℝ) ≤ (4804 / 1000000) ^ 2 := by
    rw [hNcast, div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨g1, g2⟩ := Bh_window_gen (N := 2 * n) (m := mW n) hN hm hL hU hd
    (sL := 70256 / 100000) (sU := 70286 / 100000) (sξ := 4804 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hξ (by norm_num)
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ hγ.le) g1
    norm_num
  · refine le_trans g2 (mul_le_mul_of_nonneg_left ?_ hγ.le)
    norm_num

lemma sqrt12n_le (hn : 16250 ≤ n) : √(12 / (n : ℝ)) ≤ 27175 / 1000000 := by
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma exp_neg_n_le (hn : 16250 ≤ n) : exp (-(45 / 10000 * (n : ℝ))) ≤ 1 / 10 ^ 9 := by
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : exp (-(45 / 10000 * (n : ℝ))) ≤ exp (-30) := exp_le_exp.2 (by linarith)
  have h2 : exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have := Real.exp_one_gt_d9
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h3 : exp (-30) = exp (-1) ^ 30 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h4 : exp (-1) ^ 30 ≤ (1 / 2 : ℝ) ^ 30 := pow_le_pow_left₀ (exp_pos _).le h2 30
  have h5 : (1 / 2 : ℝ) ^ 30 ≤ 1 / 10 ^ 9 := by norm_num
  linarith

/-- **The charge of the events other than the hidden event, with the two angle events proved.**
For every design and `n ≥ 16 384`: `Pr(H ∩ (E_{θ−} ∩ E_{θ+} ∩ E_A)ᶜ) ≤ 6.146·10⁻⁶ +
Pr(H ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ)`. -/
theorem extra_angle (hn : 16250 ≤ n) (D : Centres n) (H EA : Set (Ret n)) :
    (retDist D).real (H ∩ (Ethm D ∩ Ethp D ∩ EA)ᶜ) ≤
      δAng + (retDist D).real (H ∩ Ethm D ∩ Ethp D ∩ EAᶜ) := by
  have hsub : H ∩ (Ethm D ∩ Ethp D ∩ EA)ᶜ ⊆
      ((Ethm D)ᶜ ∪ (Ethp D)ᶜ) ∪ (H ∩ Ethm D ∩ Ethp D ∩ EAᶜ) := by
    intro c hc
    by_cases h1 : c ∈ Ethm D
    · by_cases h2 : c ∈ Ethp D
      · right
        exact ⟨⟨⟨hc.1, h1⟩, h2⟩, fun h3 => hc.2 ⟨⟨h1, h2⟩, h3⟩⟩
      · left; right; exact h2
    · left; left; exact h1
  have h1 := ethm_charge D
  have h2 := ethp_charge (by omega : 1 ≤ n) D
  have h3 := exp_neg_12_le
  have h4 := exp_neg_n_le hn
  have h5 : (retDist D).real (H ∩ (Ethm D ∩ Ethp D ∩ EA)ᶜ) ≤
      (retDist D).real (Ethm D)ᶜ + (retDist D).real (Ethp D)ᶜ +
        (retDist D).real (H ∩ Ethm D ∩ Ethp D ∩ EAᶜ) :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  unfold δAng
  norm_num at h3 h4 ⊢
  linarith

end BstLean.Part159.R

