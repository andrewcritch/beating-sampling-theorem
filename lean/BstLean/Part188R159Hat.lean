import BstLean.Part187All
import BstLean.Part159Hat
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2

/-! Part 187 (file `Part188R159Hat`): copy of `Part159Hat` re-proved at the floor `16200 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part188.Base159_R
open BstLean.Part159 BstLean.Part159.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat measurable_bhat)
open BstLean.Part138 (hellG)
open BstLean.Part140
open BstLean.Part143 (frameHat143 L143 goodHat_compl143s P143 cExtra143s nsq_div_mW_le128)
open BstLean.Part156 BstLean.Part157

variable {n : ℕ}

/-- The hidden charge of the computed centre at the floor `16200` (Part 159: `0.00163194`). -/
noncomputable def δHat : ℝ := 164908 / 10 ^ 8

/-- `n/m_W ≤ 1/(127 n²)` and `1/m_W ≤ 1/(127 n³)` for `n ≥ 16 384`. -/
lemma inv_mW_le {n : ℕ} (hn : 16200 ≤ n) :
    (n : ℝ) / (mW n : ℝ) ≤ 1 / (127 * (n : ℝ) ^ 2) ∧ 1 / (mW n : ℝ) ≤ 1 / (127 * (n : ℝ) ^ 3) := by
  have hn' : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million (n := n) (by omega)
    exact_mod_cast (by omega : 0 < mW n)
  have h := BstLean.Part188.Base143_R.nsq_div_mW_le128 hn
  have e1 : (n : ℝ) / (mW n : ℝ) = (n : ℝ) ^ 2 / (mW n : ℝ) / (n : ℝ) := by field_simp
  have e2 : 1 / (mW n : ℝ) = (n : ℝ) ^ 2 / (mW n : ℝ) / (n : ℝ) ^ 2 := by field_simp
  constructor
  · rw [e1]
    refine (div_le_div_of_nonneg_right h hnpos.le).trans (le_of_eq ?_)
    field_simp
  · rw [e2]
    refine (div_le_div_of_nonneg_right h (by positivity)).trans (le_of_eq ?_)
    field_simp

/-- **The hidden charge of the computed centre** (from Part 143): `Pr((goodHat n)ᶜ) ≤ 0.00164908`
for every `n ≥ 16 384`. -/
theorem hat_charge {n : ℕ} (hn : 16200 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ δHat := by
  have hn' : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have h := BstLean.Part188.Base143_R.goodHat_compl143s hn
  have h2 : BstLean.Part188.Base143_R.cExtra187 / (n : ℝ) ≤ BstLean.Part188.Base143_R.cExtra187 / 16200 :=
    div_le_div_of_nonneg_left (by unfold BstLean.Part188.Base143_R.cExtra187; norm_num) (by norm_num) hn'
  have h3 : P143 + BstLean.Part188.Base143_R.cExtra187 / 16200 ≤ δHat := by
    unfold P143 BstLean.Part188.Base143_R.cExtra187 δHat; norm_num
  linarith

end BstLean.Part188.Base159_R

