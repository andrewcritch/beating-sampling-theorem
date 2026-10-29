import BstLean.Part159Paper
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R159Hat
import BstLean.Part187R159Win
import BstLean.Part187R159Frame

/-! Part 187 (file `Part187R159Paper`): copy of `Part159Paper` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part159.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part133 (L2le)
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN mW_ge_pow42 cHat2)
open BstLean.Part140
open BstLean.Part143 (nsq_div_mW_le128)
open BstLean.Part156 BstLean.Part157

variable {n : ℕ}

/-- The hidden charge for the centre of the paper at the floor `16250` (Part 159: `0.00163204`). -/
noncomputable def δPap : ℝ := 164649 / 10 ^ 8

/-- **The hidden charge for the centre of the paper**: `Pr((GPap n)ᶜ) ≤ 0.00163204`,
`n ≥ 16 384`. -/
theorem pap_charge (hn : 16250 ≤ n) : (hidGauss (2 * n) (mW n)).real (GPap n)ᶜ ≤ δPap := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h1 := hat_charge hn
  have h2 := goodS_charge (n := n) (by omega) hm
  have h3 := goodAo_charge hn4
  have hsub : (GPap n)ᶜ ⊆ ((goodHat n)ᶜ ∪ (goodS n)ᶜ) ∪ (goodAo n)ᶜ := by
    intro θ hθ
    simp only [GPap, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have h4 := (measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have h5 : (10 : ℝ) ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) ≤ 1 / 10 ^ 8 := by
    have e : (10 : ℝ) ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) =
        10 ^ 6 / ((n : ℝ) * (mW n : ℝ)) := by
      rw [hNcast]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  unfold δPap
  unfold δHat at h1
  have h6 : (164639 / 10 ^ 8 : ℝ) + 1 / 10 ^ 8 + 9 / 10 ^ 8 ≤ 164649 / 10 ^ 8 := by norm_num
  linarith

section consts

variable (hn : 13225 ≤ n) (hK : ConstK n)

include hn hK

end consts

section world

variable (hn : 16250 ≤ n) (hC : ConstC n) (hK : ConstK n) {θ : WHid n} (hθ : θ ∈ GPap n)

include hn hC hK hθ

omit hK in
/-- The window of `B = t_W|b_W|²` on `GPap n`: `0.48687·γ ≤ B ≤ 0.50078·γ`. -/
lemma pap_B :
    2 / ((2 * n : ℕ) : ℝ) * (48685 / 100000) ≤ 2 / (mW n : ℝ) * normSq (bWp θ) ∧
      2 / (mW n : ℝ) * normSq (bWp θ) ≤ 2 / ((2 * n : ℕ) : ℝ) * (50081 / 100000) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have hmpos : (0 : ℝ) < mW n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by rw [hNcast]; linarith
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ 2 / (mW n : ℝ) := by positivity
  obtain ⟨hb1, hb2⟩ := Bh_window_16 hn hθ.1.1
  unfold Bh at hb1 hb2
  have hd := bWp_dist (by omega) hC hθ.1.2 hθ.2
  set δ := bWp θ - bhat θ with hδ
  have hdm : 2 / (mW n : ℝ) * normSq δ ≤ 2 / ((2 * n : ℕ) : ℝ) * (2 / 10 ^ 14) := by
    refine hd.trans (mul_le_mul_of_nonneg_left ?_ hγ.le)
    rw [div_le_iff₀ hmpos]
    nlinarith
  have e1 : bWp θ = bhat θ + δ := by rw [hδ]; abel
  have e2 : bhat θ = bWp θ + (-δ) := by rw [hδ]; abel
  have hneg : normSq (-δ) = normSq δ := by simp [normSq]
  have h1 := normSq_add_eta (η := 1 / 10 ^ 6) (by norm_num) (bhat θ) δ
  rw [← e1] at h1
  have h2 := normSq_add_eta (η := 1 / 10 ^ 6) (by norm_num) (bWp θ) (-δ)
  rw [← e2, hneg] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 ht
  have h2' := mul_le_mul_of_nonneg_left h2 ht
  have hδ0 : 0 ≤ 2 / (mW n : ℝ) * normSq δ := mul_nonneg ht (normSq_nonneg _)
  set γ := (2 : ℝ) / ((2 * n : ℕ) : ℝ) with hγdef
  set Bb := 2 / (mW n : ℝ) * normSq (bWp θ) with hBb
  set Bh' := 2 / (mW n : ℝ) * normSq (bhat θ) with hBh
  set Dd := 2 / (mW n : ℝ) * normSq δ with hDd
  have h1'' : Bb ≤ (1 + 1 / 10 ^ 6) * Bh' + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
    have : 2 / (mW n : ℝ) * ((1 + 1 / 10 ^ 6) * normSq (bhat θ) +
        (1 + 1 / (1 / 10 ^ 6 : ℝ)) * normSq δ) =
        (1 + 1 / 10 ^ 6) * Bh' + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
      rw [hBh, hDd]; ring
    linarith
  have h2'' : Bh' ≤ (1 + 1 / 10 ^ 6) * Bb + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
    have : 2 / (mW n : ℝ) * ((1 + 1 / 10 ^ 6) * normSq (bWp θ) +
        (1 + 1 / (1 / 10 ^ 6 : ℝ)) * normSq δ) =
        (1 + 1 / 10 ^ 6) * Bb + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
      rw [hBb, hDd]; ring
    linarith
  have h3 : (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd ≤ γ * (3 / 10 ^ 8) := by
    have : (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd ≤ (1 + 1 / (1 / 10 ^ 6 : ℝ)) * (γ * (2 / 10 ^ 14)) :=
      mul_le_mul_of_nonneg_left hdm (by norm_num)
    nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- **The window of `B·c`** for the scalar of the paper on `GPap n`: `1.994 ≤ B·c ≤ 2.057`, and
`c ≥ 0`. -/
lemma pap_window :
    0 ≤ ccP n θ ∧ 1994 / 1000 ≤ 2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ∧
      2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ≤ 2057 / 1000 := by
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨-, hκ1, hκ2⟩ := kapT_window (by omega) hK
  have hS' : |SWp θ / 2 - 1| ≤ 1 / 1000 := hθ.1.2
  obtain ⟨hSa, hSb⟩ := abs_le.mp hS'
  have hS1 : 1998 / 1000 ≤ SWp θ := by linarith
  have hS2 : SWp θ ≤ 2002 / 1000 := by linarith
  obtain ⟨hB1, hB2⟩ := pap_B hn hC hθ
  rw [hNcast] at hB1 hB2
  set Bb := 2 / (mW n : ℝ) * normSq (bWp θ) with hBb
  have hκ0 : 0 < kapT n := by linarith
  have hSκ : 0 < SWp θ * kapT n ^ 2 := by positivity
  have hκsq1 : (493719 / 1000000 : ℝ) ^ 2 ≤ kapT n ^ 2 := pow_le_pow_left₀ (by norm_num) hκ1 2
  have hκsq2 : kapT n ^ 2 ≤ (493801 / 1000000 : ℝ) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
  have hSκ1 : 1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2 ≤ SWp θ * kapT n ^ 2 :=
    mul_le_mul hS1 hκsq1 (by norm_num) (by linarith)
  have hSκ2 : SWp θ * kapT n ^ 2 ≤ 2002 / 1000 * (493801 / 1000000 : ℝ) ^ 2 :=
    mul_le_mul hS2 hκsq2 (sq_nonneg _) (by norm_num)
  have hcc0 : 0 ≤ ccP n θ := by unfold ccP; positivity
  have e : Bb * ccP n θ = Bb * (2 * (n : ℝ)) / (SWp θ * kapT n ^ 2) := by
    unfold ccP; ring
  have hBn1 : 2 * (48685 / 100000 : ℝ) ≤ Bb * (2 * (n : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hB1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    have e2 : 2 / (2 * (n : ℝ)) * (48685 / 100000) * (2 * (n : ℝ)) = 2 * (48685 / 100000) := by
      field_simp
    linarith
  have hBn2 : Bb * (2 * (n : ℝ)) ≤ 2 * (50081 / 100000 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hB2 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    have e2 : 2 / (2 * (n : ℝ)) * (50081 / 100000) * (2 * (n : ℝ)) = 2 * (50081 / 100000) := by
      field_simp
    linarith
  refine ⟨hcc0, ?_, ?_⟩
  · rw [e, le_div_iff₀ hSκ]
    have : (1994 / 1000 : ℝ) * (2002 / 1000 * (493801 / 1000000 : ℝ) ^ 2) ≤
        2 * (48685 / 100000) := by norm_num
    nlinarith
  · rw [e, div_le_iff₀ hSκ]
    have : 2 * (50081 / 100000 : ℝ) ≤
        2057 / 1000 * (1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2) := by norm_num
    nlinarith

/-- The scalar of the paper on `GPap n`: `τ₀² = B(B·c − 1)` and `τ₀ > 0`. -/
lemma pap_tau :
    tau0p θ ^ 2 = 2 / (mW n : ℝ) * normSq (bWp θ) *
      (2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ - 1) ∧ 0 < tau0p θ := by
  obtain ⟨-, hA1, -⟩ := pap_window hn hC hK hθ
  exact tau0p_of (by linarith)

end world

/-- **The frame bound for the centre of the paper**: `1.36/n` on `GPap n`, `n ≥ 16 384`, IF
`ConstC n`. -/
theorem pap_frame (hn : 16250 ≤ n) (hC : ConstC n) {θ : WHid n} (hθ : θ ∈ GPap n)
    (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir (bWp θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      136 / 100 / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have hmpos : (0 : ℝ) < mW n := by linarith
  have hd := bWp_dist (by omega) hC hθ.1.2 hθ.2
  refine pert_frame hn hθ.1.1 (e₁ := 645 / 10 ^ 4 * (n : ℝ) / (mW n : ℝ)) ?_ ?_ w
  · have h := BstLean.Part143.R.nsq_div_mW_le128 hn
    have e : 645 / 10 ^ 4 * (n : ℝ) / (mW n : ℝ) =
        645 / 10 ^ 4 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) := by field_simp
    rw [e, div_le_iff₀ hnpos]
    have h2 : 1 / (127 * (n : ℝ)) ≤ 1 / (127 * 16250) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    nlinarith
  · refine hd.trans (le_of_eq ?_)
    field_simp

end BstLean.Part159.R

