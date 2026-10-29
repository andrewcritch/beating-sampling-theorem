import BstLean.Part143AgentC

/-!
# Part 145: the numbers of `Part143AgentC` at the lower threshold `n ≥ 9216 = 96²`

At `mA n = n²`, `n ≥ 9216`: `cC0 ≤ 0.02036/n`, `cC2 ≤ 0.1531/n`, `rR0 ≤ 8.395/n`,
`rR2 ≤ 10.54/n`, `rR1' ≥ 0.3408/√n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142
open BstLean.Part143

open AgD AgS AgC

namespace AgC

section focus

variable {n : ℕ} (hn : 9216 ≤ n)

include hn

lemma n4096CM : 4096 ≤ n := le_trans (by norm_num) hn

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` at `n ≥ 9216`. -/
lemma yzrCM : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 9216 ∧ z ≤ 1 / 96 ∧ r ≤ 707107 / 1000000 * z := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr (n4096CM hn)
  have hx : (9216 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (96 : ℝ) ≤ √(n : ℝ) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  refine ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, ?_, ?_, hr1⟩
  · rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  · rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs

lemma K4_leCM : K4 n ≤ 34649 / 10000 := by
  have hx : (9216 : ℝ) ≤ n := by exact_mod_cast hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have h : 48 / (n : ℝ) ≤ 48 / 9216 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have e : ((34649 : ℝ) / 10000) ^ 2 = 1200553201 / 100000000 := by norm_num
  rw [e]
  linarith

lemma Q2_leCM : √(1 + 2 / (mA n : ℝ)) ≤ 10000001 / 10000000 := by
  have hx : (9216 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (16384 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 2 / (n : ℝ) ^ 2 ≤ 2 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have h2' : (84934656 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 2 / (n : ℝ) ^ 2 ≤ 2 / 84934656 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have e : ((10000001 : ℝ) / 10000000) ^ 2 = 100000020000001 / 100000000000000 := by norm_num
  rw [e]
  linarith

lemma SS_leCM : SS (mA n) ≤ 20001 / 10000 := by
  have hx : (9216 : ℝ) ≤ n := by exact_mod_cast hn
  have h2' : (84934656 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 5 / (n : ℝ) ^ 2 ≤ 5 / 84934656 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have hpos : (0 : ℝ) ≤ 1 + 5 / (mA n : ℝ) := by positivity
  have e : SS (mA n) = 2 * (1 + 5 / (mA n : ℝ)) := by
    unfold SS sS
    calc √(1 + 5 / (mA n : ℝ)) * (2 * √(1 + 5 / (mA n : ℝ)))
        = 2 * (√(1 + 5 / (mA n : ℝ)) * √(1 + 5 / (mA n : ℝ))) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hpos]
  rw [e, mA_eqR]
  linarith

lemma q3z_leCM : q3 (mA n) 0 ≤ 6374 / 10000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrCM hn
  have hn4 := n4096CM hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b3 := b3_le
  have g3 := g3_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 9216) := by nlinarith
  unfold q3
  rw [sqrt_mA, mA_eqR, ← hy]
  refine le_trans (le_of_eq (?_ : _ = bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
    ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))) ?_
  · rw [hy]; ring
  · calc bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
          ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)
        ≤ 28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
          1 * (4 * (11 / 5) * y ^ 2 * 2) := by gcongr
      _ ≤ 6374 / 10000 * y := by nlinarith

lemma q2z_leCM : q2 (mA n) 0 ≤ 744 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrCM hn
  have hn4 := n4096CM hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hb2 := bG_nonneg hG
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have b2 := b2_le
  have g2 := g2_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have a5 := sS_le hn4
  have a6 := dS_le hn4
  have a7 := lS_le hn4
  have n5 := sS_nn (mA n)
  have n6 := dS_nn (mA n)
  have n7 := lS_nn (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 9216) := by nlinarith
  unfold q2 eS
  rw [sqrt_mA, mA_eqR, ← hy]
  rw [← hy] at a6 a7
  refine le_trans (le_of_eq (?_ : _ = bG (kappa ∘ kappa) * (√5 * (y / 2)) * sS (mA n) +
    (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * sS (mA n) + √5 * y * dS (mA n) +
      2 * lS (mA n)))) ?_
  · rw [hy]; ring
  · calc bG (kappa ∘ kappa) * (√5 * (y / 2)) * sS (mA n) +
          (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * sS (mA n) + √5 * y * dS (mA n) +
            2 * lS (mA n))
        ≤ 33087 / 100000 * (223607 / 100000 * (y / 2)) * (2002 / 1000) +
          49376 / 100000 * (4 * (11 / 5) * y ^ 2 * (2002 / 1000) +
            223607 / 100000 * y * (447214 / 100000 * y) + 2 * (176 / 10 * y ^ 2)) := by gcongr
      _ ≤ 744 / 1000 * y := by nlinarith

end focus

end AgC

open BstLean.Part145.AgC

section focusBounds

variable {n : ℕ} (hn : 9216 ≤ n)

include hn

/-- `cC0 ≤ 0.02036/n`. -/
theorem cC0_leM : cC0 n (mA n) ≤ 2036 / 100000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrCM hn
  have h2 := sqrt2_le
  have a5 := q2z_leCM hn
  have a6 := q3z_leCM hn
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a5 a6
  have hzy : y * z ≤ y * (1 / 96) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC0_eq]
  refine le_trans (le_of_eq (?_ : _ = √2 * (q3 (mA n) 0 + q2 (mA n) 0) * z)) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 2036 / 100000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * (q3 (mA n) 0 + q2 (mA n) 0) * z
        ≤ 141422 / 100000 * (6374 / 10000 * y + 744 / 1000 * y) * z := by gcongr
      _ ≤ 2036 / 100000 * y := by nlinarith

/-- `cC2 ≤ 0.1531/n`. -/
theorem cC2_leM : cC2 n (mA n) ≤ 1531 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrCM hn
  have h3 := sqrt3_le
  have h2 := sqrt2_le
  have hQ := Q2_leCM hn
  have hzy : y * z ≤ y * (1 / 96) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √2 * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 1531 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z
        ≤ 141422 / 100000 * (2 * (17321 / 10000) * y +
          17321 / 10000 * y * (4 * (10000001 / 10000000))) * z := by gcongr
      _ ≤ 1531 / 10000 * y := by nlinarith

/-- `rR1' ≥ 0.3408/√n` (the coefficient with the minus sign: a LOWER bound). -/
theorem rR1'_geM : 3408 / 10000 / √(n : ℝ) ≤ rR1' n := sA1'_ge (n4096CM hn)

/-- `rR2 ≤ 10.54/n`. -/
theorem rR2_leM : rR2 n (mA n) ≤ 1054 / 100 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrCM hn
  have h3 := sqrt3_le
  have hQ := Q2_leCM hn
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le'
  have hzy : y * z ≤ y * (1 / 96) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [rR2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = (1 + cgS (kappa ∘ kappa)) * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) +
    2 * √3 * y)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 1054 / 100 * y) (le_of_eq (by rw [hy]; ring))
    calc (1 + cgS (kappa ∘ kappa)) * (2 * √3 * y +
          √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) +
          2 * √3 * y
        ≤ (1 + 34085 / 100000) * (2 * (17321 / 10000) * y +
          17321 / 10000 * y * (4 * (10000001 / 10000000))) * z +
          17321 / 10000 * y * (4 * (10000001 / 10000000)) + 2 * (17321 / 10000) * y := by
            gcongr
      _ ≤ 1054 / 100 * y := by nlinarith

/-- `rR0 ≤ 8.395/n`. -/
theorem rR0_leM : rR0 n (mA n) ≤ 8395 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrCM hn
  have hn4 := n4096CM hn
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le'
  have hK4 := K4_leCM hn
  have hK40 := K4_nonneg n
  have a1 := nc0_le hn4
  have a2 := SS_leCM hn
  have a3 := DS_le hn4
  have a4 := LS_le hn4
  have a5 := q2z_leCM hn
  have a6 := q3z_leCM hn
  have n1 := nc0_nn (mA n)
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a1 a3 a4 a5 a6
  have hzy : y * z ≤ y * (1 / 96) := mul_le_mul_of_nonneg_left hz1 hy0.le
  have hr2 : r ≤ 707107 / 1000000 * (1 / 96) := by linarith
  have hyr : y * r ≤ y * (707107 / 1000000 * (1 / 96)) :=
    mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [rR0_eq]
  refine le_trans (le_of_eq (?_ : _ =
    (q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) + q2 (mA n) 0 +
      (1 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
    K4 n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0)) ?_
  · rw [hy, hz, hr]; ring
  · refine le_trans (?_ : _ ≤ 8395 / 1000 * y) (le_of_eq (by rw [hy]; ring))
    calc (q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) +
          q2 (mA n) 0 + (1 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
          K4 n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0
        ≤ (6374 / 10000 * y + 34085 / 100000 * (815 / 1000 * y) +
          744 / 1000 * y + (1 + 34085 / 100000) * (12 / 1000 * y)) * z +
          34649 / 10000 * y * (20001 / 10000) + 895 / 100 * y * r + 744 / 1000 * y +
          6374 / 10000 * y := by gcongr
      _ ≤ 8395 / 1000 * y := by nlinarith

end focusBounds

end BstLean.Part145

open BstLean.Part145 in
#print axioms cC0_leM
open BstLean.Part145 in
#print axioms cC2_leM
open BstLean.Part145 in
#print axioms rR0_leM
open BstLean.Part145 in
#print axioms rR2_leM
open BstLean.Part145 in
#print axioms rR1'_geM
