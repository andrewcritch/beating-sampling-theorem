import BstLean.Part145K3

/-!
# Part 145 (K6): the numbers of `Part145K2` at the thresholds `n ≥ 4096` and `n ≥ 4489`

At `mA n = n²`:
* `n ≥ 4096 = 64²`: `cC0x ≤ 0.031644/n`, `cC2x ≤ 0.23858/n` (`cC0x_leR`, `cC2x_leR`);
* `n ≥ 4489 = 67²`: `cC0x ≤ 0.030206/n`, `cC2x ≤ 0.2279/n` (`cC0x_leS`, `cC2x_leS`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142
open BstLean.Part143

open AgD AgS AgC AgK

lemma sqrt2_geKR : (141421 : ℝ) / 100000 ≤ √2 :=
  (Real.le_sqrt' (by norm_num)).2 (by norm_num)

/-- `cK ≤ 0.038892`. -/
lemma cK_leKR : cK ≤ 38892 / 1000000 := by
  have h := sqrt2_geKR
  unfold cK dK
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ## The threshold `n ≥ 4096 = 64²` -/

namespace AgK

section focusR

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

lemma n4096KR : 4096 ≤ n := le_trans (by norm_num) hn

/-- `y = 1/n`, `z = 1/√n` at `n ≥ 4096`. -/
lemma yzKR : ∃ y z : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧
    0 < y ∧ 0 < z ∧ y ≤ 1 / 4096 ∧ z ≤ 1 / 64 := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr (n4096KR hn)
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (64 : ℝ) ≤ √(n : ℝ) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  refine ⟨y, z, hy, hz, hy0, hz0, ?_, ?_⟩
  · rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  · rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs

lemma Q2_leKR : √(1 + 2 / (mA n : ℝ)) ≤ 10000001 / 10000000 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h2' : (16777216 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 2 / (n : ℝ) ^ 2 ≤ 2 / 16777216 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have e : ((10000001 : ℝ) / 10000000) ^ 2 = 100000020000001 / 100000000000000 := by norm_num
  rw [e]
  linarith

lemma q3z_leKR : q3 (mA n) 0 ≤ 63970 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzKR hn
  have hn4 := n4096KR hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b3 := b3_le
  have g3 := g3_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 4096) := by nlinarith
  unfold q3
  rw [sqrt_mA, mA_eqR, ← hy]
  refine le_trans (le_of_eq (?_ : _ = bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
    ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))) ?_
  · rw [hy]; ring
  · calc bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
          ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)
        ≤ 28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
          1 * (4 * (11 / 5) * y ^ 2 * 2) := by gcongr
      _ ≤ 63970 / 100000 * y := by nlinarith

lemma q2z_leKR : q2 (mA n) 0 ≤ 74817 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzKR hn
  have hn4 := n4096KR hn
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
  have hyy : y ^ 2 ≤ y * (1 / 4096) := by nlinarith
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
      _ ≤ 74817 / 100000 * y := by nlinarith

end focusR

end AgK

section focusBoundsR

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `cC0x ≤ 0.031644/n` for `n ≥ 4096`. -/
theorem cC0x_leR : cC0x n (mA n) ≤ 31644 / 1000000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzKR hn
  have hn4 := n4096KR hn
  have h2 := sqrt2_le
  have hc := cK_leKR
  have hc0 := cK_nonneg
  have a1 := nc0_le hn4
  have a4 := LS_le hn4
  have a5 := q2z_leKR hn
  have a6 := q3z_leKR hn
  have n1 := nc0_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a1 a4 a5 a6
  have hzy : y * z ≤ y * (1 / 64) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC0x_eq]
  refine le_trans (le_of_eq (?_ : _ = √2 * (q3 (mA n) 0 + cK * nc0 (mA n) + q2 (mA n) 0 +
    (1 + cK) * LS (mA n)) * z)) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 31644 / 1000000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * (q3 (mA n) 0 + cK * nc0 (mA n) + q2 (mA n) 0 + (1 + cK) * LS (mA n)) * z
        ≤ 141422 / 100000 * (63970 / 100000 * y + 38892 / 1000000 * (815 / 1000 * y) +
          74817 / 100000 * y + (1 + 38892 / 1000000) * (12 / 1000 * y)) * z := by gcongr
      _ ≤ 31644 / 1000000 * y := by nlinarith

/-- `cC2x ≤ 0.23858/n` for `n ≥ 4096`. -/
theorem cC2x_leR : cC2x n (mA n) ≤ 23858 / 100000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzKR hn
  have h3 := sqrt3_le
  have h2 := sqrt2_le
  have hc := cK_leKR
  have hc0 := cK_nonneg
  have hQ := Q2_leKR hn
  have hzy : y * z ≤ y * (1 / 64) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC2x_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √2 * ((1 + cK) * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))) * z)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 23858 / 100000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * ((1 + cK) * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))) * z
        ≤ 141422 / 100000 * ((1 + 38892 / 1000000) * (2 * (17321 / 10000) * y +
          17321 / 10000 * y * (4 * (10000001 / 10000000)))) * z := by gcongr
      _ ≤ 23858 / 100000 * y := by nlinarith

end focusBoundsR

/-! ## The threshold `n ≥ 4489 = 67²` -/

namespace AgK

section focusS

variable {n : ℕ} (hn : 4489 ≤ n)

include hn

lemma n4096KS : 4096 ≤ n := le_trans (by norm_num) hn

/-- `y = 1/n`, `z = 1/√n` at `n ≥ 4489`. -/
lemma yzKS : ∃ y z : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧
    0 < y ∧ 0 < z ∧ y ≤ 1 / 4489 ∧ z ≤ 1 / 67 := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr (n4096KS hn)
  have hx : (4489 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (67 : ℝ) ≤ √(n : ℝ) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  refine ⟨y, z, hy, hz, hy0, hz0, ?_, ?_⟩
  · rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  · rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs

lemma Q2_leKS : √(1 + 2 / (mA n : ℝ)) ≤ 10000001 / 10000000 := by
  have hx : (4489 : ℝ) ≤ n := by exact_mod_cast hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h2' : (20151121 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 2 / (n : ℝ) ^ 2 ≤ 2 / 20151121 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have e : ((10000001 : ℝ) / 10000000) ^ 2 = 100000020000001 / 100000000000000 := by norm_num
  rw [e]
  linarith

lemma q3z_leKS : q3 (mA n) 0 ≤ 63933 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzKS hn
  have hn4 := n4096KS hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b3 := b3_le
  have g3 := g3_le
  have h5 := sqrt5_le'
  have hK := Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 4489) := by nlinarith
  unfold q3
  rw [sqrt_mA, mA_eqR, ← hy]
  refine le_trans (le_of_eq (?_ : _ = bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
    ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))) ?_
  · rw [hy]; ring
  · calc bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
          ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)
        ≤ 28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
          1 * (4 * (11 / 5) * y ^ 2 * 2) := by gcongr
      _ ≤ 63933 / 100000 * y := by nlinarith

lemma q2z_leKS : q2 (mA n) 0 ≤ 74750 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzKS hn
  have hn4 := n4096KS hn
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
  have hyy : y ^ 2 ≤ y * (1 / 4489) := by nlinarith
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
      _ ≤ 74750 / 100000 * y := by nlinarith

end focusS

end AgK

section focusBoundsS

variable {n : ℕ} (hn : 4489 ≤ n)

include hn

/-- `cC0x ≤ 0.030206/n` for `n ≥ 4489`. -/
theorem cC0x_leS : cC0x n (mA n) ≤ 30206 / 1000000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzKS hn
  have hn4 := n4096KS hn
  have h2 := sqrt2_le
  have hc := cK_leKR
  have hc0 := cK_nonneg
  have a1 := nc0_le hn4
  have a4 := LS_le hn4
  have a5 := q2z_leKS hn
  have a6 := q3z_leKS hn
  have n1 := nc0_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a1 a4 a5 a6
  have hzy : y * z ≤ y * (1 / 67) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC0x_eq]
  refine le_trans (le_of_eq (?_ : _ = √2 * (q3 (mA n) 0 + cK * nc0 (mA n) + q2 (mA n) 0 +
    (1 + cK) * LS (mA n)) * z)) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 30206 / 1000000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * (q3 (mA n) 0 + cK * nc0 (mA n) + q2 (mA n) 0 + (1 + cK) * LS (mA n)) * z
        ≤ 141422 / 100000 * (63933 / 100000 * y + 38892 / 1000000 * (815 / 1000 * y) +
          74750 / 100000 * y + (1 + 38892 / 1000000) * (12 / 1000 * y)) * z := by gcongr
      _ ≤ 30206 / 1000000 * y := by nlinarith

/-- `cC2x ≤ 0.2279/n` for `n ≥ 4489`. -/
theorem cC2x_leS : cC2x n (mA n) ≤ 22790 / 100000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hy1, hz1⟩ := yzKS hn
  have h3 := sqrt3_le
  have h2 := sqrt2_le
  have hc := cK_leKR
  have hc0 := cK_nonneg
  have hQ := Q2_leKS hn
  have hzy : y * z ≤ y * (1 / 67) := mul_le_mul_of_nonneg_left hz1 hy0.le
  rw [cC2x_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √2 * ((1 + cK) * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))) * z)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 22790 / 100000 * y) (le_of_eq (by rw [hy]; ring))
    calc √2 * ((1 + cK) * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))) * z
        ≤ 141422 / 100000 * ((1 + 38892 / 1000000) * (2 * (17321 / 10000) * y +
          17321 / 10000 * y * (4 * (10000001 / 10000000)))) * z := by gcongr
      _ ≤ 22790 / 100000 * y := by nlinarith

end focusBoundsS

end BstLean.Part145

open BstLean.Part145 in
#print axioms cC0x_leR
open BstLean.Part145 in
#print axioms cC2x_leR
open BstLean.Part145 in
#print axioms cC0x_leS
open BstLean.Part145 in
#print axioms cC2x_leS
