import BstLean.Part293Arithmetic
import BstLean.Part278Good

/-! The global clipped-rule perturbation bounds need only the paid operator
and row-energy bounds. They do not need a separate lower-variance event. -/
namespace BstLean.Part293
open Real BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part272

theorem odd_radical_caps {N u Q : ℝ} (hN : 0 ≤ N) (hu : 0 ≤ u)
    (hu1 : u ≤ 1) (hQ0 : 0 ≤ Q) (hQ : Q ≤ 5 * N ^ 2) :
    √(2 * (9 * ((u ^ 2) ^ 2 * Q)) + 4 * (u ^ 2 * (7 + u ^ 2) * Q)) ≤ 16 * u * N ∧
      √(52 * (9 * Q) + 8 * ((8 + 3 * u ^ 2) * Q)) ≤ 54 * N := by
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have hu4 : (u ^ 2) ^ 2 ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu2)]
  have hf : 2 * (9 * (u ^ 2) ^ 2) + 4 * (u ^ 2 * (7 + u ^ 2)) ≤ 50 * u ^ 2 := by
    nlinarith
  constructor
  · apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ = (2 * (9 * (u ^ 2) ^ 2) + 4 * (u ^ 2 * (7 + u ^ 2))) * Q := by ring
      _ ≤ (50 * u ^ 2) * (5 * N ^ 2) := mul_le_mul hf hQ hQ0 (by positivity)
      _ ≤ (16 * u * N) ^ 2 := by nlinarith [sq_nonneg (u * N)]
  · apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ = (52 * 9 + 8 * (8 + 3 * u ^ 2)) * Q := by ring
      _ ≤ 556 * (5 * N ^ 2) :=
        mul_le_mul (by nlinarith) hQ hQ0 (by norm_num)
      _ ≤ (54 * N) ^ 2 := by nlinarith [sq_nonneg N]

theorem odd_pass_caps {n : ℕ} (hn : 8001 ≤ n) (ho : Odd n) (c : Ret n)
    (hO : OpB (A2 c) 3) (s : ℝ)
    (hQ : ∑ i, BstLean.Part278.aw c s i ^ 2 ≤ 5 * (n : ℝ) ^ 2) :
    |fPassG a1St e1St c s - fPassG a1Bar e1Bar c s| ≤
        8 * ((1 / 10 ^ 45 : ℝ) / (n : ℝ) ^ 5) * n ∧
      |wPassG a1St e1St c s - wPassG a1Bar e1Bar c s| ≤
        130 * ((1 / 10 ^ 45 : ℝ) / (n : ℝ) ^ 5) * (n : ℝ) ^ 2 := by
  have hnR : (8001 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let u : ℝ := (1 / 10 ^ 45 : ℝ) / (n : ℝ) ^ 5
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (div_le_self (by norm_num) (one_le_pow₀ (by linarith : (1 : ℝ) ≤ n))).trans (by norm_num)
  have he : BstLean.Part278.epsO n = u ^ 2 := by
    unfold BstLean.Part278.epsO
    rw [BstLean.Part278.rpow_neg_ten]
    dsimp [u]
    field_simp <;> ring
  have hQ0 : 0 ≤ ∑ i, BstLean.Part278.aw c s i ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr := odd_radical_caps hn0.le hu hu1 hQ0 hQ
  have hf := BstLean.Part278.odd_fPass_err hn ho (BstLean.Part278.Jz_pos (by omega)) c s hO
  have hw := BstLean.Part278.odd_wPass_err hn ho (BstLean.Part278.Jz_pos (by omega)) c s hO
  rw [he] at hf hw
  norm_num only [show (3 : ℝ) ^ 2 = 9 by norm_num] at hf hw
  constructor
  · apply hf.trans
    apply (div_le_div_of_nonneg_right hr.1 (sqrt_nonneg _)).trans
    apply (div_le_iff₀ (sqrt_pos.mpr hn0)).mpr
    have hs : (2 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 8 * u * n by positivity)
    change 16 * u * n ≤ 8 * u * n * √(n : ℝ)
    nlinarith only [h]
  · apply hw.trans
    apply (div_le_div_of_nonneg_right
      (mul_le_mul hr.1 hr.2 (sqrt_nonneg _) (by positivity)) hn0.le).trans
    apply (div_le_iff₀ hn0).mpr
    change (16 * u * n) * (54 * n) ≤ (130 * u * (n : ℝ) ^ 2) * n
    have h := mul_le_mul_of_nonneg_left (show (864 : ℝ) ≤ 130 * n by linarith)
      (show 0 ≤ u * (n : ℝ) ^ 2 by positivity)
    nlinarith only [h]

def arithmeticInputs_of_operators {n : ℕ} (hn : 8001 ≤ n) (ho : Odd n)
    (c : Ret n) (he : 0 < eR c)
    (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * 1.081)
    (hO : OpB (A2 c) 3)
    (hQ : ∀ g, g ≤ Js n - 1 → ∑ i, BstLean.Part278.aw c (nodeS c g) i ^ 2 ≤ 5 * (n : ℝ) ^ 2)
    (hF : ∀ g, g ≤ Js n - 1 → |passF c g| ≤ 9 * n) : ArithmeticInputs c where
  energy_pos := he
  output_norm := hc
  location := fun g hg => (odd_pass_caps hn ho c hO (nodeS c g) (hQ g hg)).1
  energy := fun g hg => (odd_pass_caps hn ho c hO (nodeS c g) (hQ g hg)).2
  exact_location := hF

end BstLean.Part293

/-- info: 'BstLean.Part293.odd_pass_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.odd_pass_caps
