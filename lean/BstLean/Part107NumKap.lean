import BstLean.Part107Defs

/-!
# Part 107: facts about `κ` for `d_A ∈ {3, 4}` on `[−1, 1]` (`KapFacts107`)
-/

namespace BstLean.Part107

private lemma kap3 (a : ℝ) : kap 3 a = 1 + a + a ^ 2 + a ^ 3 := by
  simp [kap, Finset.sum_range_succ]

private lemma kap4 (a : ℝ) : kap 4 a = 1 + a + a ^ 2 + a ^ 3 + a ^ 4 := by
  simp [kap, Finset.sum_range_succ]

private lemma kap'3 (a : ℝ) : kap' 3 a = 1 + 2 * a + 3 * a ^ 2 := by
  simp [kap', Finset.sum_range_succ]; ring

private lemma kap'4 (a : ℝ) : kap' 4 a = 1 + 2 * a + 3 * a ^ 2 + 4 * a ^ 3 := by
  simp [kap', Finset.sum_range_succ]; ring

private lemma hasDeriv3 (a : ℝ) : HasDerivAt (kap 3) (kap' 3 a) a := by
  have h : kap 3 = fun a : ℝ => 1 + a + a ^ 2 + a ^ 3 := funext kap3
  rw [h, kap'3]
  have := (((hasDerivAt_const a (1 : ℝ)).add (hasDerivAt_id a)).add
    ((hasDerivAt_id a).pow 2)).add ((hasDerivAt_id a).pow 3)
  convert this using 1
  · funext x; simp
  · simp

private lemma hasDeriv4 (a : ℝ) : HasDerivAt (kap 4) (kap' 4 a) a := by
  have h : kap 4 = fun a : ℝ => 1 + a + a ^ 2 + a ^ 3 + a ^ 4 := funext kap4
  rw [h, kap'4]
  have := ((((hasDerivAt_const a (1 : ℝ)).add (hasDerivAt_id a)).add
    ((hasDerivAt_id a).pow 2)).add ((hasDerivAt_id a).pow 3)).add ((hasDerivAt_id a).pow 4)
  convert this using 1
  · funext x; simp
  · simp

private lemma abs_mul_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
  rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg y]

/-- The exact certificate for `d_A = 3`: `7.697 − κ′(a)²(1 − a²)` is a sum of squares. -/
private lemma cert3 (a : ℝ) : (1 + 2 * a + 3 * a ^ 2) ^ 2 * (1 - a ^ 2) ≤ 7697 / 1000 := by
  have h : 7697 / 1000 - (1 + 2 * a + 3 * a ^ 2) ^ 2 * (1 - a ^ 2) =
      (6697 / 1000) * (1 + (-2000 / 6697) * a + (-9275 / 6697) * a ^ 2 + (-19 / 181) * a ^ 3) ^ 2 +
      (1199127 / 133940) * (a + (-40630009 / 59956350) * a ^ 2 + (-9427082 / 9992725) * a ^ 3) ^ 2 +
      (30896138777 / 59956350000) * (a ^ 2 + (-41795339874 / 30896138777) * a ^ 3) ^ 2 +
      (473834375617 / 30896138777000) * (a ^ 3) ^ 2 := by ring
  have : 0 ≤ 7697 / 1000 - (1 + 2 * a + 3 * a ^ 2) ^ 2 * (1 - a ^ 2) := by
    rw [h]; positivity
  linarith

/-- The exact certificate for `d_A = 4`: `15.532 − κ′(a)²(1 − a²)` is a sum of squares. -/
private lemma cert4 (a : ℝ) :
    (1 + 2 * a + 3 * a ^ 2 + 4 * a ^ 3) ^ 2 * (1 - a ^ 2) ≤ 15532 / 1000 := by
  have h : 15532 / 1000 - (1 + 2 * a + 3 * a ^ 2 + 4 * a ^ 3) ^ 2 * (1 - a ^ 2) =
      (3633 / 250) * (1 + (-500 / 3633) * a + (-1877 / 1038) * a ^ 2 + (99 / 2422) * a ^ 3 +
        (2889 / 4844) * a ^ 4) ^ 2 +
      (39309737 / 908250) * (a + (-22180501 / 78619474) * a ^ 2 +
        (-156281667 / 157238948) * a ^ 3 + (-471468 / 1709119) * a ^ 4) ^ 2 +
      (57018343551 / 19654868500) * (a ^ 2 + (5494700143 / 228073374204) * a ^ 3 +
        (-364160062439 / 228073374204) * a ^ 4) ^ 2 +
      (41362812992497 / 456146748408000) * (a ^ 3 +
        (-49798588813715 / 41362812992497) * a ^ 4) ^ 2 +
      (213180968615523 / 20681406496248500) * (a ^ 4) ^ 2 := by ring
  have : 0 ≤ 15532 / 1000 - (1 + 2 * a + 3 * a ^ 2 + 4 * a ^ 3) ^ 2 * (1 - a ^ 2) := by
    rw [h]; positivity
  linarith

private lemma lip3 (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |kap 3 a - kap 3 b| ≤ LipK 3 * |a - b| := by
  have e : kap 3 a - kap 3 b = (1 + (a + b) + (a ^ 2 + a * b + b ^ 2)) * (a - b) := by
    rw [kap3, kap3]; ring
  have hL : LipK 3 = 6 := by norm_num [LipK]
  rw [e, abs_mul, hL]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have h1 := abs_le.1 ha
  have h2 := abs_le.1 hb
  have h3 := abs_le.1 (abs_mul_le_one ha ha)
  have h4 := abs_le.1 (abs_mul_le_one ha hb)
  have h5 := abs_le.1 (abs_mul_le_one hb hb)
  rw [abs_le]
  constructor <;> nlinarith

private lemma lip4 (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |kap 4 a - kap 4 b| ≤ LipK 4 * |a - b| := by
  have e : kap 4 a - kap 4 b = (1 + (a + b) + (a * a + a * b + b * b) +
      (a * a * a + a * a * b + a * b * b + b * b * b)) * (a - b) := by
    rw [kap4, kap4]; ring
  have hL : LipK 4 = 10 := by norm_num [LipK]
  rw [e, abs_mul, hL]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have h1 := abs_le.1 ha
  have h2 := abs_le.1 hb
  have h3 := abs_le.1 (abs_mul_le_one ha ha)
  have h4 := abs_le.1 (abs_mul_le_one ha hb)
  have h5 := abs_le.1 (abs_mul_le_one hb hb)
  have h6 := abs_le.1 (abs_mul_le_one (abs_mul_le_one ha ha) ha)
  have h7 := abs_le.1 (abs_mul_le_one (abs_mul_le_one ha ha) hb)
  have h8 := abs_le.1 (abs_mul_le_one (abs_mul_le_one ha hb) hb)
  have h9 := abs_le.1 (abs_mul_le_one (abs_mul_le_one hb hb) hb)
  rw [abs_le]
  constructor <;> linarith

/-- **Facts about `κ`** for `d_A ∈ {3, 4}` on `[−1, 1]`. -/
theorem kapFacts107 : KapFacts107 := by
  intro dA hdA
  rcases hdA with rfl | rfl
  · refine ⟨hasDeriv3, ?_, ?_, lip3, ?_⟩
    · intro a ha
      obtain ⟨h1, h2⟩ := abs_le.1 ha
      rw [kap3]
      refine ⟨?_, ?_⟩
      · have : 1 + a + a ^ 2 + a ^ 3 = (1 + a) * (1 + a ^ 2) := by ring
        rw [this]; exact mul_nonneg (by linarith) (by positivity)
      · push_cast; nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) (sub_nonneg.2 h2)]
    · intro a ha
      obtain ⟨h1, h2⟩ := abs_le.1 ha
      rw [kap3]; push_cast
      nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 h2)]
    · intro a _
      rw [kap'3]; simpa [cKap] using cert3 a
  · refine ⟨hasDeriv4, ?_, ?_, lip4, ?_⟩
    · intro a ha
      obtain ⟨h1, h2⟩ := abs_le.1 ha
      rw [kap4]
      refine ⟨?_, ?_⟩
      · nlinarith [sq_nonneg (a ^ 2 + a / 2), sq_nonneg (a + 2 / 3)]
      · push_cast
        nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) (sub_nonneg.2 h2),
          mul_nonneg (sq_nonneg a) (sub_nonneg.2 (abs_le.1 (abs_mul_le_one ha ha)).2)]
    · intro a ha
      obtain ⟨h1, h2⟩ := abs_le.1 ha
      rw [kap4]; push_cast
      nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 h2),
        mul_nonneg (sq_nonneg a) (sub_nonneg.2 (abs_le.1 (abs_mul_le_one ha ha)).2)]
    · intro a _
      rw [kap'4]; simpa [cKap] using cert4 a

end BstLean.Part107
