import BstLean.Part145G5
import BstLean.Part135Num

/-!
# Part 149, the window of the centre and of the scalar of the stand-in inputs

Do not use `sorry`, `native_decide` or `axiom`.

Notation: `γ = 2/(2n)`, `t = 2/(mW n)`, `B' = t|b̃|²` (`b̃ = bA n θ`, the arithmetic centre),
`τ̃₀ = tauA n θ` (the arithmetic scalar).

* `normSq_tri`: `|a|² ≤ (701/700)|b|² + 701|a − b|²`.
* `centreA_win`: on `goodAG G`: `0.4786·γ ≤ B' ≤ 0.5095·γ`.
* `tauA_sq_le`: on `goodAG G`: `τ̃₀² ≤ 0.5573·γ`.
* **`winA`**: on `goodAG G`: `B' > 0`, `τ̃₀ > 0` and `0.462 ≤ B'/(B' + τ̃₀²) ≤ 0.527`.
* `kk_win_sharp`: `0.6662 ≤ κ(κ(q)) ≤ 0.6969` for `0.462 ≤ q ≤ 0.527`.
* **`kk_win`**: `0.664 ≤ κ(κ(q)) ≤ 0.708` for `0.462 ≤ q ≤ 0.527`.
-/

namespace BstLean.Part149

open BstLean.Part143 BstLean.Part145
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142
open BstLean.Part135 (kappa_le_of_le9)

/-- `|a|² ≤ (701/700)|b|² + 701|a − b|²` (the triangle inequality and
`2|b||a − b| ≤ |b|²/700 + 700|a − b|²`). -/
lemma normSq_tri {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq a ≤ 701 / 700 * normSq b + 701 * normSq (a - b) := by
  have h := nrm_add_le' b (a - b)
  have e : b + (a - b) = a := by abel
  rw [e] at h
  have ha := nrm_sq a
  have hb := nrm_sq b
  have hd := nrm_sq (a - b)
  have ha0 := nrm_nonneg a
  have hb0 := nrm_nonneg b
  have hd0 := nrm_nonneg (a - b)
  have h2 : nrm a ^ 2 ≤ (nrm b + nrm (a - b)) ^ 2 := pow_le_pow_left₀ ha0 h 2
  nlinarith [sq_nonneg (nrm b - 700 * nrm (a - b))]

section good

variable {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 4096 ≤ n) {θ :
    HidParam (2 * n) (mW n)} (hθ : θ ∈ goodAG G)

include hG hn hθ

/-- On `goodAG G`: `0.4786·γ ≤ t|b̃|² ≤ 0.5095·γ`. -/
theorem centreA_win :
    2 / ((2 * n : ℕ) : ℝ) * (4786 / 10000) ≤ 2 / (mW n : ℝ) * normSq (bA n θ) ∧
    2 / (mW n : ℝ) * normSq (bA n θ) ≤ 2 / ((2 * n : ℕ) : ℝ) * (5095 / 10000) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
    linarith
  have ht : (0 : ℝ) < 2 / (mW n : ℝ) := by positivity
  obtain ⟨hB1, hB2⟩ := BhG0_hat hG hθ.1
  have hd : Part141.dA n θ ≤ 2 / ((2 * n : ℕ) : ℝ) / 1000000 := hθ.2
  unfold Bh at hB1 hB2
  unfold Part141.dA at hd
  have h1 := mul_le_mul_of_nonneg_left (normSq_tri (bA n θ) (bhat θ)) ht.le
  have h2 := mul_le_mul_of_nonneg_left (normSq_tri (bhat θ) (bA n θ)) ht.le
  rw [normSq_sub_comm (bhat θ) (bA n θ)] at h2
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ)
  set t : ℝ := 2 / (mW n : ℝ)
  set X := normSq (bA n θ)
  set Y := normSq (bhat θ)
  set Z := normSq (bA n θ - bhat θ)
  constructor <;> nlinarith

/-- On `goodAG G`: `τ̃₀² ≤ 0.5573·γ`. -/
theorem tauA_sq_le : tauA n θ ^ 2 ≤ 2 / ((2 * n : ℕ) : ℝ) * (5573 / 10000) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  have hqR : (40960000 : ℝ) ≤ qA n := by rw [qA_cast]; linarith
  obtain ⟨-, -, h3⟩ := scalarAG0 hG hn hθ
  obtain ⟨-, hB2⟩ := BhG0_hat hG hθ.1
  have hBpos := BhG0_pos hG hn hθ.1
  obtain ⟨hw1, hw2⟩ := w0HG0_window hG hn hθ.1
  have hw0 := wLowH_pos
  have hτ := tauHatG0_sq hG hn hθ.1
  have hd : Part141.dA n θ ≤ 2 / ((2 * n : ℕ) : ℝ) / 1000000 := hθ.2
  have hd0 := Part141.dA_nonneg n θ
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ)
  have hdγ : Part141.dA n θ / γ ≤ 1 / 1000000 := by
    rw [div_le_iff₀ hγ]; linarith
  have hiq : 1 / (qA n : ℝ) ≤ 1 / 40960000 := one_div_le_one_div_of_le (by norm_num) hqR
  have hiq0 : (0 : ℝ) ≤ 1 / (qA n : ℝ) := by positivity
  have hiq2 : (1 / (qA n : ℝ)) ^ 2 ≤ (1 / 40960000 : ℝ) ^ 2 := pow_le_pow_left₀ hiq0 hiq 2
  have hbr : 42 * (Part141.dA n θ / γ) + 3 * (1 / (qA n : ℝ)) ^ 2 ≤ (649 / 100000 : ℝ) ^ 2 := by
    norm_num at hiq2 ⊢
    linarith
  have h4 : (tauA n θ ^ 2 - tauHat (2 * n) (mW n) θ ^ 2) ^ 2 ≤ (γ * (649 / 100000)) ^ 2 := by
    rw [mul_pow]
    exact h3.trans (mul_le_mul_of_nonneg_left hbr (by positivity))
  have h5 := (abs_le_of_sq_le_sq' h4 (by positivity)).2
  have h6 : Bh (2 * n) (mW n) θ * w0H (2 * n) (mW n) θ ≤
      γ * (508 / 1000) * (1 / (4798 / 10000) - 1) :=
    mul_le_mul hB2 hw2 (by linarith) (by positivity)
  rw [hτ] at h5
  have h7 : γ * (508 / 1000) * (1 / (4798 / 10000) - 1) + γ * (649 / 100000) ≤
      γ * (5573 / 10000) := by
    have e : γ * (508 / 1000) * (1 / (4798 / 10000) - 1) + γ * (649 / 100000) =
        γ * ((508 / 1000) * (1 / (4798 / 10000) - 1) + 649 / 100000) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by norm_num) hγ.le
  linarith

/-- **The window of the centre and of the scalar of the stand-in inputs.** On `goodAG G`, with
`B' = t|b̃|²`: `B' > 0`, `τ̃₀ > 0` and `0.462 ≤ B'/(B' + τ̃₀²) ≤ 0.527`. -/
theorem winA :
    0 < 2 / (mW n : ℝ) * normSq (bA n θ) ∧ 0 < tauA n θ ∧
    462 / 1000 ≤ 2 / (mW n : ℝ) * normSq (bA n θ) /
        (2 / (mW n : ℝ) * normSq (bA n θ) + tauA n θ ^ 2) ∧
    2 / (mW n : ℝ) * normSq (bA n θ) /
        (2 / (mW n : ℝ) * normSq (bA n θ) + tauA n θ ^ 2) ≤ 527 / 1000 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  obtain ⟨hB1, hB2⟩ := centreA_win hG hn hθ
  have hT2 := tauA_sq_le hG hn hθ
  have hT1 := (scalarAG0 hG hn hθ).2.1
  have hτ := tauAG0_pos hG hn hθ
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ)
  set B : ℝ := 2 / (mW n : ℝ) * normSq (bA n θ)
  set T : ℝ := tauA n θ ^ 2
  have hB : 0 < B := by nlinarith
  have hT : 0 < T := by positivity
  refine ⟨hB, hτ, ?_, ?_⟩
  · rw [le_div_iff₀ (by linarith)]
    nlinarith
  · rw [div_le_iff₀ (by linarith)]
    nlinarith

end good

/-- `0.6662 ≤ κ(κ(q)) ≤ 0.6969` for `0.462 ≤ q ≤ 0.527`. -/
theorem kk_win_sharp {q : ℝ} (h1 : 462 / 1000 ≤ q) (h2 : q ≤ 527 / 1000) :
    6662 / 10000 ≤ kappa (kappa q) ∧ kappa (kappa q) ≤ 6969 / 10000 := by
  have hl : (58392 / 100000 : ℝ) ≤ kappa q :=
    kappa_ge_of_le7 (a := 462 / 1000) (by norm_num) h1 (by linarith) (by norm_num)
  have hu : kappa q ≤ (62714 / 100000 : ℝ) :=
    kappa_le_of_le9 (a := 527 / 1000) (by linarith) h2 (by norm_num) (by norm_num)
  have h1' : kappa q ≤ 1 := by linarith
  exact ⟨kappa_ge_of_le7 (a := 58392 / 100000) (by norm_num) hl h1' (by norm_num),
    kappa_le_of_le9 (a := 62714 / 100000) (by linarith) hu (by norm_num) (by norm_num)⟩

/-- **Bounds of `κ∘κ` on the window.** `0.664 ≤ κ(κ(q)) ≤ 0.708` for `0.462 ≤ q ≤ 0.527`. -/
theorem kk_win {q : ℝ} (h1 : 462 / 1000 ≤ q) (h2 : q ≤ 527 / 1000) :
    664 / 1000 ≤ kappa (kappa q) ∧ kappa (kappa q) ≤ 708 / 1000 := by
  obtain ⟨a, b⟩ := kk_win_sharp h1 h2
  constructor <;> linarith

end BstLean.Part149

#print axioms BstLean.Part149.winA
#print axioms BstLean.Part149.kk_win
