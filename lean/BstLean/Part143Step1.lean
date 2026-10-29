import BstLean.Part143Core
import BstLean.Part143Big
import BstLean.Part143HidK

/-!
# Part 143, first step: levers 1, 2 and 4 with the kernel constants of Part 142

Role: `delegations/statements/p143-spec.md`. The program is `arithProg141 k n` (Part 141),
unchanged. This file uses: the factor 2 of the spread (`Part143Spread`), the sharper probability
of the fixed event `good136 n` (`Part143HidK`: `0.000775` in the place of `0.002`), and the
constants of Part 142 at `n ≥ 16384` (`Part143Big`). The kernel bound is `eD142` of Part 142
(triangle inequality over the links).

* `goodHat_union`: `Pr(goodHat fails) ≤ Pr(good136 fails) + Pr(goodDist fails) + Pr(goodT fails)`.
* `goodHat_compl16`: `Pr(goodHat n fails) ≤ 0.000775 + 29.93/n` for `n ≥ 16384`.
* **`arithProgSucceeds143a`**: `Pr(ok) ≥ 1 − (0.000775 + 204.4/n + 99.8/k)`, every `n ≥ 16384`.
* **`arithProg143a_99`**: level `99/100` for every `n ≥ 22266`, `k ≥ 100n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-- The union bound for the three events of `goodHat n`. -/
lemma goodHat_union (n : ℕ) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤
      (hidGauss (2 * n) (mW n)).real (good136 n)ᶜ +
        ((hidGauss (2 * n) (mW n)).real (goodDist n (3 / 4))ᶜ +
          (hidGauss (2 * n) (mW n)).real (goodT n (1 / 400000))ᶜ) := by
  have hsub : (goodHat n)ᶜ ⊆ (good136 n)ᶜ ∪ ((goodDist n (3 / 4))ᶜ ∪ (goodT n (1 / 400000))ᶜ) := by
    intro θ hθ
    unfold goodHat at hθ
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    rcases hθ with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  exact add_le_add le_rfl (measureReal_union_le _ _)

/-- `Pr(goodHat n fails) ≤ 0.000775 + 29.93/n` for `n ≥ 16384`. -/
lemma goodHat_compl16 {n : ℕ} (hn : 16384 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ 775 / 1000000 + 2993 / 100 / (n : ℝ) := by
  have h1 := good136_prob143 (n := n) (by omega)
  have h2 := goodHatExtra16 hn
  have h := goodHat_union n
  unfold P143 at h1
  linarith

/-- **First step.** For every `n ≥ 16384`, `k ≥ 1`:
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.000775 + 204.4/n + 99.8/k)` (`θ = 0.18`). -/
theorem arithProgSucceeds143a {n : ℕ} (hn : 16384 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (775 / 1000000 + 2044 / 10 / (n : ℝ) + 998 / 10 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := progDist143 hn4 hk (θ := 18 / 100) (by norm_num) (by norm_num) (goodHat_compl16 hn)
    (XA142_nonneg hn4 (1 / 20) (η := 1 / 30) (by norm_num) (η' := 1 / 40) (by norm_num))
    (XA142_16 hn)
    (fun s hs => errSampleTailA142 hn4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hk hs)
    (eD142_nonneg hn4) (eD142_16 hn) (kernDist142 hn4)
  refine le_trans ?_ h
  have e1 : (2 / 10000 + 4 * (5011 / 10000) / (18 / 100 * (222757 / 1000000 : ℝ)) +
      2 * (14406 / 10000 : ℝ) ^ 2 / ((1 - 18 / 100) * (222757 / 1000000)) ^ 2) / (n : ℝ) ≤
      17447 / 100 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (18 / 100 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 998 / 10 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : (2044 : ℝ) / 10 / n = 2993 / 100 / n + 17447 / 100 / n := by ring
  rw [e3]
  linarith

/-- **First step, level `99/100`**: for every `n ≥ 22266` and `k ≥ 100n`. -/
theorem arithProg143a_99 {n : ℕ} (hn : 22266 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx : (22266 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hkR : (100 : ℝ) * n ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : 1 ≤ k := by omega
  have h := arithProgSucceeds143a (n := n) (by omega) hk1
  refine le_trans ?_ h
  have a1 : (2044 : ℝ) / 10 / n ≤ 2044 / 10 / 22266 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have a2 : (998 : ℝ) / 10 / k ≤ 998 / 10 / (100 * 22266) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  norm_num at a1 a2 ⊢
  linarith

end BstLean.Part143

open BstLean.Part143 in
#print axioms goodHat_compl16
open BstLean.Part143 in
#print axioms arithProgSucceeds143a
open BstLean.Part143 in
#print axioms arithProg143a_99
