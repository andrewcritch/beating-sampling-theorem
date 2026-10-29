import BstLean.Part140Sharp

/-!
# Part 140: the two-stage form (the quantifier order of Option A) for the computed centre

Role: `delegations/statements/p140-spec.md`, item 3 (more); `MM.md`, Option A:
"for most `(W, F)` there is `g_{W,F}` such that for most `A`: `|g_{W,F}(A) − B| ≤ ε·sd`".
Here `g_{W,F}(A) = gHat W A F` (computed centre, scalar from first-pass quantities). The step
from the joint probability is Markov's inequality (`twoStage139` of Part 139).

* **`optAHat140`**: for `n ≥ 4096` and `q > 0`:
  `Pr_{W,F}(Pr_A(|ĝ − B| ≤ sd/2) > 1 − q) ≥ 1 − (0.002 + 2022/n)/q`.
* **`optAHat140_explicit`**: the same for the explicit scale, with `0.002 + 70/n + 9/(ε²n)`;
  `optAHat140_explicit_frontier`: levels `(90/100, 90/100)` at `ε = 1/2` for `n ≥ 16384`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part136
open BstLean.Part138
open BstLean.Part139 hiding BM

lemma measurableSet_okHat {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (okHat n) := by
  have hN : 1 ≤ 2 * n := by omega
  exact measurableSet_le (((measurable_gHat hN).sub (measurable_Bn hN)).abs)
    ((measurable_sdn hN).div_const 2)

/-- **Option A form, relative to the realized spread.** For `n ≥ 4096` and `q > 0`:
`Pr_{W,F}(Pr_A(|ĝ − B| ≤ sd/2) > 1 − q) ≥ 1 − (0.002 + 2022/n)/q`. -/
theorem optAHat140 {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq : 0 < q) :
    1 - (2 / 1000 + 2022 / (n : ℝ)) / q ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 1 - q < (mlpGauss n (mA n) n).real
        {A | |gHat x.1 A x.2 - Bn x.1 A x.2| ≤ sdn x.1 A x.2 / 2}} :=
  twoStage139 (measurableSet_okHat (by omega)) hq (hatSucceeds140 hn)

/-- **Option A form, relative to the explicit scale.** For `n ≥ 4096`, `ε > 0`, `q > 0`:
`Pr_{W,F}(Pr_A(|ĝ − B| ≤ ε·√(S(1 − Q))) > 1 − q) ≥ 1 − (0.002 + 70/n + 9/(ε²n))/q`. -/
theorem optAHat140_explicit {n : ℕ} (hn : 4096 ≤ n) {ε : ℝ} (hε : 0 < ε) {q : ℝ} (hq : 0 < q) :
    1 - (2 / 1000 + 70 / (n : ℝ) + 9 / (ε ^ 2 * (n : ℝ))) / q ≤
      (lawWF (2 * n) (mW n) n (mF n)).real
        {x | 1 - q < (mlpGauss n (mA n) n).real
          {A | |gHat x.1 A x.2 - Bn x.1 A x.2| ≤ ε * scale139 n}} := by
  have hN : 1 ≤ 2 * n := by omega
  have hE : MeasurableSet {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 | |gHat t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} :=
    measurableSet_le (((measurable_gHat hN).sub (measurable_Bn hN)).abs) measurable_const
  exact twoStage139 hE hq (hatExplicit140 hn hε)

/-- Levels `(90/100, 90/100)` at tolerance `1/2` of the explicit scale, for `n ≥ 16384`. -/
theorem optAHat140_explicit_frontier {n : ℕ} (hn : 16384 ≤ n) :
    90 / 100 ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 90 / 100 < (mlpGauss n (mA n) n).real
        {A | |gHat x.1 A x.2 - Bn x.1 A x.2| ≤ 1 / 2 * scale139 n}} := by
  have h := optAHat140_explicit (n := n) (by omega) (ε := 1 / 2) (by norm_num)
    (q := 10 / 100) (by norm_num)
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h9 : 9 / ((1 / 2 : ℝ) ^ 2 * (n : ℝ)) ≤ 22 / 10000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h7 : 70 / (n : ℝ) ≤ 43 / 10000 := by
    rw [div_le_iff₀ hx0]
    nlinarith
  have e : (1 : ℝ) - 10 / 100 = 90 / 100 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  have : (2 / 1000 + 70 / (n : ℝ) + 9 / ((1 / 2 : ℝ) ^ 2 * (n : ℝ))) / (10 / 100) ≤
      10 / 100 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  linarith

end BstLean.Part140

open BstLean.Part140 in
#print axioms optAHat140
open BstLean.Part140 in
#print axioms optAHat140_explicit
open BstLean.Part140 in
#print axioms optAHat140_explicit_frontier
