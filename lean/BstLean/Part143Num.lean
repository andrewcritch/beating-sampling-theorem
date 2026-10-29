import BstLean.Part143Var2
import BstLean.Part143Big

/-!
# Part 143: the constant of the error tail for `n ≥ 16384`

`XAL L143 n (1/20) (1/28) (1/36) ≤ 0.3815/n` for `n ≥ 16384`: the stand-in factor `1.37`
(`Part143Lam`), `Vb n ≤ 0.2451`, `EHH n (1/20) ≤ 1.1564·10⁻⁴/n` (`Part143Big`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part140 BstLean.Part141
open BstLean.Part142

lemma VbL143_16 {n : ℕ} (hn : 16384 ≤ n) : VbL L143 n ≤ 2451 / 10000 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := Vb16 hn
  have e : VbL L143 n = Vb n - 46 / 100 / (n : ℝ) := by
    unfold VbL Vb L143
    ring
  have : (0 : ℝ) ≤ 46 / 100 / (n : ℝ) := by positivity
  linarith

lemma XAL143_16 {n : ℕ} (hn : 16384 ≤ n) :
    XAL L143 n (1 / 20) (1 / 28) (1 / 36) ≤ 3815 / 10000 * (1 / (n : ℝ)) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hy : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hV := VbL143_16 hn
  have hE := EHH16 hn
  have hP := pertA16 (n := n) (by omega)
  have e1 : (11564 : ℝ) / 100000000 / n = 11564 / 100000000 * (1 / n) := by ring
  have e2 : (27501 : ℝ) / 100000000 / n = 27501 / 100000000 * (1 / n) := by ring
  rw [e1] at hE
  rw [e2] at hP
  unfold XAL
  rw [hP]
  have e3 : L143 / (n : ℝ) = 137 / 100 * (1 / (n : ℝ)) := by unfold L143; ring
  rw [e3]
  have a1 : 137 / 100 * (1 / (n : ℝ)) * VbL L143 n ≤ 137 / 100 * (1 / (n : ℝ)) * (2451 / 10000) :=
    mul_le_mul_of_nonneg_left hV (by positivity)
  nlinarith

end BstLean.Part143

open BstLean.Part143 in
#print axioms XAL143_16
