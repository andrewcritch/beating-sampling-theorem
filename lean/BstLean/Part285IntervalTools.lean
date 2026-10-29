import BstLean.Part280Interface
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! Kernel-checked interval arithmetic for Part 285.

Mathlib's dyadic family currently covers addition and multiplication. The rules below
add powers and reciprocals of positive bounded intervals, with ordinary Lean proofs. -/
namespace Inclusion.IntervalDyadicReal

def powInterval (I : Interval Dyadic) : ℕ → Interval Dyadic
  | 0 => Interval.singleton ((1 : ℕ) : Dyadic)
  | k + 1 => (powInterval I k).mul I

@[inclusion_op interval_dyadic_real]
theorem powInterval_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (k : ℕ) :
    x ^ k ∈ powInterval I k := by
  induction k with
  | zero => simpa only [powInterval, pow_zero] using (Inclusion.IntervalDyadicReal.ofNat_mem 1)
  | succ k ih => simpa [powInterval, pow_succ] using mul_mem ih hx

def inverseInterval (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  match I.lb, I.ub with
  | some l, some u =>
    if 0 < l.toRat then
      ⟨(rat u.toRat⁻¹ prec).lb, (rat l.toRat⁻¹ prec).ub⟩
    else Interval.univ Dyadic
  | _, _ => Interval.univ Dyadic

@[inclusion_op interval_dyadic_real]
theorem inverseInterval_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    x⁻¹ ∈ inverseInterval I prec := by
  rcases I with ⟨l, u⟩
  cases l with
  | bot => exact Interval.mem_map_univ Dyadic.toReal _
  | coe l =>
    cases u with
    | top => exact Interval.mem_map_univ Dyadic.toReal _
    | coe u =>
      change x⁻¹ ∈ if 0 < l.toRat then
        (⟨(rat u.toRat⁻¹ prec).lb, (rat l.toRat⁻¹ prec).ub⟩ : Interval Dyadic)
        else Interval.univ Dyadic
      split_ifs with hp
      · have hl : l.toReal ≤ x := Interval.map_lb_le Dyadic.toReal hx
        have hu : x ≤ u.toReal := Interval.le_map_ub Dyadic.toReal hx
        have hl0 : 0 < l.toReal := by
          simpa [Dyadic.toReal] using (Rat.cast_pos.mpr hp : (0 : ℝ) < (l.toRat : ℝ))
        have hx0 : 0 < x := hl0.trans_le hl
        have hL : u.toReal⁻¹ ∈ rat u.toRat⁻¹ prec := by
          simpa [Dyadic.toReal] using ratCast_mem u.toRat⁻¹ prec
        have hU : l.toReal⁻¹ ∈ rat l.toRat⁻¹ prec := by
          simpa [Dyadic.toReal] using ratCast_mem l.toRat⁻¹ prec
        change ((rat u.toRat⁻¹ prec).map Dyadic.toReal).lb ≤ (x⁻¹ : ℝ) ∧
          (x⁻¹ : ℝ) ≤ ((rat l.toRat⁻¹ prec).map Dyadic.toReal).ub
        exact ⟨hL.1.trans (WithBot.coe_le_coe.mpr (inv_anti₀ hx0 hu)),
          (WithTop.coe_le_coe.mpr (inv_anti₀ hl0 hl)).trans hU.2⟩
      · exact Interval.mem_map_univ Dyadic.toReal _

@[inclusion_op interval_dyadic_real]
theorem divisionInterval_mem {x y : ℝ} {I J : Interval Dyadic}
    (hx : x ∈ I) (hy : y ∈ J) (prec : ℕ) :
    x / y ∈ I.mul (inverseInterval J prec) := by
  simpa only [div_eq_mul_inv] using mul_mem hx (inverseInterval_mem hy prec)

end Inclusion.IntervalDyadicReal

macro "interval_num" : tactic => do
  let n := Lean.mkIdent `n
  let prec := Lean.mkIdent `prec
  `(tactic| first
    | (generalize ($n : ℝ) = intervalDimension at *
       dyadic_interval [$prec := 512])
    | dyadic_interval [$prec := 512])

namespace BstLean.Part285.Interval
open Real

theorem rational_probe {n : ℕ} (hn : 12000 ≤ n) (hn' : n ≤ 12024) :
    (2 : ℝ) / (n : ℝ) ^ 2 ≤ (118 / 10 ^ 6 : ℝ) ^ 2 := by
  have hl : (12000 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (n : ℝ) ≤ 12024 := by exact_mod_cast hn'
  interval_num

end BstLean.Part285.Interval
