import BstLean.Part197Expr
import Mathlib.Analysis.Real.Pi.Bounds

/-! Part 197: cell enclosures for the P04 and TG scalar definitions. -/
namespace BstLean.Part197

open BstLean.Part193
open MeasureTheory Set

theorem pi_mem : (⟨314159265358979323846 / 10 ^ 20,
    314159265358979323847 / 10 ^ 20, by norm_num⟩ : Interval).Mem Real.pi := by
  constructor
  · change (314159265358979323846 / 10 ^ 20 : ℝ) ≤ Real.pi
    convert Real.pi_gt_d20.le using 1 <;> norm_num
  · change Real.pi ≤ (314159265358979323847 / 10 ^ 20 : ℝ)
    convert Real.pi_lt_d20.le using 1 <;> norm_num

theorem sqrt_pi_bounds :
    (17724538509055160 / 10 ^ 16 : ℝ) ≤ Real.sqrt Real.pi ∧
      Real.sqrt Real.pi ≤ 17724538509055161 / 10 ^ 16 := by
  apply Interval.sqrt_bounds (by norm_num) (by norm_num)
  · exact (by norm_num : (17724538509055160 / 10 ^ 16 : ℝ) ^ 2 ≤
      314159265358979323846 / 10 ^ 20).trans pi_mem.1
  · exact pi_mem.2.trans (by norm_num : (314159265358979323847 / 10 ^ 20 : ℝ) ≤
      (17724538509055161 / 10 ^ 16 : ℝ) ^ 2)

theorem exp_cell_mem {x : ℝ} {I J : Interval} (hx : I.Mem x)
    (hl : J.lo ≤ Real.exp I.lo) (hu : Real.exp I.hi ≤ J.hi) : J.Mem (Real.exp x) :=
  ⟨hl.trans (Real.exp_le_exp.mpr hx.1), (Real.exp_le_exp.mpr hx.2).trans hu⟩

theorem log_cell_mem {x : ℝ} {I J : Interval} (hx : I.Mem x) (hI : 0 < I.lo)
    (hl : J.lo ≤ Real.log I.lo) (hu : Real.log I.hi ≤ J.hi) : J.Mem (Real.log x) := by
  have hp : 0 < x := hI.trans_le hx.1
  exact ⟨hl.trans (Real.log_le_log hI hx.1), (Real.log_le_log hp hx.2).trans hu⟩

theorem kernel_cell_mem {c : ℝ} {I J : Interval} (hc : I.Mem c)
    (hlI : -1 ≤ I.lo) (huI : I.hi ≤ 1)
    (hl : J.lo ≤ BstLean.Part130.kappa I.lo)
    (hu : BstLean.Part130.kappa I.hi ≤ J.hi) : J.Mem (BstLean.Part130.kappa c) := by
  have hcdom : c ∈ Icc (-1 : ℝ) 1 := ⟨hlI.trans hc.1, hc.2.trans huI⟩
  exact ⟨hl.trans (BstLean.Part130.kappa_monotoneOn ⟨hlI, I.ordered.trans huI⟩ hcdom hc.1),
    (BstLean.Part130.kappa_monotoneOn hcdom ⟨hlI.trans I.ordered, huI⟩ hc.2).trans hu⟩

theorem kernel_slope_monotone : Monotone kernelSlope := by
  intro c d hcd
  exact div_le_div_of_nonneg_right (sub_le_sub_left (Real.arccos_le_arccos hcd) _) Real.pi_pos.le

theorem kernel_slope_cell_mem {c : ℝ} {I J : Interval} (hc : I.Mem c)
    (hl : J.lo ≤ kernelSlope I.lo) (hu : kernelSlope I.hi ≤ J.hi) : J.Mem (kernelSlope c) :=
  ⟨hl.trans (kernel_slope_monotone hc.1), (kernel_slope_monotone hc.2).trans hu⟩

theorem erfc_antitoneOn : AntitoneOn erfc (Ici 0) := by
  intro x hx y hy hxy
  rw [erfc_eq_tail hx, erfc_eq_tail hy]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hi : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  exact setIntegral_mono_set hi.integrableOn (ae_of_all _ (fun t => (Real.exp_pos _).le))
    (ae_of_all _ (fun t ht => lt_of_le_of_lt hxy ht))

theorem erfc_cell_mem {z : ℝ} {I J : Interval} (hz : I.Mem z) (hI : 0 ≤ I.lo)
    (hl : J.lo ≤ erfc I.hi) (hu : erfc I.lo ≤ J.hi) : J.Mem (erfc z) := by
  have hzp : 0 ≤ z := hI.trans hz.1
  exact ⟨hl.trans (erfc_antitoneOn hzp (hI.trans I.ordered) hz.2),
    (erfc_antitoneOn hI hzp hz.1).trans hu⟩

noncomputable def p04M (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2) / Real.pi - c * kernelSlope c
noncomputable def p04V (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2) * kernelSlope c
noncomputable def p04PairTail (v : ℝ) : ℝ := erfc (v / Real.sqrt 2)
noncomputable def p04OuterTail (v z : ℝ) : ℝ := p04PairTail v + 2 * Real.exp (-z)

theorem p04M_mem {c : ℝ} {C R D P : Interval} (hc : C.Mem c)
    (hr : R.Mem (Real.sqrt (1 - c ^ 2))) (hd : D.Mem (kernelSlope c))
    (hp : P.Mem Real.pi) (hpos : 0 < P.lo) :
    (Interval.sub (Interval.divPos R P hpos) (Interval.mul C D)).Mem (p04M c) :=
  Interval.mem_sub (Interval.mem_divPos hr hp hpos) (Interval.mem_mul hc hd)

theorem p04V_mem {c : ℝ} {R D : Interval}
    (hr : R.Mem (Real.sqrt (1 - c ^ 2))) (hd : D.Mem (kernelSlope c)) :
    (Interval.mul R D).Mem (p04V c) := Interval.mem_mul hr hd

theorem p04_outer_tail_mem {v z : ℝ} {P E : Interval}
    (hp : P.Mem (erfc (v / Real.sqrt 2))) (he : E.Mem (Real.exp (-z))) :
    (Interval.add P (Interval.mul (Interval.point 2) E)).Mem (p04OuterTail v z) :=
  Interval.mem_add hp (Interval.mem_mul (Interval.mem_point 2) he)

theorem tangent_constant_mem {x c : ℝ} {X C L : Interval}
    (hx : X.Mem x) (hc : C.Mem c) (hl : L.Mem (Real.log (1 + x)))
    (hden : 0 < (Interval.add (Interval.point 1) X).lo) (hC : 0 < C.lo) :
    (Interval.divPos
      (Interval.sub L (Interval.divPos X (Interval.add (Interval.point 1) X) hden))
      C hC).Mem (tangentConstant x c) := by
  exact Interval.mem_divPos
    (Interval.mem_sub hl (Interval.mem_divPos hx
      (Interval.mem_add (Interval.mem_point 1) hx) hden)) hc hC

noncomputable def tgY (c tau : ℝ) : ℝ := Real.exp (c * tau) - 1
noncomputable def tgTprime (c tau v : ℝ) : ℝ := tgY c tau / (c * (1 + v * tgY c tau))
noncomputable def tgK0 (c tau v : ℝ) : ℝ := tangentConstant (v * tgY c tau) c
noncomputable def tgK1 (L u : ℝ) : ℝ := tangentConstant u L
noncomputable def tgX (L T alpha : ℝ) : ℝ := Real.exp (L * T * alpha) - 1

theorem tgY_mem {c tau : ℝ} {E : Interval} (he : E.Mem (Real.exp (c * tau))) :
    (Interval.sub E (Interval.point 1)).Mem (tgY c tau) :=
  Interval.mem_sub he (Interval.mem_point 1)

theorem tgX_mem {L T alpha : ℝ} {E : Interval}
    (he : E.Mem (Real.exp (L * T * alpha))) :
    (Interval.sub E (Interval.point 1)).Mem (tgX L T alpha) :=
  Interval.mem_sub he (Interval.mem_point 1)

theorem tg_constants_nonneg {c L tau v u : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hv : 0 < 1 + v * tgY c tau) (hu : -1 < u) :
    0 ≤ tgK0 c tau v ∧ 0 ≤ tgK1 L u := by
  exact ⟨tangent_constant_nonneg (tg_world_domain hv).1 hc, tangent_constant_nonneg hu hL⟩

theorem tgTprime_mem {c tau v : ℝ} {C V Y : Interval} (hc : C.Mem c) (hv : V.Mem v)
    (hy : Y.Mem (tgY c tau))
    (hden : 0 < (Interval.mul C (Interval.add (Interval.point 1) (Interval.mul V Y))).lo) :
    (Interval.divPos Y (Interval.mul C (Interval.add (Interval.point 1) (Interval.mul V Y)))
      hden).Mem (tgTprime c tau v) :=
  Interval.mem_divPos hy (Interval.mem_mul hc
    (Interval.mem_add (Interval.mem_point 1) (Interval.mem_mul hv hy))) hden

theorem tg_world_domain_from_cell {c tau v : ℝ} {V Y : Interval} (hv : V.Mem v)
    (hy : Y.Mem (tgY c tau))
    (hden : 0 < (Interval.add (Interval.point 1) (Interval.mul V Y)).lo) :
    0 < 1 + v * tgY c tau ∧ -1 < v * tgY c tau := by
  have hp := hden.trans_le
    (Interval.mem_add (Interval.mem_point 1) (Interval.mem_mul hv hy)).1
  exact ⟨hp, (tg_world_domain hp).1⟩

theorem tg_agent_domain_from_cell {u : ℝ} {U : Interval} (hu : U.Mem u) (hU : -1 < U.lo) :
    0 < 1 + u := (tg_agent_domain (hU.trans_le hu.1)).1

end BstLean.Part197
