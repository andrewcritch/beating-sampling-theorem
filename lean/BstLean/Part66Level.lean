import BstLean.Part66Defs
import BstLean.Part66Disc
import BstLean.Part62Interp
import BstLean.Part48Rot
import BstLean.Part48Trig
import BstLean.Part48Var

/-!
# Part 66, Stage A: the weighted-rotation small-ball level

Source: `delegations/answers/omSBL-cx.md`, "Preferred route", the simple level.
Specification: `delegations/statements/p66-spec.md`, Stage A item 1.

Headline: `sb_level_weighted h (1 ≤ h) p (0 < p) : SBLevel h p (tW h p)`,
`tW h p = (p / (2 (2h+1)²))^{2h}`. No fourth-moment constant enters.

Route. `f = P ≥ 0`, `m = E f > 0`, `ε = t m`, `E = {f < ε}`, `N = 2h+1`, `α = 1/(2h)`,
`X_s = rotX s X Y`, `Y_s = rotY s X Y = X_{s+π/2}`.
1. (`weighted_circle`) For `F ≥ 0` trigonometric of degree `≤ h` with `F ≤ S` everywhere,
   `∫_circ 1{F(s) < ε} F(s+π/2) ds ≤ C ε^α S^{1−α}`, `C = 4πN N^α`
   (`Part62Interp.trig_sublevel_explicit` applied at each point `u`, so no maximum is needed).
2. (`Part66Disc.trig_le_disc_sum`) `F_w(u) ≤ S(w) = Σ_{k<N} f(X_{2πk/N})`, and `E S = N m`.
3. Independence and rotation invariance: `∫_w ∫_circ 1{f(X_s)<ε} f(Y_s) = 2π γ(E) m`.
4. Young (`geom_mean_le_arith_mean2_weighted`) in place of Jensen:
   `S^{1−α} ≤ λ^{1−α}((1−α) S/λ + α)` with `λ = N m`. So `2π γ(E) m ≤ C ε^α (N m)^{1−α}
   = 4π N² t^α m`, and `γ(E) ≤ 2N² t^α = p`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part66

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part48 (SBLevel IsTrig circ rotX rotY rot_preserving trig_of_poly gauss_poly_integrable)
open BstLean.Part62 (trig_sublevel_explicit)

/-- **Weighted sublevel bound on the circle.** -/
theorem weighted_circle (h : ℕ) (hh : 1 ≤ h) (F : ℝ → ℝ) (hF : IsTrig h F) (hFc : Continuous F)
    (hF0 : ∀ s, 0 ≤ F s) (ε : ℝ) (hε : 0 < ε) (S : ℝ) (hS : ∀ u, F u ≤ S) :
    ∫⁻ s, {s | F s < ε}.indicator (fun s => ENNReal.ofReal (F (s + Real.pi / 2))) s ∂circ ≤
      ENNReal.ofReal (4 * Real.pi * (2 * h + 1) * (2 * h + 1) ^ ((1 : ℝ) / (2 * h)) *
        ε ^ ((1 : ℝ) / (2 * h)) * S ^ (1 - (1 : ℝ) / (2 * h))) := by
  set α : ℝ := (1 : ℝ) / (2 * h) with hα
  set C : ℝ := 4 * Real.pi * (2 * h + 1) * (2 * h + 1) ^ α with hC
  have hpi := Real.pi_pos
  have hC0 : 0 < C := by positivity
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hα0 : 0 < α := by positivity
  have hα1 : α ≤ 1 := by rw [hα, div_le_one (by positivity)]; linarith
  have hS0 : 0 ≤ S := (hF0 0).trans (hS 0)
  set A := {s | F s < ε} with hAdef
  set B := C * ε ^ α * S ^ (1 - α) with hB
  have hAm : MeasurableSet A := measurableSet_lt hFc.measurable measurable_const
  have key : ∀ u, ENNReal.ofReal (F u) * circ A ≤ ENNReal.ofReal B := by
    intro u
    rcases (hF0 u).eq_or_lt with h0 | h0
    · rw [← h0, ENNReal.ofReal_zero, zero_mul]; exact bot_le
    · have hsub := trig_sublevel_explicit h hh F hF ε u hε (by rw [abs_of_pos h0]; exact h0)
      have hAeq : {s | |F s| < ε} = A := by
        ext s; simp [hAdef, abs_of_nonneg (hF0 s)]
      rw [hAeq, abs_of_pos h0] at hsub
      calc ENNReal.ofReal (F u) * circ A
          ≤ ENNReal.ofReal (F u) * ENNReal.ofReal (C * (ε / F u) ^ α) := by gcongr
        _ = ENNReal.ofReal (F u * (C * (ε / F u) ^ α)) := (ENNReal.ofReal_mul h0.le).symm
        _ ≤ ENNReal.ofReal B := by
          apply ENNReal.ofReal_le_ofReal
          have e1 : F u * (C * (ε / F u) ^ α) = C * ε ^ α * F u ^ (1 - α) := by
            rw [Real.div_rpow hε.le h0.le, Real.rpow_sub h0, Real.rpow_one]
            have : 0 < F u ^ α := Real.rpow_pos_of_pos h0 _
            field_simp
          rw [e1, hB]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0.le (hS u) (by linarith))
            (by positivity)
  rw [lintegral_indicator hAm]
  have hfin : circ A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ A))
    rw [circ, Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  rcases eq_or_ne (circ A) 0 with hA0 | hA0
  · rw [Measure.restrict_eq_zero.mpr hA0, lintegral_zero_measure]; exact bot_le
  · have hmul : (∫⁻ s in A, ENNReal.ofReal (F (s + Real.pi / 2)) ∂circ) * circ A ≤
        ENNReal.ofReal B * circ A := by
      rw [← lintegral_mul_const' _ _ hfin]
      calc ∫⁻ s in A, ENNReal.ofReal (F (s + Real.pi / 2)) * circ A ∂circ
          ≤ ∫⁻ _s in A, ENNReal.ofReal B ∂circ := lintegral_mono fun s => key _
        _ = ENNReal.ofReal B * circ A := by
          rw [lintegral_const, Measure.restrict_apply_univ]
    exact (ENNReal.mul_le_mul_iff_left hA0 hfin).mp hmul

/-- `Y_s = X_{s + π/2}`. -/
lemma rotY_eq {ι : Type*} (s : ℝ) (x y : ι → ℝ) : rotY s x y = rotX (s + Real.pi / 2) x y := by
  funext i; simp [rotX, rotY, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]

/-- `w ↦ X_s(w)` pushes `γ ⊗ γ` to `γ`, in lintegral form. -/
lemma lintegral_rotX {ι : Type} [Fintype ι] (s : ℝ) (g : (ι → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ w, g (rotX s w.1 w.2) ∂((stdGauss ι).prod (stdGauss ι)) = ∫⁻ z, g z ∂stdGauss ι := by
  have h1 := (rot_preserving (ι := ι) s).lintegral_comp (f := fun q => g q.1) (hg.comp measurable_fst)
  simp only at h1
  rw [h1]
  exact (measurePreserving_fst (μ := stdGauss ι) (ν := stdGauss ι)).lintegral_comp hg

/-- **The weighted-rotation small-ball level** (p66-spec Stage A item 1). -/
theorem sb_level_weighted (h : ℕ) (hh : 1 ≤ h) (p : ℝ) (hp : 0 < p) : SBLevel h p (tW h p) := by
  intro ι _ P hdeg hnn
  set f : (ι → ℝ) → ℝ := fun z => MvPolynomial.eval z P with hfdef
  set m := ∫ z, MvPolynomial.eval z P ∂stdGauss ι with hm
  set t := tW h p with ht
  have ht0 : 0 < t := tW_pos h p hp
  have hm0 : 0 ≤ m := integral_nonneg hnn
  rcases hm0.eq_or_lt with hm00 | hmpos
  · have : {z | MvPolynomial.eval z P < t * m} = ∅ := by
      ext z; simp only [← hm00, mul_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_lt]; exact hnn z
    rw [this, measure_empty]; exact bot_le
  have hpi := Real.pi_pos
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  set N : ℝ := 2 * (h : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  set α : ℝ := (1 : ℝ) / (2 * h) with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α ≤ 1 := by rw [hα, div_le_one (by positivity)]; linarith
  set C : ℝ := 4 * Real.pi * N * N ^ α with hC
  set ε := t * m with hε
  have hε0 : 0 < ε := mul_pos ht0 hmpos
  set lam := N * m with hlam
  have hlam0 : 0 < lam := mul_pos hN0 hmpos
  set K0 := C * ε ^ α * lam ^ (1 - α) with hK0
  have hK00 : 0 < K0 := by positivity
  set μ2 := (stdGauss ι).prod (stdGauss ι) with hμ2
  have hfc : Continuous f := MvPolynomial.continuous_eval P
  set E := {z | f z < ε} with hEdef
  have hEm : MeasurableSet E := measurableSet_lt hfc.measurable measurable_const
  set H : (ι → ℝ) × (ι → ℝ) → ℝ≥0∞ :=
    fun q => E.indicator (fun _ => (1 : ℝ≥0∞)) q.1 * ENNReal.ofReal (f q.2) with hHdef
  have hHm : Measurable H :=
    ((measurable_const.indicator hEm).comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp (hfc.measurable.comp measurable_snd))
  set G : (ι → ℝ) × (ι → ℝ) → ℝ → ℝ≥0∞ :=
    fun w s => H (rotX s w.1 w.2, rotY s w.1 w.2) with hGdef
  have hGm : Measurable (Function.uncurry G) := by
    refine hHm.comp (Continuous.measurable ?_)
    unfold rotX rotY; fun_prop
  have : SFinite circ := by unfold circ; infer_instance
  -- the lower side: `2π γ(E) m`
  have hfi : ENNReal.ofReal m = ∫⁻ z, ENNReal.ofReal (f z) ∂stdGauss ι :=
    ofReal_integral_eq_lintegral_ofReal (gauss_poly_integrable P) (ae_of_all _ hnn)
  have hconst : ∀ s, ∫⁻ w, G w s ∂μ2 = stdGauss ι E * ENNReal.ofReal m := by
    intro s
    have h1 := (rot_preserving (ι := ι) s).lintegral_comp hHm
    show ∫⁻ w, H (rotX s w.1 w.2, rotY s w.1 w.2) ∂μ2 = _
    refine h1.trans ?_
    rw [hHdef]
    beta_reduce
    rw [lintegral_prod_mul (f := E.indicator (fun _ => (1 : ℝ≥0∞)))
      (g := fun z => ENNReal.ofReal (f z)) (measurable_const.indicator hEm).aemeasurable
      (ENNReal.measurable_ofReal.comp hfc.measurable).aemeasurable, lintegral_indicator_const hEm,
      one_mul, hfi]
  have hlow : ∫⁻ w, ∫⁻ s, G w s ∂circ ∂μ2 =
      ENNReal.ofReal (2 * Real.pi) * (stdGauss ι E * ENNReal.ofReal m) := by
    rw [lintegral_lintegral_swap hGm.aemeasurable]
    simp_rw [hconst]
    rw [lintegral_const, mul_comm]
    congr 1
    rw [circ, Measure.restrict_apply_univ, Real.volume_Ioc]; congr 1; ring
  -- the per-`w` bound
  set Sw : (ι → ℝ) × (ι → ℝ) → ℝ := fun w =>
    ∑ k ∈ Finset.range (2 * h + 1), f (rotX (2 * Real.pi * k / (2 * h + 1 : ℕ)) w.1 w.2) with hSw
  have hSw0 : ∀ w, 0 ≤ Sw w := fun w => Finset.sum_nonneg fun k _ => hnn _
  have hupper : ∀ w, ∫⁻ s, G w s ∂circ ≤ ENNReal.ofReal (C * ε ^ α * Sw w ^ (1 - α)) := by
    intro w
    set F : ℝ → ℝ := fun s => f (rotX s w.1 w.2) with hF
    have hFt : IsTrig h F := trig_of_poly P h hdeg w.1 w.2
    have hFc : Continuous F := by
      rw [hF]; refine hfc.comp ?_; unfold rotX; fun_prop
    have hGw : (fun s => G w s) =
        {s | F s < ε}.indicator (fun s => ENNReal.ofReal (F (s + Real.pi / 2))) := by
      funext s
      simp only [hGdef, hHdef, hF, rotY_eq, Set.indicator, hEdef, Set.mem_ofPred_eq]
      split_ifs <;> simp
    rw [show (fun s => G w s) = G w from rfl] at hGw
    rw [hGw]
    have := weighted_circle h hh F hFt hFc (fun s => hnn _) ε hε0 (Sw w)
      (trig_le_disc_sum h F hFt (fun s => hnn _))
    exact this
  -- Young's inequality in place of Jensen
  set c1 := K0 * (1 - α) / lam with hc1
  set c2 := K0 * α with hc2
  have hyoung : ∀ w, ENNReal.ofReal (C * ε ^ α * Sw w ^ (1 - α)) ≤
      ENNReal.ofReal c1 * ENNReal.ofReal (Sw w) + ENNReal.ofReal c2 := by
    intro w
    have h1a : 0 ≤ 1 - α := by linarith
    have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
    have hSw0' := hSw0 w
    rw [← ENNReal.ofReal_mul hc10, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hy := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - α) (w₂ := α)
      (p₁ := Sw w / lam) (p₂ := 1) (by linarith) hα0.le (by have := hSw0 w; positivity)
      zero_le_one (by ring)
    rw [Real.one_rpow, mul_one, Real.div_rpow (hSw0 w) hlam0.le] at hy
    have hl : 0 < lam ^ (1 - α) := Real.rpow_pos_of_pos hlam0 _
    have hy' : Sw w ^ (1 - α) ≤ lam ^ (1 - α) * ((1 - α) * (Sw w / lam) + α) := by
      rw [div_le_iff₀ hl] at hy; linarith
    calc C * ε ^ α * Sw w ^ (1 - α) ≤ C * ε ^ α * (lam ^ (1 - α) * ((1 - α) * (Sw w / lam) + α)) :=
          mul_le_mul_of_nonneg_left hy' (by positivity)
      _ = c1 * Sw w + c2 := by rw [hc1, hc2, hK0]; field_simp
  -- `E S = N m`
  have hSint : ∫⁻ w, ENNReal.ofReal (Sw w) ∂μ2 = ENNReal.ofReal lam := by
    have hmeas : ∀ k : ℕ, Measurable fun w : (ι → ℝ) × (ι → ℝ) =>
        ENNReal.ofReal (f (rotX (2 * Real.pi * k / (2 * h + 1 : ℕ)) w.1 w.2)) := by
      intro k
      refine ENNReal.measurable_ofReal.comp (hfc.comp ?_).measurable
      unfold rotX; fun_prop
    have hsum : ∀ w, ENNReal.ofReal (Sw w) = ∑ k ∈ Finset.range (2 * h + 1),
        ENNReal.ofReal (f (rotX (2 * Real.pi * k / (2 * h + 1 : ℕ)) w.1 w.2)) := fun w =>
      ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn _)
    rw [lintegral_congr hsum, lintegral_finsetSum _ fun k _ => hmeas k]
    have hk : ∀ k : ℕ, ∫⁻ w, ENNReal.ofReal (f (rotX (2 * Real.pi * k / (2 * h + 1 : ℕ)) w.1 w.2)) ∂μ2
        = ENNReal.ofReal m := by
      intro k
      rw [lintegral_rotX _ (fun z => ENNReal.ofReal (f z))
        (ENNReal.measurable_ofReal.comp hfc.measurable), hfi]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hlam,
      ENNReal.ofReal_mul hN0.le]
    congr 1
    rw [hN]; norm_cast
  have hup : ∫⁻ w, ∫⁻ s, G w s ∂circ ∂μ2 ≤ ENNReal.ofReal K0 := by
    calc ∫⁻ w, ∫⁻ s, G w s ∂circ ∂μ2
        ≤ ∫⁻ w, (ENNReal.ofReal c1 * ENNReal.ofReal (Sw w) + ENNReal.ofReal c2) ∂μ2 :=
          lintegral_mono fun w => (hupper w).trans (hyoung w)
      _ = ENNReal.ofReal c1 * ENNReal.ofReal lam + ENNReal.ofReal c2 := by
          have hSm : Measurable fun w => ENNReal.ofReal (Sw w) := by
            refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
            rw [hSw]; refine continuous_finsetSum _ fun k _ => hfc.comp ?_
            unfold rotX; fun_prop
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hSm, hSint,
            lintegral_const, measure_univ, mul_one]
      _ = ENNReal.ofReal K0 := by
          have : 0 ≤ 1 - α := by linarith
          rw [← ENNReal.ofReal_mul (by rw [hc1]; positivity),
            ← ENNReal.ofReal_add (by rw [hc1]; positivity) (by positivity)]
          congr 1
          rw [hc1, hc2]; field_simp; ring
  -- `K0 = 4π N² t^α m`
  have htα : t ^ α = p / (2 * N ^ 2) := by
    rw [ht, tW, ← hN]
    have hH0 : (2 * h : ℕ) ≠ 0 := by omega
    rw [hα, show ((1 : ℝ) / (2 * h)) = ((2 * h : ℕ) : ℝ)⁻¹ by push_cast; ring]
    exact Real.pow_rpow_inv_natCast (by positivity) hH0
  have hK0e : K0 = 4 * Real.pi * N ^ 2 * t ^ α * m := by
    rw [hK0, hC, hε, hlam, Real.mul_rpow ht0.le hmpos.le, Real.mul_rpow hN0.le hmpos.le]
    have e1 : N ^ α * N ^ (1 - α) = N := by
      rw [← Real.rpow_add hN0]; simp
    have e2 : m ^ α * m ^ (1 - α) = m := by
      rw [← Real.rpow_add hmpos]; simp
    calc 4 * Real.pi * N * N ^ α * (t ^ α * m ^ α) * (N ^ (1 - α) * m ^ (1 - α))
        = 4 * Real.pi * N * (N ^ α * N ^ (1 - α)) * t ^ α * (m ^ α * m ^ (1 - α)) := by ring
      _ = _ := by rw [e1, e2]; ring
  -- conclude
  have hfinal := hlow.symm.le.trans hup
  have hEfin : stdGauss ι E ≠ ⊤ := measure_ne_top _ _
  set a := (stdGauss ι E).toReal with hadef
  have ha : stdGauss ι E = ENNReal.ofReal a := (ENNReal.ofReal_toReal hEfin).symm
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  rw [ha, ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff hK00.le, hK0e, htα] at hfinal
  show stdGauss ι E ≤ ENNReal.ofReal p
  rw [ha]
  apply ENNReal.ofReal_le_ofReal
  have hN2 : 0 < N ^ 2 := by positivity
  have : 2 * Real.pi * (a * m) ≤ 2 * Real.pi * (p * m) := by
    calc 2 * Real.pi * (a * m) ≤ 4 * Real.pi * N ^ 2 * (p / (2 * N ^ 2)) * m := hfinal
      _ = 2 * Real.pi * (p * m) := by field_simp; ring
  have := le_of_mul_le_mul_left this (by positivity)
  exact le_of_mul_le_mul_right this hmpos

end BstLean.Part66
