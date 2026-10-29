import BstLean.Part48Interp
import BstLean.Part48Hyper
import BstLean.Part48Rot
import BstLean.Part48Trig
import BstLean.Part48Var
import BstLean.Part48PZ
import BstLean.Part48Avg

/-!
# Part 48, wave 2: the rotation small ball and a positive small-ball level (omQ4 §3–§4)

Specification: `delegations/answers/p48-spec-opus.md`, §2, §3 and §5. **Proved** here from
`Part48Interp` (`trig_sublevel`), `Part48Hyper` (`fourth_moment`), `Part48Trig` (`trig_of_poly`),
`Part48Rot` (`rotX_rot`), `Part48PZ` (`pz_lower`), `Part48Avg` (`rot_avg`) and `Part48Var`. All of
them are proved; nothing in Part 48 uses `sorry`.

* `mean_sq_le`: `(E P)² ≤ E P²` (variance expansion).
* `rot_smallball`: for `P` of degree `≤ h` with `E P⁴ ≤ K (E P²)²`, and a constant `C` of the
  interpolation lemma (hypothesis `hC`, the conclusion of `trig_sublevel`):
  `γ{|P| < u ‖P‖₂} ≤ (4 K C / 2π) (2u)^{1/(2h)}`. Route (omQ4 §4, with `L′ = ‖P‖₂/2` in place of
  `L = ‖P‖₂/√2`, which avoids a limit): `ε = u‖P‖₂`, `S = {|P| < ε}`, `G = {P² ≥ E P²/2}`,
  `A = {|P(X)| < ε, ∃ s₀, |P(X_{s₀})| > L′}` (open in its second condition). `S ×ˢ G ⊆ A`
  (`s₀ = π/2`), `γ(G) ≥ 1/(4K)` (`pz_lower`), `2π (γ⊗γ)(A) = ∫ circ{s : rot_s w ∈ A}` (`rot_avg`),
  and for each `w` the angle set is empty or lies in `{s : |P(X_s)| < ε}` of a trigonometric
  polynomial with a value `> L′` (`rotX_rot`, `trig_of_poly`, `hC`).
* `sb_level_exists`: every degree `h` and every `p > 0` have a level `t > 0` with `SBLevel h p t`.
  Route: `H = max h 1`, `K` from `fourth_moment H`, `C` from `trig_sublevel H`, `E P ≤ √(E P²)`
  for `P ≥ 0`, and `t = (p/A)^{2H}/2` with `A = 4KC/2π`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part48

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)

/-- `(E P)² ≤ E P²` under the standard Gaussian. -/
theorem mean_sq_le {ι : Type} [Fintype ι] (P : MvPolynomial ι ℝ) :
    (∫ z, MvPolynomial.eval z P ∂stdGauss ι) ^ 2 ≤ ∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι := by
  set m := ∫ z, MvPolynomial.eval z P ∂stdGauss ι
  have hi := gauss_poly_integrable P
  have hi2 : Integrable (fun z => (MvPolynomial.eval z P) ^ 2) (stdGauss ι) := by
    have := gauss_poly_integrable (P ^ 2); simpa only [map_pow] using this
  have hi3 : Integrable (fun z => (MvPolynomial.eval z P) ^ 2 - (2 * m) * MvPolynomial.eval z P)
      (stdGauss ι) := hi2.sub (hi.const_mul _)
  have h0 : 0 ≤ ∫ z, (MvPolynomial.eval z P - m) ^ 2 ∂stdGauss ι :=
    integral_nonneg fun _ => sq_nonneg _
  have he (z : ι → ℝ) : (MvPolynomial.eval z P - m) ^ 2 =
      ((MvPolynomial.eval z P) ^ 2 - (2 * m) * MvPolynomial.eval z P) + m ^ 2 := by ring
  simp_rw [he] at h0
  rw [integral_add hi3 (integrable_const _), integral_sub hi2 (hi.const_mul _), integral_const_mul,
    integral_const] at h0
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at h0
  nlinarith

/-- **The rotation small ball** (omQ4 §4): `γ{|P| < u ‖P‖₂} ≤ (4KC/2π)(2u)^{1/(2h)}`. -/
theorem rot_smallball {ι : Type} [Fintype ι] (h : ℕ) (hh : 1 ≤ h) (C K : ℝ)
    (hC : ∀ F : ℝ → ℝ, IsTrig h F → ∀ ε s0 : ℝ, 0 < ε → 0 < |F s0| →
      circ {s | |F s| < ε} ≤ ENNReal.ofReal (C * (ε / |F s0|) ^ ((1 : ℝ) / (2 * h))))
    (P : MvPolynomial ι ℝ) (hP : P.totalDegree ≤ h)
    (hK : ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
      K * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2)
    (u : ℝ) (hu : 0 < u) :
    stdGauss ι {z | |MvPolynomial.eval z P| <
        u * Real.sqrt (∫ z', (MvPolynomial.eval z' P) ^ 2 ∂stdGauss ι)} ≤
      ENNReal.ofReal (4 * K * C / (2 * Real.pi) * (2 * u) ^ ((1 : ℝ) / (2 * h))) := by
  set f : (ι → ℝ) → ℝ := fun z => MvPolynomial.eval z P with hf
  set E := ∫ z', (MvPolynomial.eval z' P) ^ 2 ∂stdGauss ι with hEdef
  have hE0 : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  rcases hE0.eq_or_lt with hE | hE
  · have : {z | |MvPolynomial.eval z P| < u * Real.sqrt E} = ∅ := by
      ext z; simp [← hE]
    rw [this, measure_empty]; exact bot_le
  set α : ℝ := (1 : ℝ) / (2 * h) with hα
  have hα0 : 0 ≤ α := by positivity
  set ε := u * Real.sqrt E with hε
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
  have hε0 : 0 < ε := mul_pos hu hsE
  set L' := Real.sqrt E / 2 with hL'
  have hL'0 : 0 < L' := by positivity
  have hfc : Continuous f := MvPolynomial.continuous_eval P
  -- the set A
  set A : Set ((ι → ℝ) × (ι → ℝ)) :=
    {w | |f w.1| < ε} ∩ {w | ∃ s0 : ℝ, L' < |f (rotX s0 w.1 w.2)|} with hAdef
  have hrc (s0 : ℝ) : Continuous (fun w : (ι → ℝ) × (ι → ℝ) => rotX s0 w.1 w.2) := by
    unfold rotX; fun_prop
  have hAm : MeasurableSet A := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (continuous_abs.comp (hfc.comp continuous_fst)).measurable measurable_const
    · have : IsOpen {w : (ι → ℝ) × (ι → ℝ) | ∃ s0 : ℝ, L' < |f (rotX s0 w.1 w.2)|} := by
        have : {w : (ι → ℝ) × (ι → ℝ) | ∃ s0 : ℝ, L' < |f (rotX s0 w.1 w.2)|} =
            ⋃ s0 : ℝ, {w | L' < |f (rotX s0 w.1 w.2)|} := by ext w; simp
        rw [this]
        exact isOpen_iUnion fun s0 => isOpen_lt continuous_const
          (continuous_abs.comp (hfc.comp (hrc s0)))
      exact this.measurableSet
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push Not at hneg
    have h0 := hC (fun _ => 1) ⟨fun j => if j = 0 then 1 else 0, fun _ => 0, fun s => by
      simp [ite_mul, Finset.sum_ite_eq']⟩ 2 0 (by norm_num) (by norm_num)
    have hpos : circ {s : ℝ | |(fun _ : ℝ => (1 : ℝ)) s| < 2} = ENNReal.ofReal (2 * Real.pi) := by
      simp [circ, Real.volume_Ioc]
    rw [hpos] at h0
    have h3 : C * (2 / |(1 : ℝ)|) ^ α ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le (Real.rpow_nonneg (by positivity) _)
    rw [ENNReal.ofReal_eq_zero.mpr h3] at h0
    have := ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)
    exact absurd h0 (not_le.mpr this)
  -- pointwise bound
  have hpt : ∀ w : (ι → ℝ) × (ι → ℝ), circ {s | (rotX s w.1 w.2, rotY s w.1 w.2) ∈ A} ≤
      ENNReal.ofReal (C * (ε / L') ^ α) := by
    intro w
    by_cases hw : ∃ s1 : ℝ, L' < |f (rotX s1 w.1 w.2)|
    · obtain ⟨s1, hs1⟩ := hw
      have hsub : {s | (rotX s w.1 w.2, rotY s w.1 w.2) ∈ A} ⊆
          {s | |f (rotX s w.1 w.2)| < ε} := fun s hs => hs.1
      refine (measure_mono hsub).trans ((hC (fun s => f (rotX s w.1 w.2))
        (trig_of_poly P h hP w.1 w.2) ε s1 hε0 (hL'0.trans hs1)).trans ?_)
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hC0
      apply Real.rpow_le_rpow (by positivity) _ hα0
      exact div_le_div_of_nonneg_left hε0.le hL'0 hs1.le
    · have : {s | (rotX s w.1 w.2, rotY s w.1 w.2) ∈ A} = ∅ := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, s0, hs0⟩
        apply hw
        refine ⟨s + s0, ?_⟩
        simpa [rotX_rot] using hs0
      rw [this, measure_empty]; exact bot_le
  -- integrate
  have havg := rot_avg A hAm
  have hint : ∫⁻ w, circ {s | (rotX s w.1 w.2, rotY s w.1 w.2) ∈ A} ∂((stdGauss ι).prod (stdGauss ι)) ≤
      ENNReal.ofReal (C * (ε / L') ^ α) := by
    calc _ ≤ ∫⁻ _, ENNReal.ofReal (C * (ε / L') ^ α) ∂((stdGauss ι).prod (stdGauss ι)) :=
          lintegral_mono hpt
      _ = _ := by simp
  -- product rectangle
  set S := {z | |f z| < ε} with hS
  set G := {z | E / 2 ≤ (f z) ^ 2} with hG
  have hrect : S ×ˢ G ⊆ A := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    refine ⟨hx, Real.pi / 2, ?_⟩
    have hrot : rotX (Real.pi / 2) x y = y := by funext i; simp [rotX]
    rw [hrot]
    have h1 : Real.sqrt (E / 2) ≤ |f y| := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hy
    have h2 : L' < Real.sqrt (E / 2) := by
      rw [hL', Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
      have hs2 : Real.sqrt 2 < 2 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      exact div_lt_div_of_pos_left hsE (by positivity) hs2
    exact h2.trans_le h1
  have hpz := pz_lower P K hE hK
  have hprod : stdGauss ι S * stdGauss ι G ≤ ((stdGauss ι).prod (stdGauss ι)) A := by
    rw [← Measure.prod_prod]; exact measure_mono hrect
  have hK0 : 0 < K := by
    have h1 := mean_sq_le (P ^ 2)
    simp only [map_pow] at h1
    have h2 : ∫ z, ((MvPolynomial.eval z) P ^ 2) ^ 2 ∂stdGauss ι =
        ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι := by
      congr 1; funext z; ring
    rw [h2] at h1
    have h3 : E ^ 2 ≤ K * E ^ 2 := h1.trans hK
    have hE2 : 0 < E ^ 2 := by positivity
    nlinarith
  have hr : ε / L' = 2 * u := by
    rw [hε, hL']; field_simp
  rw [hr] at hint
  set r := (2 * u) ^ α with hrdef
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hfin : stdGauss ι S ≠ ⊤ := measure_ne_top _ _
  set a := (stdGauss ι S).toReal with hadef
  have ha : stdGauss ι S = ENNReal.ofReal a := (ENNReal.ofReal_toReal hfin).symm
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have key : ENNReal.ofReal (2 * Real.pi * (a * (1 / (4 * K)))) ≤ ENNReal.ofReal (C * r) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha0, ← ha]
    calc ENNReal.ofReal (2 * Real.pi) * (stdGauss ι S * ENNReal.ofReal (1 / (4 * K)))
        ≤ ENNReal.ofReal (2 * Real.pi) * (stdGauss ι S * stdGauss ι G) := by gcongr
      _ ≤ ENNReal.ofReal (2 * Real.pi) * ((stdGauss ι).prod (stdGauss ι)) A := by gcongr
      _ ≤ _ := by rw [havg]; exact hint
  have key' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key
  rw [ha]
  apply ENNReal.ofReal_le_ofReal
  have hpi := Real.pi_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : a * (2 * Real.pi) = 2 * Real.pi * (a * (1 / (4 * K))) * (4 * K) := by
    field_simp
  rw [this]
  calc 2 * Real.pi * (a * (1 / (4 * K))) * (4 * K) ≤ C * r * (4 * K) :=
        mul_le_mul_of_nonneg_right key' (by positivity)
    _ = 4 * K * C * r := by ring
/-- **A positive small-ball level** for every degree and every probability `p > 0`. -/
theorem sb_level_exists (h : ℕ) (p : ℝ) (hp : 0 < p) : ∃ t : ℝ, 0 < t ∧ SBLevel h p t := by
  set H := max h 1 with hHdef
  have hH : 1 ≤ H := le_max_right _ _
  obtain ⟨K, hK0, hK⟩ := fourth_moment H
  obtain ⟨C, hC0, hC⟩ := trig_sublevel H hH
  set A := 4 * K * C / (2 * Real.pi) with hA
  have hA0 : 0 < A := by rw [hA]; have := Real.pi_pos; positivity
  set t := (p / A) ^ (2 * H) / 2 with htdef
  have ht : 0 < t := by positivity
  refine ⟨t, ht, ?_⟩
  intro ι _ P hdeg hnn
  have hdegH : P.totalDegree ≤ H := hdeg.trans (le_max_left _ _)
  have key := rot_smallball H hH C K hC P hdegH (hK ι P hdegH) t ht
  have hEP : ∫ z, MvPolynomial.eval z P ∂stdGauss ι ≤
      Real.sqrt (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (mean_sq_le P))
  refine le_trans (measure_mono ?_) (key.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [abs_of_nonneg (hnn z)]
    exact lt_of_lt_of_le hz (mul_le_mul_of_nonneg_left hEP ht.le)
  · have h1 : 2 * t = (p / A) ^ (2 * H) := by
      rw [htdef]; field_simp
    rw [h1]
    have hH0 : (2 * H : ℕ) ≠ 0 := by omega
    have h2 : ((p / A) ^ (2 * H)) ^ ((1 : ℝ) / (2 * H)) = p / A := by
      rw [show ((1 : ℝ) / (2 * H)) = ((2 * H : ℕ) : ℝ)⁻¹ by push_cast; ring]
      exact Real.pow_rpow_inv_natCast (by positivity) hH0
    rw [h2, ← hA]
    rw [mul_div_cancel₀ _ hA0.ne']
end BstLean.Part48
