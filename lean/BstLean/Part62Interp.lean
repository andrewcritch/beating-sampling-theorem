import BstLean.Part48Defs

/-!
# Part 62: interpolation on the circle with the constant stated (copy of `Part48Interp`)

Copy-and-generalize of `Part48Interp.lean` (its lemmas are private there). The only change: the
headline `trig_sublevel_explicit` states the constant `C_h = 4π N N^{1/(2h)}`, `N = 2h + 1`, which
`Part48Interp.trig_sublevel` hides behind `∃ C`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part62

open MeasureTheory Polynomial
open BstLean.Part48 (IsTrig circ)
open scoped ENNReal

private lemma lagrange_bound (S : Finset ℂ) (Q : ℂ[X]) (hdeg : Q.degree < S.card) (δ ε : ℝ)
    (hδ : 0 < δ) (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ ‖a - b‖) (hnorm : ∀ a ∈ S, ‖a‖ = 1)
    (hε : 0 ≤ ε) (hQ : ∀ a ∈ S, ‖Q.eval a‖ ≤ ε) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖Q.eval z‖ ≤ S.card * ε * (2 / δ) ^ (S.card - 1) := by
  classical
  have hinj : Set.InjOn (id : ℂ → ℂ) S := Set.injOn_id _
  have hQe := Lagrange.eq_interpolate_of_eval_eq (s := S) (v := id) (r := fun a => Q.eval a) hinj hdeg
    (fun i _ => rfl)
  rw [hQe, Lagrange.interpolate_apply, eval_finsetSum]
  have hterm : ∀ i ∈ S, ‖eval z (C (Q.eval i) * Lagrange.basis S id i)‖ ≤ ε * (2 / δ) ^ (S.card - 1) := by
    intro i hi
    rw [eval_mul, eval_C, norm_mul]
    refine mul_le_mul (hQ i hi) ?_ (norm_nonneg _) hε
    rw [Lagrange.basis, eval_prod, norm_prod]
    have hcard : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi
    rw [← hcard, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hd := hsep i hi j hjS (Ne.symm hji)
    have hpos : 0 < ‖i - j‖ := lt_of_lt_of_le hδ hd
    rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, norm_mul, norm_inv]
    simp only [id]
    have hzj : ‖z - j‖ ≤ 2 := by
      calc ‖z - j‖ ≤ ‖z‖ + ‖j‖ := norm_sub_le _ _
        _ = 2 := by rw [hz, hnorm j hjS]; norm_num
    rw [inv_mul_le_iff₀ hpos]
    calc ‖z - j‖ ≤ 2 := hzj
      _ ≤ ‖i - j‖ * (2 / δ) := by
        rw [mul_div_assoc', le_div_iff₀ hδ]; nlinarith
  calc ‖∑ i ∈ S, eval z (C (Q.eval i) * Lagrange.basis S id i)‖
      ≤ ∑ i ∈ S, ‖eval z (C (Q.eval i) * Lagrange.basis S id i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, ε * (2 / δ) ^ (S.card - 1) := Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
private lemma exp_pow_eq (s : ℝ) (n : ℕ) :
    Complex.exp (s * Complex.I) ^ n = Complex.exp (((n : ℝ) * s : ℝ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private lemma trig_poly_repr {h : ℕ} {F : ℝ → ℝ} (hF : IsTrig h F) :
    ∃ Q : ℂ[X], Q.natDegree ≤ 2 * h ∧ ∀ s : ℝ,
      Q.eval (Complex.exp (s * Complex.I)) = Complex.exp (s * Complex.I) ^ h * (F s : ℂ) := by
  obtain ⟨a, b, hab⟩ := hF
  refine ⟨∑ j ∈ Finset.range (h + 1), (C ((a j - b j * Complex.I) / 2) * X ^ (h + j) +
      C ((a j + b j * Complex.I) / 2) * X ^ (h - j)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    have hj' : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · intro s
    rw [hab s, eval_finsetSum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    rw [exp_pow_eq, exp_pow_eq, exp_pow_eq, Nat.cast_add, Nat.cast_sub hj']
    have e1 : (((h : ℝ) + j) * s : ℝ) = (h : ℝ) * s + j * s := by ring
    have e2 : (((h : ℝ) - j) * s : ℝ) = (h : ℝ) * s - j * s := by ring
    rw [e1, e2]
    push_cast
    rw [add_mul, sub_mul, Complex.exp_add, Complex.exp_sub]
    rw [Complex.exp_mul_I ((j : ℂ) * s)]
    set c := Complex.cos ((j : ℂ) * s)
    set sn := Complex.sin ((j : ℂ) * s)
    set E := Complex.exp ((h : ℂ) * s * Complex.I)
    have hcs : c ^ 2 + sn ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
    have hinv : (c + sn * Complex.I)⁻¹ = c - sn * Complex.I := by
      apply inv_eq_of_mul_eq_one_right
      linear_combination hcs - sn ^ 2 * Complex.I_sq
    rw [div_eq_mul_inv E, hinv]
    have hb : ((b j : ℝ) : ℂ) = (b j : ℂ) := rfl
    linear_combination (-(E * (b j : ℂ) * sn)) * Complex.I_sq
private lemma chord_lower (a b : ℝ) (hab : |a - b| ≤ Real.pi) :
    2 / Real.pi * |a - b| ≤ ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ := by
  have h1 : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I) =
      Complex.exp (b * Complex.I) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  set y := (a - b) / 2 with hy
  have hy' : |y| ≤ Real.pi / 2 := by rw [hy, abs_div, abs_two]; linarith
  have hpi := Real.pi_pos
  have key : 2 / Real.pi * |y| ≤ |Real.sin y| := by
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0] at hy' ⊢
      exact (Real.mul_le_sin h0 hy').trans (le_abs_self _)
    · rw [abs_of_neg h0] at hy' ⊢
      have := Real.mul_le_sin (by linarith : 0 ≤ -y) hy'
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have : |a - b| = 2 * |y| := by rw [hy, abs_div, abs_two]; ring
  rw [this]
  nlinarith

private lemma greedy (E : Set ℝ) (r : ℝ) (hr : 0 < r) (N : ℕ)
    (hE : ENNReal.ofReal (2 * r * N) < volume E) :
    ∃ S : Finset ℝ, S.card = N + 1 ∧ (S : Set ℝ) ⊆ E ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ |a - b| := by
  classical
  have step : ∀ k : ℕ, k ≤ N + 1 → ∃ S : Finset ℝ, S.card = k ∧ (S : Set ℝ) ⊆ E ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ |a - b| := by
    intro k
    induction k with
    | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨S, hcard, hSE, hsep⟩ := ih (by omega)
      set U := ⋃ a ∈ S, Set.Ioo (a - r) (a + r) with hU
      have hUvol : volume U ≤ ENNReal.ofReal (2 * r * k) := by
        calc volume U ≤ ∑ a ∈ S, volume (Set.Ioo (a - r) (a + r)) := measure_biUnion_finset_le _ _
          _ = ∑ _a ∈ S, ENNReal.ofReal (2 * r) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Real.volume_Ioo]; congr 1; ring
          _ = ENNReal.ofReal (2 * r * k) := by
              rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_comm,
                ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * r), ENNReal.ofReal_natCast]
      have hlt : volume U < volume E := by
        refine lt_of_le_of_lt hUvol (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hE)
        have : (k : ℝ) ≤ N := by exact_mod_cast (by omega : k ≤ N)
        nlinarith
      have hx : ∃ x ∈ E, x ∉ U := by
        by_contra hcon
        push Not at hcon
        exact absurd (measure_mono hcon) (not_le.mpr hlt)
      obtain ⟨x, hxE, hxU⟩ := hx
      have hfar : ∀ a ∈ S, r ≤ |x - a| := by
        intro a ha
        by_contra hc
        push Not at hc
        apply hxU
        rw [hU, Set.mem_iUnion₂]
        refine ⟨a, ha, ?_⟩
        rw [abs_lt] at hc
        constructor <;> linarith
      have hxS : x ∉ S := by
        intro hxS
        have := hfar x hxS
        simp at this
        linarith
      refine ⟨insert x S, by rw [Finset.card_insert_of_notMem hxS, hcard], ?_, ?_⟩
      · intro y hy
        rw [Finset.coe_insert] at hy
        rcases hy with rfl | hy
        · exact hxE
        · exact hSE hy
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hfar b hb
        · rw [abs_sub_comm]; exact hfar a ha
        · exact hsep a ha b hb hab
  exact step (N + 1) le_rfl

private lemma half_bound (h : ℕ) (hh : 1 ≤ h) (F : ℝ → ℝ) (hF : IsTrig h F) (ε s0 : ℝ) (hε : 0 < ε)
    (hM : 0 < |F s0|) (c : ℝ) (B : Set ℝ) (hB : B ⊆ Set.Ioc c (c + Real.pi))
    (hBF : ∀ x ∈ B, |F x| < ε) :
    volume B ≤ ENNReal.ofReal (2 * Real.pi * (2 * h + 1) *
      ((2 * h + 1) * ε / |F s0|) ^ ((1 : ℝ) / (2 * h))) := by
  classical
  set M := |F s0| with hMdef
  set N : ℝ := 2 * h + 1 with hN
  set α : ℝ := (1 : ℝ) / (2 * h) with hα
  have hpi := Real.pi_pos
  have hN0 : 0 < N := by positivity
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hα0 : 0 < α := by positivity
  set bound := 2 * Real.pi * N * (N * ε / M) ^ α with hbound
  have hb0 : 0 ≤ bound := by positivity
  by_contra hcon
  push Not at hcon
  have hfin : volume B ≤ ENNReal.ofReal Real.pi := by
    refine (measure_mono hB).trans ?_
    rw [Real.volume_Ioc]; apply le_of_eq; congr 1; ring
  have hBtop : volume B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
  set lam := (volume B).toReal with hlam
  have hBeq : volume B = ENNReal.ofReal lam := (ENNReal.ofReal_toReal hBtop).symm
  have hlam_gt : bound < lam := by
    rw [hBeq] at hcon
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb0).mp hcon
  have hlam0 : 0 < lam := lt_of_le_of_lt hb0 hlam_gt
  set r := lam / (2 * N) with hr
  have hr0 : 0 < r := by positivity
  have hgreedy : ENNReal.ofReal (2 * r * ((2 * h : ℕ) : ℝ)) < volume B := by
    rw [hBeq]
    apply (ENNReal.ofReal_lt_ofReal_iff hlam0).mpr
    rw [hr]
    push_cast
    rw [hN]
    field_simp
    nlinarith
  obtain ⟨S, hScard, hSB, hSsep⟩ := greedy B r hr0 (2 * h) hgreedy
  set e : ℝ → ℂ := fun t => Complex.exp (t * Complex.I) with he
  have hdist : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 * r / Real.pi ≤ ‖e a - e b‖ := by
    intro a ha b hb hab
    have hab' : |a - b| ≤ Real.pi := by
      have h1 := hB (hSB ha); have h2 := hB (hSB hb)
      simp only [Set.mem_Ioc] at h1 h2
      rw [abs_le]; constructor <;> linarith
    refine le_trans ?_ (chord_lower a b hab')
    rw [div_mul_eq_mul_div, mul_comm 2 r]
    exact div_le_div_of_nonneg_right (by nlinarith [hSsep a ha b hb hab]) hpi.le
  have hinj : Set.InjOn e S := by
    intro a ha b hb hab
    by_contra hne
    have := hdist a ha b hb hne
    rw [hab, sub_self, norm_zero] at this
    have : 0 < 2 * r / Real.pi := by positivity
    linarith
  set T := S.image e with hT
  have hTcard : T.card = 2 * h + 1 := by rw [hT, Finset.card_image_of_injOn hinj, hScard]
  obtain ⟨Q, hQdeg, hQ⟩ := trig_poly_repr hF
  have hdeg : Q.degree < T.card := by
    rw [hTcard]
    refine lt_of_le_of_lt degree_le_natDegree ?_
    exact_mod_cast (by omega : Q.natDegree < 2 * h + 1)
  have hsepT : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r / Real.pi ≤ ‖a - b‖ := by
    intro a ha b hb hab
    rw [hT, Finset.mem_image] at ha hb
    obtain ⟨t, ht, rfl⟩ := ha
    obtain ⟨t', ht', rfl⟩ := hb
    exact hdist t ht t' ht' (fun h' => hab (by rw [h']))
  have hnormT : ∀ a ∈ T, ‖a‖ = 1 := by
    intro a ha
    rw [hT, Finset.mem_image] at ha
    obtain ⟨t, -, rfl⟩ := ha
    exact Complex.norm_exp_ofReal_mul_I t
  have hQT : ∀ a ∈ T, ‖Q.eval a‖ ≤ ε := by
    intro a ha
    rw [hT, Finset.mem_image] at ha
    obtain ⟨t, ht, rfl⟩ := ha
    rw [hQ t, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact (hBF t (hSB ht)).le
  have hLag := lagrange_bound T Q hdeg (2 * r / Real.pi) ε (by positivity) hsepT hnormT hε.le hQT
    (e s0) (Complex.norm_exp_ofReal_mul_I s0)
  rw [hQ s0, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, hTcard] at hLag
  -- hLag : M ≤ (2h+1) ε (2/(2r/π))^(2h)
  have h2r : 2 / (2 * r / Real.pi) = Real.pi / r := by field_simp
  rw [h2r, show 2 * h + 1 - 1 = 2 * h by omega] at hLag
  push_cast at hLag
  rw [← hN] at hLag
  -- (π/r)^(2h) ≥ M/(Nε)
  have hx0 : 0 < Real.pi / r := by positivity
  have hy : M / (N * ε) ≤ (Real.pi / r) ^ (2 * h) := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hroot : (M / (N * ε)) ^ α ≤ Real.pi / r := by
    have := Real.rpow_le_rpow (by positivity) hy hα0.le
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, hα, Nat.cast_mul, Nat.cast_ofNat,
      mul_one_div_cancel (by positivity), Real.rpow_one] at this
  have hinv : (M / (N * ε)) ^ α = ((N * ε / M) ^ α)⁻¹ := by
    rw [← Real.inv_rpow (by positivity), inv_div]
  rw [hinv] at hroot
  have hpos : 0 < (N * ε / M) ^ α := by positivity
  have hr_le : r ≤ Real.pi * (N * ε / M) ^ α := by
    rw [inv_le_iff_one_le_mul₀' hpos, mul_div_assoc', le_div_iff₀ hr0] at hroot
    linarith
  have : lam = 2 * N * r := by rw [hr]; field_simp
  have : lam ≤ bound := by
    rw [this, hbound]; nlinarith
  linarith

/-- **Interpolation on the circle**: the sublevel set of a trigonometric polynomial of degree `≤ h`
has measure `≤ C_h (ε / |F s₀|)^{1/(2h)}`. -/
theorem trig_sublevel_explicit (h : ℕ) (hh : 1 ≤ h) :
    ∀ F : ℝ → ℝ, IsTrig h F → ∀ ε s0 : ℝ, 0 < ε → 0 < |F s0| →
      circ {s | |F s| < ε} ≤ ENNReal.ofReal (4 * Real.pi * (2 * h + 1) * (2 * h + 1) ^ ((1 : ℝ) / (2 * h)) *
        (ε / |F s0|) ^ ((1 : ℝ) / (2 * h))) := by
  have hpi := Real.pi_pos
  set N : ℝ := 2 * h + 1 with hN
  set α : ℝ := (1 : ℝ) / (2 * h) with hα
  have hN0 : 0 < N := by positivity
  intro F hF ε s0 hε hM
  set A := {s | |F s| < ε} with hA
  have hbd : 2 * Real.pi * N * (N * ε / |F s0|) ^ α = 2 * Real.pi * N * N ^ α * (ε / |F s0|) ^ α := by
    rw [mul_div_assoc, Real.mul_rpow hN0.le (by positivity)]; ring
  have h1 := half_bound h hh F hF ε s0 hε hM 0 (A ∩ Set.Ioc 0 Real.pi)
    (by rw [zero_add]; exact Set.inter_subset_right) (fun x hx => hx.1)
  have h2 := half_bound h hh F hF ε s0 hε hM Real.pi (A ∩ Set.Ioc Real.pi (Real.pi + Real.pi))
    Set.inter_subset_right (fun x hx => hx.1)
  rw [hbd] at h1 h2
  unfold circ
  rw [Measure.restrict_apply' measurableSet_Ioc]
  have hsub : A ∩ Set.Ioc 0 (2 * Real.pi) ⊆
      (A ∩ Set.Ioc 0 Real.pi) ∪ (A ∩ Set.Ioc Real.pi (Real.pi + Real.pi)) := by
    rintro x ⟨hxA, hx0, hx1⟩
    by_cases hx : x ≤ Real.pi
    · exact Or.inl ⟨hxA, hx0, hx⟩
    · exact Or.inr ⟨hxA, lt_of_not_ge hx, by linarith⟩
  calc volume (A ∩ Set.Ioc 0 (2 * Real.pi))
      ≤ volume (A ∩ Set.Ioc 0 Real.pi) + volume (A ∩ Set.Ioc Real.pi (Real.pi + Real.pi)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (2 * Real.pi * N * N ^ α * (ε / |F s0|) ^ α) +
        ENNReal.ofReal (2 * Real.pi * N * N ^ α * (ε / |F s0|) ^ α) := add_le_add h1 h2
    _ = ENNReal.ofReal (4 * Real.pi * N * N ^ α * (ε / |F s0|) ^ α) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end BstLean.Part62
