import BstLean.Part48Defs
import BstLean.Part66Comb

/-!
# Part 66: interpolation on the circle with ordered nodes (omSBL-cx step 1)

Sorting the `2h+1` greedy nodes gives `|a_i − a_j| ≥ |i − j| r`, and the Lagrange denominators
are then at least `δ^d i! (d−i)!`. Summing `1/(i!(d−i)!)` gives `2^d/d!`. The headline:

  `trig_sublevel_ord`: `circ{|F| < ε} ≤ 8π N (ε / (|F s₀| (2h)!))^{1/(2h)}`, `N = 2h+1`.

The private helpers `exp_pow_eq`, `trig_poly_repr`, `chord_lower`, `greedy` are copied from
`Part62Interp` (where they are private).

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part66

open MeasureTheory Polynomial
open BstLean.Part48 (IsTrig circ)
open scoped ENNReal

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


lemma lagrange_bound_ord (d : ℕ) (v : ℕ → ℂ) (Q : ℂ[X]) (hdeg : Q.degree < (d + 1 : ℕ))
    (δ ε : ℝ) (hδ : 0 < δ) (hinj : Set.InjOn v (Finset.range (d + 1)))
    (hsep : ∀ i ∈ Finset.range (d + 1), ∀ j ∈ Finset.range (d + 1),
      δ * |(i : ℝ) - j| ≤ ‖v i - v j‖)
    (hnorm : ∀ i ∈ Finset.range (d + 1), ‖v i‖ = 1)
    (hε : 0 ≤ ε) (hQ : ∀ i ∈ Finset.range (d + 1), ‖Q.eval (v i)‖ ≤ ε) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖Q.eval z‖ ≤ ε * (4 / δ) ^ d / d.factorial := by
  classical
  set s := Finset.range (d + 1) with hs
  have hcard : s.card = d + 1 := Finset.card_range _
  have hQe := Lagrange.eq_interpolate_of_eval_eq (s := s) (v := v) (r := fun i => Q.eval (v i))
    hinj (by rw [hcard]; exact hdeg) (fun i _ => rfl)
  rw [hQe, Lagrange.interpolate_apply, eval_finsetSum]
  have hterm : ∀ i ∈ s, ‖eval z (C (Q.eval (v i)) * Lagrange.basis s v i)‖ ≤
      ε * ((2 / δ) ^ d / ((i.factorial : ℝ) * (d - i).factorial)) := by
    intro i hi
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [eval_mul, eval_C, norm_mul]
    refine mul_le_mul (hQ i hi) ?_ (norm_nonneg _) hε
    have hcard' : (s.erase i).card = d := by rw [Finset.card_erase_of_mem hi, hcard]; rfl
    have hP : ∏ j ∈ s.erase i, |(i : ℝ) - j| = (i.factorial : ℝ) * (d - i).factorial :=
      prod_dist d i hi'
    have hpow : (2 / δ) ^ d = ∏ _j ∈ s.erase i, (2 / δ) := by rw [Finset.prod_const, hcard']
    rw [Lagrange.basis, eval_prod, norm_prod, ← hP, hpow, ← Finset.prod_div_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hjS : j ∈ s := Finset.mem_of_mem_erase hj
    have hij0 : 0 < |(i : ℝ) - j| := by
      rw [abs_pos, sub_ne_zero]; exact_mod_cast hji.symm
    have hd := hsep i hi j hjS
    have hpos : 0 < ‖v i - v j‖ := lt_of_lt_of_le (by positivity) hd
    rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, norm_mul, norm_inv]
    have hzj : ‖z - v j‖ ≤ 2 := by
      calc ‖z - v j‖ ≤ ‖z‖ + ‖v j‖ := norm_sub_le _ _
        _ = 2 := by rw [hz, hnorm j hjS]; norm_num
    rw [inv_mul_le_iff₀ hpos]
    calc ‖z - v j‖ ≤ 2 := hzj
      _ = δ * |(i : ℝ) - j| * (2 / δ / |(i : ℝ) - j|) := by field_simp
      _ ≤ ‖v i - v j‖ * (2 / δ / |(i : ℝ) - j|) :=
          mul_le_mul_of_nonneg_right hd (by positivity)
  calc ‖∑ i ∈ s, eval z (C (Q.eval (v i)) * Lagrange.basis s v i)‖
      ≤ ∑ i ∈ s, ‖eval z (C (Q.eval (v i)) * Lagrange.basis s v i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ε * ((2 / δ) ^ d / ((i.factorial : ℝ) * (d - i).factorial)) :=
        Finset.sum_le_sum hterm
    _ = ε * (2 / δ) ^ d * ∑ i ∈ s, (1 : ℝ) / ((i.factorial : ℝ) * (d - i).factorial) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ε * (4 / δ) ^ d / d.factorial := by
        rw [hs, sum_inv_fact, show (4 / δ) = 2 * (2 / δ) by ring, mul_pow]; ring

/-- Sorted greedy nodes are separated in proportion to their index gap. -/
lemma sorted_gap (S : Finset ℝ) (n : ℕ) (hS : S.card = n) (r : ℝ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ |a - b|) (k i : ℕ) (hik : i + k < n) :
    (k : ℝ) * r ≤ S.orderEmbOfFin hS ⟨i + k, hik⟩ - S.orderEmbOfFin hS ⟨i, by omega⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    set σ := S.orderEmbOfFin hS
    have hlt : σ ⟨i + k, by omega⟩ < σ ⟨i + (k + 1), hik⟩ := by
      apply σ.strictMono; simp [Fin.lt_def]
    have hmem1 := S.orderEmbOfFin_mem hS ⟨i + k, by omega⟩
    have hmem2 := S.orderEmbOfFin_mem hS ⟨i + (k + 1), hik⟩
    have hstep := hsep _ hmem2 _ hmem1 (ne_of_gt hlt)
    rw [abs_of_pos (by linarith)] at hstep
    push_cast
    linarith

private lemma half_bound_ord (h : ℕ) (hh : 1 ≤ h) (F : ℝ → ℝ) (hF : IsTrig h F) (ε s0 : ℝ)
    (hε : 0 < ε) (hM : 0 < |F s0|) (c : ℝ) (B : Set ℝ) (hB : B ⊆ Set.Ioc c (c + Real.pi))
    (hBF : ∀ x ∈ B, |F x| < ε) :
    volume B ≤ ENNReal.ofReal (4 * Real.pi * (2 * h + 1) *
      (ε / (|F s0| * (2 * h).factorial)) ^ ((1 : ℝ) / (2 * h))) := by
  classical
  set M := |F s0| with hMdef
  set d := 2 * h with hd
  set N : ℝ := 2 * h + 1 with hN
  set α : ℝ := (1 : ℝ) / (2 * h) with hα
  set Df : ℝ := (d.factorial : ℝ) with hDf
  have hDf0 : 0 < Df := by rw [hDf]; exact_mod_cast d.factorial_pos
  have hpi := Real.pi_pos
  have hN0 : 0 < N := by positivity
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hα0 : 0 < α := by positivity
  set bound := 4 * Real.pi * N * (ε / (M * Df)) ^ α with hbound
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
  -- sorted nodes indexed by `ℕ`
  set σ := S.orderEmbOfFin hScard with hσ
  set u : ℕ → ℝ := fun k => if hk : k < 2 * h + 1 then σ ⟨k, hk⟩ else 0 with hu
  have huS : ∀ k, k < 2 * h + 1 → u k ∈ S := by
    intro k hk; simp only [hu, dif_pos hk]; exact S.orderEmbOfFin_mem hScard _
  have hgap : ∀ i j, i < 2 * h + 1 → j < 2 * h + 1 → |(i : ℝ) - j| * r ≤ |u i - u j| := by
    intro i j hi hj
    rcases le_total i j with hij | hij
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
      have := sorted_gap S (2 * h + 1) hScard r hSsep k i hj
      simp only [hu, dif_pos hi, dif_pos hj]
      rw [abs_sub_comm, abs_sub_comm (σ _)]
      push_cast
      rw [show ((i : ℝ) + k - i) = k by ring, abs_of_nonneg (by positivity),
        abs_of_nonneg (by have : (0:ℝ) ≤ k * r := by positivity
                          linarith)]
      exact this
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
      have := sorted_gap S (2 * h + 1) hScard r hSsep k j hi
      simp only [hu, dif_pos hi, dif_pos hj]
      push_cast
      rw [show ((j : ℝ) + k - j) = k by ring, abs_of_nonneg (by positivity),
        abs_of_nonneg (by have : (0:ℝ) ≤ k * r := by positivity
                          linarith)]
      exact this
  set e : ℝ → ℂ := fun t => Complex.exp (t * Complex.I) with he
  set v : ℕ → ℂ := fun k => e (u k) with hv
  set δ := 2 * r / Real.pi with hδ
  have hδ0 : 0 < δ := by positivity
  have hsepv : ∀ i ∈ Finset.range (2 * h + 1), ∀ j ∈ Finset.range (2 * h + 1),
      δ * |(i : ℝ) - j| ≤ ‖v i - v j‖ := by
    intro i hi j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hab' : |u i - u j| ≤ Real.pi := by
      have h1 := hB (hSB (huS i hi')); have h2 := hB (hSB (huS j hj'))
      simp only [Set.mem_Ioc] at h1 h2
      rw [abs_le]; constructor <;> linarith
    refine le_trans ?_ (chord_lower (u i) (u j) hab')
    have := hgap i j hi' hj'
    rw [hδ]
    calc 2 * r / Real.pi * |(i : ℝ) - j| = 2 / Real.pi * (|(i : ℝ) - j| * r) := by ring
      _ ≤ 2 / Real.pi * |u i - u j| := mul_le_mul_of_nonneg_left this (by positivity)
  have hinj : Set.InjOn v (Finset.range (2 * h + 1)) := by
    intro i hi j hj hij
    have := hsepv i hi j hj
    rw [hij, sub_self, norm_zero] at this
    have h0 : |(i : ℝ) - j| = 0 := by
      have := abs_nonneg ((i : ℝ) - j)
      nlinarith
    rw [abs_eq_zero, sub_eq_zero] at h0
    exact_mod_cast h0
  have hnormv : ∀ i ∈ Finset.range (2 * h + 1), ‖v i‖ = 1 := fun i _ =>
    Complex.norm_exp_ofReal_mul_I _
  obtain ⟨Q, hQdeg, hQ⟩ := trig_poly_repr hF
  have hdeg : Q.degree < ((2 * h + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    exact_mod_cast (by omega : Q.natDegree < 2 * h + 1)
  have hQv : ∀ i ∈ Finset.range (2 * h + 1), ‖Q.eval (v i)‖ ≤ ε := by
    intro i hi
    rw [hv]; simp only [he]
    rw [hQ (u i), norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact (hBF _ (hSB (huS i (Finset.mem_range.mp hi)))).le
  have hLag := lagrange_bound_ord (2 * h) v Q hdeg δ ε hδ0 hinj hsepv hnormv hε.le hQv
    (e s0) (Complex.norm_exp_ofReal_mul_I s0)
  rw [hQ s0, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs] at hLag
  -- hLag : M ≤ ε (4/δ)^(2h) / (2h)!
  have h4 : 4 / δ = 2 * Real.pi / r := by rw [hδ]; field_simp; ring
  rw [h4, ← hMdef] at hLag
  have hx0 : 0 < 2 * Real.pi / r := by positivity
  have hy : M * Df / ε ≤ (2 * Real.pi / r) ^ (2 * h) := by
    rw [div_le_iff₀ hε]
    rw [le_div_iff₀ hDf0] at hLag
    rw [hDf]; linarith
  have hroot : (M * Df / ε) ^ α ≤ 2 * Real.pi / r := by
    have := Real.rpow_le_rpow (by positivity) hy hα0.le
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, hα, Nat.cast_mul, Nat.cast_ofNat,
      mul_one_div_cancel (by positivity), Real.rpow_one] at this
  have hinv : (M * Df / ε) ^ α = ((ε / (M * Df)) ^ α)⁻¹ := by
    rw [← Real.inv_rpow (by positivity), inv_div]
  rw [hinv] at hroot
  have hpos : 0 < (ε / (M * Df)) ^ α := by positivity
  have hr_le : r ≤ 2 * Real.pi * (ε / (M * Df)) ^ α := by
    rw [inv_le_iff_one_le_mul₀' hpos, mul_div_assoc', le_div_iff₀ hr0] at hroot
    linarith
  have : lam = 2 * N * r := by rw [hr]; field_simp
  have : lam ≤ bound := by
    rw [this, hbound]; nlinarith
  linarith

/-- **Interpolation on the circle with ordered nodes**:
`circ{|F| < ε} ≤ 8π N (ε / (|F s₀| (2h)!))^{1/(2h)}`. -/
theorem trig_sublevel_ord (h : ℕ) (hh : 1 ≤ h) :
    ∀ F : ℝ → ℝ, IsTrig h F → ∀ ε s0 : ℝ, 0 < ε → 0 < |F s0| →
      circ {s | |F s| < ε} ≤ ENNReal.ofReal (8 * Real.pi * (2 * h + 1) *
        (ε / (|F s0| * (2 * h).factorial)) ^ ((1 : ℝ) / (2 * h))) := by
  intro F hF ε s0 hε hM
  set A := {s | |F s| < ε} with hA
  set b := 4 * Real.pi * (2 * h + 1) * (ε / (|F s0| * (2 * h).factorial)) ^ ((1 : ℝ) / (2 * h))
    with hb
  have hb0 : 0 ≤ b := by have := Real.pi_pos; positivity
  have h1 := half_bound_ord h hh F hF ε s0 hε hM 0 (A ∩ Set.Ioc 0 Real.pi)
    (by rw [zero_add]; exact Set.inter_subset_right) (fun x hx => hx.1)
  have h2 := half_bound_ord h hh F hF ε s0 hε hM Real.pi (A ∩ Set.Ioc Real.pi (Real.pi + Real.pi))
    Set.inter_subset_right (fun x hx => hx.1)
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
    _ ≤ ENNReal.ofReal b + ENNReal.ofReal b := add_le_add h1 h2
    _ = _ := by
        rw [← ENNReal.ofReal_add hb0 hb0]; congr 1; rw [hb]; ring

end BstLean.Part66
