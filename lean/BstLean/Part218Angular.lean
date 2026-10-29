import BstLean.Part159Kap

/-! A calculus proof of the quartic envelope for the even ReLU kernel. -/
namespace BstLean.Part218
open Real Set
open BstLean.Part130 BstLean.Part132 BstLean.Part159

noncomputable def angularG (x : ℝ) : ℝ := kappa x - 1 / π - x / 2
noncomputable def angularF (x : ℝ) : ℝ := √(1 - x ^ 2) + x * arcsin x - 1 - x ^ 2 / 2
noncomputable def angularN (x : ℝ) : ℝ := 4 - 4 * √(1 - x ^ 2) - 3 * x * arcsin x + x ^ 2
noncomputable def angularD (x : ℝ) : ℝ := x / √(1 - x ^ 2) - 3 * arcsin x + 2 * x

lemma angularF_eq (x : ℝ) : angularF x = π * angularG x - x ^ 2 / 2 := by
  unfold angularF angularG
  rw [kappa_arcsin]
  field_simp
  ring

lemma angularG_even (x : ℝ) : angularG (-x) = angularG x := by
  unfold angularG
  rw [kappa_arcsin, kappa_arcsin]
  simp only [neg_sq, arcsin_neg]
  field_simp
  ring

lemma angular_derivatives {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt angularF (arcsin x - x) x ∧
    HasDerivAt angularN (angularD x) x ∧
    HasDerivAt angularD
      ((1 - √(1 - x ^ 2)) ^ 2 * (2 * √(1 - x ^ 2) + 1) / (√(1 - x ^ 2)) ^ 3) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith
  have hs : 0 < √(1 - x ^ 2) := sqrt_pos.mpr hp
  have hsq := sq_sqrt hp.le
  have dq : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have ds := dq.sqrt hp.ne'
  have da := hasDerivAt_arcsin (by linarith : x ≠ -1) hx1.ne
  have df := ((ds.add ((hasDerivAt_id x).mul da)).sub_const 1).sub
    ((hasDerivAt_pow 2 x).div_const 2)
  have dn := (((ds.const_mul 4).const_sub 4).sub
    (((hasDerivAt_id x).const_mul 3).mul da)).add (hasDerivAt_pow 2 x)
  have dd := (((hasDerivAt_id x).div ds hs.ne').sub (da.const_mul 3)).add
    ((hasDerivAt_id x).const_mul 2)
  change HasDerivAt angularF _ x at df
  change HasDerivAt angularN _ x at dn
  change HasDerivAt angularD _ x at dd
  refine ⟨?_, ?_, ?_⟩
  · convert df using 1
    dsimp only [id_eq]
    field_simp
    ring
  · convert dn using 1
    dsimp [angularD]
    field_simp
    ring
  · convert dd using 1
    dsimp only [id_eq]
    field_simp
    nlinarith [hsq]

lemma angularD_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 ≤ angularD x := by
  have hc : ContinuousOn angularD (Icc 0 x) := by
    unfold angularD
    apply ContinuousOn.add
    · apply ContinuousOn.sub
      · exact continuousOn_id.div (by fun_prop) (fun t ht =>
          (sqrt_pos.mpr (by nlinarith [ht.1, ht.2] : 0 < 1 - t ^ 2)).ne')
      · fun_prop
    · fun_prop
  have hmono : MonotoneOn angularD (Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc
    · rw [interior_Icc]
      intro t ht
      exact (angular_derivatives ht.1.le (lt_of_lt_of_le ht.2 hx1.le)).2.2.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(angular_derivatives ht.1.le (lt_of_lt_of_le ht.2 hx1.le)).2.2.deriv]
      positivity
  have h := hmono ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
  simpa [angularD] using h

lemma angularN_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ angularN x := by
  have hmono : MonotoneOn angularN (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · unfold angularN; fun_prop
    · rw [interior_Icc]
      intro t ht
      exact (angular_derivatives ht.1.le ht.2).2.1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(angular_derivatives ht.1.le ht.2).2.1.deriv]
      exact angularD_nonneg ht.1.le ht.2
  have h := hmono ⟨le_rfl, zero_le_one⟩ ⟨hx0, hx1⟩ hx0
  simpa [angularN] using h

lemma angularF_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    angularF x ≤ (π / 2 - 3 / 2) * x ^ 4 := by
  rcases hx0.eq_or_lt with hx | hx
  · rw [← hx]; simp [angularF]
  have hmono : MonotoneOn (fun t => angularF t / t ^ 4) (Icc x 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · apply ContinuousOn.div
      · unfold angularF; fun_prop
      · fun_prop
      · intro t ht; exact pow_ne_zero _ (ne_of_gt (hx.trans_le ht.1))
    · rw [interior_Icc]
      intro t ht
      exact (((angular_derivatives (hx.trans ht.1).le ht.2).1).div
        (hasDerivAt_pow 4 t) (pow_ne_zero _ (hx.trans ht.1).ne')).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have ht0 := hx.trans ht.1
      have hd := ((angular_derivatives ht0.le ht.2).1).div
        (hasDerivAt_pow 4 t) (pow_ne_zero _ ht0.ne')
      change HasDerivAt (fun t => angularF t / t ^ 4) _ t at hd
      rw [hd.deriv]
      have he : ((arcsin t - t) * t ^ 4 - angularF t * (4 * t ^ (4 - 1))) / (t ^ 4) ^ 2 =
          angularN t / t ^ 5 := by
        unfold angularF angularN
        field_simp
        ring
      norm_num only [Nat.cast_ofNat] at *
      rw [he]
      exact div_nonneg (angularN_nonneg ht0.le ht.2.le) (pow_nonneg ht0.le _)
  have h := hmono ⟨le_rfl, hx1⟩ ⟨hx1, le_rfl⟩ hx1
  have he : angularF 1 / (1 : ℝ) ^ 4 = π / 2 - 3 / 2 := by norm_num [angularF]; ring
  change angularF x / x ^ 4 ≤ angularF 1 / (1 : ℝ) ^ 4 at h
  rw [he] at h
  exact (div_le_iff₀ (pow_pos hx 4)).mp h

/-- The paper's sharp quartic envelope holds on the complete cosine interval. -/
theorem angularG_envelope {x : ℝ} (hx : |x| ≤ 1) :
    x ^ 2 / (2 * π) ≤ angularG x ∧
    angularG x ≤ x ^ 2 / (2 * π) + (1 / 2 - 3 / (2 * π)) * x ^ 4 := by
  have hp := pi_pos
  have he : angularG |x| = angularG x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, angularG_even]
  have hlow := kappa_ge_poly (abs_nonneg x) hx
  have hhigh := angularF_upper (abs_nonneg x) hx
  rw [angularF_eq, he] at hhigh
  have hdef : kappa |x| = angularG x + 1 / π + |x| / 2 := by rw [← he]; unfold angularG; ring
  rw [hdef] at hlow
  have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have h4 : |x| ^ 4 = x ^ 4 := by
    calc
      _ = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  rw [h2, h4] at hhigh hlow
  constructor
  · have h := div_nonneg (by positivity : 0 ≤ |x| ^ 6 / 80 + x ^ 4 / 24) hp.le
    field_simp at hlow ⊢
    nlinarith [pow_nonneg (abs_nonneg x) 6, pow_nonneg (abs_nonneg x) 4]
  · field_simp at hhigh ⊢
    nlinarith

end BstLean.Part218
#print axioms BstLean.Part218.angularG_envelope
