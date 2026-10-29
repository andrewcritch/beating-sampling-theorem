import BstLean.Part132Quad

/-! The endpoint quotient bounds the Taylor remainder on the complete kernel interval. -/
namespace BstLean.Part205
open Real Set BstLean.Part130 BstLean.Part132

noncomputable def slopeK (r : ℝ) : ℝ := (π - Real.arccos r) / π

noncomputable def remainderK (r y : ℝ) : ℝ :=
  kappa y - kappa r - slopeK r * (y - r)

noncomputable def endpointK (r : ℝ) : ℝ :=
  (1 - kappa r - slopeK r * (1 - r)) / (1 - r) ^ 2

lemma remainder_nonneg {r y : ℝ} (hr0 : -1 < r) (hr1 : r < 1)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) : 0 ≤ remainderK r y := by
  have h := ge_of_deriv_sign
    (f := fun x => kappa x - (kappa r + slopeK r * (x - r)))
    (f' := fun x => slopeK x - slopeK r)
    (a := -1) (b := 1) (c := r)
    (by have hk := continuous_kappa; unfold slopeK; fun_prop)
    (fun x hx => by
      convert (hasDerivAt_kappa hx.1 hx.2).sub
        (((hasDerivAt_id x).sub_const r).const_mul (slopeK r) |>.const_add (kappa r))
        using 1
      · funext x; rfl
      · simp [slopeK])
    hr0.le hr1.le
    (fun x hx => by
      unfold slopeK
      exact sub_nonneg.mpr (div_le_div_of_nonneg_right
        (by linarith [Real.antitone_arccos hx.1.le]) Real.pi_pos.le))
    (fun x hx => by
      unfold slopeK
      exact sub_nonpos.mpr (div_le_div_of_nonneg_right
        (by linarith [Real.antitone_arccos hx.2.le]) Real.pi_pos.le))
    y ⟨hy0, hy1⟩
  simp only [sub_self, mul_zero, add_zero, sub_self] at h
  unfold remainderK
  linarith

lemma hasDerivAt_slopeK {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    HasDerivAt slopeK (1 / (π * √(1 - x ^ 2))) x := by
  convert ((Real.hasDerivAt_arccos hx0.ne' hx1.ne).const_sub π).div_const π
    using 1
  · rfl
  · simp only [neg_neg]
    ring

/-- Every interior interpolation point stays inside the kernel interval. -/
lemma path_interior {r y s : ℝ} (hr0 : -1 < r) (hr1 : r < 1)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    -1 < r + s * (y - r) ∧ r + s * (y - r) < 1 := by
  have h1 := mul_nonneg hs0 (sub_nonneg.mpr hy0)
  have h2 := mul_nonneg hs0 (sub_nonneg.mpr hy1)
  have h3 := mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hr0)
  have h4 := mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hr1)
  constructor <;> nlinarith

/-- The endpoint path bounds the absolute value of every other path. -/
lemma path_abs_le {r y s : ℝ} (hr : 0 ≤ r) (hy0 : -1 ≤ y) (hy1 : y ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |r + s * (y - r)| ≤ r + s * (1 - r) := by
  rw [abs_le]
  have h1 := mul_nonneg hs0 (sub_nonneg.mpr hy0)
  have h2 := mul_nonneg hs0 (sub_nonneg.mpr hy1)
  have h3 := mul_nonneg (sub_nonneg.mpr hs1) hr
  constructor <;> nlinarith

/-- Compare the second derivatives along two paths without differentiating an endpoint. -/
lemma path_curvature_le {r y s : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    1 / (π * √(1 - (r + s * (y - r)) ^ 2)) ≤
      1 / (π * √(1 - (r + s * (1 - r)) ^ 2)) := by
  have hp := path_interior (by linarith : -1 < r) hr1 (by norm_num : (-1 : ℝ) ≤ 1)
    le_rfl hs0 hs1
  have hpos : 0 < 1 - (r + s * (1 - r)) ^ 2 := by nlinarith [hp.1, hp.2]
  have hab := path_abs_le hr0 hy0 hy1 hs0 hs1.le
  have hb : 0 ≤ r + s * (1 - r) := by positivity
  have hs := sq_le_sq₀ (abs_nonneg _) hb |>.mpr hab
  rw [sq_abs] at hs
  exact one_div_le_one_div_of_le
    (mul_pos Real.pi_pos (Real.sqrt_pos.mpr hpos))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) Real.pi_pos.le)

/-- Two integrations of a nonnegative second derivative. -/
lemma two_derivative_nonneg {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hdf : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g s) s)
    (hdg : ∀ s ∈ Ioo (0 : ℝ) 1, 0 ≤ deriv g s)
    (hgd : ∀ s ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ g s)
    (hg0 : g 0 = 0) : f 0 ≤ f 1 := by
  have hm : MonotoneOn g (Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hg.continuousOn ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hgd s hs).differentiableWithinAt
    · rw [interior_Icc]
      exact hdg
  have hmf : MonotoneOn f (Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hf.continuousOn ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hdf s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hdf s hs).deriv]
      have h := hm (by norm_num) ⟨hs.1.le, hs.2.le⟩ hs.1.le
      rwa [hg0] at h
  exact hmf (by norm_num) (by norm_num) (by norm_num)

/-- The global Taylor remainder uses the exact endpoint quotient. -/
theorem global_taylor {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2)
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ remainderK r y ∧ remainderK r y ≤ endpointK r * (y - r) ^ 2 := by
  have hr : r < 1 := by linarith
  refine ⟨remainder_nonneg (by linarith) hr hy0 hy1, ?_⟩
  by_cases hdy : y = r
  · subst y
    simp [remainderK]
  have hd : y - r ≠ 0 := sub_ne_zero.mpr hdy
  have he : 1 - r ≠ 0 := by linarith
  let d := y - r
  let e := 1 - r
  let F : ℝ → ℝ := fun s =>
    remainderK r (r + s * e) / e ^ 2 - remainderK r (r + s * d) / d ^ 2
  let G : ℝ → ℝ := fun s =>
    (slopeK (r + s * e) - slopeK r) / e -
      (slopeK (r + s * d) - slopeK r) / d
  have paths : ∀ s ∈ Ioo (0 : ℝ) 1,
      (-1 < r + s * e ∧ r + s * e < 1) ∧
      (-1 < r + s * d ∧ r + s * d < 1) := by
    intro s hs
    exact ⟨path_interior (by linarith) hr (by norm_num) le_rfl hs.1.le hs.2,
      path_interior (by linarith) hr hy0 hy1 hs.1.le hs.2⟩
  have df : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt F (G s) s := by
    intro s hs
    obtain ⟨hp, hq⟩ := paths s hs
    have de := (hasDerivAt_const s r).add ((hasDerivAt_id s).mul_const e)
    have dd := (hasDerivAt_const s r).add ((hasDerivAt_id s).mul_const d)
    have dkE := (hasDerivAt_kappa hp.1 hp.2).comp s de
    have dkD := (hasDerivAt_kappa hq.1 hq.2).comp s dd
    have h := ((dkE.sub_const (kappa r)).sub
      ((de.sub_const r).const_mul (slopeK r))).div_const (e ^ 2)
    have h' := ((dkD.sub_const (kappa r)).sub
      ((dd.sub_const r).const_mul (slopeK r))).div_const (d ^ 2)
    convert h.sub h' using 1
    · rfl
    · dsimp [G, slopeK, d, e]
      field_simp
      <;> ring
  have dg : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt G
      (1 / (π * √(1 - (r + s * e) ^ 2)) -
        1 / (π * √(1 - (r + s * d) ^ 2))) s := by
    intro s hs
    obtain ⟨hp, hq⟩ := paths s hs
    have de := (hasDerivAt_const s r).add ((hasDerivAt_id s).mul_const e)
    have dd := (hasDerivAt_const s r).add ((hasDerivAt_id s).mul_const d)
    have h := (((hasDerivAt_slopeK hp.1 hp.2).comp s de).sub_const
      (slopeK r)).div_const e
    have h' := (((hasDerivAt_slopeK hq.1 hq.2).comp s dd).sub_const
      (slopeK r)).div_const d
    convert h.sub h' using 1
    · rfl
    · dsimp [d, e]
      field_simp
      <;> ring
  have hF : F 0 ≤ F 1 := two_derivative_nonneg
    (by have hk := continuous_kappa; dsimp [F, remainderK, slopeK]; fun_prop)
    (by dsimp [G, slopeK]; fun_prop) df
    (fun s hs => by
      rw [(dg s hs).deriv]
      exact sub_nonneg.mpr (path_curvature_le hr0.le hr hy0 hy1 hs.1.le hs.2))
    (fun s hs => (dg s hs).differentiableAt)
    (by simp [G])
  have h0 : F 0 = 0 := by simp [F, remainderK]
  have h1 : F 1 = endpointK r - remainderK r y / (y - r) ^ 2 := by
    have hp : r + 1 * e = 1 := by dsimp [e]; ring
    have hq : r + 1 * d = y := by dsimp [d]; ring
    dsimp [F]
    rw [hp, hq]
    simp [remainderK, endpointK, kappa_one, e, d]
  rw [h0, h1] at hF
  exact (div_le_iff₀ (sq_pos_of_ne_zero hd)).mp (by linarith)

end BstLean.Part205

#print axioms BstLean.Part205.remainder_nonneg
#print axioms BstLean.Part205.path_curvature_le
#print axioms BstLean.Part205.global_taylor
