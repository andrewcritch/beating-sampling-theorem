import BstLean.Part153All
import BstLean.Part151AllB

/-!
# Part 154: the third Poincaré fact of Lemma V: the truncated angle `φ`
Do not use `sorry`, `native_decide` or `axiom`.

`q(ξ) = √t·a₂(x(ξ))` is in the nonnegative orthant; `b` is a centre with nonnegative coordinates,
`b ≠ 0`. `v₁ = ⟨q, b̂⟩`, `v₂ = |Π_b q|`, `ρ = √(v₁² + v₂²) = |q|`, `Θ = arccos(v₁/ρ)`,
`φ = Θ·min(1, ρ/r_ϑ)` (`phiV` of Part 151). Its pointwise Lipschitz constant in `q` is at most
`1/ρ` where `ρ > r_ϑ` and at most `(1 + π/2)/r_ϑ ≤ √6.61/r_ϑ` where `ρ ≤ r_ϑ` (`ellSqV`).
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part134 (lam res sig)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT)
open BstLean.Part151 (phiV ellSqV rhoV)

/-! ## Angles in a real inner product space -/

section geoPhi

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open InnerProductGeometry

/-- The distance from `x` to the line `ℝy` is at most `|x − y|`. -/
private lemma norm_mul_sin_le_Phi (x y : V) : ‖x‖ * Real.sin (angle x y) ≤ ‖x - y‖ := by
  by_cases hy : y = 0
  · subst hy; simp [angle_zero_right]
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hs := sin_angle_mul_norm_mul_norm x y
  have h1 : Real.sin (angle x y) * (‖x‖ * ‖y‖) ≤ ‖x - y‖ * ‖y‖ := by
    rw [hs]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have e := norm_sub_sq_real x y
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, mul_pow, e]
    nlinarith [sq_nonneg (‖y‖ ^ 2 - inner ℝ x y)]
  have h2 : ‖x‖ * Real.sin (angle x y) * ‖y‖ ≤ ‖x - y‖ * ‖y‖ := by
    have e : ‖x‖ * Real.sin (angle x y) * ‖y‖ = Real.sin (angle x y) * (‖x‖ * ‖y‖) := by ring
    rw [e]; exact h1
  exact le_of_mul_le_mul_right h2 hy0

private lemma angle_le_Phi {x y : V} (h : 0 ≤ inner ℝ x y) : angle x y ≤ π / 2 := by
  by_contra hc
  exact absurd (inner_neg_iff_pi_div_two_lt_angle.mpr (not_le.mp hc)) (not_lt.mpr h)

/-- Chord and arc: `|x|·∠(x, y) ≤ (π/2)·|x − y|` if `⟨x, y⟩ ≥ 0`. -/
private lemma norm_mul_angle_le_Phi {x y : V} (h : 0 ≤ inner ℝ x y) :
    ‖x‖ * angle x y ≤ π / 2 * ‖x - y‖ := by
  have h1 := Real.mul_le_sin (angle_nonneg x y) (angle_le_Phi h)
  have h2 := norm_mul_sin_le_Phi x y
  have hπ := Real.pi_pos
  have h3 : angle x y ≤ π / 2 * Real.sin (angle x y) := by
    have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ π / 2)
    have e : π / 2 * (2 / π * angle x y) = angle x y := by field_simp
    linarith
  calc ‖x‖ * angle x y ≤ ‖x‖ * (π / 2 * Real.sin (angle x y)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = π / 2 * (‖x‖ * Real.sin (angle x y)) := by ring
    _ ≤ π / 2 * ‖x - y‖ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The sharp local form: `(|x| − |x − y|)·∠(x, y) ≤ |x − y|` if `⟨x, y⟩ ≥ 0`. -/
private lemma sub_mul_angle_le_Phi {x y : V} (h : 0 ≤ inner ℝ x y) :
    (‖x‖ - ‖x - y‖) * angle x y ≤ ‖x - y‖ := by
  have h2 := norm_mul_sin_le_Phi x y
  have h0 : 0 ≤ angle x y := angle_nonneg x y
  have h1 : angle x y ≤ π / 2 := angle_le_Phi h
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = angle x y := ⟨_, rfl⟩
  rw [← hθ] at h0 h1 h2 ⊢
  have hπ := Real.pi_pos
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, h1⟩
  have hcs : θ * Real.cos θ ≤ Real.sin θ := by
    rcases eq_or_lt_of_le h1 with e | hlt
    · rw [e, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
    · have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
      have h3 := Real.le_tan h0 hlt
      rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at h3
      exact h3
  have h1s : 1 ≤ Real.sin θ + Real.cos θ := by
    refine BstLean.Part151.le_of_sqV (by positivity) ?_
    nlinarith [mul_nonneg hs0 hc0, Real.sin_sq_add_cos_sq θ]
  have h3 : θ * (1 - Real.sin θ) ≤ Real.sin θ :=
    (mul_le_mul_of_nonneg_left (by linarith) h0).trans hcs
  nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_left h3 (norm_nonneg x),
    mul_le_mul_of_nonneg_left h2 h0]

private lemma abs_angle_sub_le_Phi (x y b : V) : |angle x b - angle y b| ≤ angle x y := by
  have h1 := angle_le_angle_add_angle x y b
  have h2 := angle_le_angle_add_angle y x b
  rw [angle_comm y x] at h2
  rw [abs_le]; constructor <;> linarith

end geoPhi

/-! ## The truncated angle as a function on `ℝ^m` -/

section vecPhi

variable {m : ℕ}

open InnerProductGeometry

private noncomputable abbrev EPhi (z : Fin m → ℝ) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 z

private lemma norm_EPhi (z : Fin m → ℝ) : ‖EPhi z‖ = nrm z := by
  rw [EuclideanSpace.norm_eq]
  simp [nrm, normSq]

private lemma inner_EPhi (z w : Fin m → ℝ) : inner ℝ (EPhi z) (EPhi w) = ∑ j, z j * w j := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, mul_comm]

private lemma norm_EPhi_sub (z w : Fin m → ℝ) : ‖EPhi z - EPhi w‖ = nrm (z - w) := by
  rw [← norm_EPhi]; rfl

/-- The angle between `z` and `b`. -/
private noncomputable def angPhi (b z : Fin m → ℝ) : ℝ := angle (EPhi z) (EPhi b)

private noncomputable def V1Phi (b z : Fin m → ℝ) : ℝ := nrm b * lam b z

private noncomputable def V2Phi (b z : Fin m → ℝ) : ℝ := nrm (res b z)

private lemma lam_smul_Phi (b : Fin m → ℝ) (s : ℝ) (h : Fin m → ℝ) :
    lam b (s • h) = s * lam b h := by
  unfold lam
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]

private lemma res_smul_Phi (b : Fin m → ℝ) (s : ℝ) (h : Fin m → ℝ) :
    res b (s • h) = s • res b h := by
  unfold res
  rw [lam_smul_Phi, smul_sub, smul_smul]

private lemma pyth_Phi {b : Fin m → ℝ} (hb : normSq b ≠ 0) (z : Fin m → ℝ) :
    normSq z = normSq b * lam b z ^ 2 + normSq (res b z) := by
  have hb' : b ≠ 0 := by rintro rfl; exact hb (by simp [normSq])
  have ho := BstLean.Part134.res_orth hb' z
  have hr : ∀ j, res b z j = z j - lam b z * b j := fun j => by simp [res]
  have e : ∀ j, z j ^ 2 =
      b j ^ 2 * lam b z ^ 2 + res b z j ^ 2 + 2 * lam b z * (res b z j * b j) := by
    intro j; rw [hr]; ring
  show ∑ j, z j ^ 2 = (∑ j, b j ^ 2) * lam b z ^ 2 + ∑ j, res b z j ^ 2
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ho]
  ring

private lemma rho_Phi {b : Fin m → ℝ} (hb : normSq b ≠ 0) (z : Fin m → ℝ) :
    rhoV (V1Phi b) (V2Phi b) z = nrm z := by
  unfold rhoV V1Phi V2Phi
  rw [BstLean.Part153.nrm_sq, mul_pow, BstLean.Part153.nrm_sq, ← pyth_Phi hb]
  rfl

private lemma theta_Phi {b : Fin m → ℝ} (hb : normSq b ≠ 0) (z : Fin m → ℝ) :
    BstLean.Part151.thetaV (V1Phi b) (V2Phi b) z = angPhi b z := by
  have hnb : nrm b ≠ 0 := by
    intro h0
    apply hb
    rw [← BstLean.Part153.nrm_sq, h0]; simp
  unfold BstLean.Part151.thetaV angPhi angle
  rw [rho_Phi hb, inner_EPhi, norm_EPhi, norm_EPhi]
  congr 1
  unfold V1Phi lam
  rw [← BstLean.Part153.nrm_sq b]
  have e : nrm b * ((∑ j, z j * b j) / nrm b ^ 2) = (∑ j, z j * b j) / nrm b := by
    field_simp
  rw [e, div_div, mul_comm]

private lemma phi_eq_Phi {b : Fin m → ℝ} (hb : normSq b ≠ 0) (γ ϑ : ℝ) (z : Fin m → ℝ) :
    phiV γ ϑ (V1Phi b) (V2Phi b) z = angPhi b z * min 1 (nrm z / BstLean.Part151.rV γ ϑ) := by
  unfold phiV
  rw [theta_Phi hb, rho_Phi hb]

private lemma ell_eq_Phi {b : Fin m → ℝ} (hb : normSq b ≠ 0) (γ ϑ : ℝ) (z : Fin m → ℝ) :
    ellSqV γ ϑ (V1Phi b) (V2Phi b) z =
      if BstLean.Part151.rV γ ϑ < nrm z then 1 / nrm z ^ 2
      else 661 / 100 / BstLean.Part151.rV γ ϑ ^ 2 := by
  unfold ellSqV
  rw [rho_Phi hb]

private lemma angPhi_mem {b z : Fin m → ℝ} (hb0 : ∀ j, 0 ≤ b j) (hz : ∀ j, 0 ≤ z j) :
    0 ≤ angPhi b z ∧ angPhi b z ≤ π / 2 :=
  ⟨angle_nonneg _ _, angle_le_Phi (by
    rw [inner_EPhi]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (hb0 j))⟩

private lemma facts_Phi (b : Fin m → ℝ) {z z' : Fin m → ℝ} (hz : ∀ j, 0 ≤ z j)
    (hz' : ∀ j, 0 ≤ z' j) :
    ∃ θ : ℝ, 0 ≤ θ ∧ |angPhi b z' - angPhi b z| ≤ θ ∧ nrm z * θ ≤ π / 2 * nrm (z' - z) ∧
      (nrm z - nrm (z' - z)) * θ ≤ nrm (z' - z) ∧ |nrm z' - nrm z| ≤ nrm (z' - z) := by
  have hi : 0 ≤ inner ℝ (EPhi z) (EPhi z') := by
    rw [inner_EPhi]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hz j) (hz' j)
  have hd : ‖EPhi z - EPhi z'‖ = nrm (z' - z) := by
    rw [norm_sub_rev, norm_EPhi_sub]
  refine ⟨angle (EPhi z) (EPhi z'), angle_nonneg _ _, ?_, ?_, ?_, ?_⟩
  · have h := abs_angle_sub_le_Phi (EPhi z') (EPhi z) (EPhi b)
    rw [angle_comm (EPhi z') (EPhi z)] at h
    exact h
  · have h := norm_mul_angle_le_Phi hi
    rwa [hd, norm_EPhi] at h
  · have h := sub_mul_angle_le_Phi hi
    rwa [hd, norm_EPhi] at h
  · have h := abs_norm_sub_norm_le (EPhi z') (EPhi z)
    rwa [norm_EPhi_sub, norm_EPhi, norm_EPhi] at h

/-- The decomposition `Δ(Θ·g) = ΔΘ·g + Θ′·Δg`. -/
private lemma core_Phi {a a' θ R R' d r : ℝ} (hr : 0 < r) (ha' : 0 ≤ a') (ha'2 : a' ≤ π / 2)
    (hθ : 0 ≤ θ) (hab : |a' - a| ≤ θ) (hR : 0 ≤ R) (hRR : |R' - R| ≤ d) :
    |a' * min 1 (R' / r) - a * min 1 (R / r)| ≤ (R * θ + π / 2 * d) / r := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hRR
  have hπ := Real.pi_pos
  have hg0 : 0 ≤ min 1 (R / r) := le_min zero_le_one (div_nonneg hR hr.le)
  have hg1 : min 1 (R / r) ≤ R / r := min_le_right _ _
  have hgg : |min 1 (R' / r) - min 1 (R / r)| ≤ d / r := by
    have h := abs_min_sub_min_le_max 1 (R' / r) 1 (R / r)
    rw [sub_self, abs_zero, ← sub_div, abs_div, abs_of_pos hr] at h
    have h' : |R' - R| / r ≤ d / r := div_le_div_of_nonneg_right hRR hr.le
    exact h.trans (max_le (div_nonneg hd0 hr.le) h')
  have e : a' * min 1 (R' / r) - a * min 1 (R / r) =
      (a' - a) * min 1 (R / r) + a' * (min 1 (R' / r) - min 1 (R / r)) := by ring
  rw [e]
  have hA : |(a' - a) * min 1 (R / r)| ≤ θ * (R / r) := by
    rw [abs_mul, abs_of_nonneg hg0]
    exact mul_le_mul hab hg1 hg0 hθ
  have hB : |a' * (min 1 (R' / r) - min 1 (R / r))| ≤ π / 2 * (d / r) := by
    rw [abs_mul, abs_of_nonneg ha']
    exact mul_le_mul ha'2 hgg (abs_nonneg _) (by positivity)
  have hC : θ * (R / r) + π / 2 * (d / r) = (R * θ + π / 2 * d) / r := by ring
  have hD := abs_add_le ((a' - a) * min 1 (R / r)) (a' * (min 1 (R' / r) - min 1 (R / r)))
  linarith

/-- (h1): `φ` is Lipschitz with the constant `π/r` on the orthant. -/
private lemma glob_Phi {b : Fin m → ℝ} (hb0 : ∀ j, 0 ≤ b j) {r : ℝ} (hr : 0 < r)
    {z z' : Fin m → ℝ} (hz : ∀ j, 0 ≤ z j) (hz' : ∀ j, 0 ≤ z' j) :
    |angPhi b z' * min 1 (nrm z' / r) - angPhi b z * min 1 (nrm z / r)| ≤
      π / r * nrm (z' - z) := by
  obtain ⟨θ, hθ, hab, h1, -, hRR⟩ := facts_Phi b hz hz'
  have hc := core_Phi hr (angPhi_mem hb0 hz').1 (angPhi_mem hb0 hz').2 hθ hab
    (BstLean.Part153.nrm_nonneg z) hRR
  refine hc.trans ?_
  rw [div_le_iff₀ hr]
  have e : π / r * nrm (z' - z) * r = π * nrm (z' - z) := by field_simp
  rw [e]; linarith

/-- (h2) at any point: the local constant `(1 + π/2)/r + δ`. -/
private lemma small_Phi {b : Fin m → ℝ} (hb0 : ∀ j, 0 ≤ b j) {r : ℝ} (hr : 0 < r)
    {z : Fin m → ℝ} (hz : ∀ j, 0 ≤ z j) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ z' : Fin m → ℝ, (∀ j, 0 ≤ z' j) → nrm (z' - z) < ρ₀ →
      |angPhi b z' * min 1 (nrm z' / r) - angPhi b z * min 1 (nrm z / r)| ≤
        ((1 + π / 2) / r + δ) * nrm (z' - z) := by
  have hπ := Real.pi_pos
  have hπ4 : π ≤ 4 := Real.pi_le_four
  have hR0 := BstLean.Part153.nrm_nonneg z
  rcases eq_or_lt_of_le hR0 with hR | hR
  · refine ⟨1, one_pos, fun z' hz' _ => ?_⟩
    obtain ⟨θ, hθ, hab, h1, -, hRR⟩ := facts_Phi b hz hz'
    have hc := core_Phi hr (angPhi_mem hb0 hz').1 (angPhi_mem hb0 hz').2 hθ hab hR0 hRR
    refine hc.trans ?_
    have hd0 := BstLean.Part153.nrm_nonneg (z' - z)
    rw [← hR, zero_mul, zero_add, div_le_iff₀ hr]
    have e : ((1 + π / 2) / r + δ) * nrm (z' - z) * r =
        (1 + π / 2) * nrm (z' - z) + δ * r * nrm (z' - z) := by field_simp
    rw [e]
    have : 0 ≤ δ * r * nrm (z' - z) := by positivity
    linarith
  · refine ⟨δ * nrm z * r / 2, by positivity, fun z' hz' hd => ?_⟩
    obtain ⟨θ, hθ, hab, h1, h2, hRR⟩ := facts_Phi b hz hz'
    have hc := core_Phi hr (angPhi_mem hb0 hz').1 (angPhi_mem hb0 hz').2 hθ hab hR0 hRR
    refine hc.trans ?_
    have hd0 := BstLean.Part153.nrm_nonneg (z' - z)
    obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = nrm (z' - z) := ⟨_, rfl⟩
    obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = nrm z := ⟨_, rfl⟩
    rw [← hdd] at hd hd0 h1 h2 ⊢
    rw [← hRd] at hd h1 h2 hR ⊢
    -- `d·θ ≤ d·δ·r`
    have h3 : d * (R * θ) ≤ d * (π / 2 * d) := mul_le_mul_of_nonneg_left h1 hd0
    have h4 : R * (d * θ) ≤ R * (d * (δ * r)) := by
      have h5 : π / 2 * d ≤ R * (δ * r) := by nlinarith
      have h6 : d * (π / 2 * d) ≤ d * (R * (δ * r)) := mul_le_mul_of_nonneg_left h5 hd0
      nlinarith
    have h7 : d * θ ≤ d * (δ * r) := le_of_mul_le_mul_left h4 hR
    rw [div_le_iff₀ hr]
    have e : ((1 + π / 2) / r + δ) * d * r = (1 + π / 2) * d + δ * r * d := by field_simp
    rw [e]
    nlinarith

/-- (h2) where `|z| > r`: the local constant `1/|z| + δ`. -/
private lemma big_Phi {b : Fin m → ℝ} {r : ℝ} (hr : 0 < r)
    {z : Fin m → ℝ} (hz : ∀ j, 0 ≤ z j) (hzr : r < nrm z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ z' : Fin m → ℝ, (∀ j, 0 ≤ z' j) → nrm (z' - z) < ρ₀ →
      |angPhi b z' * min 1 (nrm z' / r) - angPhi b z * min 1 (nrm z / r)| ≤
        (1 / nrm z + δ) * nrm (z' - z) := by
  have hR : 0 < nrm z := hr.trans hzr
  refine ⟨min (nrm z - r) (min (nrm z / 2) (δ * nrm z ^ 2 / 2)),
    lt_min (by linarith) (lt_min (by positivity) (by positivity)), fun z' hz' hd => ?_⟩
  obtain ⟨θ, hθ, hab, -, h2, hRR⟩ := facts_Phi b hz hz'
  have hd1 : nrm (z' - z) < nrm z - r := hd.trans_le (min_le_left _ _)
  have hd2 : nrm (z' - z) < nrm z / 2 :=
    hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : nrm (z' - z) < δ * nrm z ^ 2 / 2 :=
    hd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hd0 := BstLean.Part153.nrm_nonneg (z' - z)
  have hz'r : r < nrm z' := by
    have := (abs_le.mp hRR).1
    linarith
  have g1 : min 1 (nrm z / r) = 1 := min_eq_left ((one_le_div hr).mpr hzr.le)
  have g2 : min 1 (nrm z' / r) = 1 := min_eq_left ((one_le_div hr).mpr hz'r.le)
  rw [g1, g2, mul_one, mul_one]
  refine hab.trans ?_
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = nrm (z' - z) := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = nrm z := ⟨_, rfl⟩
  rw [← hdd] at hd2 hd3 hd0 h2 ⊢
  rw [← hRd] at hd2 hd3 h2 hR ⊢
  -- `(1/R + δ)(R − d) ≥ 1`
  have h3 : 1 ≤ (1 / R + δ) * (R - d) := by
    have e : (1 / R + δ) * (R - d) = 1 - d / R + δ * (R - d) := by field_simp
    rw [e]
    have h4 : d / R ≤ δ * R / 2 := by
      rw [div_le_iff₀ hR]; nlinarith
    nlinarith
  have h5 : θ * 1 ≤ θ * ((1 / R + δ) * (R - d)) := mul_le_mul_of_nonneg_left h3 hθ
  have h6 : 0 ≤ 1 / R + δ := by positivity
  have h7 := mul_le_mul_of_nonneg_left h2 h6
  nlinarith

private lemma meas_nrm_Phi : Measurable (fun z : Fin m → ℝ => nrm z) := by
  unfold nrm normSq
  fun_prop

end vecPhi

/-- **The Poincaré fact for the truncated angle** (Lemma S, second assertion, for `φ`):
`Var_ξ φ ≤ E_ξ[X·ℓ_φ²]`, `X(ξ) = t·τ²·‖𝒥(x)Π_x‖_op²/|y|²`. -/
theorem phi_poincare {n m : ℕ} (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ}
    (hb : normSq b ≠ 0) (hb0 : ∀ j, 0 ≤ b j) {γ ϑ : ℝ} (hγ : 0 < γ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) :
    ∫ ξ, (phiV γ ϑ
          (fun ξ => √(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ξ))))
          (fun ξ => sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ξ -
        ∫ ζ, phiV γ ϑ
          (fun ξ => √(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ξ))))
          (fun ξ => sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ζ
            ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      ∫ ξ, (2 / (m : ℝ) * τ ^ 2 * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
          (normSq (c + τ • ξ))⁻¹)) *
        ellSqV γ ϑ
          (fun ξ => √(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ξ))))
          (fun ξ => sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ξ
        ∂stdGauss (Fin n) := by
  have hr : 0 < BstLean.Part151.rV γ ϑ := mul_pos (Real.sqrt_pos.mpr hγ) (by linarith)
  have hst0 : 0 ≤ √(2 / (m : ℝ)) := Real.sqrt_nonneg _
  have hπ := Real.pi_pos
  -- the pointwise constant
  have hell0 : ∀ z : Fin m → ℝ, 0 ≤ ellSqV γ ϑ (V1Phi b) (V2Phi b) z := by
    intro z
    rw [ell_eq_Phi hb]
    split_ifs <;> positivity
  have hellb : ∀ z : Fin m → ℝ, ellSqV γ ϑ (V1Phi b) (V2Phi b) z ≤
      661 / 100 / BstLean.Part151.rV γ ϑ ^ 2 := by
    intro z
    rw [ell_eq_Phi hb]
    split_ifs with h
    · have h1 : 1 / nrm z ^ 2 ≤ 1 / BstLean.Part151.rV γ ϑ ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hr.le h.le 2)
      refine h1.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    · exact le_rfl
  have hmeas : Measurable (fun z : Fin m → ℝ => √(ellSqV γ ϑ (V1Phi b) (V2Phi b) z)) := by
    have e : (fun z : Fin m → ℝ => ellSqV γ ϑ (V1Phi b) (V2Phi b) z) = fun z =>
        if BstLean.Part151.rV γ ϑ < nrm z then 1 / nrm z ^ 2
        else 661 / 100 / BstLean.Part151.rV γ ϑ ^ 2 := funext fun z => ell_eq_Phi hb γ ϑ z
    have h1 : Measurable (fun z : Fin m → ℝ => ellSqV γ ϑ (V1Phi b) (V2Phi b) z) := by
      rw [e]
      exact Measurable.ite (measurableSet_lt measurable_const meas_nrm_Phi)
        (measurable_const.div (meas_nrm_Phi.pow_const 2)) measurable_const
    exact h1.sqrt
  obtain ⟨-, -, hv⟩ := BstLean.Part153.lemmaS_loc_meas_sl hn A₁ A₂ c hτ
    (φ := phiV γ ϑ (V1Phi b) (V2Phi b))
    (ℓ := fun z => √(ellSqV γ ϑ (V1Phi b) (V2Phi b) z))
    (fun _ => ⟨π / BstLean.Part151.rV γ ϑ, by positivity, fun u hu v hv _ _ => by
      rw [phi_eq_Phi hb, phi_eq_Phi hb]
      exact glob_Phi hb0 hr hv hu⟩)
    (by
      intro z hz δ hδ
      by_cases hzr : BstLean.Part151.rV γ ϑ < nrm z
      · obtain ⟨ρ₀, hρ₀, h⟩ := big_Phi (b := b) hr hz hzr hδ
        refine ⟨ρ₀, hρ₀, fun z' hz' hd => ?_⟩
        have hR : 0 < nrm z := hr.trans hzr
        have e : √(ellSqV γ ϑ (V1Phi b) (V2Phi b) z) = 1 / nrm z := by
          rw [ell_eq_Phi hb]
          simp only [hzr, ↓reduceIte]
          rw [← _root_.one_div_pow, Real.sqrt_sq (by positivity)]
        rw [phi_eq_Phi hb, phi_eq_Phi hb]
        show _ ≤ (√(ellSqV γ ϑ (V1Phi b) (V2Phi b) z) + δ) * _
        rw [e]
        exact h z' hz' hd
      · obtain ⟨ρ₀, hρ₀, h⟩ := small_Phi hb0 hr hz hδ
        refine ⟨ρ₀, hρ₀, fun z' hz' hd => ?_⟩
        have e : (1 + π / 2) / BstLean.Part151.rV γ ϑ ≤
            √(ellSqV γ ϑ (V1Phi b) (V2Phi b) z) := by
          rw [ell_eq_Phi hb]
          simp only [hzr, ↓reduceIte]
          rw [Real.le_sqrt' (by positivity), div_pow]
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          have := Real.pi_lt_d4
          nlinarith
        rw [phi_eq_Phi hb, phi_eq_Phi hb]
        refine (h z' hz' hd).trans ?_
        exact mul_le_mul_of_nonneg_right (by linarith) (BstLean.Part153.nrm_nonneg _))
    (fun z _ => Real.sqrt_nonneg _) hmeas
    (fun _ => ⟨√(661 / 100 / BstLean.Part151.rV γ ϑ ^ 2), fun z _ _ =>
      Real.sqrt_le_sqrt (hellb z)⟩)
  -- the two coordinates
  have k1 : ∀ ξ : Fin n → ℝ,
      √(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ξ))) =
        V1Phi b (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) := by
    intro ξ
    unfold V1Phi
    rw [lam_smul_Phi]
    show _ = √(normSq b) * _
    ring
  have k2 : ∀ ξ : Fin n → ℝ, sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ξ))) =
        V2Phi b (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) := by
    intro ξ
    unfold V2Phi
    rw [res_smul_Phi, BstLean.Part153.nrm_smul, abs_of_nonneg hst0]
    rfl
  have kφ : ∀ ξ : Fin n → ℝ, phiV γ ϑ
        (fun ξ => √(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ξ))))
        (fun ξ => sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ξ =
      phiV γ ϑ (V1Phi b) (V2Phi b) (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) := by
    intro ξ
    simp only [phiV, BstLean.Part151.thetaV, rhoV, k1, k2]
  have kℓ : ∀ ξ : Fin n → ℝ, ellSqV γ ϑ
        (fun ξ => √(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ξ))))
        (fun ξ => sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ξ =
      √(ellSqV γ ϑ (V1Phi b) (V2Phi b)
        (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ^ 2 := by
    intro ξ
    rw [Real.sq_sqrt (hell0 _)]
    simp only [ellSqV, rhoV, k1, k2]
    rfl
  simp only [kφ, kℓ]
  refine hv.trans (le_of_eq ?_)
  rw [← integral_const_mul]
  congr 1
  funext ξ
  ring

end BstLean.Part154
