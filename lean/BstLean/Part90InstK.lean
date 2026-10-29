import BstLean.Part90Defs

/-!
# Part 90: the instance `modRK m 3 t v E` with the slice level `κ_p = R_p²(3 + S_p²)/2`

The slice model of Part 86 is instantiated again with the level `tauK p = R²(3 + S²)/2`
(`S = axialS`, `R = axialR` of the slice), which is a lower bound of the residual kernel on the
slice (`KernelLow3`) and satisfies `R² ≤ (2/3) tauK ≤ (4/3) R²`.
-/

namespace BstLean.Part90

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono varU Tens TSymm)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV kJ tauR polarPoint perpDir axialR axialS axialMeasure polarState lawRK)
open BstLean.Part78 (nsq frobH zv)
open BstLean.Part80 (kA FeatOpA)
open BstLean.Part82 (T3 SymT frobT trT cfun aU3 HU3)
open BstLean.Part86
open BstLean.Part89 (Ybar SliceOpF)

/-- The level `κ_p = R²(3 + S²)/2`. -/
noncomputable def tauK {m : ℕ} (p : ℝ × (Fin m → ℝ)) : ℝ :=
  axialR p.1 (radF53 p.2) ^ 2 * (3 + axialS p.1 (radF53 p.2) ^ 2) / 2

noncomputable def rhoK {m : ℕ} (p : ℝ × (Fin m → ℝ)) : ℝ := Real.sqrt (tauK p)

/-! ## Pointwise facts -/

theorem tauK_nonneg {m : ℕ} (p : ℝ × (Fin m → ℝ)) : 0 ≤ tauK p := by
  unfold tauK; positivity

theorem instK_rho {m : ℕ} : ∀ p : ℝ × (Fin m → ℝ), 0 ≤ rhoK p ∧ rhoK p ^ 2 = tauK p :=
  fun p => ⟨Real.sqrt_nonneg _, Real.sq_sqrt (tauK_nonneg p)⟩

theorem measurable_tauK {m : ℕ} : Measurable (tauK (m := m)) := by
  unfold tauK axialR axialS radF53
  fun_prop

lemma axS_sq_le {m : ℕ} (p : ℝ × (Fin m → ℝ)) : axialS p.1 (radF53 p.2) ^ 2 ≤ 1 := by
  have h := XInst.axial_sq_le p.1 (radF53 p.2)
  have := sq_nonneg (axialR p.1 (radF53 p.2))
  linarith

/-- `R² ≤ (2/3) κ`. -/
theorem R_sq_le_tauK {m : ℕ} (p : ℝ × (Fin m → ℝ)) :
    axialR p.1 (radF53 p.2) ^ 2 ≤ 2 / 3 * tauK p := by
  unfold tauK
  nlinarith [sq_nonneg (axialR p.1 (radF53 p.2)), sq_nonneg (axialS p.1 (radF53 p.2)),
    mul_nonneg (sq_nonneg (axialR p.1 (radF53 p.2))) (sq_nonneg (axialS p.1 (radF53 p.2)))]

/-- `κ ≤ 2 R²`. -/
theorem tauK_le_R_sq {m : ℕ} (p : ℝ × (Fin m → ℝ)) :
    tauK p ≤ 2 * axialR p.1 (radF53 p.2) ^ 2 := by
  unfold tauK
  nlinarith [sq_nonneg (axialR p.1 (radF53 p.2)), axS_sq_le p,
    mul_nonneg (sq_nonneg (axialR p.1 (radF53 p.2))) (sub_nonneg.mpr (axS_sq_le p))]

lemma axR_nonneg {m : ℕ} (p : ℝ × (Fin m → ℝ)) : 0 ≤ axialR p.1 (radF53 p.2) := by
  unfold axialR radF53; positivity

lemma axR_le_rhoK {m : ℕ} (p : ℝ × (Fin m → ℝ)) : axialR p.1 (radF53 p.2) ≤ rhoK p := by
  have h : axialR p.1 (radF53 p.2) ^ 2 ≤ tauK p := by
    have := R_sq_le_tauK p; have := tauK_nonneg p; linarith
  have := Real.abs_le_sqrt h
  rwa [abs_of_nonneg (axR_nonneg p)] at this

/-- Either `R = 0` or `S² + R² = 1`. -/
lemma ax_dich (a r : ℝ) : axialR a r = 0 ∨ axialS a r ^ 2 + axialR a r ^ 2 = 1 := by
  by_cases h : a ^ 2 + r ^ 2 = 0
  · left; unfold axialR; simp [h]
  · right
    unfold axialS axialR
    have hp : 0 < a ^ 2 + r ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [div_pow, div_pow, Real.sq_sqrt hp.le, ← add_div, div_self h]

/-! ## The points of a slice -/

lemma dot_polar {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : UnitV v) (p : ℝ × (Fin m → ℝ))
    (g : Fin (m + 1) → ℝ) :
    ∑ i, v i * polarState v (p, g) i = axialS p.1 (radF53 p.2) := by
  have e : polarState v (p, g) = axialS p.1 (radF53 p.2) • v +
      axialR p.1 (radF53 p.2) • perpDir v g := rfl
  have h1 : ∑ i, v i ^ 2 = 1 := hv
  have h2 := BstLean.Part56.perpDir_orth56 v g hv
  have h3 : ∑ i, v i * polarState v (p, g) i =
      axialS p.1 (radF53 p.2) * ∑ i, v i ^ 2 +
        axialR p.1 (radF53 p.2) * ∑ i, v i * perpDir v g i := by
    rw [e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h3, h1, h2]
  ring

lemma sph_polar {m : ℕ} (hm : 1 ≤ m) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (p : ℝ × (Fin m → ℝ))
    (hp : axialS p.1 (radF53 p.2) ^ 2 + axialR p.1 (radF53 p.2) ^ 2 = 1) :
    ∀ᵐ g ∂stdGauss (Fin (m + 1)), ∑ i, polarState v (p, g) i ^ 2 = 1 := by
  filter_upwards [BstLean.Part89.perp_unit hm v hv] with g hg
  have e : polarState v (p, g) = axialS p.1 (radF53 p.2) • v +
      axialR p.1 (radF53 p.2) • perpDir v g := rfl
  rw [e, XInst.comb_sq, BstLean.Part56.perpDir_orth56 v g hv, hg]
  have h1 : ∑ i, v i ^ 2 = 1 := hv
  rw [h1]
  linarith

lemma kapm_self_nonneg {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S]
    [MeasurableSpace G] (M : Mod n I J S G) (x : Fin n → ℝ) : 0 ≤ kapm M x x := by
  unfold kapm
  exact Finset.sum_nonneg fun q _ => mul_self_nonneg _

/-! ## The facts of the instance -/

/-- The slice feature operator bound with the level `κ_p`. -/
theorem instK_opF (m : ℕ) (hm : 5000 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E) (hKL : KernelLow3 (m + 1)) :
    SliceOpF (modRK m 3 t v E) (2 / 3 * (CLs 3 / (m : ℝ))) tauK := by
  have hF := BstLean.Part89.instSliceOpF m 3 t v E (by norm_num) hm hv hE
  have hK := rot_KR v hv E hE
  have hL0 := BstLean.Part89.CLs_div_nonneg m 3
  refine ⟨measurable_tauK, fun p => ⟨tauK_nonneg p, ?_, ?_⟩⟩
  · rcases ax_dich p.1 (radF53 p.2) with h0 | h1
    · refine ae_of_all _ fun g => ?_
      have : tauK p = 0 := by unfold tauK; rw [h0]; ring
      rw [this]
      exact kapm_self_nonneg _ _
    · change ∀ᵐ g ∂stdGauss (Fin (m + 1)), _
      filter_upwards [sph_polar (by omega) v hv p h1] with g hg
      have e : kapm (modRK m 3 t v E) (polarState v (p, g)) (polarState v (p, g)) =
          tauR 3 v (polarState v (p, g)) := hK _ _
      change _ ≤ kapm (modRK m 3 t v E) (polarState v (p, g)) (polarState v (p, g))
      rw [e]
      have h := hKL v hv (polarState v (p, g)) hg
      rw [dot_polar v hv p g] at h
      refine le_trans (le_of_eq ?_) h
      unfold tauK
      have : axialR p.1 (radF53 p.2) ^ 2 = 1 - axialS p.1 (radF53 p.2) ^ 2 := by linarith
      rw [this]
  · intro c
    refine ((hF.2 p).2.2 c).trans ?_
    have h1 := R_sq_le_tauK p
    have h2 : CLs 3 / (m : ℝ) * axialR p.1 (radF53 p.2) ^ 2 ≤
        2 / 3 * (CLs 3 / (m : ℝ)) * tauK p := by
      have := mul_le_mul_of_nonneg_left h1 hL0
      linarith
    exact mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg fun q _ => sq_nonneg _)

/-- Slice decorrelation at the level `(2/3) CLs 3/m`. -/
theorem instK_decor (m : ℕ) (hm : 5000 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E) (hKL : KernelLow3 (m + 1)) :
    Decor86 (modRK m 3 t v E) (2 / 3 * (CLs 3 / (m : ℝ))) := by
  have hF := instK_opF m hm t v hv E hE hKL
  have hL0 := BstLean.Part89.CLs_div_nonneg m 3
  have hS : SliceOp (modRK m 3 t v E) (2 / 3 * (CLs 3 / (m : ℝ))) :=
    fun p => ⟨tauK p, hF.2 p⟩
  exact decor86 (modRK m 3 t v E) 3 _ (XInst.regRK m 3 t v hv E) (XRotB.rot_twoPt v hv E hE) hS
    (by positivity)

/-- The kernel is at most `3 κ_p` in the slice `p`. -/
theorem instK_up (m : ℕ) (hm : 5000 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E)
    (hKU : ∀ v : Fin (m + 1) → ℝ, UnitV v → ∀ x : Fin (m + 1) → ℝ, ∑ i, x i ^ 2 = 1 →
      tauR 3 v x ≤ (1 - (∑ i, v i * x i) ^ 2) *
        (3 + 2 * (∑ i, v i * x i) ^ 2 + (∑ i, v i * x i) ^ 4)) :
    ∀ᵐ p ∂(modRK m 3 t v E).pi, ∀ᵐ g ∂(modRK m 3 t v E).ga,
      kapm (modRK m 3 t v E) ((modRK m 3 t v E).X (p, g)) ((modRK m 3 t v E).X (p, g)) ≤
        3 * tauK p := by
  have hK := rot_KR v hv E hE
  change ∀ᵐ p ∂axialMeasure t v, ∀ᵐ g ∂stdGauss (Fin (m + 1)),
    kapm (modRK m 3 t v E) (polarState v (p, g)) (polarState v (p, g)) ≤ 3 * tauK p
  filter_upwards [BstLean.Part89.axial_ne_zero t v] with p hp
  have h1 := BstLean.Part89.axial_sq_eq p.1 (radF53 p.2) hp
  filter_upwards [sph_polar (by omega) v hv p h1] with g hg
  have e : kapm (modRK m 3 t v E) (polarState v (p, g)) (polarState v (p, g)) =
      tauR 3 v (polarState v (p, g)) := hK _ _
  rw [e]
  have h := hKU v hv (polarState v (p, g)) hg
  rw [dot_polar v hv p g] at h
  refine h.trans ?_
  unfold tauK
  have hR : axialR p.1 (radF53 p.2) ^ 2 = 1 - axialS p.1 (radF53 p.2) ^ 2 := by linarith
  rw [hR]
  have hs := axS_sq_le p
  have hs0 := sq_nonneg (axialS p.1 (radF53 p.2))
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg (sub_nonneg.mpr hs)
    (add_nonneg (by norm_num : (0:ℝ) ≤ 3) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs0)))]

/-- The fourth-moment feature bound at the level `κ_p` (monotonicity). -/
theorem instK_feat4 (m : ℕ) (hm : 5000 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E)
    (h4 : ∀ (p : ℝ × (Fin m → ℝ)) (c : JR (m + 1) 3 → ℝ),
      ∫ g, (∑ q, c q * (modRK m 3 t v E).ps ((modRK m 3 t v E).X (p, g)) q) ^ 4
        ∂(modRK m 3 t v E).ga ≤
        (27 * (CLs 3 / (m : ℝ) * axialR p.1 (radF53 p.2) ^ 2)) ^ 2 * (∑ q, c q ^ 2) ^ 2) :
    ∀ (p : ℝ × (Fin m → ℝ)) (c : JR (m + 1) 3 → ℝ),
      ∫ g, (∑ q, c q * (modRK m 3 t v E).ps ((modRK m 3 t v E).X (p, g)) q) ^ 4
        ∂(modRK m 3 t v E).ga ≤
        (27 * (2 / 3 * (CLs 3 / (m : ℝ)) * tauK p)) ^ 2 * (∑ q, c q ^ 2) ^ 2 := by
  intro p c
  refine (h4 p c).trans ?_
  have hL0 := BstLean.Part89.CLs_div_nonneg m 3
  have h1 := R_sq_le_tauK p
  have h2 : CLs 3 / (m : ℝ) * axialR p.1 (radF53 p.2) ^ 2 ≤
      2 / 3 * (CLs 3 / (m : ℝ)) * tauK p := by
    have := mul_le_mul_of_nonneg_left h1 hL0
    linarith
  have h3 : 0 ≤ CLs 3 / (m : ℝ) * axialR p.1 (radF53 p.2) ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  linarith

/-- The oscillation hypothesis at the level `κ_p`, from the one at the level `R_p²`. -/
theorem instK_osc (m : ℕ) (hm : 5000 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E) :
    ∀ (ℓ : Fin (m + 1) → ℝ) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (T : T3 (m + 1))
      (A : Fin (3 + 1) → Fin (m + 1) → ℝ) (c e1 e2 e4 e0 : ℝ), 0 ≤ e1 → 0 ≤ e2 → 0 ≤ e4 →
      SliceOscM (modRK m 3 t v E) ℓ H T A c (fun p => axialR p.1 (radF53 p.2) ^ 2)
        (fun p => axialR p.1 (radF53 p.2)) e1 e2 e4 e0 →
      SliceOscM (modRK m 3 t v E) ℓ H T A c tauK rhoK e1 e2 e4 (2 * e0) := by
  intro ℓ H T A c e1 e2 e4 e0 he1 he2 he4 h
  unfold SliceOscM at h ⊢
  filter_upwards [h] with p hp
  obtain ⟨Abar, Hbar, z, hz, h0, hA, hH⟩ := hp
  have hR0 := axR_nonneg p
  have hRr := axR_le_rhoK p
  have hRt : axialR p.1 (radF53 p.2) ^ 2 ≤ tauK p := by
    have := R_sq_le_tauK p; have := tauK_nonneg p; linarith
  have htR := tauK_le_R_sq p
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hca : 0 ≤ |c| := abs_nonneg c
  have hsH : 0 ≤ Real.sqrt (frobH Hbar) := Real.sqrt_nonneg _
  have hsT : 0 ≤ Real.sqrt (frobT T) := Real.sqrt_nonneg _
  refine ⟨Abar, Hbar, z, hz, ?_, ?_, ?_⟩
  · have h1 : c ^ 2 * tauK p * z ^ 2 ≤
        c ^ 2 * (2 * axialR p.1 (radF53 p.2) ^ 2) * z ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htR hc2) (sq_nonneg z)
    nlinarith
  · refine hA.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
    have ha : e1 * (|c| * axialR p.1 (radF53 p.2)) * Real.sqrt (frobH Hbar) ≤
        e1 * (|c| * rhoK p) * Real.sqrt (frobH Hbar) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRr hca) he1) hsH
    have hb : e2 * (c ^ 2 * axialR p.1 (radF53 p.2) ^ 2) * Real.sqrt (frobT T) ≤
        e2 * (c ^ 2 * tauK p) * Real.sqrt (frobT T) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRt hc2) he2) hsT
    linarith
  · refine hH.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRr hca) he4) hsT

/-! ## The third moment of the level -/

lemma tauK_le_two {m : ℕ} (p : ℝ × (Fin m → ℝ)) : tauK p ≤ 2 := by
  have h1 := tauK_le_R_sq p
  have h2 := BstLean.Part89.instTauLe m p
  linarith

/-- `(87/100)³ ≤ E_p κ_p³`. -/
theorem instK_tau3 (m : ℕ) (hm : 5000 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E)
    (hm8 : 10000 ≤ m) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ)) :
    (87 / 100 : ℝ) ^ 3 ≤ ∫ p, tauK p ^ 3 ∂axialMeasure t v := by
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  have : IsProbabilityMeasure (axialMeasure t v) :=
    BstLean.Part56.axialMeasure_probability b v hb0 t
  have hlow2 := BstLean.Part80.pLowRK_sharp (m + 1) (by omega) v hv t ht0 htn
  have hlow4 := BstLean.Part80.pLow4RK_sharp (m + 1) (by omega) v hv t ht0 htn
  have hsl2 := XIdent.lawRK_integral_slices t v hv (fun x => (∑ i, v i * x i) ^ 2) (by fun_prop)
  have hsl4 := XIdent.lawRK_integral_slices t v hv (fun x => (∑ i, v i * x i) ^ 4) (by fun_prop)
  simp only [dot_polar v hv, integral_const, probReal_univ, one_smul] at hsl2 hsl4
  rw [hsl2] at hlow2
  rw [hsl2, hsl4] at hlow4
  have hS2int : Integrable (fun p : ℝ × (Fin m → ℝ) => axialS p.1 (radF53 p.2) ^ 2)
      (axialMeasure t v) :=
    XInst.int_bdd _ _ (BstLean.Part89.measurable_sF m) 1 fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact axS_sq_le p
  have hS4int : Integrable (fun p : ℝ × (Fin m → ℝ) => axialS p.1 (radF53 p.2) ^ 4)
      (axialMeasure t v) :=
    XInst.int_bdd _ _ (by unfold axialS radF53; fun_prop) 1 fun p => by
      rw [abs_of_nonneg (by positivity)]
      have h := axS_sq_le p
      have h0 := sq_nonneg (axialS p.1 (radF53 p.2))
      nlinarith
  have hTint : Integrable (fun p : ℝ × (Fin m → ℝ) => tauK p) (axialMeasure t v) :=
    XInst.int_bdd _ _ measurable_tauK 2 fun p => by
      rw [abs_of_nonneg (tauK_nonneg p)]; exact tauK_le_two p
  have hT3int : Integrable (fun p : ℝ × (Fin m → ℝ) => tauK p ^ 3) (axialMeasure t v) :=
    XInst.int_bdd _ _ (measurable_tauK.pow_const 3) 8 fun p => by
      rw [abs_of_nonneg (pow_nonneg (tauK_nonneg p) 3)]
      have := pow_le_pow_left₀ (tauK_nonneg p) (tauK_le_two p) 3
      norm_num at this ⊢
      exact this
  -- the mean of the level
  have hcong : ∫ p, tauK p ∂axialMeasure t v =
      ∫ p, (3 / 2 - axialS p.1 (radF53 p.2) ^ 2 - 1 / 2 * axialS p.1 (radF53 p.2) ^ 4)
        ∂axialMeasure t v := by
    apply integral_congr_ae
    filter_upwards [BstLean.Part89.axial_ne_zero t v] with p hp
    have h := BstLean.Part89.axial_sq_eq p.1 (radF53 p.2) hp
    have hR : axialR p.1 (radF53 p.2) ^ 2 = 1 - axialS p.1 (radF53 p.2) ^ 2 := by linarith
    unfold tauK
    rw [hR]
    ring
  have hmean : 87 / 100 ≤ ∫ p, tauK p ∂axialMeasure t v := by
    have hlin : ∫ p : ℝ × (Fin m → ℝ),
        (3 / 2 - axialS p.1 (radF53 p.2) ^ 2 - 1 / 2 * axialS p.1 (radF53 p.2) ^ 4)
          ∂axialMeasure t v =
        3 / 2 - (∫ p : ℝ × (Fin m → ℝ), axialS p.1 (radF53 p.2) ^ 2 ∂axialMeasure t v) -
          1 / 2 * ∫ p : ℝ × (Fin m → ℝ), axialS p.1 (radF53 p.2) ^ 4 ∂axialMeasure t v := by
      have hA : Integrable (fun p : ℝ × (Fin m → ℝ) =>
          (3 / 2 : ℝ) - axialS p.1 (radF53 p.2) ^ 2) (axialMeasure t v) :=
        (integrable_const _).sub hS2int
      have h1 := integral_sub hA (hS4int.const_mul (1 / 2))
      have h2 := integral_sub (integrable_const (3 / 2 : ℝ)) hS2int
      rw [h1, h2, integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
    rw [hcong, hlin]
    have hm' : (10000 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10000 ≤ m + 1)
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by linarith
    have h100 : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / 10000 :=
      one_div_le_one_div_of_le (by norm_num) hm'
    have hhalf : 1 / (2 * ((m + 1 : ℕ) : ℝ)) = 1 / 2 * (1 / ((m + 1 : ℕ) : ℝ)) := by
      field_simp
    rw [hhalf] at hlow4
    linarith
  -- Jensen through the tangent line of `x³` at `87/100`
  have htan : ∀ p : ℝ × (Fin m → ℝ),
      3 * (87 / 100 : ℝ) ^ 2 * tauK p - 2 * (87 / 100 : ℝ) ^ 3 ≤ tauK p ^ 3 := by
    intro p
    have h0 := tauK_nonneg p
    nlinarith [mul_nonneg (sq_nonneg (tauK p - 87 / 100))
      (by linarith : (0 : ℝ) ≤ tauK p + 2 * (87 / 100))]
  have hI2 : Integrable (fun p : ℝ × (Fin m → ℝ) =>
      3 * (87 / 100 : ℝ) ^ 2 * tauK p - 2 * (87 / 100 : ℝ) ^ 3) (axialMeasure t v) :=
    (hTint.const_mul _).sub (integrable_const _)
  have hmono := integral_mono hI2 hT3int htan
  have heq : ∫ p : ℝ × (Fin m → ℝ), (3 * (87 / 100 : ℝ) ^ 2 * tauK p - 2 * (87 / 100 : ℝ) ^ 3)
      ∂axialMeasure t v =
      3 * (87 / 100 : ℝ) ^ 2 * (∫ p : ℝ × (Fin m → ℝ), tauK p ∂axialMeasure t v) -
        2 * (87 / 100 : ℝ) ^ 3 := by
    rw [integral_sub (hTint.const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
  rw [heq] at hmono
  nlinarith

end BstLean.Part90

#print axioms BstLean.Part90.instK_rho
#print axioms BstLean.Part90.measurable_tauK
#print axioms BstLean.Part90.tauK_nonneg
#print axioms BstLean.Part90.R_sq_le_tauK
#print axioms BstLean.Part90.tauK_le_R_sq
#print axioms BstLean.Part90.instK_opF
#print axioms BstLean.Part90.instK_decor
#print axioms BstLean.Part90.instK_up
#print axioms BstLean.Part90.instK_feat4
#print axioms BstLean.Part90.instK_osc
#print axioms BstLean.Part90.instK_tau3
