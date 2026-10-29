import BstLean.Part162LSs

/-! The cutoff proof retains an arbitrary proved radial moment bound.
This proof extends Part162's cutoff and limit argument without changing Part162. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Filter Topology Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq gradSq_le measurable_gradSq)
open BstLean.Part161 (momN momN_nonneg momN_pow mink4)
open BstLean.Part162
variable {ι : Type} [Fintype ι]
variable {H₁ : (ι → ℝ) → ℝ} {L : ℝ}

theorem ls_eps_radius [DecidableEq ι] [Nonempty ι] (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {q : ℕ} (hq : 1 ≤ q)
    (hqk : 2 * q < Fintype.card ι) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ ε : ℝ, (∫ Z, (if ε < radF53 Z then (radF53 Z ^ (2 * q))⁻¹ else 0)
      ∂stdGauss ι) ≤ R ^ (2 * q)) {ε : ℝ} (hε : 0 < ε) :
    momN (stdGauss ι) (2 * q) (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι) ≤
      2 * L * ((stdGauss ι).real {v | radF53 v ≤ ε}) ^ (((2 * q : ℕ) : ℝ)⁻¹) +
      cLS q * (momN (stdGauss ι) (2 * q) (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
          R +
        2 * L / ε * ((stdGauss ι).real {v | radF53 v ≤ ε}) ^ (((2 * q : ℕ) : ℝ)⁻¹)) +
      2 * L * (stdGauss ι).real {v | radF53 v ≤ ε} := by
  set γ := stdGauss ι with hγ
  have hp0 : 2 * q ≠ 0 := by omega
  have hc := hL.continuous hL0
  set G : (ι → ℝ) → ℝ := fun v => H₁ (unitF53 v) with hGd
  have mG : Measurable G := hc.measurable.comp measurable_unitF
  have bG : ∀ v, |G v| ≤ L := hom_unit_bound hL0 hL hhom
  set m := ∫ v, G v ∂γ with hm
  have hmL : |m| ≤ L := by
    rw [hm]; refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |G v| ∂γ ≤ ∫ _v, L ∂γ :=
          integral_mono (intB mG.abs (M := L) fun v => by rw [abs_abs]; exact bG v)
            (integrable_const _) bG
      _ = L := by simp
  set g := gtr H₁ ε with hgd
  have hgL := gtr_lip hL0 hL hhom hε
  have hgc : Continuous g := hgL.continuous (by positivity)
  have mg : Measurable g := hgc.measurable
  have bg : ∀ v, |g v| ≤ L := gtr_abs_le hL0 hL hhom hε
  set mε := ∫ v, g v ∂γ with hmε
  have hmεL : |mε| ≤ L := by
    rw [hmε]; refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |g v| ∂γ ≤ ∫ _v, L ∂γ :=
          integral_mono (intB mg.abs (M := L) fun v => by rw [abs_abs]; exact bg v)
            (integrable_const _) bg
      _ = L := by simp
  set S := {v : ι → ℝ | radF53 v ≤ ε} with hS
  have mS : MeasurableSet S := measurableSet_le measurable_radF measurable_const
  set β := γ.real S with hβ
  have hβ0 : 0 ≤ β := measureReal_nonneg
  set c := cLS q with hcd
  have hc0 : 0 ≤ c := cLS_nonneg q
  -- `|G − g| ≤ 2L·1_S`
  have hGg : ∀ v, |G v - g v| ≤ S.indicator (fun _ => 2 * L) v := fun v => by
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv]
      exact (abs_sub _ _).trans (by linarith [bG v, bg v])
    · rw [Set.indicator_of_notMem hv]
      have hv' : ε < radF53 v := lt_of_not_ge hv
      rw [hgd, gtr_eq_far hhom hε hv', hGd]; simp
  have iInd : ∀ C : ℝ, Integrable (S.indicator (fun _ => C)) γ := fun C =>
    (integrable_const C).indicator mS
  have intInd : ∀ C : ℝ, ∫ v, S.indicator (fun _ => C) v ∂γ = β * C := fun C => by
    rw [integral_indicator mS, setIntegral_const, smul_eq_mul]
  -- Step 4: the mean shift
  have hb3 : |mε - m| ≤ 2 * L * β := by
    rw [hmε, hm, ← integral_sub (intB mg bg) (intB mG bG)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |g v - G v| ∂γ ≤ ∫ v, S.indicator (fun _ => 2 * L) v ∂γ :=
          integral_mono ((intB mg bg).sub (intB mG bG)).abs (iInd _)
            fun v => by rw [abs_sub_comm]; exact hGg v
      _ = 2 * L * β := by rw [intInd]; ring
  -- Step 1: Minkowski for `G − m = (G − g) + (g − mε) + (mε − m)`
  set X := momN γ (2 * q) (fun v => G v - m) with hX
  set b2 := momN γ (2 * q) (fun v => g v - mε) with hb2
  have hX0 : 0 ≤ X := momN_nonneg _ _ _
  have hb20 : 0 ≤ b2 := momN_nonneg _ _ _
  have hmk1 := mink4 γ (2 * q) (g1 := fun v => |G v - g v|) (g2 := fun v => |g v - mε|)
    (g3 := fun _ => |mε - m|) (g4 := fun _ => 0) (mG.sub mg).abs (mg.sub_const _).abs
    measurable_const measurable_const (fun v => abs_nonneg _) (fun v => abs_nonneg _)
    (fun _ => abs_nonneg _) (fun _ => le_rfl) (M := 2 * L)
    (fun v => (abs_sub _ _).trans (by linarith [bG v, bg v]))
    (fun v => (abs_sub _ _).trans (by linarith [bg v]))
    (fun _ => (abs_sub _ _).trans (by linarith)) (fun _ => by positivity)
    (b1 := 2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹)) (b2 := b2) (b3 := |mε - m|) (b4 := 0)
    (by positivity) hb20 (abs_nonneg _) le_rfl
    (by
      rw [mul_pow, Real.rpow_inv_natCast_pow hβ0 hp0]
      calc ∫ v, |G v - g v| ^ (2 * q) ∂γ ≤ ∫ v, S.indicator (fun _ => (2 * L) ^ (2 * q)) v ∂γ := by
            refine integral_mono (intB ((mG.sub mg).abs.pow_const _) (M := (2 * L) ^ (2 * q))
              fun v => ?_) (iInd _) fun v => ?_
            · rw [abs_pow, abs_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [bG v, bg v])) _
            · by_cases hv : v ∈ S
              · have := hGg v
                rw [Set.indicator_of_mem hv] at this ⊢
                exact pow_le_pow_left₀ (abs_nonneg _) this _
              · have := hGg v
                rw [Set.indicator_of_notMem hv] at this ⊢
                have h0 : |G v - g v| = 0 := le_antisymm this (abs_nonneg _)
                rw [h0, zero_pow hp0]
        _ = (2 * L) ^ (2 * q) * β := by rw [intInd]; ring)
    (by rw [momN_pow γ hp0])
    (by simp)
    (by simp [zero_pow hp0])
  simp only [add_zero] at hmk1
  have hX1 : X ≤ 2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹) + b2 + |mε - m| := by
    have hXp : X ^ (2 * q) ≤ (2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹) + b2 + |mε - m|) ^ (2 * q) := by
      rw [hX, momN_pow γ hp0]
      refine le_trans (integral_mono (intB ((mG.sub_const _).abs.pow_const _)
        (M := (2 * L) ^ (2 * q)) fun v => ?_) (intB ((((mG.sub mg).abs.add (mg.sub_const _).abs).add
          measurable_const).pow_const _) (M := (2 * L + 2 * L + 2 * L) ^ (2 * q)) fun v => ?_)
          fun v => ?_) hmk1
      · rw [abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [bG v])) _
      · show |(|G v - g v| + |g v - mε| + |mε - m|) ^ (2 * q)| ≤ (2 * L + 2 * L + 2 * L) ^ (2 * q)
        have h0 : 0 ≤ |G v - g v| + |g v - mε| + |mε - m| := by positivity
        have h1 : |G v - g v| ≤ 2 * L := (abs_sub _ _).trans (by linarith [bG v, bg v])
        have h2 : |g v - mε| ≤ 2 * L := (abs_sub _ _).trans (by linarith [bg v])
        have h3 : |mε - m| ≤ 2 * L := (abs_sub _ _).trans (by linarith)
        rw [abs_of_nonneg (pow_nonneg h0 _)]
        exact pow_le_pow_left₀ h0 (by linarith) _
      · refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
        calc |G v - m| = |(G v - g v) + (g v - mε) + (mε - m)| := by ring_nf
          _ ≤ |G v - g v| + |g v - mε| + |mε - m| := abs_add_three _ _ _
    exact le_of_pow_le_pow_left₀ hp0 (by positivity) hXp
  -- Step 2: Poincaré for the truncated lift
  set Z := momN γ (2 * q) (fun v => √(gradSq g v)) with hZ
  have hZ0 : 0 ≤ Z := momN_nonneg _ _ _
  have hcp : c ^ (2 * q) = (π / 2) ^ (2 * q) * gmom (2 * q) := by
    rw [hcd, cLS, mul_pow, Real.rpow_inv_natCast_pow (gmom_nonneg _) hp0]
  have hb2Z : b2 ≤ c * Z := by
    have hP := poincare_p (by positivity : (0 : ℝ) ≤ 2 * L / ε) hgL (p := 2 * q) (by omega)
    have h1 : b2 ^ (2 * q) ≤ (c * Z) ^ (2 * q) := by
      rw [hb2, momN_pow γ hp0, mul_pow, hcp, hZ, momN_pow γ hp0]
      simp_rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_assoc]
      exact hP
    exact le_of_pow_le_pow_left₀ hp0 (by positivity) h1
  -- Step 3: the gradient of the truncated lift
  set T : (ι → ℝ) → ℝ := fun v => gradSq H₁ v - G v ^ 2 with hTd
  have mT : Measurable T := (measurable_gradSq H₁).sub (mG.pow_const 2)
  have bT : ∀ v, √(T v) ≤ L := fun v => by
    rw [show L = √(L ^ 2) from (Real.sqrt_sq hL0).symm]
    refine Real.sqrt_le_sqrt ?_
    have := gradSq_le hL0 hL v
    simp only [hTd]; nlinarith [sq_nonneg (G v)]
  set Y := momN γ (2 * q) (fun v => √(T v)) with hY
  have hY0 : 0 ≤ Y := momN_nonneg _ _ _
  set B' := R with hB'
  have hB'0 : 0 ≤ B' := hR0
  set h1 : (ι → ℝ) → ℝ := fun v => if ε < radF53 v then √(T v) / radF53 v else 0 with hh1
  have mh1 : Measurable h1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_radF) (mT.sqrt.div measurable_radF)
      measurable_const
  have bh1 : ∀ v, 0 ≤ h1 v ∧ h1 v ≤ 2 * L / ε := fun v => by
    simp only [hh1]
    split_ifs with hv
    · have hr : 0 < radF53 v := lt_trans hε hv
      refine ⟨div_nonneg (Real.sqrt_nonneg _) hr.le, ?_⟩
      calc √(T v) / radF53 v ≤ L / ε := by
            rw [div_le_div_iff₀ hr hε]
            nlinarith [bT v, Real.sqrt_nonneg (T v)]
        _ ≤ 2 * L / ε := div_le_div_of_nonneg_right (by linarith) hε.le
    · exact ⟨le_rfl, by positivity⟩
  have hgr : ∀ v, √(gradSq g v) ≤ h1 v + S.indicator (fun _ => 2 * L / ε) v := fun v => by
    by_cases hv : ε < radF53 v
    · have hvS : v ∉ S := fun h => absurd h (not_le.mpr hv)
      simp only [hh1, if_pos hv, Set.indicator_of_notMem hvS, add_zero]
      exact gtr_grad_le hhom hε hv
    · have hvS : v ∈ S := le_of_not_gt hv
      simp only [hh1, if_neg hv, Set.indicator_of_mem hvS, zero_add]
      rw [show 2 * L / ε = √((2 * L / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (gradSq_le (by positivity) hgL v)
  -- `∫ h1^{2q} ≤ (Y B')^{2q}`
  set F : (ι → ℝ) → ℝ := fun u => √(T u) ^ (2 * q) with hF
  set Gr : ℝ → ℝ := fun ρ => if ε < ρ then (ρ ^ (2 * q))⁻¹ else 0 with hGr
  have hpt : ∀ v, h1 v ^ (2 * q) = F (unitF53 v) * Gr (radF53 v) := fun v => by
    by_cases hv : ε < radF53 v
    · have hr : 0 < radF53 v := lt_trans hε hv
      have hv0 : v ≠ 0 := fun h => by rw [h] at hr; simp [radF53] at hr
      have hTu : T (unitF53 v) = T v := by
        simp only [hTd, hGd]
        rw [unitF_unitF hv0]
        congr 1
        have : unitF53 v = (radF53 v)⁻¹ • v := by unfold unitF53; rw [one_div]; rfl
        rw [this, gradSq_hom hhom (inv_pos.mpr hr)]
      simp only [hh1, hF, hGr, if_pos hv, hTu, div_pow]
      ring
    · simp only [hh1, hGr, if_neg hv, mul_zero, zero_pow hp0]
  have mF : Measurable F := mT.sqrt.pow_const _
  have mGr : Measurable Gr := Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_id.pow_const _).inv measurable_const
  have hnz : ∀ᵐ v ∂γ, v ≠ 0 := by
    have h0 : γ {(0 : ι → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton (0 : ι → ℝ))
    rw [ae_iff]
    simpa using h0
  have hFu : ∫ v, F (unitF53 v) ∂γ = Y ^ (2 * q) := by
    rw [hY, momN_pow γ hp0]
    refine integral_congr_ae (hnz.mono fun v hv => ?_)
    simp only [hF, abs_of_nonneg (Real.sqrt_nonneg _)]
    congr 2
    simp only [hTd, hGd]
    rw [unitF_unitF hv]
    congr 1
    have hr : 0 < radF53 v := radF_pos hv
    have : unitF53 v = (radF53 v)⁻¹ • v := by unfold unitF53; rw [one_div]; rfl
    rw [this, gradSq_hom hhom (inv_pos.mpr hr)]
  have hI1 : ∫ v, h1 v ^ (2 * q) ∂γ ≤ (Y * B') ^ (2 * q) := by
    simp_rw [hpt]
    rw [polar_integral_mul F Gr mF mGr, hFu, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hY0 _)
    exact hR ε
  have hmk2 := mink4 γ (2 * q) (g1 := h1) (g2 := S.indicator (fun _ => 2 * L / ε))
    (g3 := fun _ => 0) (g4 := fun _ => 0) mh1 (measurable_const.indicator mS) measurable_const
    measurable_const (fun v => (bh1 v).1)
    (fun v => by by_cases hv : v ∈ S <;> simp [hv]; positivity) (fun _ => le_rfl) (fun _ => le_rfl)
    (M := 2 * L / ε) (fun v => (bh1 v).2)
    (fun v => by by_cases hv : v ∈ S <;> simp [hv]; positivity)
    (fun _ => by positivity) (fun _ => by positivity)
    (b1 := Y * B') (b2 := 2 * L / ε * β ^ (((2 * q : ℕ) : ℝ)⁻¹)) (b3 := 0) (b4 := 0)
    (mul_nonneg hY0 hB'0) (by positivity) le_rfl le_rfl hI1
    (by
      rw [mul_pow, Real.rpow_inv_natCast_pow hβ0 hp0]
      have e : ∀ v, S.indicator (fun _ => 2 * L / ε) v ^ (2 * q) =
          S.indicator (fun _ => (2 * L / ε) ^ (2 * q)) v := fun v => by
        by_cases hv : v ∈ S <;> simp [hv, zero_pow hp0]
      simp_rw [e]
      rw [intInd]; ring_nf; exact le_rfl)
    (by simp [zero_pow hp0]) (by simp [zero_pow hp0])
  simp only [add_zero] at hmk2
  have hZ1 : Z ≤ Y * B' + 2 * L / ε * β ^ (((2 * q : ℕ) : ℝ)⁻¹) := by
    have h3 : Z ^ (2 * q) ≤ (Y * B' + 2 * L / ε * β ^ (((2 * q : ℕ) : ℝ)⁻¹)) ^ (2 * q) := by
      rw [hZ, momN_pow γ hp0]
      simp_rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      refine le_trans (integral_mono (intB ((measurable_gradSq g).sqrt.pow_const _)
        (M := (2 * L / ε) ^ (2 * q)) fun v => ?_) (intB ((mh1.add
          (measurable_const.indicator mS)).pow_const _) (M := (2 * L / ε + 2 * L / ε) ^ (2 * q))
          fun v => ?_) fun v => ?_) hmk2
      · rw [abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
        refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ _
        rw [show 2 * L / ε = √((2 * L / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_le_sqrt (gradSq_le (by positivity) hgL v)
      · have h0 : 0 ≤ h1 v + S.indicator (fun _ => 2 * L / ε) v := by
          have := (bh1 v).1
          by_cases hv : v ∈ S <;> simp [hv] <;> positivity
        have h2 : S.indicator (fun _ => 2 * L / ε) v ≤ 2 * L / ε := by
          by_cases hv : v ∈ S <;> simp [hv]; positivity
        show |(h1 v + S.indicator (fun _ => 2 * L / ε) v) ^ (2 * q)| ≤ _
        rw [abs_of_nonneg (pow_nonneg h0 _)]
        exact pow_le_pow_left₀ h0 (by linarith [(bh1 v).2]) _
      · exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hgr v) _
    exact le_of_pow_le_pow_left₀ hp0 (by positivity) h3
  -- combine
  calc X ≤ 2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹) + b2 + |mε - m| := hX1
    _ ≤ 2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹) + c * (Y * B' + 2 * L / ε * β ^ (((2 * q : ℕ) : ℝ)⁻¹)) +
          2 * L * β := by
        gcongr
        exact hb2Z.trans (mul_le_mul_of_nonneg_left hZ1 hc0)


theorem ls_mom_radius [DecidableEq ι] [Nonempty ι] (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {q : ℕ} (hq : 1 ≤ q)
    (hqk : 2 * q < Fintype.card ι) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ ε : ℝ, (∫ Z, (if ε < radF53 Z then (radF53 Z ^ (2 * q))⁻¹ else 0)
      ∂stdGauss ι) ≤ R ^ (2 * q)) :
    momN (stdGauss ι) (2 * q) (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι) ≤
      cLS q * (momN (stdGauss ι) (2 * q) (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
        R) := by
  set X := momN (stdGauss ι) (2 * q) (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι)
  set A := cLS q * (momN (stdGauss ι) (2 * q) (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
        R)
  set k := Fintype.card ι
  set p := 2 * q
  set r : ℝ := ((p : ℕ) : ℝ)⁻¹ with hr
  have hp0 : (0 : ℝ) < p := by positivity
  have hr0 : 0 < r := inv_pos.mpr hp0
  have hc0 := cLS_nonneg q
  set C := 2 * L + cLS q * (2 * L * 2) + 2 * L with hC
  have hC0 : 0 ≤ C := by positivity
  have hkp : (p : ℝ) + 1 ≤ k := by
    have : p + 1 ≤ k := hqk
    exact_mod_cast this
  -- the bound at every level `0 < ε ≤ 1/2`
  have hlev : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → X ≤ A + C * (2 * ε) ^ r := fun ε hε hε2 => by
    have h := ls_eps_radius hL0 hL hhom hq hqk hR0 hR hε
    set β := (stdGauss ι).real {v | radF53 v ≤ ε}
    have hβ0 : 0 ≤ β := measureReal_nonneg
    have hβ := smallBall_le (ι := ι) hε.le
    have h2e0 : 0 < 2 * ε := by positivity
    have h2e1 : 2 * ε ≤ 1 := by linarith
    -- `β^{1/p} ≤ (2ε)^{k/p} ≤ (2ε)·(2ε)^{1/p}` and `β ≤ (2ε)^{1/p}`
    have hβr : β ^ r ≤ (2 * ε) ^ ((k : ℝ) * r) := by
      calc β ^ r ≤ ((2 * ε) ^ k) ^ r := Real.rpow_le_rpow hβ0 hβ hr0.le
        _ = (2 * ε) ^ ((k : ℝ) * r) := by rw [← Real.rpow_natCast, ← Real.rpow_mul h2e0.le]
    have hkr : (k : ℝ) * r ≥ 1 + r := by
      rw [hr]; field_simp; linarith
    have h1 : (2 * ε) ^ ((k : ℝ) * r) ≤ (2 * ε) * (2 * ε) ^ r := by
      calc (2 * ε) ^ ((k : ℝ) * r) ≤ (2 * ε) ^ (1 + r) :=
            Real.rpow_le_rpow_of_exponent_ge h2e0 h2e1 hkr
        _ = (2 * ε) * (2 * ε) ^ r := by rw [Real.rpow_add h2e0, Real.rpow_one]
    have h2 : (2 * ε) * (2 * ε) ^ r ≤ (2 * ε) ^ r := by
      have := Real.rpow_nonneg h2e0.le r
      nlinarith
    have hβle : β ≤ (2 * ε) ^ r := by
      calc β ≤ (2 * ε) ^ k := hβ
        _ = (2 * ε) ^ ((k : ℝ)) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 * ε) ^ r := Real.rpow_le_rpow_of_exponent_ge h2e0 h2e1 (by
            have : r ≤ 1 := by rw [hr]; exact inv_le_one_of_one_le₀ (by
              have : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
              linarith)
            have : (1 : ℝ) ≤ k := by exact_mod_cast (Fintype.card_pos : 0 < k)
            linarith)
    have hT1 : 2 * L * β ^ r ≤ 2 * L * (2 * ε) ^ r :=
      mul_le_mul_of_nonneg_left (hβr.trans (h1.trans h2)) (by positivity)
    have hT2 : 2 * L / ε * β ^ r ≤ 2 * L * 2 * (2 * ε) ^ r := by
      calc 2 * L / ε * β ^ r ≤ 2 * L / ε * ((2 * ε) * (2 * ε) ^ r) :=
            mul_le_mul_of_nonneg_left (hβr.trans h1) (by positivity)
        _ = 2 * L * 2 * (2 * ε) ^ r := by field_simp
    have hT3 : 2 * L * β ≤ 2 * L * (2 * ε) ^ r := mul_le_mul_of_nonneg_left hβle (by positivity)
    have hp' : ((2 * q : ℕ) : ℝ)⁻¹ = r := rfl
    rw [hp'] at h
    calc X ≤ 2 * L * β ^ r + cLS q * (momN (stdGauss ι) (2 * q)
            (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
          R + 2 * L / ε * β ^ r) + 2 * L * β := h
      _ ≤ 2 * L * (2 * ε) ^ r + cLS q * (momN (stdGauss ι) (2 * q)
            (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
          R + 2 * L * 2 * (2 * ε) ^ r) +
            2 * L * (2 * ε) ^ r := by gcongr
      _ = A + C * (2 * ε) ^ r := by rw [hC]; ring
  -- the limit `ε → 0`
  have hcont : ContinuousAt (fun ε : ℝ => A + C * (2 * ε) ^ r) 0 := by
    have h0 : ContinuousAt (fun y : ℝ => y ^ r) (2 * 0) :=
      Real.continuousAt_rpow_const _ _ (Or.inr hr0.le)
    exact continuousAt_const.add (continuousAt_const.mul
      (h0.comp (continuousAt_const.mul continuousAt_id)))
  have ht : Tendsto (fun ε : ℝ => A + C * (2 * ε) ^ r) (𝓝[>] 0) (𝓝 (A + C * (2 * 0) ^ r)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), X ≤ A + C * (2 * ε) ^ r := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    exact hlev ε hε.1 hε.2.le
  have := ge_of_tendsto ht hev
  rwa [mul_zero, Real.zero_rpow hr0.ne', mul_zero, add_zero] at this


#print axioms ls_eps_radius
#print axioms ls_mom_radius
end BstLean.Part223
