import BstLean.Part291LocalCentre

namespace BstLean.BlueprintLow
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

/-- Rational witnesses for one continuum dimension band and one noise endpoint. -/
structure LocalCentreWitness (nlo nhi : ℕ) (Θ full : ℝ) where
  root : ℝ
  W : ℝ
  R : ℝ
  G : ℝ
  Nu : ℝ
  T1 : ℝ
  T2 : ℝ
  E1 : ℝ
  E2 : ℝ
  X : ℝ
  Droot : ℝ
  D : ℝ
  Rroot : ℝ
  Rd : ℝ
  root_pos : 0 < root
  root_sq : root ^ 2 ≤ nlo
  wn_cap : (1 + 2 / root) ^ 2 ≤ W
  rho_cap : 4 * W / (1.29521 * nlo) ≤ R
  gamma_cap : 2 * W * Θ / (0.989 * nlo) ≤ G
  nu_cap : 4 * R + R ^ 2 ≤ Nu
  E1_nonneg : 0 ≤ E1
  E2_nonneg : 0 ≤ E2
  gap1 : 2 * R * E1 ≤ 0.105169208 ^ 2
  gap2 : 2 * G * E2 ≤ 0.06334 ^ 2
  tail1 : exp (-E1) ≤ T1
  tail2 : exp (-E2) ≤ T2
  X_nonneg : 0 ≤ X
  moment_cap :
    4 * 0.090846 * 1.193734 * (0.004172 + 0.34 * Θ) / 1.600601 +
      W * nhi * (T1 / 1.118033988 + T2 / 1.067707825) +
      4 * W * ((2 * Θ * R + 0.6863 * (4 * W / 1.29521) * Nu) / 3.141592 + Θ / 10 ^ 40) +
      4 * Θ * W * 2.519668 * R ≤ X ^ 2
  Droot_nonneg : 0 ≤ Droot
  Droot_sq : 1.045222 * Θ ≤ Droot ^ 2
  D_cap : 4.89898 * (0.013351983 + 2 * Droot / 8000) ≤ D
  Rroot_nonneg : 0 ≤ Rroot
  Rroot_sq : 1.269 * Θ ≤ Rroot ^ 2
  Rd_cap : (Θ * 1.002293 + Rroot) / 89.442719 ≤ Rd
  full_cap : (X + D + Rd + 0.010727) ^ 2 ≤ full

theorem LocalCentreWitness.bound {n nlo nhi : ℕ}
    (hnlo : 8000 ≤ nlo) (hnhi : nhi ≤ 11882) (hn : n ∈ Icc nlo nhi)
    {Θ full : ℝ} (hΘ : Θ ∈ Icc (0.46 : ℝ) 0.54) (C : LocalCentreWitness nlo nhi Θ full) :
    fullFormula n n 0.011 1.25 1.14 0.46 Θ (0.004172 + 0.34 * Θ) 1.269 ≤ full := by
  have hband : LowBand n := ⟨hnlo.trans hn.1, hn.2.trans hnhi⟩
  have hθ0 : 0 < Θ := lt_of_lt_of_le (by norm_num) hΘ.1
  have hN0 : (8000 : ℝ) ≤ nlo := by exact_mod_cast hnlo
  have hN : (nlo : ℝ) ≤ n := by exact_mod_cast hn.1
  have hNR : (8000 : ℝ) ≤ n := hN0.trans hN
  have hw := BstLean.Part277.wn_upperP hnlo hn.1 C.root_pos C.root_sq C.wn_cap
  have hw0 := (centreWnBand hband.1).1
  have hW0 : 0 ≤ C.W := by linarith
  have hc := BstLean.Part253.cs_lower
  have hR : rhoBar n csC ≤ C.R := by
    unfold rhoBar
    apply le_trans ?_ C.rho_cap
    gcongr
  have hG : gammaRatio n 0.011 Θ ≤ C.G := by
    unfold gammaRatio
    apply le_trans ?_ C.gamma_cap
    norm_num only
    gcongr
  have hm := localCentreMoment (Nhi := (nhi : ℝ)) hband hΘ hw hR hG C.nu_cap
    (by exact_mod_cast hn.2) (by positivity : 0 ≤ 0.004172 + 0.34 * Θ)
    C.E1_nonneg C.E2_nonneg C.gap1 C.gap2 C.tail1 C.tail2
  have hX : √(momentAllowance n csC 0.011 1.25 1.14 Θ (0.004172 + 0.34 * Θ)) ≤ C.X :=
    sqrt_le_iff.mpr ⟨C.X_nonneg,hm.trans C.moment_cap⟩
  have hwu := (centreWnBand hband.1).2
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.013351983 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (0.011 : ℝ) - 1.29521 * 0.46 / 2) / 8000 := by gcongr
      _ ≤ (0.013351983 : ℝ) ^ 2 := by norm_num
  have h2 : √(wn n * Θ) ≤ C.Droot :=
    sqrt_le_iff.mpr ⟨C.Droot_nonneg,
      (mul_le_mul_of_nonneg_right hwu hθ0.le).trans C.Droot_sq⟩
  have hD : sharpDeviation n csC 0.011 0.46 Θ ≤ C.D := by
    unfold sharpDeviation
    have hpart : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) +
        2 * √(wn n * Θ) / n ≤ 0.013351983 + 2 * C.Droot / 8000 := by
      apply add_le_add h1
      have hnR0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hNR
      have hnR : (8000 : ℝ) ≤ n := hNR
      calc
        _ ≤ 2 * C.Droot / n := by
          apply div_le_div_of_nonneg_right ?_ hnR0.le
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ ≤ 2 * C.Droot / 8000 := by
          have hd : C.Droot / n ≤ C.Droot / 8000 :=
            div_le_div_of_nonneg_left C.Droot_nonneg (by norm_num) hnR
          calc
            _ = 2 * (C.Droot / n) := by ring
            _ ≤ 2 * (C.Droot / 8000) := mul_le_mul_of_nonneg_left hd (by norm_num)
            _ = _ := by ring
    calc
      _ ≤ 4.89898 * (0.013351983 + 2 * C.Droot / 8000) := by
        exact mul_le_mul hs hpart (by positivity) (by norm_num)
      _ ≤ C.D := C.D_cap
  have hD0 : 0 ≤ sharpDeviation n csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hr : √(1.269 * Θ) ≤ C.Rroot := sqrt_le_iff.mpr ⟨C.Rroot_nonneg,C.Rroot_sq⟩
  have hN22 := centreN22Band hband.1
  have hN220 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  have hroot := centreRootN hband.1
  have hrad : xiNr n Θ 1.269 ≤ C.Rd := by
    unfold xiNr
    apply le_trans ?_ C.Rd_cap
    have he : 1 + N22bar n 12 ≤ (1.002293 : ℝ) := by linarith
    gcongr
    exact add_nonneg (mul_nonneg hθ0.le (by norm_num)) C.Rroot_nonneg
  have hrad0 : 0 ≤ xiNr n Θ 1.269 := by unfold xiNr; positivity
  have hf : finiteEnergy n n 0.011 ≤ 0.010727 := by
    convert BstLean.Part277.finite_centre_8000 hband.1 using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ C.full_cap
  gcongr

theorem localMomentCertificate {n : ℕ} (hn : LowBand n) {Θ : ℝ}
    (hΘ : Θ ∈ Icc (0.46 : ℝ) 0.54) :
    MomentCertificate n 0.011 1.25 1.14 0.46 Θ (0.004172 + 0.34 * Θ) (fun _ => 0.006) where
  delta_nonneg := by norm_num
  delta_lt := by norm_num
  k_gt := by norm_num
  k3_gt := by norm_num
  theta_lower := by norm_num
  v_pos := fun _ _ => by norm_num
  supremum := fun _ hw => hsAffinePrefix hn.1 hw hΘ.2
  ratio := by have h := centreRhoBand hn; linarith [h.2]
  ratio_gamma := (centreGamma54 hn.1 (by linarith [hΘ.1]) hΘ.2).2.trans (by norm_num)
  gap := by have h := centreFirstGap (centreRhoBand hn).2; linarith
  gap_gamma := by
    have h := centreSecondGap54 (centreGamma54 hn.1 (by linarith [hΘ.1]) hΘ.2).2
    linarith

end BstLean.BlueprintLow
