import BstLean.Part255Table
import BstLean.Part254SharpNetwork
import BstLean.Part255Symmetry

/-! Covariance transfer on the local events. The eigenvalue route avoids any
unproved substitution of a local plane coefficient into a pointwise bound. -/
namespace BstLean.Part255
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part208 BstLean.Part238
open BstLean.Part199 (exampleWide exampleCore example_nested radiusMinus)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4 nrm)
open BstLean.Part254 (gaussianScalar gaussianTail gaussianOutside gaussianPair)

noncomputable def localGaussian (p : Parameters) (θ : ℝ) : ℝ :=
  gaussianScalar 12225 θ exampleWide exampleCore p.cLam p.wLam
    (1 - 4 * θ / 12225)⁻¹ (13/10)
    (gaussianTail exampleWide.pair + delta / payment)

theorem local_cutoff : delta / payment ≤ (28 / 10^16 : ℝ) := by
  have h := BstLean.Part246.cutoff_46 (by rw [mask_exponent] :
    (46 : ℝ) ≤ 2 * maskSlack^2 * (mA 12225 : ℝ))
  simpa only [delta_eq, payment] using h

theorem Dq_local_gaussian (p : Parameters) (hp : Valid p)
    (D : Design 12225) (k : Ret 12225) {lo hi : ℝ}
    (hτ : 0 < D.tau0 k)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Icc (46/100) (528/1000))
    (hloc : thetaC k.1.2 (D.tau0 k) ∈ Icc lo hi)
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤
      (13/10) * (2/(12225 : ℝ))/12225)
    (hC : k ∈ agentEv D (localEvent p lo hi payment)) (v : Fin (mA 12225) → ℝ) :
    Dq k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) v ≤
      localGaussian p (thetaC k.1.2 (D.tau0 k)) * (2/(12225 : ℝ))/12225 * normSq v := by
  have hθ1 : thetaC k.1.2 (D.tau0 k) < 1 := hw.2.trans_lt (by norm_num)
  have hc := ne_zero_of_thetaC_lt (by norm_num : 0 < 12225) hτ hθ1
  obtain ⟨hR,hat,_⟩ := chi_core_M12 (by norm_num : 11883 ≤ 12225) k.1.2 hτ hw.1 hw.2
  obtain ⟨hr₀,_⟩ := BstLean.Part235.wide_radius_caps (by norm_num : 11883 ≤ 12225) hw.1 hw.2
  obtain ⟨hr₁,_⟩ := BstLean.Part235.core_radius_caps (by norm_num : 11883 ≤ 12225) hw.1 hw.2
  obtain ⟨hcau,ha,hu⟩ := centre_decomp hc
  have hsm1 := axialProjLower_le_one 12225 ha hτ exampleCore.t_nonneg exampleCore.z_nonneg hat
  have hcp : p.chi^2 < 1 := pow_lt_one₀ hp.chi_nonneg hp.chi_lt (by norm_num)
  have hb : sharpBadMass 12225 exampleWide exampleCore p.wLam p.cE p.o p.cS p.chi
      ((k.1.2,D.tau0 k),(k.2.1.1.1,k.2.1.1.2)) ≤ delta/payment := by
    rcases hC hτ with hno | hb
    · exact False.elim (hno hloc)
    · exact hb
  have hd := Dq_gaussian_symmetric (by norm_num : 6 ≤ 12225)
    k.2.1.1.1 k.2.1.1.2 k.1.2 (uC k.1.2) hcau ha hu hτ
    exampleWide exampleCore example_nested hp.cE_nonneg hp.o_nonneg hp.cS_nonneg
    hp.wLam_nonneg (by norm_num : (0 : ℝ) ≤ 13/10) hθ1
    (by linarith) (by linarith) hR hcp hsm1 (centre_proj_lower' hcau hu ha hτ hat) hb hX v
  have hθ0 : 0 ≤ thetaC k.1.2 (D.tau0 k) := by linarith [hw.1]
  have hE : 0 ≤ (1 - 4 * thetaC k.1.2 (D.tau0 k) / 12225)⁻¹ := by
    apply inv_nonneg.mpr
    linarith [hw.2]
  refine hd.trans ?_
  apply mul_le_mul_of_nonneg_right _ (normSq_nonneg v)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12225)
  apply mul_le_mul_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2/12225)
  exact BstLean.Part254.gaussianScalar_mono_K hθ0 hE ((min_le_right _ _).trans hp.core_lam)

theorem localGaussian_le_envelope (p : Parameters) (hp : Valid p) {θ : ℝ}
    (hw : θ ∈ Icc (46/100 : ℝ) (528/1000))
    (hwR : radiusMinus 12225 θ exampleWide ≤ p.wRadius)
    (hcR : radiusMinus 12225 θ exampleCore ≤ p.cRadius)
    (hw1 : p.wRadius < 1) (hc1 : p.cRadius < 1) :
    localGaussian p θ ≤ envelope p θ := by
  have hθ0 : 0 ≤ θ := by linarith [hw.1]
  have hwpos : 0 < 1 - p.wRadius := by linarith
  have hcpos : 0 < 1 - p.cRadius := by linarith
  have hrw : 0 < 1 - radiusMinus 12225 θ exampleWide := by linarith
  have hrc : 0 < 1 - radiusMinus 12225 θ exampleCore := by linarith
  have hinvw : (1-radiusMinus 12225 θ exampleWide)⁻¹ ≤ (1-p.wRadius)⁻¹ :=
    inv_anti₀ hwpos (by linarith)
  have hinvc : (1-radiusMinus 12225 θ exampleCore)⁻¹ ≤ (1-p.cRadius)⁻¹ :=
    inv_anti₀ hcpos (by linarith)
  have hpair := BstLean.Part254.gaussian_core_pair_upper
  have hout := BstLean.Part254.gaussian_core_outside_upper
  have hexc := gaussian_exceptional_single local_cutoff
  have hp0 : 0 ≤ gaussianPair exampleCore := BstLean.Part254.gaussianTail_nonneg _
  have ho0 : 0 ≤ gaussianOutside exampleCore :=
    add_nonneg (BstLean.Part254.gaussianTail_nonneg _) (by positivity)
  have hpair' := mul_le_mul (mul_le_mul_of_nonneg_left hinvc hp.wLam_nonneg) hpair
    hp0 (mul_nonneg hp.wLam_nonneg (inv_nonneg.mpr hcpos.le))
  have hout' := mul_le_mul (mul_le_mul_of_nonneg_left hinvw hp.wLam_nonneg) hout
    ho0 (mul_nonneg hp.wLam_nonneg (inv_nonneg.mpr hwpos.le))
  have hex := mul_le_mul_of_nonneg_left hexc (by norm_num : (0 : ℝ) ≤ 13/10)
  have hs := add_le_add
    (add_le_add (le_refl (p.cLam * (1-4*θ/12225)⁻¹)) hpair') hout'
  unfold localGaussian gaussianScalar envelope
  simpa only [div_eq_mul_inv, Nat.cast_ofNat] using
    add_le_add (mul_le_mul_of_nonneg_left hs hθ0) hex

theorem envelope_mono (p : Parameters) (hp : Valid p) {θ θ' : ℝ}
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hhi : θ' ≤ 528/1000)
    (hw1 : p.wRadius < 1) (hc1 : p.cRadius < 1) : envelope p θ ≤ envelope p θ' := by
  have hd : 0 < 1 - 4*θ'/12225 := by linarith
  have hd' : 0 < 1 - 4*θ/12225 := by linarith
  have he := div_le_div_of_nonneg_left hp.cLam_nonneg hd (by linarith :
    1 - 4*θ'/12225 ≤ 1 - 4*θ/12225)
  have hterm : 0 ≤ p.cLam/(1-4*θ/12225) + p.wLam/(1-p.cRadius)*(1374279/10^9) +
      p.wLam/(1-p.wRadius)*(6216465741/10^12) := by
    have := hp.cLam_nonneg
    have := hp.wLam_nonneg
    have : 0 < 1-p.cRadius := by linarith
    have : 0 < 1-p.wRadius := by linarith
    positivity
  have hsum : p.cLam/(1-4*θ/12225) + p.wLam/(1-p.cRadius)*(1374279/10^9) +
      p.wLam/(1-p.wRadius)*(6216465741/10^12) ≤
      p.cLam/(1-4*θ'/12225) + p.wLam/(1-p.cRadius)*(1374279/10^9) +
      p.wLam/(1-p.wRadius)*(6216465741/10^12) :=
    add_le_add (add_le_add he le_rfl) le_rfl
  exact add_le_add (mul_le_mul hθ hsum hterm (h0.trans hθ)) le_rfl

end BstLean.Part255
