import BstLean.Part293Assembly
import BstLean.Part293Elementary
import BstLean.Part290Supply
import BstLean.Part252SharedPackage

/-! Exact adapter from the Part290 World record into the design-parametric RF assembly. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part289

theorem window_of_supply {n : ℕ} (hn : 8000 ≤ n)
    (S : BstLean.Part290.WorldSupply (statedDesign2 n)
      (BstLean.Part290.worldFrameCertificate hn)) (z : Ret n)
    (hz : z ∈ Hof (BstLean.Part290.worldHidden n) ∩
      (Ethm (statedDesign2 n).toCentres ∩ Ethp (statedDesign2 n).toCentres)) :
    BstLean.Part161.WINDOW (idealDesignFloor n (scaleFloor n)) z := by
  have hθ := S.noise_window z hz
  have hτ : 0 < (idealDesignFloor n (scaleFloor n)).tau0 z :=
    (S.scale_identity z.1.1 hz.1).1
  apply BstLean.Part252.window_of_theta (by omega) _ _ hτ
  constructor
  · exact (by norm_num : (46 / 100 : ℝ) ≤ 472 / 1000).trans hθ.1
  · exact hθ.2.trans (by norm_num : (528 / 1000 : ℝ) ≤ 54 / 100)

noncomputable def worldCharge_of_supply {n : ℕ} (hn : 8000 ≤ n)
    (S : BstLean.Part290.WorldSupply (statedDesign2 n)
      (BstLean.Part290.worldFrameCertificate hn)) :
    NetworkCharge (retDist (statedDesign2 n).toCentres) worldCharge where
  event := Hof (BstLean.Part290.worldHidden n)
  measurable := measurableSet_Hof S.hidden_measurable
  nonneg := by norm_num [worldCharge]
  complement := S.retained_charge.le.trans (by norm_num [worldCharge])

noncomputable def angleCharge_of_supply {n : ℕ} (hn : 8000 ≤ n)
    (S : BstLean.Part290.WorldSupply (statedDesign2 n)
      (BstLean.Part290.worldFrameCertificate hn)) :
    NetworkCharge (retDist (statedDesign2 n).toCentres) angleCharge :=
  NetworkCharge.of_restricted _ (measurableSet_Hof S.hidden_measurable)
    ((measurableSet_Ethm _).inter (measurableSet_Ethp _))
    (by norm_num [angleCharge]) (S.angle_charge.trans (angle_payment hn))

noncomputable def worldInputs_of_supply {n : ℕ} (hn : 8000 ≤ n)
    (S : BstLean.Part290.WorldSupply (statedDesign2 n)
      (BstLean.Part290.worldFrameCertificate hn))
    {E : Set (Ret n)} (hsub : E ⊆ Hof (BstLean.Part290.worldHidden n)) : WorldInputs n E := by
  let c := BstLean.Part290.worldFrameCertificate hn
  let k := BstLean.Part236.coeffK c (1 / 10 ^ 9)
  let d := BstLean.Part236.coeffD c (1 / 10 ^ 9)
  have hk0 : 0 ≤ k := BstLean.Part236.coeffK_nonneg c (by norm_num)
  have hd0 : 0 ≤ d := BstLean.Part236.coeffD_nonneg c (by norm_num)
  have hk : k ≤ coeffK := S.frame_caps.2.1.trans (by norm_num [coeffK])
  have hd : d ≤ coeffD := S.frame_caps.2.2.trans (by norm_num [coeffD])
  obtain ⟨ik, id, mk, md⟩ := S.error_moments E
  refine {
    x := fun z => k * √(BstLean.Part236.yK z.1.1)
    y := fun z => d * BstLean.Part236.yD z.1.1
    x_nonneg := fun _ => mul_nonneg hk0 (sqrt_nonneg _)
    y_nonneg := fun z => mul_nonneg hd0 (S.error_nonneg z.1.1).2
    maximum := ?_
    radius_integrable := S.replacement_integrable.mono_set hsub
    radius_moment := ?_
    x_integrable := ik
    y_integrable := id
    x_moment := mk.trans ?_
    y_moment := md.trans ?_
    frame := ?_ }
  · intro z hz
    have he := S.error_max z.1.1 (hsub hz)
    change k * √(BstLean.Part236.yK z.1.1) + d * BstLean.Part236.yD z.1.1 ≤ _
    change k * √(BstLean.Part236.yK z.1.1) + d * BstLean.Part236.yD z.1.1 ≤
      25 * k + 2500 * d at he
    norm_num [coeffK, coeffD] at hk hd
    norm_num [frameMaximum]
    linarith
  · apply (setIntegral_mono_set S.replacement_integrable
      (Filter.Eventually.of_forall (fun z => sq_nonneg (HbarW (statedDesign2 n) z)))
      (Filter.Eventually.of_forall hsub)).trans
    exact S.replacement_moment.trans (by norm_num [radiusMoment])
  · change (372 / 1000 : ℝ) * k ^ 2 ≤ 0.372 * coeffK ^ 2
    rw [show (372 / 1000 : ℝ) = 0.372 by norm_num]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0 hk 2) (by norm_num)
  · change (448 / 1000 : ℝ) * d ≤ 0.448 * coeffD
    rw [show (448 / 1000 : ℝ) = 0.448 by norm_num]
    exact mul_le_mul_of_nonneg_left hd (by norm_num)
  · intro z hz z' hz' w
    have hzEq : z' = z := hz'
    subst z'
    have hf := S.frame z.1.1 (hsub hz) w
    apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hb : BstLean.Part236.frameBase c (1 / 10 ^ 9) (1 / 10 ^ 12) ≤ worldBase :=
      S.frame_caps.1.trans (by norm_num [worldBase])
    change BstLean.Part236.frameBase c (1 / 10 ^ 9) (1 / 10 ^ 12) +
      (k * √(BstLean.Part236.yK z.1.1) + d * BstLean.Part236.yD z.1.1) ≤ _
    linarith

end BstLean.Part293

/-- info: 'BstLean.Part293.worldInputs_of_supply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.worldInputs_of_supply
