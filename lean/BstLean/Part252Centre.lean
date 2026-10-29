import BstLean.Part252Scalar
import BstLean.Part164Ev
import BstLean.Part169In

/-! Only the upper output-centre tail is needed for the stored-pass root. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part169

def outputCentreEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n}

theorem outputCentreEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (outputCentreEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact measurableSet_le hc ((hb.const_mul _).mul_const _)

theorem outputCentreEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (outputCentreEvent D)ᶜ ≤ exp (-12) := by
  let T : Set (ARet n) := {x | chiUp n ≤ normSq x.2}
  have hT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)
  have ht : (cAm n).real T ≤ exp (-12) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
    simp only [Fintype.card_fin] at hU
    have he : T = univ ×ˢ {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} := by
      ext x
      simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    simpa only [measure_univ, one_mul, chiUp, normSq, Measure.real] using hU
  refine (charge_of_noise D (outputCentreEvent_measurable D) hT ?_).trans ht
  intro x hx
  have hx' : normSq x.2.1.2 < chiUp n := not_le.mp hx
  let v : ℝ := 2 / (mA n : ℝ)
  let B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, sq_sqrt hv, sq_sqrt hB]
  change normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
  rw [hc]
  exact mul_le_mul_of_nonneg_left hx'.le (mul_nonneg hv hB)

theorem chi_row : chiUp 12225 / 12225 ≤ chi := by
  have hs : √((12225 : ℝ) * 12) ≤ 384 := by
    apply (sqrt_le_iff).2
    norm_num
  unfold chiUp chi
  norm_num only [Nat.cast_ofNat] at hs ⊢
  linarith

theorem outputCentre_row {c : Ret 12225}
    (hc : c ∈ outputCentreEvent (paperCentres 12225)) :
    normSq c.2.1.2 ≤ (2 / (12225 : ℝ)) * eR c * 12225 * chi := by
  change normSq c.2.1.2 ≤ 2 / (mA 12225 : ℝ) * normSq (bR c) * chiUp 12225 at hc
  have hn := normSq_nonneg (bR c)
  have hm := mul_le_mul_of_nonneg_left chi_row hn
  norm_num [mA, eR] at hc ⊢
  linarith

theorem exp_neg12_row : exp (-12) ≤ (6144212354 / 10 ^ 15 : ℝ) := by
  have he : exp (-1) ≤ (36787944117145 / 10 ^ 14 : ℝ) := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hh := pow_le_pow_left₀ (exp_pos (-1 : ℝ)).le he 12
  have hid : exp (-12) = exp (-1) ^ 12 := by
    rw [← exp_nat_mul]
    norm_num
  rw [hid]
  exact hh.trans (by norm_num)

theorem outputCentre_charge_row :
    (retDist (paperCentres 12225)).real (outputCentreEvent (paperCentres 12225))ᶜ ≤
      (6144212354 / 10 ^ 15 : ℝ) :=
  (outputCentreEvent_charge (by norm_num) _).trans exp_neg12_row

end BstLean.Part252
