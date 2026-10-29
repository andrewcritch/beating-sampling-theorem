import BstLean.Part252Centre

/-! A nonzero hidden centre has a nonzero output centre outside a null event. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164

def positiveOutputEvent {n : ℕ} (D : Centres n) : Set (Ret n) :=
  {c | 0 < normSq (D.bA c.1 c.2.1.1) → 0 < normSq c.2.1.2}

theorem positiveOutputEvent_measurable {n : ℕ} (D : Centres n) :
    MeasurableSet (positiveOutputEvent D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have he : positiveOutputEvent D = {c : Ret n | 0 < normSq (D.bA c.1 c.2.1.1)}ᶜ ∪
      {c : Ret n | 0 < normSq c.2.1.2} := by
    ext c
    exact imp_iff_not_or
  rw [he]
  exact (measurableSet_lt measurable_const hb).compl.union (measurableSet_lt measurable_const hc)

theorem positiveOutputEvent_charge {n : ℕ} (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (positiveOutputEvent D)ᶜ ≤ 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let T : Set (ARet n) := {x | x.2 = 0}
  have hT : MeasurableSet T := measurableSet_eq_fun measurable_snd measurable_const
  have ht : (cAm n).real T = 0 := by
    have he : T = univ ×ˢ ({0} : Set (Fin n → ℝ)) := by ext x; simp [T]
    rw [he, cAm, measureReal_def, Measure.prod_prod]
    have hz : stdGauss (Fin n) ({0} : Set (Fin n → ℝ)) = 0 := by
      unfold stdGauss
      exact measure_singleton _
    rw [hz, mul_zero]
    rfl
  refine (charge_of_noise D (positiveOutputEvent_measurable D) hT ?_).trans ht.le
  intro x hx hB
  have hξ : x.2.1.2 ≠ 0 := hx
  have hξn : 0 < normSq x.2.1.2 :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm fun h => hξ (normSq_eq_zero h))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : 0 < 2 / (mA n : ℝ) := by norm_num [mA]; positivity
  change 0 < normSq (cOf (2 / (mA n : ℝ))
    (D.bA (retValW D x.1) x.2.1.1) x.2.1.2)
  unfold cOf
  rw [normSq_smul, mul_pow, sq_sqrt hv.le, sq_sqrt (normSq_nonneg _)]
  exact mul_pos (mul_pos hv hB) hξn

end BstLean.Part252
