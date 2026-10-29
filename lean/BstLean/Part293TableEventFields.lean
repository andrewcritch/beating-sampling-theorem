import BstLean.Part292TableEvents
import BstLean.Part293World
import BstLean.Part293OddBounds

/-! Deterministic fields of the actual table event, independent of its final charge. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169 BstLean.Part170
open BstLean.Part289

theorem tableWorldGuard_of_supply {n : ℕ} (hn : 8000 ≤ n)
    (S : BstLean.Part290.WorldSupply (statedDesign2 n)
      (BstLean.Part290.worldFrameCertificate hn)) (z : Ret n)
    (hz : z ∈ Hof (BstLean.Part290.worldHidden n) ∩
      (Ethm (statedDesign2 n).toCentres ∩ Ethp (statedDesign2 n).toCentres)) :
    BstLean.Part292.tableWorldGuard z.1 := by
  have hθ := S.noise_window z hz
  have hτ := (S.scale_identity z.1.1 hz.1).1
  refine ⟨⟨hτ, ?_, ?_⟩, hθ.2⟩
  · exact (by norm_num : (46 / 100 : ℝ) ≤ 472 / 1000).trans hθ.1
  · exact hθ.2.trans (by norm_num : (528 / 1000 : ℝ) ≤ 55 / 100)

def arithmeticInputs_of_table {n : ℕ} (hn : 8000 ≤ n) (ho : Odd n) (c : Ret n)
    (ht : c ∈ BstLean.Part292.tableEvent n) (hw : BstLean.Part292.tableWorldGuard c.1)
    (he : 0 < eR c) (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * 1.081) :
    ArithmeticInputs c := by
  have hn' : 8001 ≤ n := by obtain ⟨k, hk⟩ := ho; omega
  have h := (ht hw).2
  have hA := opB_of_opN _ h.1
  have hB := opB_of_opN _ h.2.1
  have hB3 := BstLean.Part278.OpB_mono hB
    (by unfold BstLean.Part292.lowSecondOperator; positivity)
    (BstLean.Part292.lowSecondOperator_le hn)
  have hs (g : ℕ) (hg : g ≤ Js n - 1) : nodeS c g ^ 2 ≤ 1 := by
    have hJ : 0 < Js n := by unfold Js; omega
    have hh := (BstLean.Part292.node_geometry_low hn hw c.2.1.1
      (show g < Js n by omega)).2.1
    change (391 / 1000 : ℝ) ≤ 1 - nodeS c g ^ 2 at hh
    linarith
  exact arithmeticInputs_of_operators hn' ho c he hc hB3
    (fun g hg => BstLean.Part292.low_odd_row_energy hn c hA (hs g hg))
    (fun g hg => BstLean.Part292.low_odd_passF hn' c hA hB g (hs g hg))

end BstLean.Part293
