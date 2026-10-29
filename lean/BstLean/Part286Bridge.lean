import BstLean.Part270Bridge
import BstLean.Part269FrameAdapter
import BstLean.Part278Row

/-!
# Part 286: generic bridges for the 12 350–13 224 rows

* `localRoot_from_numerics`: the local root supply of one row from the exact World window and
  the Part 269 source numerics (the same proof as the Part 270 rows, with generic arguments).
* `stated_from_row`: the stated program from one row whose base event is `sourceBase n`.
  Even `n`: `statedDesign_even` and `classifier_from_row`. Odd `n`: `classifier_from_row_st`
  with `oddRoot_row`.
-/

namespace BstLean.Part286

open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169 BstLean.Part188 BstLean.Part192

theorem localRoot_from_numerics {n : ℕ} (hn : 12225 ≤ n) (hu : n ≤ 16384)
    {wp : WorldParameters} (W : WorldPackage (paperProgram n) wp)
    (hidden_eq : W.hidden = BstLean.Part227.hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7))
    (lower : (202225/100000 : ℝ) ≤ BstLean.Part227.productLower n (1232/10^7))
    (upper : BstLean.Part227.productUpper n (1232/10^7) ≤ (202831/100000 : ℝ))
    (R : BstLean.Part263.ScalarRow n)
    (N : ∀ i : Fin 60, (10 ≤ i.val ∧ i.val ≤ 52) →
      BstLean.Part269.CellSourceNumerics n (R.table i) R.M R.H R.xi)
    (hM : R.M ≤ 91/1000) (hH : R.H ≤ (2101/100)/n) (hxi : R.xi ≤ 4/100)
    (hE : ∀ i : Fin 60, 10 ≤ i.val ∧ i.val ≤ 52 → (R.table i).energy ≤ 702/1000) :
    BstLean.Part262.LocalRootSupply n (Hof W.hidden) := by
  have key : ∀ c, c ∈ Hof W.hidden → c ∈ BstLean.Part262.sourceBase n →
      WFInterfaces (paperDesignP n) c (91/1000) ((2101/100)/n) (4/100) ∧
        centreEnergy (paperDesignP n) c ≤ 702/1000 := by
    intro c hw hc
    have hθ := BstLean.Part269.exact_world_window (by omega) W hidden_eq lower upper hw hc
    obtain ⟨i, hi, hm⟩ := BstLean.Part263.scalarRow_world_cover R hθ
    have F := BstLean.Part269.network_from_numerics hn hu (N i hi)
      (BstLean.Part263.scalarRow_cell_subset R i hm)
      (BstLean.Part269.direction_from_exact_window hn hθ)
      (BstLean.Part269.events_from_exact_window hn W hw hc hθ)
    refine ⟨⟨BstLean.Part219.directionMoment_mono F.interfaces.direction hM, ?_, ?_⟩,
      F.centre_energy.trans (hE i hi)⟩
    · exact ⟨by positivity, F.interfaces.energy.2.1,
        F.interfaces.energy.2.2.trans (pow_le_pow_left₀ F.interfaces.energy.1 hH 32)⟩
    · refine ⟨by norm_num, F.interfaces.parallel.2.trans ?_⟩
      exact sqrt_le_sqrt (div_le_div_of_nonneg_right hxi (Nat.cast_nonneg n))
  refine ⟨?_, fun c hw hc => (key c hw hc).1, fun c hw hc => (key c hw hc).2⟩
  intro c hw hc
  have hθ := BstLean.Part269.direction_from_exact_window hn
    (BstLean.Part269.exact_world_window (by omega) W hidden_eq lower upper hw hc)
  exact BstLean.Part252.window_of_theta (by omega) (paperDesignP n) c
    (BstLean.Part269.world_scale_pos W hw)
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- **The stated program from one row** whose base event is `sourceBase n`, odd and even. -/
theorem stated_from_row {n : ℕ} (R : BstLean.Part259.RowInputs n) (hn : 12000 ≤ n)
    (hbase : R.baseEvent = BstLean.Part262.sourceBase n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  rcases Nat.even_or_odd n with he | ho
  · rw [BstLean.Part272.statedDesign_even (by omega) he]
    exact BstLean.Part259.classifier_from_row R t
  · refine BstLean.Part278.classifier_from_row_st R t
      (BstLean.Part278.oddRoot_row R hn ho t (fun c hc => ?_))
    rw [hbase] at hc
    exact ⟨hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.2⟩

end BstLean.Part286
