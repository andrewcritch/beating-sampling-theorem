import BstLean.Part293Assembly

/-! Exact low-floor pass interfaces, with the root price rounded only to the END allowance. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part228 BstLean.Part241 BstLean.Part289

structure RootInputs {n : ℕ} (t : ℝ) (z : Ret n) where
  split : SplitData n
  fluctuation : ℝ
  bias : ℝ
  lowerTail : ℝ
  upperTail : ℝ
  arithmetic : ℝ
  centre : z.1.2 ≠ 0
  bias_bound : BIAS_hyp (idealDesignFloor n (scaleFloor n)) z split bias
  fluctuation_bound : FLUCT_hyp (idealDesignFloor n (scaleFloor n)) t z split fluctuation
  tail : BulkChernoffDomain (idealDesignFloor n (scaleFloor n)) z lowerTail upperTail
  table_comparison : |√(qTilde (statedDesign2 n) t z) -
    √(qTilde (idealDesignFloor n (scaleFloor n)) t z)| ≤ arithmetic
  total : fluctuation + bias +
    bulkTailRoot (idealDesignFloor n (scaleFloor n)) z lowerTail upperTail + arithmetic ≤
      rootAllowance

theorem rootPrice_of_pass {n : ℕ} (hn : 8000 ≤ n) (t : ℝ) {E : Set (Ret n)}
    (S : ∀ z ∈ E, RootInputs t z) :
    RootPrice E (QStand (statedDesign2 n) t) (qTilde (statedDesign2 n) t) rootAllowance := by
  refine ⟨by norm_num [rootAllowance], ?_⟩
  intro z hz
  let P := S z hz
  have h := repla_root_of_split (by omega : 2 ≤ n)
    (idealDesignFloor n (scaleFloor n)) t z P.centre P.tail.tau_pos P.split
    P.fluctuation_bound P.bias_bound
    (tail_hyp_chernoff (idealDesignFloor n (scaleFloor n)) z P.tail)
  have ht := abs_sub_le (√(QStand (idealDesignFloor n (scaleFloor n)) t z))
    (√(qTilde (idealDesignFloor n (scaleFloor n)) t z))
    (√(qTilde (statedDesign2 n) t z))
  rw [abs_sub_comm (√(qTilde (idealDesignFloor n (scaleFloor n)) t z))] at ht
  rw [QStand_statedDesign2]
  exact (ht.trans (add_le_add h P.table_comparison)).trans P.total

end BstLean.Part293

/-- info: 'BstLean.Part293.rootPrice_of_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.rootPrice_of_pass
