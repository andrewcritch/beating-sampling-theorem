import BstLean.Part252Pass
import BstLean.Part252Scalar

/-! The dimension-12225 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12225) (wl ws : ℝ) : SplitData 12225 :=
  BstLean.Part162.dPaper (paperDesignP 12225) c wl ws
    (√(2 / (12225 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12225 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12225 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12225) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12225) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12225 : ℝ)) * eR c * 12225 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12225) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12225 - 1)))
    (rowSplit c wl ws).good a ∂muI 12225 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12225) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12225 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12225) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12225 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12225) c (rowSplit c wl ws),
    hellG2 12225 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12225 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12225} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12225} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12225} (R : RootSource t c) :
    |√(QStand (paperDesignP 12225) t c) - √(qTilde (paperDesignP 12225) t c)| ≤
      BstLean.Part243.rowRoot := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part252
