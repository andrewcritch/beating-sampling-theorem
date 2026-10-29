import BstLean.Part262Events

/-! A dimension-dependent root constructor retains the original stored-pass
distribution, paper split, and realized network moment fields. -/
namespace BstLean.Part262
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part252 (eta mixtureFloor biasFloor chi epsilon varianceMax
  energyError locationError locationNorm varianceNorm biasRootCap)

noncomputable def rowSplit {n : ℕ} (c : Ret n) (wl ws : ℝ) : SplitData n :=
  BstLean.Part162.dPaper (paperDesignP n) c wl ws
    (√(2 / (n : ℝ) * mixtureFloor)) eta
    BstLean.Part252.eta_pos BstLean.Part252.eta_lt_one

theorem row_split_floor (n : ℕ) :
    (2 / (n : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (n : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg n))
    (by norm_num [mixtureFloor]))]
  unfold biasFloor
  ring

structure RootNumerics (n : ℕ) (root : ℝ) : Prop where
  dimension : 8000 ≤ n
  price : BstLean.Part241.squaredPrice n chi biasFloor epsilon varianceMax
    energyError locationError locationNorm varianceNorm ≤ biasRootCap ^ 2
  reserve : (23 / 10000 : ℝ) + biasRootCap + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ root

theorem bias_root {n : ℕ} {root : ℝ} (N : RootNumerics n root) :
    BstLean.Part241.biasRoot n chi biasFloor epsilon varianceMax
      energyError locationError locationNorm varianceNorm ≤ biasRootCap :=
  Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], N.price⟩

/-- Each field concerns the original split and actual retained network.
The fluctuation field remains an analytic obligation beyond the checked pilot. -/
structure RootEvidence {n : ℕ} (t : ℝ) (c : Ret n) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP n) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤ (2 / (n : ℝ)) * eR c * n * chi
  moments : BstLean.Part252.PaperMoments c
    (keptIx (paperDesignP n) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  fluctuation : FLUCT_hyp (paperDesignP n) t c (rowSplit c wl ws) (23 / 10000)

noncomputable def rootInputs {n : ℕ} {root t : ℝ} {c : Ret n}
    (N : RootNumerics n root) (E : RootEvidence t c) :
    BstLean.Part243.RootInputs n t c root where
  split := rowSplit c E.wl E.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := 0
  mix := 23 / 10000
  displacement := 0
  window := E.window
  passes := BstLean.Part252.passInputs_of_paperMoments (by have := N.dimension; omega) c
    BstLean.Part252.eta_pos BstLean.Part252.eta_lt_one (sqrt_nonneg _)
    E.energy_pos BstLean.Part252.bias_floor_ge (by norm_num [epsilon])
    BstLean.Part252.bias_threshold_pos (by norm_num [energyError])
    (by norm_num [locationError]) (by norm_num [locationNorm])
    (by norm_num [varianceNorm]) (row_split_floor n).le E.centre E.moments
  fluctuation := by simpa using E.fluctuation
  scalar := by
    have hb := bias_root N
    simp only [mul_zero, sqrt_zero, zero_add, add_zero]
    linarith [N.reserve]

theorem replacement {n : ℕ} {root t : ℝ} {c : Ret n}
    (N : RootNumerics n root) (E : RootEvidence t c) :
    |√(QStand (paperDesignP n) t c) - √(qTilde (paperDesignP n) t c)| ≤ root := by
  let R := rootInputs N E
  exact (BstLean.Part241.root_new_8000 N.dimension t c R.split R.window
    R.passes R.fluctuation).trans R.scalar

/-- The base-event payment and actual root fields consumed by RowInputs.
This structure is an interface; no unconditional interval value is asserted. -/
structure BaseRootSupply (n : ℕ) (H : Set (Ret n)) (root charge : ℝ) where
  event : Set (Ret n)
  measurable : MeasurableSet event
  payment : (retDist (paperCentres n)).real (H ∩ eventᶜ) ≤ charge
  inputs : ∀ (t : ℝ) (c : Ret n), c ∈ H → c ∈ event →
    BstLean.Part243.RootInputs n t c root

noncomputable def baseRootSupply {n : ℕ} {root b : ℝ} (hn : 12225 ≤ n)
    (N : RootNumerics n root) (H : Set (Ret n))
    (hTable : (retDist (paperCentres n)).real (tableEvent n)ᶜ ≤ b)
    (hEvidence : ∀ (t : ℝ) (c : Ret n), c ∈ H → c ∈ sourceBase n → RootEvidence t c) :
    BaseRootSupply n H root (599145 / 10 ^ 9 + b) where
  event := sourceBase n
  measurable := sourceBase_measurable (by omega)
  payment := sourceBase_charge hn hTable H
  inputs := fun t c hw hc => rootInputs N (hEvidence t c hw hc)

theorem baseRootSupply_row_root {n : ℕ} {H : Set (Ret n)} {root charge radius : ℝ}
    {covarianceEvent : Set (BstLean.Part160.AgFam n)}
    (S : BaseRootSupply n H root charge) :
    ∀ (t : ℝ) c, c ∈ goodSet H
      (S.event ∩ BstLean.Part259.covarianceGood covarianceEvent)
      (HbarW (paperDesignP n)) radius →
      Nonempty (BstLean.Part243.RootInputs n t c root) := by
  intro t c hc
  exact ⟨S.inputs t c hc.1.1 hc.2.1⟩

end BstLean.Part262
