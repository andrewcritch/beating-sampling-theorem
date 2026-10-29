import BstLean.Part293EnvelopePass

/-! Fixed bias caps let the table adapter spend the available root allowance. -/
namespace BstLean.Part293
open Real MeasureTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242 BstLean.Part289

structure CappedPassInputs {n : ℕ} (t : ℝ) (z : Ret n) where
  split : SplitData n
  window : WINDOW (idealDesignFloor n (scaleFloor n)) z
  eta : split.eta = 0.0045
  bias : SYPassInputsFloor (scaleFloor n) z split
    1.081 0.17919 0.028 0.00411 0.1802 0.05125 0.85428 0.86139 3.721 0.0003804
  removed : ∫ a, BstLean.Part161.removed (stdGauss (Fin (n - 1))) split.good a
    ∂muI n ≤ Envelope.B (1 / n)
  mixture : ∫ a in keptIx (idealDesignFloor n (scaleFloor n)) z split,
    (√(goodMean (stdGauss (Fin (n - 1))) split.good
      (pLat (idealDesignFloor n (scaleFloor n)) t z) a) - √(q0Lat t z split a)) ^ 2 ∂muI n ≤
      Envelope.chi2 (1 / n) / 4 +
        6 * mixL3 n (Envelope.eps (1 / n)) (Envelope.A (1 / n)) (Envelope.D (1 / n)) ^ 3
  displacement : ∫ a in keptIx (idealDesignFloor n (scaleFloor n)) z split,
    hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq z.2.1.2)
      (split.S0 a) (split.Sb a) ∂muI n ≤ Envelope.Dd (1 / n)
  arithmetic : |√(qTilde (statedDesign2 n) t z) -
    √(qTilde (idealDesignFloor n (scaleFloor n)) t z)| ≤ 1 / 10 ^ 20

noncomputable def CappedPassInputs.toPassSupplies {n : ℕ} (hn : 8000 ≤ n)
    {t : ℝ} {z : Ret n} (P : CappedPassInputs t z) : PassSupplies t z where
  split := P.split
  chi := 1.081
  vmax := 0.00411
  aw := 0.1802
  af := 0.05125
  F8 := 0.85428
  F24 := 0.86139
  reciprocal := 3.721
  Cv := 0.0003804
  eps := Envelope.eps (1 / n)
  A := Envelope.A (1 / n)
  Dm := Envelope.D (1 / n)
  C := Envelope.chi2 (1 / n)
  B := Envelope.B (1 / n)
  Dd := Envelope.Dd (1 / n)
  window := P.window
  eta := P.eta
  bias := P.bias
  bias_numerics := by constructor <;> norm_num
  mixture_numerics := Envelope.mixtureNumericsBand hn
  removed := P.removed
  mixture := P.mixture
  displacement := P.displacement
  arithmetic := P.arithmetic

end BstLean.Part293

/-- info: 'BstLean.Part293.CappedPassInputs.toPassSupplies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.CappedPassInputs.toPassSupplies
