import BstLean.Part293Envelope
import BstLean.Part293Passes

/-! One scalar envelope supplies every numerical field in the analytic pass interface. -/
namespace BstLean.Part293
open Real MeasureTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242 BstLean.Part289

structure EnvelopePassInputs {n : ℕ} (t : ℝ) (z : Ret n) where
  split : SplitData n
  window : WINDOW (idealDesignFloor n (scaleFloor n)) z
  eta : split.eta = 0.0045
  bias : SYPassInputsFloor (scaleFloor n) z split
    (Envelope.chi (1 / n)) 0.17919 0.028
    (Envelope.vmax (1 / n)) (Envelope.aw (1 / n)) (Envelope.af (1 / n))
    (Envelope.F8 (1 / n)) (Envelope.F24 (1 / n)) (Envelope.Gamma (1 / n))
    (Envelope.Cv (1 / n))
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

noncomputable def EnvelopePassInputs.toPassSupplies {n : ℕ} (hn : 8000 ≤ n)
    {t : ℝ} {z : Ret n} (P : EnvelopePassInputs t z) : PassSupplies t z where
  split := P.split
  chi := Envelope.chi (1 / n)
  vmax := Envelope.vmax (1 / n)
  aw := Envelope.aw (1 / n)
  af := Envelope.af (1 / n)
  F8 := Envelope.F8 (1 / n)
  F24 := Envelope.F24 (1 / n)
  reciprocal := Envelope.Gamma (1 / n)
  Cv := Envelope.Cv (1 / n)
  eps := Envelope.eps (1 / n)
  A := Envelope.A (1 / n)
  Dm := Envelope.D (1 / n)
  C := Envelope.chi2 (1 / n)
  B := Envelope.B (1 / n)
  Dd := Envelope.Dd (1 / n)
  window := P.window
  eta := P.eta
  bias := P.bias
  bias_numerics := by
    have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
    exact Envelope.biasNumericsBand _ (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  mixture_numerics := Envelope.mixtureNumericsBand hn
  removed := P.removed
  mixture := P.mixture
  displacement := P.displacement
  arithmetic := P.arithmetic

theorem rootPrice_of_envelope {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (t : ℝ) {E : Set (Ret n)} (P : ∀ z ∈ E, EnvelopePassInputs t z) :
    RootPrice E (QStand (statedDesign2 n) t) (qTilde (statedDesign2 n) t) rootAllowance :=
  rootPrice_of_pass hn t (fun z hz => ((P z hz).toPassSupplies hn).toRootInputs hn hn')

end BstLean.Part293

/-- info: 'BstLean.Part293.rootPrice_of_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.rootPrice_of_envelope
