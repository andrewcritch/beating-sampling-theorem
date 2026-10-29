import BstLean.Part242HQPass
import BstLean.Part242Pass

/-! The improved integrated moments enter the original conditional-pass root. -/
namespace BstLean.Part242
open MeasureTheory Real
open scoped ENNReal
open BstLean.Part130 (normSq)
open BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169
open BstLean.Part29 (stdGauss)

variable {n : ℕ}

lemma condMom_nonneg (split : SplitData n)
    (F : Ix n → (Fin (n - 1) → ℝ) → ℝ) (k : ℕ) (a : Ix n) :
    0 ≤ condMom split F k a := by
  unfold condMom
  have hβ := removed_le_one (stdGauss (Fin (n - 1))) split.good a
  exact mul_nonneg (inv_nonneg.mpr (by linarith))
    (integral_nonneg fun v => pow_nonneg (abs_nonneg _) k)

theorem mixture_price_SY2 (D : Design n) (t : ℝ) (c : Ret n) (split : SplitData n)
    {ε δ A Dm C : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hδ : 0 ≤ δ)
    (hA : 0 < A) (hDm : 0 < Dm)
    (hS0 : ∀ a ∈ keptIx D c split, 0 < split.S0 a)
    (hwin : ∀ a ∈ keptIx D c split, ∀ v ∈ slice split a,
      |sA D c a v / split.S0 a - 1| ≤ ε ∧ |lA D c a v - split.lam0 a| ≤ δ)
    (hcent : ∀ a ∈ keptIx D c split,
      (∫ v in slice split a, (lA D c a v - split.lam0 a) ∂stdGauss (Fin (n - 1))) = 0 ∧
      (∫ v in slice split a, (sA D c a v / split.S0 a - 1) ∂stdGauss (Fin (n - 1))) = 0)
    (hv : LBound ((muI n).restrict (keptIx D c split)) 3 (condMom split (epsF D c split) 2) A)
    (hw : LBound ((muI n).restrict (keptIx D c split)) 3 (condMom split (delF D c split) 2) Dm)
    (iChi : IntegrableOn (chiK D c split) (keptIx D c split) (muI n))
    (hChi : ∫ a in keptIx D c split, chiK D c split a ∂muI n ≤ C) :
    ∫ a in keptIx D c split,
      (sqrt (goodMean (stdGauss (Fin (n - 1))) split.good (pLat D t c) a) -
        sqrt (q0Lat t c split a)) ^ 2 ∂muI n ≤ C / 4 + 6 * mixL3 n ε A Dm ^ 3 := by
  have hL := HQ_L3 n hε1 hA hDm hv hw
    (condMom_nonneg split _ 2) (condMom_nonneg split _ 2)
  apply HQ_integral iChi hChi hL
    (fun a => BstLean.Part207.hqL_nonneg hε1 (condMom_nonneg split _ 2 a)
      (condMom_nonneg split _ 2 a))
  apply (ae_restrict_iff' (measurableSet_keptSet _ split.mgood (measurableSet_bulkIx D c) _)).mpr
  apply Filter.Eventually.of_forall
  intro a ha
  have hβ : removed (stdGauss (Fin (n - 1))) split.good a < 1 :=
    lt_of_le_of_lt ha.2 split.eta_lt
  exact root_le_hq_paper D t c split a hβ (hS0 a ha) hε0 hε1 hδ (hwin a ha)
    (hcent a ha).1 (hcent a ha).2

theorem fluctuation_of_SY2 (D : Design n) (t : ℝ) (c : Ret n) (split : SplitData n)
    {ε A Dm C B Dd : ℝ}
    (hB : ∫ a, removed (stdGauss (Fin (n - 1))) split.good a ∂muI n ≤ B)
    (hMix : ∫ a in keptIx D c split,
      (sqrt (goodMean (stdGauss (Fin (n - 1))) split.good (pLat D t c) a) -
        sqrt (q0Lat t c split a)) ^ 2 ∂muI n ≤ C / 4 + 6 * mixL3 n ε A Dm ^ 3)
    (hDisp : ∫ a in keptIx D c split,
      hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
        (split.S0 a) (split.Sb a) ∂muI n ≤ Dd) :
    FLUCT_hyp D t c split
      (sqrt (2 * (1 + split.eta⁻¹) * B) + sqrt (C / 4 + 6 * mixL3 n ε A Dm ^ 3) + sqrt Dd) :=
  ⟨B, C / 4 + 6 * mixL3 n ε A Dm ^ 3, Dd, hB, hMix, hDisp, le_rfl⟩

theorem root_SY_SY2_8000 (hn : 8000 ≤ n) (t : ℝ) (c : Ret n) (split : SplitData n)
    (hW : WINDOW (paperDesignP n) c)
    {χ d ε vmax aw af F8 F24 Γ Cv εmix A Dm C B Dd : ℝ}
    (P : SYPassInputs c split χ d ε vmax aw af F8 F24 Γ Cv)
    (hB : ∫ a, removed (stdGauss (Fin (n - 1))) split.good a ∂muI n ≤ B)
    (hMix : ∫ a in keptIx (paperDesignP n) c split,
      (sqrt (goodMean (stdGauss (Fin (n - 1))) split.good (pLat (paperDesignP n) t c) a) -
        sqrt (q0Lat t c split a)) ^ 2 ∂muI n ≤ C / 4 + 6 * mixL3 n εmix A Dm ^ 3)
    (hDisp : ∫ a in keptIx (paperDesignP n) c split,
      hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq c.2.1.2)
        (split.S0 a) (split.Sb a) ∂muI n ≤ Dd) :
    |sqrt (QStand (paperDesignP n) t c) - sqrt (qTilde (paperDesignP n) t c)| ≤
      sqrt (2 * (1 + split.eta⁻¹) * B) + sqrt (C / 4 + 6 * mixL3 n εmix A Dm ^ 3) +
        sqrt Dd + syBiasRoot n χ d ε vmax aw af F8 F24 Γ Cv + 1 / 10 ^ 8 + 1 / 10 ^ 20 := by
  exact conditional_pass_root_SY_8000 hn t c split hW P
    (fluctuation_of_SY2 (paperDesignP n) t c split hB hMix hDisp)

/-- A retained-data selection of the proved packages adds no event charge. -/
theorem root_SY_on_event_8000 (hn : 8000 ≤ n) (t Hroot : ℝ) {E : Set (Ret n)}
    (h : ∀ c ∈ E, ∃ (split : SplitData n) (χ d ε vmax aw af F8 F24 Γ Cv hfl : ℝ),
      WINDOW (paperDesignP n) c ∧ SYPassInputs c split χ d ε vmax aw af F8 F24 Γ Cv ∧
      FLUCT_hyp (paperDesignP n) t c split hfl ∧
      hfl + syBiasRoot n χ d ε vmax aw af F8 F24 Γ Cv + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ Hroot) :
    REPLA_mix_hyp (paperDesignP n) t Hroot E := by
  intro c hc
  obtain ⟨split, χ, d, ε, vmax, aw, af, F8, F24, Γ, Cv, hfl, hW, P, hF, hsum⟩ := h c hc
  exact (conditional_pass_root_SY_8000 hn t c split hW P hF).trans hsum

end BstLean.Part242
