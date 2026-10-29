import BstLean.Part278Err
import BstLean.Part241Frontier
import BstLean.Part188R161Fl

/-!
# Part 278 (O4): root transfer between two tables, and the use of the reserve `10⁻²⁰`

Paper: `theorem7-09-assembly.tex` (the root of the odd tables, paid by the reserved `10⁻²⁰`).

* `QStand_st`: `Q` does not read the stored tables, so `Q(statedDesign) = Q(paperDesignP)`.
* `qTilde_table_root`: two designs with the same `τ₀` and the same retained data:
  `|√q̃(D′) − √q̃(D)| ≤ √K` when the Gaussian Hellinger term of the two tables is at most `K` at
  every latitude.
* `qTilde_table_root_window`: the same with a relative scale error `δ_S ≤ 1/2`, a location error
  `δ_λ` and a scale floor `S₀`: `K = n δ_S² + δ_λ² |c_A|²/(2 S₀)`.
* `repla_transfer`: `REPLA(D, h_A)` and a table root `≤ δ` give `REPLA(D′, h_A + δ)`.
* `root_new_8000_st`: the root of `Part241.root_new_8000` for the stated design, under the
  hypothesis `hodd` (odd root `≤ 10⁻²⁰`).
* `repla_of_hyps_chi_st`: `REPLA_mix_hyp (statedDesign n) t hAL E` for `n ≥ 16 200` from the
  hypotheses of `Part188.Base161_R.repla_of_hyps_chi` for `paperDesignP` and `hodd` on `E`.

O4 step 1 (the check). `Part241.root_new_8000` gets its last term `10⁻²⁰` from
`0 ≤ 1/10^20` by `linarith`; `Part161.repla_arith` closes `0.002159 + 0.004295 + √(8e^{−20})
≤ hAL` from `tail_root_num` (`< 0.000129`) without the `10⁻²⁰`. The two theorems
`root_new_8000_st` and `repla_of_hyps_chi_st` below spend that reserve, and no other term.
-/

namespace BstLean.Part278

open Real MeasureTheory
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157 (Ret Design qTilde QStand REPLA_mix_hyp)
open BstLean.Part161 (qTilde_eq_lat qtLat latC muI gP_root root_mix_abs measurable_qtLat
  gP_nonneg gP_le_one hellG2 hellG2_le_window measurableSet_clsSet SplitData WINDOW
  FLUCT_hyp FLUCT_chi_hyp BIAS_hyp)
open BstLean.Part169 (paperDesignP)
open BstLean.Part272 (statedDesign)

variable {n : ℕ}

/-- `Q` reads only the centres and `τ₀`, which the two designs share. -/
theorem QStand_st (t : ℝ) (c : Ret n) :
    QStand (statedDesign n) t c = QStand (paperDesignP n) t c := rfl

theorem latC_congr (D D' : Design n) (hτ : D'.tau0 = D.tau0) (c : Ret n) :
    latC D' c = latC D c := by
  funext a; unfold latC; rw [hτ]

/-- **O4.** Two tables on the same retained data and the same draws. -/
theorem qTilde_table_root (D D' : Design n) (hτ : D'.tau0 = D.tau0) (t : ℝ) (c : Ret n) {K : ℝ}
    (hK : ∀ s, hellG2 n (((D'.mix c s).1 - (D.mix c s).1) ^ 2 * normSq c.2.1.2)
      (D'.mix c s).2 (D.mix c s).2 ≤ K) :
    |√(qTilde D' t c) - √(qTilde D t c)| ≤ √K := by
  have hpt : ∀ a, (√(qtLat D' t c a) - √(qtLat D t c a)) ^ 2 ≤ K := by
    intro a
    unfold qtLat
    rw [latC_congr D D' hτ c]
    exact (gP_root _ (measurableSet_clsSet c t) _ _ _ _ _).trans (hK _)
  have h := root_mix_abs (muI n) (X := qtLat D' t c) (Y := qtLat D t c) (K := fun _ => K)
    (measurable_qtLat D' t c) (measurable_qtLat D t c) (fun a => gP_nonneg _ _ _)
    (fun a => gP_le_one _ _ _) (fun a => gP_nonneg _ _ _) (fun a => gP_le_one _ _ _)
    (integrable_const K) hpt
  have hc : ∫ _a, K ∂muI n = K := by simp
  rw [qTilde_eq_lat, qTilde_eq_lat]
  rw [hc] at h
  exact h

/-- **O4** with a relative scale error, a location error and a scale floor. -/
theorem qTilde_table_root_window (D D' : Design n) (hτ : D'.tau0 = D.tau0) (t : ℝ) (c : Ret n)
    {dL δS S0 : ℝ} (hS0 : 0 < S0) (hSD : ∀ s, S0 ≤ (D.mix c s).2)
    (hSD' : ∀ s, 0 < (D'.mix c s).2)
    (hL : ∀ s, |(D'.mix c s).1 - (D.mix c s).1| ≤ dL)
    (hS : ∀ s, |(D'.mix c s).2 / (D.mix c s).2 - 1| ≤ δS) (hδS : δS ≤ 1 / 2) :
    |√(qTilde D' t c) - √(qTilde D t c)| ≤
      √(n * δS ^ 2 + dL ^ 2 * normSq c.2.1.2 / (2 * S0)) := by
  refine qTilde_table_root D D' hτ t c fun s => ?_
  have hS2 : 0 < (D.mix c s).2 := lt_of_lt_of_le hS0 (hSD s)
  have hδ0 : 0 ≤ δS := (abs_nonneg _).trans (hS s)
  have hc0 := normSq_nonneg c.2.1.2
  have h := hellG2_le_window n (hSD' s) hS2 (mul_nonneg (sq_nonneg ((D'.mix c s).1 - (D.mix c s).1)) hc0) (hS s)
    (by linarith)
  refine h.trans (add_le_add ?_ ?_)
  · have hden : 1 ≤ 4 * (1 - δS) ^ 2 := by nlinarith
    have hsq : ((D'.mix c s).2 / (D.mix c s).2 - 1) ^ 2 ≤ δS ^ 2 := by
      rw [← sq_abs ((D'.mix c s).2 / (D.mix c s).2 - 1)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hS s) 2
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    calc (n:ℝ) * ((D'.mix c s).2 / (D.mix c s).2 - 1) ^ 2 / (4 * (1 - δS) ^ 2)
        ≤ (n:ℝ) * ((D'.mix c s).2 / (D.mix c s).2 - 1) ^ 2 :=
          div_le_self (mul_nonneg hn0 (sq_nonneg _)) hden
      _ ≤ n * δS ^ 2 := mul_le_mul_of_nonneg_left hsq hn0
  · have hl : ((D'.mix c s).1 - (D.mix c s).1) ^ 2 ≤ dL ^ 2 := by
      rw [← sq_abs ((D'.mix c s).1 - (D.mix c s).1)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hL s) 2
    calc ((D'.mix c s).1 - (D.mix c s).1) ^ 2 * normSq c.2.1.2 / (2 * (D.mix c s).2)
        ≤ dL ^ 2 * normSq c.2.1.2 / (2 * (D.mix c s).2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl hc0) (by linarith)
      _ ≤ dL ^ 2 * normSq c.2.1.2 / (2 * S0) :=
          div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) hc0) (by linarith)
            (by linarith [hSD s])

/-- `REPLA(D, h_A)` and a table root `δ` give `REPLA(D′, h_A + δ)` when `Q` agrees. -/
theorem repla_transfer {D D' : Design n} {t hA δ : ℝ} {E : Set (Ret n)}
    (hQ : ∀ c, QStand D' t c = QStand D t c) (h : REPLA_mix_hyp D t hA E)
    (hd : ∀ c ∈ E, |√(qTilde D' t c) - √(qTilde D t c)| ≤ δ) :
    REPLA_mix_hyp D' t (hA + δ) E := by
  intro c hc
  rw [hQ c]
  have h1 := h c hc
  have h2 := hd c hc
  have h3 := abs_sub_le (√(QStand D t c)) (√(qTilde D t c)) (√(qTilde D' t c))
  rw [abs_sub_comm (√(qTilde D t c))] at h3
  linarith

/-- **O4.** The root of `Part241.root_new_8000` for the stated design, when the odd tables move
the root of `q̃` by at most `10⁻²⁰` (`hodd`). This spends the reserve `10⁻²⁰` and nothing else. -/
theorem root_new_8000_st (hn : 8000 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hW : WINDOW (paperDesignP n) c)
    {χ d ε vmax aw af Hf Cv B hmix Dd : ℝ}
    (P : BstLean.Part241.PassInputs c split χ d ε vmax aw af Hf Cv)
    (hF : FLUCT_hyp (paperDesignP n) t c split (√(2 * (1 + split.eta⁻¹) * B) + hmix + √Dd))
    (hodd : |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20) :
    |√(QStand (statedDesign n) t c) - √(qTilde (statedDesign n) t c)| ≤
      √(2 * (1 + split.eta⁻¹) * B) + hmix + √Dd +
        BstLean.Part241.biasRoot n χ d ε vmax aw af Hf Cv + 1 / 10 ^ 8 + 1 / 10 ^ 20 := by
  obtain ⟨hroot, htail⟩ := BstLean.Part241.conditional_pass_root_frontier hn t c split hW P hF
  rw [QStand_st]
  have h3 := abs_sub_le (√(QStand (paperDesignP n) t c)) (√(qTilde (paperDesignP n) t c))
    (√(qTilde (statedDesign n) t c))
  rw [abs_sub_comm (√(qTilde (paperDesignP n) t c))] at h3
  linarith

/-- **O4.** `REPLA_mix_hyp` for the stated design at `n ≥ 16 200`, from the hypotheses of
`Part188.Base161_R.repla_of_hyps_chi` for `paperDesignP` and the odd root bound `hodd` on `E`. -/
theorem repla_of_hyps_chi_st (hn : 16200 ≤ n) (t : ℝ) {E : Set (Ret n)}
    (hw : ∀ c ∈ E, WINDOW (paperDesignP n) c)
    (hd : ∀ c ∈ E, ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
      FLUCT_chi_hyp (paperDesignP n) c d ε₀ δ₀ slow (2159 / 10 ^ 6) ∧
        BIAS_hyp (paperDesignP n) c d (4295 / 10 ^ 6))
    (hodd : ∀ c ∈ E,
      |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20) :
    REPLA_mix_hyp (statedDesign n) t BstLean.Part156.hAL E := by
  have h0 : REPLA_mix_hyp (paperDesignP n) t (6583 / 10 ^ 6) E := by
    intro c hc
    obtain ⟨d, ε₀, δ₀, slow, hF, hB⟩ := hd c hc
    have hwc := hw c hc
    have h := BstLean.Part161.repla_root_of_split (by omega) (paperDesignP n) t c hwc.1 hwc.2.1 d
      (BstLean.Part161.fluct_of_chi (paperDesignP n) t c d hF) hB
      (BstLean.Part188.Base161_R.tail_of_window hn (paperDesignP n) c hwc)
    have ht := BstLean.Part161.tail_root_num
    linarith
  have h1 := repla_transfer (D := paperDesignP n) (D' := statedDesign n)
    (fun c => QStand_st t c) h0 hodd
  unfold BstLean.Part156.hAL
  exact h1

end BstLean.Part278
