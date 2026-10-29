import BstLean.Part177En
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R161Tail
import BstLean.Part187R161Red
import BstLean.Part187R161Fl
import BstLean.Part187R159Hat
import BstLean.Part187R159Win
import BstLean.Part187R159Frame
import BstLean.Part187R159Paper
import BstLean.Part187R159PaperF
import BstLean.Part187R159PaperW
import BstLean.Part187R159Uncond
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16
import BstLean.Part187R160Ledger2Gen
import BstLean.Part187R160Lib
import BstLean.Part187R160Event
import BstLean.Part187R160Cov
import BstLean.Part187R160MFNum
import BstLean.Part187R160Cov8
import BstLean.Part187R160ScEv
import BstLean.Part187R160Theta
import BstLean.Part187R160Sc
import BstLean.Part187R160ScTab
import BstLean.Part187R160ScLo
import BstLean.Part187R165Ev
import BstLean.Part187R160MFB3
import BstLean.Part187R160MFB4
import BstLean.Part187R160MFBNum
import BstLean.Part187R160Comb
import BstLean.Part187R163Comb
import BstLean.Part187R164Bnd
import BstLean.Part187R164End
import BstLean.Part187R165End
import BstLean.Part187R169In
import BstLean.Part187R169Mom
import BstLean.Part187R169Op
import BstLean.Part187R169Var
import BstLean.Part187R170End
import BstLean.Part187R175Mass
import BstLean.Part187R175Cert

/-! Part 187 (file `Part187R177En`): copy of `Part177En` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part177.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg hid2 mA)
open BstLean.Part157
open BstLean.Part161 (Ix muI xLat latC hhMat consV uHat)
open BstLean.Part160 (AgFam agKey agentEv)
open BstLean.Part153 (nuA)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

lemma charge_num {n : ℕ} (hn : 16250 ≤ n) :
    Real.exp (8 * ((2400 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2) / (11 / 10) ^ 200 ≤ 1 / 10 ^ 6 := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 8 * ((2400 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (16250 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
    push_cast; nlinarith
  have h2 : Real.exp (8 * ((2400 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤ 3 :=
    (Real.exp_le_exp.2 h1).trans (by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith)
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ (3 : ℝ) := h2
    _ ≤ 1 / 10 ^ 6 * (11 / 10) ^ 200 := by norm_num


/-- **The charge of the energy event**: at most `10⁻⁶` for every `(ĉ, τ₀)` (`n ≥ 16 384`, no upper
end), from the moment hypothesis `HMom n` (Markov at order 200 on `Y`, Jensen, Tonelli). -/
theorem SEn_charge (hn : 16250 ≤ n) (hmom : HMom n) (ch : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real {θ | ((ch, τ), θ) ∉ SEn n} ≤ 1 / 10 ^ 6 := by
  have hn1 : 1 ≤ n := by omega
  have mf := measurable_fK (n := n) ch τ
  have f0 : ∀ θ a v, 0 ≤ fK ch τ θ a v := fun θ a v => by unfold fK; exact omK_nonneg _ _
  have fb : ∀ θ a v, fK ch τ θ a v ≤ BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n :=
    fun θ a v => by unfold fK; exact omK_le hn1 θ (normSq_ptK_le hn1 ch τ a v)
  -- measurability in (a, v) for fixed θ
  have mfθ : ∀ θ, Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => fK ch τ θ p.1 p.2) := fun θ =>
    measurable_fK_av ch τ θ
  -- Jensen: `Y^200 ≤ ∫∫ f^2400`
  have hJ : ∀ θ, YEn ((ch, τ), θ) ^ 200 ≤ ∫ a, ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1)) ∂muI n := by
    intro θ
    set B := BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n
    have hB0 : 0 ≤ B := le_trans (f0 θ 0 0) (fb θ 0 0)
    have bnd : ∀ a v, |fK ch τ θ a v ^ 12| ≤ B ^ 12 := fun a v => by
      rw [abs_of_nonneg (pow_nonneg (f0 θ a v) _)]; exact pow_le_pow_left₀ (f0 θ a v) (fb θ a v) _
    have bnd2 : ∀ a v, |fK ch τ θ a v ^ 2400| ≤ B ^ 2400 := fun a v => by
      rw [abs_of_nonneg (pow_nonneg (f0 θ a v) _)]; exact pow_le_pow_left₀ (f0 θ a v) (fb θ a v) _
    have mF : Measurable (fun a => ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))) :=
      (((mfθ θ).pow_const 12).stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin (n - 1)))).measurable
    have mG : Measurable (fun a => ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1))) :=
      (((mfθ θ).pow_const 2400).stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin (n - 1)))).measurable
    have iv : ∀ a, Integrable (fun v => fK ch τ θ a v ^ 12) (stdGauss (Fin (n - 1))) := fun a =>
      intOfBdd ((measurable_fK_v ch τ θ a).pow_const 12) (bnd a)
    have iv2 : ∀ a, Integrable (fun v => fK ch τ θ a v ^ 2400) (stdGauss (Fin (n - 1))) := fun a =>
      intOfBdd ((measurable_fK_v ch τ θ a).pow_const 2400) (bnd2 a)
    have Fb : ∀ a, |∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))| ≤ B ^ 12 := fun a => by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ v, |fK ch τ θ a v ^ 12| ∂stdGauss (Fin (n - 1)) ≤ ∫ v, B ^ 12 ∂stdGauss (Fin (n - 1)) :=
            integral_mono (iv a).abs (integrable_const _) (bnd a)
        _ = B ^ 12 := by simp
    have F0 : ∀ a, 0 ≤ ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1)) := fun a =>
      integral_nonneg fun v => pow_nonneg (f0 θ a v) _
    have Gb : ∀ a, |∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1))| ≤ B ^ 2400 := fun a => by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ v, |fK ch τ θ a v ^ 2400| ∂stdGauss (Fin (n - 1)) ≤ ∫ v, B ^ 2400 ∂stdGauss (Fin (n - 1)) :=
            integral_mono (iv2 a).abs (integrable_const _) (bnd2 a)
        _ = B ^ 2400 := by simp
    have iF : Integrable (fun a => ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))) (muI n) := intOfBdd mF Fb
    have iF2 : Integrable (fun a => (∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))) ^ 200) (muI n) :=
      intOfBdd (mF.pow_const 200) (fun a => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (Fb a) _)
    have iG : Integrable (fun a => ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1))) (muI n) := intOfBdd mG Gb
    have hout := (convexOn_pow 200).map_integral_le (μ := muI n)
      (f := fun a => ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))) (continuous_pow 200).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun a => Set.mem_Ici.mpr (F0 a)) iF iF2
    rw [YEn_eq]
    refine hout.trans (integral_mono iF2 iG fun a => ?_)
    have hin := (convexOn_pow 200).map_integral_le (μ := stdGauss (Fin (n - 1)))
      (f := fun v => fK ch τ θ a v ^ 12) (continuous_pow 200).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun v => Set.mem_Ici.mpr (pow_nonneg (f0 θ a v) _)) (iv a)
      (by simpa only [Function.comp_def, ← pow_mul] using iv2 a)
    simpa only [Function.comp_def, ← pow_mul] using hin
  -- integrability for each `θ`
  have hint : ∀ θ : TH n, (∀ a, Integrable (fun v => fK ch τ θ a v ^ 2400) (stdGauss (Fin (n - 1))))
      ∧ Integrable (fun a => ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1))) (muI n) := by
    intro θ
    set B := BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n
    have bnd2 : ∀ a v, |fK ch τ θ a v ^ 2400| ≤ B ^ 2400 := fun a v => by
      rw [abs_of_nonneg (pow_nonneg (f0 θ a v) _)]; exact pow_le_pow_left₀ (f0 θ a v) (fb θ a v) _
    have iv2 : ∀ a, Integrable (fun v => fK ch τ θ a v ^ 2400) (stdGauss (Fin (n - 1))) := fun a =>
      intOfBdd ((measurable_fK_v ch τ θ a).pow_const 2400) (bnd2 a)
    refine ⟨iv2, intOfBdd (M := B ^ 2400) (((mfθ θ).pow_const 2400).stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable fun a => ?_⟩
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |fK ch τ θ a v ^ 2400| ∂stdGauss (Fin (n - 1))
        ≤ ∫ v, B ^ 2400 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (iv2 a).abs (integrable_const _) (bnd2 a)
      _ = B ^ 2400 := by simp
  -- the lintegral form
  have hL : ∀ θ : TH n, ENNReal.ofReal (∫ a, ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1)) ∂muI n)
      = ∫⁻ a, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1)) ∂muI n := by
    intro θ
    rw [ofReal_integral_eq_lintegral_ofReal (hint θ).2 (Filter.Eventually.of_forall fun a =>
      integral_nonneg fun v => pow_nonneg (f0 θ a v) _)]
    refine lintegral_congr fun a => ?_
    exact ofReal_integral_eq_lintegral_ofReal ((hint θ).1 a)
      (Filter.Eventually.of_forall fun v => pow_nonneg (f0 θ a v) _)
  -- joint measurability
  have mJ : Measurable (fun p : (TH n × Ix n) × (Fin (n - 1) → ℝ) =>
      ENNReal.ofReal (fK ch τ p.1.1 p.1.2 p.2 ^ 2400)) :=
    ENNReal.measurable_ofReal.comp (mf.pow_const 2400)
  have mI : Measurable (fun p : TH n × Ix n =>
      ∫⁻ v, ENNReal.ofReal (fK ch τ p.1 p.2 v ^ 2400) ∂stdGauss (Fin (n - 1))) :=
    mJ.lintegral_prod_right'
  have mO : Measurable (fun θ : TH n =>
      ∫⁻ a, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1)) ∂muI n) :=
    mI.lintegral_prod_right'
  -- the total
  set E : ℝ := Real.exp (8 * ((2400 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2) with hE
  have hpt : ∀ a v, ∫⁻ θ, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂nuA n ≤ ENNReal.ofReal E := by
    intro a v
    obtain ⟨hi, hb⟩ := hmom (ptK ch τ a v) (normSq_ptK_le hn1 ch τ a v) 2400
    have e : ∀ θ : TH n, fK ch τ θ a v ^ 2400 =
        (normSq (hid2 θ.1 θ.2 (ptK ch τ a v)) / (n : ℝ)) ^ 2400 := fun θ => by
      unfold fK omK; rfl
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun θ =>
      pow_nonneg (div_nonneg (normSq_nonneg _) (Nat.cast_nonneg n)) _)]
    exact ENNReal.ofReal_le_ofReal hb
  have htot : ∫⁻ θ, ∫⁻ a, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1))
      ∂muI n ∂nuA n ≤ ENNReal.ofReal E := by
    rw [lintegral_lintegral_swap mI.aemeasurable]
    calc ∫⁻ a, ∫⁻ θ, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1)) ∂nuA n
          ∂muI n
        = ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n := by
          refine lintegral_congr fun a => ?_
          have ma : Measurable (fun p : TH n × (Fin (n - 1) → ℝ) =>
              ENNReal.ofReal (fK ch τ p.1 a p.2 ^ 2400)) :=
            ENNReal.measurable_ofReal.comp ((measurable_fK_θv ch τ a).pow_const 2400)
          exact lintegral_lintegral_swap ma.aemeasurable
      _ ≤ ∫⁻ a, ∫⁻ v, ENNReal.ofReal E ∂stdGauss (Fin (n - 1)) ∂muI n :=
          lintegral_mono fun a => lintegral_mono fun v => hpt a v
      _ = ENNReal.ofReal E := by
          have hρ : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by
            unfold stdGauss; infer_instance
          simp
  -- Markov
  set T : ℝ := (11 / 10) ^ 200 with hT
  have hT0 : 0 < T := by positivity
  have hsub : {θ | ((ch, τ), θ) ∉ SEn n} ⊆ {θ : TH n | ENNReal.ofReal T ≤
      ∫⁻ a, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1)) ∂muI n} := by
    intro θ hθ
    simp only [SEn, Set.mem_ofPred_eq, not_le] at hθ
    simp only [Set.mem_ofPred_eq]
    rw [← hL θ]
    refine ENNReal.ofReal_le_ofReal ?_
    exact (pow_le_pow_left₀ (by norm_num) hθ.le 200).trans (hJ θ)
  have hM := meas_ge_le_lintegral_div mO.aemeasurable (μ := nuA n)
    (ε := ENNReal.ofReal T) (by simpa using hT0) ENNReal.ofReal_ne_top
  have hfin : (nuA n) {θ | ((ch, τ), θ) ∉ SEn n} ≤ ENNReal.ofReal (E / T) := by
    refine (measure_mono hsub).trans (hM.trans ?_)
    rw [ENNReal.ofReal_div_of_pos hT0]
    exact ENNReal.div_le_div_right htot _
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hfin).trans ?_
  exact charge_num hn

/-- **The charge of the energy event under the distribution of the retained data.** -/
theorem SEn_ret_charge (hn : 16250 ≤ n) (hmom : HMom n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SEn n))ᶜ ≤
      1 / 10 ^ 6 := by
  rw [BstLean.Part160.agentEv_compl]
  exact BstLean.Part160.retDist_agent_charge (paperDesign n fT wT hf hw)
    (BstLean.Part160.paperDesign_tauWorld fT wT hf hw) (measurableSet_SEn n) (by norm_num)
    (fun c τ _ => SEn_charge hn hmom c τ)

end BstLean.Part177.R
