import BstLean.Part247TI
import BstLean.Part246Charge
import BstLean.Part245Moment

/-! Option B: actual sharp TI supply, one covariance payment, and the moment payment.
The World noise window and positive scale remain explicit. -/
namespace BstLean.Part249
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part199 (exampleWide exampleCore)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4)
open BstLean.Part238

noncomputable def optionBDelta (n : ℕ) : ℝ :=
  53 * exp (-46) + 12 * exp (-2 * BstLean.Part247.eta ^ 2 * (mA n : ℝ))

def optionBSharp (n : ℕ) : Set (AgFam n) :=
  SharpCovEvent n exampleWide exampleCore (46 / 100) (528 / 1000)
    (67 / 100) (595 / 1000) (35 / 1000) (25 / 100) (63 / 100)
    (optionBDelta n / (1 / 4000))

theorem optionBSharp_measurable (n : ℕ) : MeasurableSet (optionBSharp n) :=
  measurableSet_SharpCovEvent _ _ _ _ _ _ _ _ _ _

theorem optionB_core_TI3 {n : ℕ} (hn : 11883 ≤ n) :
    TI3_hyp n (40 / 100) (63 / 100) (595 / 1000) (35 / 1000) (25 / 100)
      (optionBDelta n) :=
  BstLean.Part246.ta_TI3_sharp (by omega) (by norm_num) (by norm_num)
    (by norm_num [BstLean.Part247.eta]) (by norm_num)
    (BstLean.Part246.ta_num_sharp_of_244 (by norm_num) (BstLean.Part247.core_num hn))

theorem optionB_wide_TI3 {n : ℕ} (hn : 11883 ≤ n) :
    TI3_hyp n (34 / 100) (73 / 100) (663 / 1000) (35 / 1000) (40 / 100)
      (optionBDelta n) :=
  BstLean.Part246.ta_TI3_sharp (by omega) (by norm_num) (by norm_num)
    (by norm_num [BstLean.Part247.eta]) (by norm_num)
    (BstLean.Part246.ta_num_sharp_of_244 (by norm_num) (BstLean.Part247.wide_num hn))

theorem optionB_wide_TI {n : ℕ} (hn : 11883 ≤ n) :
    TI_hyp n (34 / 100) (73 / 100) (67 / 100) (optionBDelta n) :=
  TI_hyp_mono BstLean.Part247.wide_lam le_rfl
    (BstLean.Part244.TI_hyp_of_TI3 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (optionB_wide_TI3 hn))

theorem optionB_cutoff {n : ℕ} (hn : 11883 ≤ n) :
    optionBDelta n / (1 / 4000) ≤ (28 / 10 ^ 16 : ℝ) :=
  BstLean.Part246.cutoff_46 (BstLean.Part247.eta_exponent hn)

theorem optionB_ret_charge {n : ℕ} (hn : 11883 ≤ n)
    (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (optionBSharp n))ᶜ ≤ (1 / 4000 : ℝ) :=
  SharpCovEvent_ret_charge_M12 hn D hτW (by norm_num) (by norm_num)
    (by norm_num) (BstLean.Part247.core_lam.trans (by norm_num))
    (by unfold optionBDelta; positivity) (by norm_num)
    (optionB_wide_TI hn) (optionB_core_TI3 hn)

theorem optionB_covariance {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Icc (46 / 100) (528 / 1000))
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ (13 / 10) * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈ optionBSharp n) :
    COV_at D k (34 / 100) :=
  BstLean.Part246.cov_at_034_sharp_M12_charge_067 hn D k hτ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
    ((min_le_right _ _).trans BstLean.Part247.core_lam) le_rfl
    (BstLean.Part247.eta_exponent hn) hw hX hC

def optionBGood {n : ℕ} (D : Design n) : Set (Ret n) :=
  agentEv D (optionBSharp n) ∩ agentEv D (BstLean.Part245.MomentM12 n)

theorem optionBGood_measurable {n : ℕ} (D : Design n) : MeasurableSet (optionBGood D) :=
  (measurableSet_agentEv D (optionBSharp_measurable n)).inter
    (measurableSet_agentEv D (BstLean.Part245.measurableSet_MomentM12 n))

theorem optionB_good_charge {n : ℕ} (hn : 11883 ≤ n) (D : Design n)
    (hτW : TauWorld D) :
    (retDist D.toCentres).real (optionBGood D)ᶜ ≤ (3 / 10000 : ℝ) := by
  unfold optionBGood
  rw [Set.compl_inter]
  exact (measureReal_union_le _ _).trans
    ((add_le_add (optionB_ret_charge hn D hτW)
      (BstLean.Part245.moment_M12_ret hn D hτW)).trans (by norm_num))

theorem optionB_covariance_of_good {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Icc (46 / 100) (528 / 1000))
    (hk : k ∈ optionBGood D) : COV_at D k (34 / 100) :=
  optionB_covariance hn D k hτ hw (hk.2 hτ) (hk.1 hτ)

end BstLean.Part249
