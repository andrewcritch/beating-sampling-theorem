import BstLean.Part271R4CommonNumerics
import BstLean.Part271R4TableSharedTransfer
import BstLean.Part271R4CovarianceShared
import BstLean.Part271R4SupplyCore

namespace BstLean.Part271.R4.CommonSupplies
open Real Set BstLean.Part263

noncomputable def supplies {lo hi n : ℕ} (hlo : 13225 ≤ lo) (hhi : hi ≤ 16199)
    (hwidth : hi ≤ lo + 9) (G : GridCertificate lo)
    (htop : G.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000))
    (hn : n ∈ Icc lo hi) : Supplies n := by
  have ha : 13225 ≤ n := hlo.trans hn.1
  have hb : n ≤ 16199 := hn.2.trans hhi
  have hlo0 : (0 : ℝ) < lo := by exact_mod_cast (show 0 < lo by omega)
  let contain := SharedTable.containment G.top htop
  let T := SharedTable.tableCertificate.onBlock hlo hwidth G contain
  let F := SharedTable.frameCertificate.onBlock hlo hwidth G contain
  let R := T.scalarRow hn
  refine {
    scalar := R
    repair := F.repair hn
    covariance := SharedCovariance.covarianceInputs ⟨ha,hb⟩ R
      (by change G.top ∈ Icc _ _; exact htop) (F.repair hn)
    numerics := ?_
    direction_cap := ?_
    energy_cap := ?_
    parallel_cap := ?_
    centre_energy_cap := ?_
    frame_cap := ?_ }
  · intro i hi
    exact CommonNumerics.sourceNumerics ha hb R.H R.energy_allowance i hi
  · change SharedTable.tableCertificate.M ≤ 91 / 1000
    norm_num [SharedTable.tableCertificate]
  · change ((SharedTable.tableCertificate.H * (13225 : ℝ) / lo) * lo / n) ≤ (2101/100)/n
    rw [div_mul_cancel₀ _ (ne_of_gt hlo0)]
    exact div_le_div_of_nonneg_right (by norm_num [SharedTable.tableCertificate]) (Nat.cast_nonneg n)
  · change SharedTable.tableCertificate.xi ≤ 4 / 100
    norm_num [SharedTable.tableCertificate]
  · intro i hi
    exact CommonNumerics.energy_cap i hi
  · change SharedTable.tableCertificate.targetFrame ≤ BstLean.Part271.GlobalMaster.agent.frame
    norm_num [SharedTable.tableCertificate,BstLean.Part271.GlobalMaster.agent]

end BstLean.Part271.R4.CommonSupplies
