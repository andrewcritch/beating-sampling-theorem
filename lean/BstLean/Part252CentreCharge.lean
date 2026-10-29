import BstLean.Part252CentreMeas
import BstLean.Part252Centre
import BstLean.Part153PPs3
import BstLean.Part154Num

/-! A fixed measurable centre source has a charge below the centre ledger allowance. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160

theorem centreSources_charge_row (J : ℕ) (c : Fin 12225 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA 12225).real (BstLean.Part211.CentreSource 12225 J c τ 2)ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  have hh := BstLean.Part211.centre_source_charge (n := 12225) (J := J) (P := 160)
    (η := 6 / 1000) (by norm_num) (by norm_num) (by norm_num) c hτ
    (by norm_num : (0 : ℝ) < 2) (by norm_num) (rhoBar_lt (by norm_num))
  have hj0 := jS_nonneg 12225 160 (6 / 1000)
  have hj := jS_160_le (n := 12225) (by norm_num)
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hbase : jS 12225 160 (6 / 1000) ^ 2 * 12225 /
      (((12225 : ℝ) - 1 - 2 * 160) * 2) ≤ (3 / 5 : ℝ) := by
    norm_num at *
    linarith
  have hp := pow_le_pow_left₀ (by positivity) hbase 160
  have hp' : (jS 12225 160 (6 / 1000) ^ 2 * 12225 /
      (((12225 : ℝ) - 1 - 2 * 160) * 2)) ^ 160 ≤ (1 / 10 ^ 12 : ℝ) :=
    hp.trans (by norm_num)
  have he : exp (-(12225 : ℝ) / 2) ≤ (1 / 10 ^ 10 : ℝ) := by
    have h : exp (-(12225 : ℝ) / 2) ≤ exp (-12) ^ 2 := by
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      norm_num
    exact h.trans ((pow_le_pow_left₀ (exp_pos _).le exp_neg12_row 2).trans (by norm_num))
  have ht := exp_neg12_row
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem centreSources_ret_charge_row (J : ℕ) (D : Design 12225) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (CentreSources 12225 J))ᶜ ≤
      (103 / 10 ^ 6 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (measurableSet_CentreSources (by norm_num) J)
    (by norm_num)
  intro c τ hτ
  exact centreSources_charge_row J c hτ

end BstLean.Part252
