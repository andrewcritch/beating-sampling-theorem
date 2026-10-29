import BstLean.Part269Repair12350

namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264

theorem envelope_dimension_le {a n : ℕ} (ha : 11883 ≤ a) (han : a ≤ n)
    (p : Parameters) (hp : Valid p) {θ : ℝ} (hθ : 0 ≤ θ) (hhi : θ ≤ 528/1000) :
    envelope n p θ ≤ envelope a p θ := by
  have haR : (11883 : ℝ) ≤ a := by exact_mod_cast ha
  have hanR : (a : ℝ) ≤ n := by exact_mod_cast han
  have ha0 : (0 : ℝ) < a := by linarith
  have hd : 0 < 1 - 4*θ/a := by
    have h := (div_lt_one ha0).mpr (by linarith : 4*θ < (a : ℝ))
    linarith
  have hdiv : 4*θ/(n : ℝ) ≤ 4*θ/a :=
    div_le_div_of_nonneg_left (by positivity) ha0 hanR
  have hterm := div_le_div_of_nonneg_left hp.cLam_nonneg hd
    (show 1 - 4*θ/a ≤ 1 - 4*θ/n by linarith)
  unfold BstLean.Part263.envelope
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hterm le_rfl) le_rfl) hθ) le_rfl

theorem common_cap_bound {n : ℕ} (hn : 12350 ≤ n) (j : Fin 43) {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hupper : θ ≤ (scalarRow12350.table (sourceIndex j)).upper) :
    envelope n (parameters j) θ ≤ cap12350 j := by
  have hp := parameters_valid j
  have hhi := repair12350.endpoint_upper j
  have hm := envelope_mono (by omega : 11883 ≤ n) (parameters j) hp
    hθ hupper hhi hp.wRadius_lt hp.cRadius_lt
  exact hm.trans ((envelope_dimension_le (by norm_num : 11883 ≤ 12350) hn
    (parameters j) hp (hθ.trans hupper) hhi).trans (repair12350.endpoint j))

end BstLean.Part269
