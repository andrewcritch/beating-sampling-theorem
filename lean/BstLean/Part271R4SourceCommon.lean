import BstLean.Part250Bounds
import BstLean.Part264bSourceCommon
import BstLean.Part269TailBounds
import BstLean.Part277Uniform
import BstLean.Part269Source

/-! Generic arithmetic helpers for block source certificates. -/
namespace BstLean.Part271.R4

open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211
open BstLean.Part228

theorem source_dimension {a b n : ℕ} (ha : a ≤ n) (hb : n ≤ b) :
    Bounds (n : ℝ) (a : ℝ) (b : ℝ) := by
  constructor
  · exact_mod_cast ha
  · exact_mod_cast hb

theorem source_cs : Bounds csC (1.29521 : ℝ) 1.295212 :=
  ⟨BstLean.Part253.cs_lower, BstLean.Part264.pilot_cs_upper⟩

theorem source_phi0 : Bounds (phiG 0) (0 : ℝ) 0.399 :=
  ⟨(phiG_pos 0).le, BstLean.Part264.pilot_phi_zero_upper⟩

theorem source_phi1 : Bounds (phiG 1) (0 : ℝ) 0.243 :=
  ⟨(phiG_pos 1).le, BstLean.Part264.pilot_phi_one_upper⟩

theorem source_pi {ρ : ℝ} (hlo : 0 < ρ) (hhi : ρ ≤ 0.00026185) :
    Bounds (piBar ρ) (0 : ℝ) (1 / 10^40) :=
  ⟨piBar_nonneg _, BstLean.Part264b.piBar_upper_of_bounds hlo hhi⟩

theorem source_gap2 {ρ : ℝ} (hρ : ρ ≤ 0.00026185) :
    (0.09438 : ℝ) ≤ gap 2 ρ 1.22 := by
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * ρ) := le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem source_gap1 {ρ : ℝ} (hρ : ρ ≤ 0.000090016) :
    (0.055043 : ℝ) ≤ gap 1 ρ 1.12 := by
  have hs : (0.99995499 : ℝ) ≤ √(1 - ρ) := le_sqrt_of_sq_le (by linarith)
  have hk : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.12 ≤ 0.94491119 := by
    calc
      _ ≤ (1 : ℝ) / 1.05830052 := by gcongr
      _ ≤ (0.94491119 : ℝ) := by norm_num
  unfold gap
  rw [one_mul]
  linarith

theorem source_tail {d ρ k g r E T : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ r)
    (hg : 0 ≤ g) (hgap : g ≤ gap d ρ k) (hE : 0 ≤ E)
    (hscalar : 2 * E * r ≤ g ^ 2) (hexp : exp (-E) ≤ T) : tail d ρ k ≤ T := by
  have hsq := pow_le_pow_left₀ hg hgap 2
  have hprod := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * E by positivity)
  have he : E ≤ gap d ρ k ^ 2 / (2 * ρ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * ρ)).mpr
    nlinarith only [hscalar, hsq, hprod]
  unfold tail
  apply le_trans _ hexp
  apply exp_le_exp.mpr
  rw [neg_div]
  linarith

theorem source_qb_nonneg {ρ p : ℝ} (hρ : 0 ≤ ρ) (hp : 0 ≤ p) : 0 ≤ QB ρ p := by
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hν : 0 ≤ nuR ρ := by unfold nuR; positivity
  unfold QB cc0 cc1 cc2
  positivity

theorem source_moment_nonneg {n : ℕ} {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance n csC 0.011 1.22 1.12 Θ S := by
  have hcs := csC_positive.le
  have hw : 0 ≤ wn n := by unfold wn; positivity
  have hρ : 0 ≤ rhoBar n csC := by unfold rhoBar; positivity
  have hπ := piBar_nonneg (rhoBar n csC)
  have hν : 0 ≤ nuR (rhoBar n csC) := by unfold nuR; positivity
  have hqb := source_qb_nonneg hρ hπ
  have hK : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  unfold momentAllowance restAllowance linearAllowance bN badAllowance tail
  positivity

theorem source_bn_nonneg {n : ℕ} {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN n csC Θ := by
  have hcs := csC_positive.le
  have hw : 0 ≤ wn n := by unfold wn; positivity
  have hρ : 0 ≤ rhoBar n csC := by unfold rhoBar; positivity
  have hqb := source_qb_nonneg hρ (piBar_nonneg (rhoBar n csC))
  unfold bN
  positivity

end BstLean.Part271.R4
