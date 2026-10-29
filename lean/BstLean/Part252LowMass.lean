import BstLean.Part252LatitudeMoments
import BstLean.Part222Mass
import BstLean.Part162Mass

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem latitude_mass_of_MASS {n : ℕ} (hn : 2 ≤ n) (D : Design n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < D.tau0 c) {d β : ℝ} (hd : 0 ≤ d)
    (hM : MASS_at D c d β) :
    ∫ a, (stdGauss (Fin (n - 1))).real
      {v | sgA D c a v < √(2 / (n : ℝ) * d)} ∂muI n ≤ β / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [mass_eq_stand hn D c hc hτ]
  have hs : {ξ : Fin n → ℝ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) <
      √(2 / (n : ℝ) * d)} =
      {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1) (hStand D c ξ)) <
        2 / (n : ℝ) * d} := by
    ext ξ
    simp only [Set.mem_setOf_eq]
    change √(2 / (mA n : ℝ)) * √(normSq (res (D.bA c.1 c.2.1.1)
      (hStand D c ξ))) < _ ↔ _
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_lt_sqrt_iff (mul_nonneg (by positivity) (normSq_nonneg _))
  rw [hs, le_div_iff₀ hnR, mul_comm]
  exact hM

theorem low_mass_of_interfaces {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12225).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12225) c M H xi)
    (hE : centreEnergy (paperDesignP 12225) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12225 : ℝ))))
    (hprice : massBound 12225 M H xi E u mixtureFloor ≤ 12225 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12225 - 1))).real
      {v | sgA (paperDesignP 12225) c a v < √(2 / (12225 : ℝ) * mixtureFloor)}
        ∂muI 12225 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12225).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12225) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12225) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12225)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part252
