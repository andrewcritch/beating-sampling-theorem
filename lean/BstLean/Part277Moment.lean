import BstLean.Part277Energy
import BstLean.Part264Centre

/-! Part 277, moment pair: `Part264.centreCertificate_from_moment` with the pair `(k, k3)` of the
moment certificate and the operator cap `MP` as parameters, on every `n ≥ 8000`.
The old lemma fixes `(k, k3, MP) = (1.22, 1.12, 1.22)`. The paper uses `(1.25, 1.14)` below
`11364`. Below `12225` the operator cap is above `1.22` (`operator_allowance_11883` gives
`1.2236`), so `MP` must be a parameter too. -/
namespace BstLean.Part277
open Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part182 BstLean.Part206
  BstLean.Part211

theorem gMinus_ge_989 {n : ℕ} (hn : 8000 ≤ n) : (0.989 : ℝ) ≤ gMinus n := by
  have h := gMinus_lowerP (n0 := 8000) le_rfl hn (s := 0.9999) (t := 3.464102)
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num)
  exact le_trans (by norm_num) h

theorem gPlus_le_1011 {n : ℕ} (hn : 8000 ≤ n) : BstLean.Part211.gPlus n ≤ (1.011 : ℝ) :=
  (gPlus_upperP (n0 := 8000) le_rfl hn (t := 3.464102) (sqrt_le_iff.mpr (by norm_num))).trans
    (by norm_num)

theorem energy_root_guard_8000 {n : ℕ} (hn : 8000 ≤ n) :
    2 * √(12 : ℝ) / n < √(1 - 2 / (n : ℝ) ^ 2) :=
  energy_root_guardP (n0 := 8000) le_rfl hn (s := 0.9999) (t := 3.464102)
    (sqrt_le_iff.mpr (by norm_num)) (le_sqrt_of_sq_le (by norm_num)) (by norm_num)

theorem plow_lower_8000 {n : ℕ} (hn : 8000 ≤ n) : (0.56 : ℝ) ≤ plow n 0.011 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  have h13 : 13 / (n : ℝ) ≤ 13 / 8000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 8000) := by norm_num
    _ ≤ _ := by gcongr

/-- **The centre certificate with the pair and the operator cap as parameters.** -/
theorem centreCertificate_from_momentP {n : ℕ} (hn : 8000 ≤ n)
    {thetaHi S qWorld k k3 MP F r : ℝ}
    (M : MomentCertificate n 0.011 k k3 (0.46) thetaHi S (fun _ => 0.006))
    (hq : qWorld ∈ Icc (-1 : ℝ) 1)
    (hDomain : BstLean.Part206.energyRatio n (gMinus n) qWorld ≤ 1)
    (hGap : BstLean.Part154.eMP n 0.011
      (momentAllowance n BstLean.Part154.csC 0.011 k k3 thetaHi S)
      (BstLean.Part154.bN n BstLean.Part154.csC thetaHi) ≤ 1 / 10)
    (hUpper : BstLean.Part206.energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) qWorld ≤ 1)
    (hr0 : 0 < r) (hr : r ^ 2 ≤ n) (hF : finiteEnergy n n (11 / 1000) ≤ F)
    (hFr : F / r < 56 / 100)
    (hlow : ∀ θ ∈ Icc (0.46 : ℝ) thetaHi,
      0 ≤ meanLowerRoot n θ ∧
      0 ≤ kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2 ∧
      0 ≤ √(gMinus n * (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) -
        2 / (n : ℝ) ^ 2)) - 2 * √(12 * BstLean.Part211.gPlus n) / n -
        finiteEnergy n n 0.011 / √(n : ℝ)) :
    CentreCertificate n n 0.011 k k3 (0.46) thetaHi S MP qWorld (fun _ => 0.006) where
  toMomentCertificate := M
  delta_upper := by norm_num
  signal_domain := hq
  energy_domain := hDomain
  energy_root := energy_root_guard_8000 hn
  energy_lower := by have := gMinus_ge_989 hn; linarith
  energy_upper := by have := gPlus_le_1011 hn; linarith
  relative_gap := hGap
  finite_guard := by
    rw [show (0.011 : ℝ) = 11 / 1000 by norm_num]
    have hnn : r ≤ √(n : ℝ) := le_sqrt_of_sq_le hr
    have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 11 / 1000)
    have hfd : finiteEnergy n n (11 / 1000) / √(n : ℝ) ≤ F / r :=
      div_le_div₀ (hf0.trans hF) hF hr0 hnn
    have hp := plow_lower_8000 hn
    have : (0.56 : ℝ) ≤ plow n (11 / 1000) := by convert hp using 2 <;> norm_num
    linarith
  lower_root := fun θ hθ => (hlow θ hθ).1
  lower_bracket := fun θ hθ => (hlow θ hθ).2.1
  lower_guard := fun θ hθ => by
    exact (hlow θ hθ).2.2
  upper_clip := hUpper

end BstLean.Part277
