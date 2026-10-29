import BstLean.Part293Root
import BstLean.Part293SYPass
import BstLean.Part293MixtureNumerics
import BstLean.Part228Scale

/-! The low-band pass constructor uses the sharp bias and original conditional-mixture integrals. -/
namespace BstLean.Part293
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part228 BstLean.Part242 BstLean.Part289

structure PassSupplies {n : ℕ} (t : ℝ) (z : Ret n) where
  split : SplitData n
  chi : ℝ
  vmax : ℝ
  aw : ℝ
  af : ℝ
  F8 : ℝ
  F24 : ℝ
  reciprocal : ℝ
  Cv : ℝ
  eps : ℝ
  A : ℝ
  Dm : ℝ
  C : ℝ
  B : ℝ
  Dd : ℝ
  window : WINDOW (idealDesignFloor n (scaleFloor n)) z
  eta : split.eta = 0.0045
  bias : SYPassInputsFloor (scaleFloor n) z split chi 0.17919 0.028
    vmax aw af F8 F24 reciprocal Cv
  bias_numerics : BiasNumerics chi vmax aw af F8 F24 reciprocal Cv
  mixture_numerics : MixtureNumerics n eps A Dm C B Dd
  removed : ∫ a, BstLean.Part161.removed (stdGauss (Fin (n - 1))) split.good a ∂muI n ≤ B
  mixture : ∫ a in keptIx (idealDesignFloor n (scaleFloor n)) z split,
    (√(goodMean (stdGauss (Fin (n - 1))) split.good
      (pLat (idealDesignFloor n (scaleFloor n)) t z) a) - √(q0Lat t z split a)) ^ 2 ∂muI n ≤
      C / 4 + 6 * mixL3 n eps A Dm ^ 3
  displacement : ∫ a in keptIx (idealDesignFloor n (scaleFloor n)) z split,
    hellG2 n ((split.lam0 a - split.lamb a) ^ 2 * normSq z.2.1.2)
      (split.S0 a) (split.Sb a) ∂muI n ≤ Dd
  arithmetic : |√(qTilde (statedDesign2 n) t z) -
    √(qTilde (idealDesignFloor n (scaleFloor n)) t z)| ≤ 1 / 10 ^ 20

noncomputable def PassSupplies.toRootInputs {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    {t : ℝ} {z : Ret n} (S : PassSupplies t z) : RootInputs t z where
  split := S.split
  fluctuation := 0.002329
  bias := 0.00406
  lowerTail := -(8 / √(n : ℝ)) / (2 * (idealDesignFloor n (scaleFloor n)).tau0 z ^ 2)
  upperTail := (8 / √(n : ℝ)) / (2 * (idealDesignFloor n (scaleFloor n)).tau0 z ^ 2)
  arithmetic := 1 / 10 ^ 20
  centre := S.window.1
  bias_bound := (conditional_pass_bias_SY_floor (by omega) (scaleFloor n) z S.split S.bias).trans
    (bias_root_le hn hn' S.bias_numerics)
  fluctuation_bound := by
    refine ⟨S.B, S.C / 4 + 6 * mixL3 n S.eps S.A S.Dm ^ 3, S.Dd,
      S.removed, S.mixture, S.displacement, ?_⟩
    rw [S.eta]
    exact fluctuation_price_le hn hn' S.mixture_numerics
  tail := bulk_domain_explicit (by omega) _ _ S.window
  table_comparison := S.arithmetic
  total := by
    change 0.002329 + 0.00406 + frontierTailRoot (idealDesignFloor n (scaleFloor n)) z +
      1 / 10 ^ 20 ≤ rootAllowance
    have ht := frontierTailRoot_lt hn _ _ S.window
    norm_num [rootAllowance] at *
    linarith

end BstLean.Part293

/-- info: 'BstLean.Part293.PassSupplies.toRootInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.PassSupplies.toRootInputs
