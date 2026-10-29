import BstLean.Part59Defs
import BstLean.Part48Defs
import BstLean.Part53T2_Gaussian
import BstLean.Part53T2_Comparison
import BstLean.Part53T2_Polar
import BstLean.Part53T2_Bounds
import BstLean.Part71Iface
import BstLean.Part71Transfer
import BstLean.Part59T2

/-!
# Part 71: Prop T2* for `ChiLaw`

A copy of `Part59T2.lean` with `UpLaw n μ K` replaced by `ChiLaw n μ K` (used only through
`chiLaw_sph`); `radial_comparison59` is reused from Part 59.
* `gaussian_floor71`: the first event, `Pr_Z{V(σZ) < 4sN°} ≤ p`.
* `propT2s71`: Prop T2* from `PropF71`, `RadialTail71` and `SBLevel`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part71

open BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Tens TSymm fval varU sdU frob)
open BstLean.Part43 (varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (sg Ncirc)

variable {n d : ℕ}

/-- The first event of Prop T2*: the Gaussian floor. -/
lemma gaussian_floor71 (d k : ℕ) (K : ℝ) (nF : ℕ) (hF : PropF71 d k K nF)
    (p t : ℝ) (hSB : SBLevel (2 * k) p t) (ht : 0 < t)
    (n : ℕ) (hn : nF ≤ n) (μ : Measure (Fin n → ℝ)) (hμ : ChiLaw n μ K)
    (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (hTk : 0 < frob (T k)) :
    stdGauss (CoefIdxD n d) {Z | varFQ μ k f0 T (sg n d • Z) <
      4 * (t / 32) * Ncirc n d k f0 T} ≤ ENNReal.ofReal p := by
  have hS := chiLaw_sph hμ
  obtain ⟨P, hdeg, hP⟩ := BstLean.Part45.var_poly45 (d := d) hS k T
  have heq (Z : CoefIdxD n d → ℝ) :
      MvPolynomial.eval Z P = varFQ μ k f0 T (sg n d • Z) := by
    rw [hP, BstLean.Part53.T2Aux.gaussian_variance_eq μ hS]
  have hnonneg (Z : CoefIdxD n d → ℝ) : 0 ≤ MvPolynomial.eval Z P := by
    rw [hP]
    exact integral_nonneg fun _ => sq_nonneg _
  have hb := hSB (CoefIdxD n d) P hdeg hnonneg
  have hfloor := hF n hn μ hμ f0 T hT hTk
  have hlevel : 4 * (t / 32) * Ncirc n d k f0 T ≤
      t * ∫ Z, varFQ μ k f0 T (sg n d • Z) ∂stdGauss (CoefIdxD n d) := by
    nlinarith [mul_le_mul_of_nonneg_left hfloor ht.le]
  apply le_trans (measure_mono ?_) hb
  intro Z hZ
  change MvPolynomial.eval Z P < t * ∫ Z', MvPolynomial.eval Z' P ∂stdGauss (CoefIdxD n d)
  simp_rw [heq]
  exact lt_of_lt_of_le hZ hlevel

lemma fval_cont59 (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    Continuous (fun x => fval k f0 T (mapMD M x)) := by
  unfold fval
  exact continuous_const.add (continuous_finsetSum _ fun j _ =>
    BstLean.Part53.T2Aux.continuous_u T j M)

/-- **Prop T2*** from Prop F, the radial tail and the small-ball level. -/
theorem propT2s71 (d k : ℕ) (hk : 1 ≤ k) (K : ℝ) (nF : ℕ) (hF : PropF71 d k K nF)
    (C : ℝ) (nR : ℕ) (hC : 0 ≤ C) (hRT : RadialTail71 d k K C nR)
    (p t : ℝ) (hSB : SBLevel (2 * k) p t) (ht : 0 < t) :
    PropT2_71 d k K p (t / 32) C (max (max nF nR) 1) := by
  classical
  intro n hn μ hμ f0 T hT hTk
  have hnF : nF ≤ n := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hn
  have hnR : nR ≤ n := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hμS := chiLaw_sph hμ
  have hN := BstLean.Part53.T2Aux.Ncirc_positive (d := d) hn1 k hk f0 T hTk
  have hs : 0 < t / 32 := by positivity
  have hp := BstLean.Part53.T2Aux.smallball_probability_nonneg (2 * k) (by omega) p t hSB ht
  have hq : 0 ≤ C / ((n : ℝ) * (t / 32)) := div_nonneg hC (by positivity)
  have hcomp (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) :
      Real.sqrt (varFQ μ k f0 T (sg n d • Z)) ≤
        Real.sqrt (varFQ μ k f0 T (unitOfD Z)) + radDef59 μ k f0 T (unitOfD Z) (lam59 n d Z) := by
    have h := radial_comparison59 hμS k f0 T (unitOfD Z) (lam59 n d Z)
    have hsc : lam59 n d Z • unitOfD Z = sg n d • Z := BstLean.Part53.T2Aux.scale_unit Z hZ
    rw [hsc] at h
    exact h
  exact BstLean.Part53.T2Aux.floor_transfer (stdGauss (CoefIdxD n d))
    (fun Z => varFQ μ k f0 T (unitOfD Z))
    (fun Z => varFQ μ k f0 T (sg n d • Z))
    (fun Z => radDef59 μ k f0 T (unitOfD Z) (lam59 n d Z))
    {Z | Z ≠ 0} (t / 32) (Ncirc n d k f0 T) p (C / ((n : ℝ) * (t / 32)))
    (mul_pos hs hN).le hp hq
    (fun Z _ => integral_nonneg fun _ => sq_nonneg _)
    (fun Z _ => integral_nonneg fun _ => sq_nonneg _)
    hcomp
    (gaussian_floor71 d k K nF hF p t hSB ht n hnF μ hμ f0 T hT hTk)
    (hRT n hnR μ hμ f0 T hT hTk (t / 32) hs)

end BstLean.Part71
