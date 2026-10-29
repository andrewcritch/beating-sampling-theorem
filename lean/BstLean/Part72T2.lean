import BstLean.Part59Defs
import BstLean.Part48Defs
import BstLean.Part53T2_Gaussian
import BstLean.Part53T2_Comparison
import BstLean.Part53T2_Polar
import BstLean.Part53T2_Bounds
import BstLean.Part72Iface
import BstLean.Part71Transfer
import BstLean.Part59T2

/-!
# Part 72: Prop T2* for an abstract class of distributions

A copy of `Part71T2.lean` with `ChiLaw n μ K` replaced by membership `L n μ` in a class
`L : DistClass` with `SphClass L` (every member is a probability distribution carried by the
sphere); `chiLaw_sph` is replaced by `hL`. Names end in `72`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72
open BstLean.Part71

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
lemma gaussian_floor72 (L : DistClass) (hL : SphClass L) (d k : ℕ) (nF : ℕ) (hF : PropF72 L d k nF)
    (p t : ℝ) (hSB : SBLevel (2 * k) p t) (ht : 0 < t)
    (n : ℕ) (hn : nF ≤ n) (μ : Measure (Fin n → ℝ)) (hμ : L n μ)
    (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (hTk : 0 < frob (T k)) :
    stdGauss (CoefIdxD n d) {Z | varFQ μ k f0 T (sg n d • Z) <
      4 * (t / 32) * Ncirc n d k f0 T} ≤ ENNReal.ofReal p := by
  have hS := hL n μ hμ
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

private lemma fval_cont59 (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    Continuous (fun x => fval k f0 T (mapMD M x)) := by
  unfold fval
  exact continuous_const.add (continuous_finsetSum _ fun j _ =>
    BstLean.Part53.T2Aux.continuous_u T j M)

/-- **Prop T2*** from Prop F, the radial tail and the small-ball level. -/
theorem propT2s72 (L : DistClass) (hL : SphClass L) (d k : ℕ) (hk : 1 ≤ k) (nF : ℕ) (hF : PropF72 L d k nF)
    (C : ℝ) (nR : ℕ) (hC : 0 ≤ C) (hRT : RadialTail72 L d k C nR)
    (p t : ℝ) (hSB : SBLevel (2 * k) p t) (ht : 0 < t) :
    PropT2_72 L d k p (t / 32) C (max (max nF nR) 1) := by
  classical
  intro n hn μ hμ f0 T hT hTk
  have hnF : nF ≤ n := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hn
  have hnR : nR ≤ n := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hμS := hL n μ hμ
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
    (gaussian_floor72 L hL d k nF hF p t hSB ht n hnF μ hμ f0 T hT hTk)
    (hRT n hnR μ hμ f0 T hT hTk (t / 32) hs)

end BstLean.Part72
