import BstLean.Part53Defs
import BstLean.Part48Defs
import BstLean.Part53T2_Gaussian
import BstLean.Part53T2_Tail

/-!
# Part 53, wave 1: Prop T2, the floor on the coefficient sphere (§7 of the source)

Specification: `delegations/answers/p53-spec-opus.md` §3.10.
Replace each `sorry` by a proof. Do not edit the statements. Do not use `native_decide` or `axiom`
anywhere. This file imports `Part53Defs` only (a prover may also import finished Part 29–52 files,
but no other Part 53 wave-1 file).

Suggested route.
* `√V(W) ≥ √V(λW) − Σ_{j ≥ 1} |λ^j − 1| sd_j(W)` (`V(λW) = Var_x Σ_j λ^j f_j(Wφ(x))`), so
  `{V(W) < sN°} ⊆ {V(σZ) < 4sN°} ∪ {Σ_j |λ^j − 1| sd_j(W) ≥ √(sN°)}`.
* First event: `V(σZ)` is a nonnegative polynomial of degree `≤ 2k` in `Z` (`Part45DegDrop.var_poly45`
  with `Pcal`; the constant `f₀` does not change the variance), `E V(σZ) ≥ N°/8` (Prop F),
  `4s = t/8`, so `SBLevel (2k) p t` gives probability `≤ p`.
* Second event: Markov, polar independence, `E|λ^j − 1|² ≤ C_j/𝒟`,
  `E_W sd_j² ≤ E_Z E_μ f_j(σZφ)² ≤ C n^{⌊k/2⌋} N°` (Lemma W with `b = 0, ψ = φ(x)`, Lemma Tr for
  `T_j` in terms of `T°`), and `n^{⌊k/2⌋}/𝒟 ≤ d!/n` (`k ≤ 2d + 1`).
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount)
open BstLean.Part43 (BofQ varFQ)

variable {n d : ℕ}

open BstLean.Part48 (SBLevel)

/-- **Prop T2.** -/
theorem propT2_of (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (hkd : k ≤ 2 * d + 1) (Λ : ℝ) (nF : ℕ)
    (hF : PropF53 d k Λ nF) (hW : LemmaW53 k) (hTr : LemmaTr53) (hP : GaussPolar53)
    (p t : ℝ) (hSB : SBLevel (2 * k) p t) (ht : 0 < t) :
    ∃ (C : ℝ) (n0 : ℕ), PropT2_53 d k Λ p (t / 32) C n0 := by
  classical
  obtain ⟨C, hC, htail⟩ := T2Aux.radialDefect_tail d k (by omega) hkd hW hTr hP
  refine ⟨C, max nF 1, ?_⟩
  intro n hn μ hμ f0 T hT hTk
  have hnF : nF ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hμS : BstLean.Part40.SphLaw n μ := by
    obtain ⟨hp, ρ, -, -, hμeq, -⟩ := hμ
    refine ⟨hp, ?_⟩
    rw [hμeq]
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (BstLean.Part29.uniformSphere_ae_sphere n)
  have hN := T2Aux.Ncirc_positive (d := d) hn1 k hk f0 T hTk
  have hs : 0 < t / 32 := by positivity
  have hp := T2Aux.smallball_probability_nonneg (2 * k) (by omega) p t hSB ht
  have hq : 0 ≤ C / ((n : ℝ) * (t / 32)) := div_nonneg hC (by positivity)
  have hcomp (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) :
      Real.sqrt (varFQ μ k f0 T (sg n d • Z)) ≤
        Real.sqrt (varFQ μ k f0 T (unitOfD Z)) +
          T2Aux.radialDefect μ k T (unitOfD Z) (T2Aux.radialScale n d Z) := by
    have h := T2Aux.radial_sd_comparison hμS k f0 T (unitOfD Z) (T2Aux.radialScale n d Z)
    rw [T2Aux.scale_unit Z hZ] at h
    exact h
  exact T2Aux.floor_transfer (stdGauss (CoefIdxD n d))
    (fun Z => varFQ μ k f0 T (unitOfD Z))
    (fun Z => varFQ μ k f0 T (sg n d • Z))
    (fun Z => T2Aux.radialDefect μ k T (unitOfD Z) (T2Aux.radialScale n d Z))
    {Z | Z ≠ 0} (t / 32) (Ncirc n d k f0 T) p (C / ((n : ℝ) * (t / 32)))
    (mul_pos hs hN).le hp hq
    (fun Z _ => integral_nonneg fun _ => sq_nonneg _)
    (fun Z _ => integral_nonneg fun _ => sq_nonneg _)
    hcomp
    (T2Aux.gaussian_floor d k Λ nF hF p t hSB ht n hnF μ hμ f0 T hT hTk)
    (htail n hn1 μ hμS f0 T hT hN (t / 32) hs)

end BstLean.Part53
