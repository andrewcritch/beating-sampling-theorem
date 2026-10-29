import BstLean.Part53Defs
import BstLean.Part53Error_Integrability
import BstLean.Part53Error_Feature
import BstLean.Part53Error_HeatSum
import BstLean.Part53Error_Chaos
import BstLean.Part53Error_Bound

/-!
# Part 53, wave 1: Prop E, the error in the Gaussian proxy (§5 of the source, with the `L²` repair)

Specification: `delegations/answers/p53-spec-opus.md` §3.4.
Replace each `sorry` by a proof. Do not edit the statements. Do not use `native_decide` or `axiom`
anywhere. This file imports `Part53Defs` only (a prover may also import finished Part 29–52 files,
but no other Part 53 wave-1 file).

Suggested route.
* `mapMD M x = linZ M φ(x)` and `fvA k (TF k f0 T) = fval k f0 T`. Expand
  `(B − g₀)(σZ)² = B² − 2Bg₀ + g₀²`, write `B(σZ) = E_{x∼μ} h(σZφ(x))`, exchange `E_Z` and `E_μ`
  (Fubini; the integrands are polynomials in `Z` and bounded in `x` on the sphere), and apply Lemma W
  three times: `(φ(x), φ(x'))`, `(φ(x), e₀)`, `(e₀, e₀)`, with `b = σ²(c₀ − 1)` for `g₀`. This gives
  (W3): `E_Z(B − g₀)² = Σ_c c!‖E_μ F_c − G_c‖²`.
* Main term: `‖E φ^{⊗c} − e₀^{⊗c}‖ ≤ A_c √η_n`, `η_n = e^Λ c_d/n` (Lemma G and the density ratio;
  Lemma Σ(i),(ii),(iv); use `‖φ̄‖ ≤ √(d+1)` and `u ≤ d+1` rather than powers of `1 + η_n`).
* Trace term: Lemma Tr, and `(E_μ δ°^i)² ≤ E_μ δ°^{2i} ≤ d^{2i} e^Λ (8i−1)!! n^{−2i}` (Jensen; Lemma U,
  Lemma S at `q = 2i`). Every index `c + 2i ≥ 2` appears in `N°`.
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount)
open BstLean.Part43 (BofQ varFQ)

variable {n d : ℕ}

/-- **Prop E.** -/
theorem propE53_of (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (Λ : ℝ)
    (hW : LemmaW53 k) (hU : LemmaU53 d) (hS : LemmaS53) (hG : LemmaG53 d) (hTr : LemmaTr53) :
    ∃ (C : ℝ) (n0 : ℕ), PropE53 d k Λ C n0 := by
  suffices hbound : ∃ (C : ℝ) (n0 : ℕ), ∀ n : ℕ, n0 ≤ n →
      ∀ μ : Measure (Fin n → ℝ), DensLaw n μ Λ →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        ∫ Z, (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
          ∂stdGauss (CoefIdxD n d) ≤ C / n * Ncirc n d k f0 T by
    obtain ⟨C, n0, hbound⟩ := hbound
    refine ⟨C, n0, ?_⟩
    intro n hn μ hμ f0 T hT hTk
    exact ⟨error53_integrable_dens hμ k f0 T, hbound n hn μ hμ f0 T hT hTk⟩
  refine ⟨2 * error53_correction_constant d k Λ + 2 * error53_main_constant d k Λ, 1, ?_⟩
  intro n hn μ hμ f0 T hT hTk
  exact error53_normalized_bound hn hd hμ hU hS hG hTr k f0 T hT

end BstLean.Part53
