import BstLean.Part157All
import BstLean.Part158All

/-!
# Part 159 (file `Hid`): from an event of the hidden World matrices to the World hypotheses

Role: `delegations/statements/p159-spec.md`. Do not use `sorry`, `native_decide` or `axiom`.

The World hypotheses of Part 157 (`FRAME_W_hyp`, and in `EVENTS_hyp` the event `H` with its charge
and the restricted Hellinger moment) are statements about the retained data `Ret n`. Every World
estimate of the library (Parts 136 to 143) is a statement about the hidden World matrices
`θ = (W₁, W₂)` with the distribution `hidGauss (2n) (mW n)`. This file gives the transfer, for
EVERY design.

* `Hof G`: the retained data whose hidden World matrices are in `G`.
* `hid_charge`: `Pr((Hof G)ᶜ) = Pr(Gᶜ)`.
* `frame_of_hid`: a frame bound on `G` for the centre `D.bW` gives `FRAME_W_hyp` on every set of
  retained data inside `Hof G`.
* `hellHid bW τ θ = E_u H_u²` as a function of the hidden matrices, for a centre map `bW` and a
  scalar map `τ`; `HbarW2_eq_hellHid`: it is the squared World radius of Part 157 when
  `τ₀ = τ(W₁, W₂)`.
* `moment_of_hid`: `E[1_{Hof G}·H̄_W²] ≤ E_θ[1_G·K]` if `H̄_W² ≤ K(θ)` on `G`.
* `events_of_hid`: `EVENTS_hyp` from the three numbers.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part156 BstLean.Part157

variable {n : ℕ}

/-- The retained data whose hidden World matrices `(W₁, W₂)` are in `G`. -/
def Hof (G : Set (WHid n)) : Set (Ret n) := {c | c.1.1 ∈ G}

lemma measurable_hidOf : Measurable (fun c : Ret n => c.1.1) := measurable_fst.comp measurable_fst

lemma measurableSet_Hof {G : Set (WHid n)} (hG : MeasurableSet G) : MeasurableSet (Hof G) :=
  measurable_hidOf hG

/-- **The charge of a hidden event** is the same for the retained data of every design. -/
theorem hid_charge (D : Centres n) {G : Set (WHid n)} (hG : MeasurableSet G) :
    (retDist D).real (Hof G)ᶜ = (hidGauss (2 * n) (mW n)).real Gᶜ := by
  have e : (Hof G)ᶜ = (fun c : Ret n => c.1.1) ⁻¹' Gᶜ := rfl
  rw [e, ← map_measureReal_apply measurable_hidOf hG.compl, retDist_hid D]

/-- **The World frame hypothesis from a frame bound on a hidden event.** -/
theorem frame_of_hid (D : Centres n) {L : ℝ} {G : Set (WHid n)}
    (h : ∀ θ ∈ G, ∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (D.bW θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
        L * ∑ j, w j ^ 2)
    {E : Set (Ret n)} (hE : E ⊆ Hof G) : FRAME_W_hyp D L E :=
  fun c hc w => h c.1.1 (hE hc) w

/-- **`E_u H_u²` as a function of the hidden World matrices**, for a centre map `bW` and a scalar
map `τ` (the stand-in scalar `τ₀` as a function of `(W₁, W₂)`). -/
noncomputable def hellHid (bW : WHid n → Fin (mW n) → ℝ) (τ : WHid n → ℝ) (θ : WHid n) : ℝ :=
  ∫ u, hu2 n (lam (bW θ) (hid2 θ.1 θ.2 u)) (sig (2 / (mW n : ℝ)) (bW θ) (hid2 θ.1 θ.2 u)) (τ θ)
    ∂uniformSphere (2 * n)

lemma hellHid_nonneg (bW : WHid n → Fin (mW n) → ℝ) (τ : WHid n → ℝ) (θ : WHid n) :
    0 ≤ hellHid bW τ θ := integral_nonneg fun _ => hu2_nonneg _ _ _ _

/-- The squared World radius of Part 157 is `hellHid` when `τ₀` is a function of `(W₁, W₂)`. -/
theorem HbarW2_eq_hellHid (D : Design n) {τ : WHid n → ℝ} (c : Ret n)
    (hτ : D.tau0 c = τ c.1.1) : HbarW2 D c = hellHid D.bW τ c.1.1 := by
  unfold HbarW2 hellHid lamWu sigWu
  rw [hτ]

/-- **The restricted Hellinger moment from a bound on a hidden event.** If `H̄_W² ≤ K(W₁, W₂)` for
the retained data with `(W₁, W₂) ∈ G`, then `E[1_{Hof G}·H̄_W²] ≤ E[1_G·K]`. -/
theorem moment_of_hid (hn : 1 ≤ n) (D : Design n) {G : Set (WHid n)} (hG : MeasurableSet G)
    {K : WHid n → ℝ} (hK : Integrable (G.indicator K) (hidGauss (2 * n) (mW n)))
    (hle : ∀ c : Ret n, c.1.1 ∈ G → HbarW2 D c ≤ K c.1.1) :
    ∫ c in Hof G, HbarW D c ^ 2 ∂retDist D.toCentres ≤
      ∫ θ, G.indicator K θ ∂hidGauss (2 * n) (mW n) := by
  have hH := measurableSet_Hof (n := n) hG
  have hmap := retDist_hid D.toCentres
  have iK : Integrable (fun c : Ret n => G.indicator K c.1.1) (retDist D.toCentres) := by
    have h1 : Integrable (G.indicator K) ((retDist D.toCentres).map (fun c : Ret n => c.1.1)) := by
      rw [hmap]; exact hK
    exact (integrable_map_measure h1.aestronglyMeasurable measurable_hidOf.aemeasurable).1 h1
  have e2 : ∫ c, G.indicator K c.1.1 ∂retDist D.toCentres =
      ∫ θ, G.indicator K θ ∂hidGauss (2 * n) (mW n) := by
    have h1 : AEStronglyMeasurable (G.indicator K)
        ((retDist D.toCentres).map (fun c : Ret n => c.1.1)) := by
      rw [hmap]; exact hK.aestronglyMeasurable
    have h2 := integral_map (μ := retDist D.toCentres) measurable_hidOf.aemeasurable h1
    rw [hmap] at h2
    exact h2.symm
  rw [← e2, ← integral_indicator hH]
  refine integral_mono ?_ iK ?_
  · exact (integrableOn_HbarW_sq hn D (Hof G)).integrable_indicator hH
  · intro c
    by_cases hc : c ∈ Hof G
    · have hc' : c.1.1 ∈ G := hc
      simp only [Set.indicator_of_mem hc, Set.indicator_of_mem hc']
      rw [HbarW_sq]
      exact hle c hc'
    · have hc' : c.1.1 ∉ G := hc
      simp only [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc']
      exact le_rfl

/-- **`EVENTS_hyp` for the event `Hof G`**, from a bound `δ_hid` of `Pr(Gᶜ)`, a bound `v_W` of the
restricted mean of a majorant `K` of `H̄_W²`, and the charge of the other events. -/
theorem events_of_hid (hn : 1 ≤ n) (D : Design n) {G : Set (WHid n)} (hG : MeasurableSet G)
    {K : WHid n → ℝ} (hK : Integrable (G.indicator K) (hidGauss (2 * n) (mW n)))
    (hle : ∀ c : Ret n, c.1.1 ∈ G → HbarW2 D c ≤ K c.1.1)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁) {δhid vW δextra : ℝ}
    (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ δhid)
    (h2 : ∫ θ, G.indicator K θ ∂hidGauss (2 * n) (mW n) ≤ vW)
    (h3 : (retDist D.toCentres).real (Hof G ∩ E₁ᶜ) ≤ δextra) :
    EVENTS_hyp D.toCentres (Hof G) E₁ (HbarW D) δhid vW δextra :=
  ⟨measurableSet_Hof hG, hE₁, measurable_HbarW D, by rw [hid_charge D.toCentres hG]; exact h1,
    integrableOn_HbarW_sq hn D _, (moment_of_hid hn D hG hK hle).trans h2, h3⟩

end BstLean.Part159

open BstLean.Part159 in
#print axioms hid_charge
open BstLean.Part159 in
#print axioms frame_of_hid
open BstLean.Part159 in
#print axioms moment_of_hid
open BstLean.Part159 in
#print axioms events_of_hid
