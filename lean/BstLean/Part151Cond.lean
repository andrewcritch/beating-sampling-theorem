import BstLean.Part151Struct
import BstLean.Part151Tail

/-!
# Part 151, item 3: the conditional program theorem

Role: `delegations/statements/p151-spec.md`, item 3. Paper source:
`proofs/option-n/theorem5-13-events-final.tex` (Proposition VA (b) is the hypothesis `H2`;
Proposition "The union bound" is the conclusion).

Notation as in `Part151Struct`. `S = 4/n`. `B = Bn W A F` is the true target, `sd = sdn W A F`
the true spread (Part 130), `B′ = gA W A F` the population mean over the stand-in input
(Part 141), `V′ = vHat bh k ω = t_F·|Δ̂′|²`.

The three hypotheses, each a `Prop` with a name, so that a later Part can prove them one at a
time:

* `H1 n εW p₁`: `Pr_{W,A,F}(|B′ − B| > ε_W·sd) ≤ p₁` (the population bound of the `W` stage).
* `H2 n k bh G E cV p₂`: `E` is a measurable event of `((W, A, (F₁, F₂)), η)` (so it does not
  use the last row `f₃`), `Pr(Eᶜ) ≤ p₂`, `V′ ≤ c_V·S/n` on `E`, and `E` is inside the event
  `G` of `(W, A, F)`.
* `H3 n G d₀ p₃`: `Pr_{W,A,F}(G and sd² < d₀·S) ≤ p₃` (the lower tail of the spread).

* **`cond151_gen`**: for an estimator `g` that is equal to `gSampH bh k` on `E`:
  `Pr(|g − B| ≤ sd/2) ≥ 1 − (p₁ + p₂ + p₃ + 2Φ̄((1/2 − ε_W)·√(n·d₀/c_V)))`.
* **`cond151`**: the same for `g = gSampH bh k`.
* **`condProg151`**: the same for the straight-line program `fullProg150 k n J` of Part 150
  (centre `bTW J`), if `τ̃₀ > 0` on `E`.
* `cond151_exp`, `cond151_mills`: the Gaussian tail replaced by `exp(−a²/2)` and by
  `2φ(a)(1/a − 1/a³ + 3/a⁵)`.
* `H2_of_joint`: `H2` from an event of all variables that does not depend on the last row.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 (cenA tauWA gA)
open BstLean.Part150 (CMap gSampH bTW measurable_bTW fullProg150 fullVal fullProg150_gSampH)

variable {k n : ℕ}

/-- The type of `(W, A, F)`. -/
abbrev Trip (n : ℕ) : Type :=
  MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1

/-- **Hypothesis H1** (the population bound of the `W` stage):
`Pr_{W,A,F}(|B′ − B| > ε_W·sd) ≤ p₁`, with `B′ = E_{x∼ν′} F(A(x))`. -/
def H1 (n : ℕ) (εW p₁ : ℝ) : Prop :=
  (mlpTriple 2 n).real {t | εW * sdn t.1 t.2.1 t.2.2 <
    |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2|} ≤ p₁

/-- **Hypothesis H3** (the lower tail of the spread): `Pr_{W,A,F}(G and sd² < d₀·S) ≤ p₃`,
`S = 4/n`. Take `G = univ` for the plain form. -/
def H3 (n : ℕ) (G : Set (Trip n)) (d₀ p₃ : ℝ) : Prop :=
  (mlpTriple 2 n).real (G ∩ {t | sdn t.1 t.2.1 t.2.2 ^ 2 < d₀ * (4 / (n : ℝ))}) ≤ p₃

/-- **Hypothesis H2** (the variance bound on an event that does not use the last row of `F`):
`E` is a measurable set of values of `((W, A, (F₁, F₂)), η)`, `Pr(Eᶜ) ≤ p₂`, on `E` the
conditional variance `V′ = t_F·|Δ̂′|²` is at most `c_V·S/n`, and `E` is inside `G`. -/
structure H2 (n k : ℕ) (bh : CMap n) (G : Set (Trip n)) (E : Set (Fix k n)) (cV p₂ : ℝ) :
    Prop where
  meas : MeasurableSet E
  prob : (fixP k n).real Eᶜ ≤ p₂
  var : ∀ ω ∈ E, vHat bh k ω ≤ cV * (4 / (n : ℝ)) / n
  sub : ∀ p : Joint k n, restJ p ∈ E → p.1 ∈ G

lemma jointP_fst (S : Set (Trip n)) :
    (jointP k n).real {p | p.1 ∈ S} = (mlpTriple 2 n).real S := by
  have e : {p : Joint k n | p.1 ∈ S} = S ×ˢ (univ : Set (Fin k → Fin n → ℝ)) := by
    ext p; simp
  unfold jointP
  rw [e, measureReal_prod_prod]
  simp

/-- **The conditional program theorem, general estimator.** Let `n ≥ 1`, `bh` a measurable
centre map, and `g` any function of all variables that is equal to the estimator
`gSampH bh k` where the fixed variables are in `E`. Under `H1`, `H2`, `H3`, with
`ε_W < 1/2`, `d₀ > 0`, `c_V > 0`:
`Pr_{W,A,F,η}(|g − B| ≤ sd/2) ≥ 1 − (p₁ + p₂ + p₃ + 2Φ̄((1/2 − ε_W)·√(n·d₀/c_V)))`. -/
theorem cond151_gen (hn : 1 ≤ n) {bh : CMap n} (hbh : Measurable bh) {G : Set (Trip n)}
    {E : Set (Fix k n)} {εW p₁ cV p₂ d₀ p₃ : ℝ} (h1 : H1 n εW p₁) (h2 : H2 n k bh G E cV p₂)
    (h3 : H3 n G d₀ p₃) (hεW : εW < 1 / 2) (hd₀ : 0 < d₀) (hcV : 0 < cV) (g : Joint k n → ℝ)
    (hgE : ∀ p : Joint k n, restJ p ∈ E → g p = gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2) :
    1 - (p₁ + p₂ + p₃ + 2 * PhiBar ((1 / 2 - εW) * √(n * d₀ / cV))) ≤
      (jointP k n).real {p | |g p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : (0 : ℝ) < 4 / (n : ℝ) := by positivity
  have hv : 0 < cV * (4 / (n : ℝ)) / n := by positivity
  have hεA : 0 < 1 / 2 - εW := by linarith
  have hd : 0 < √(d₀ * (4 / (n : ℝ))) := Real.sqrt_pos.mpr (by positivity)
  have hfin := finalStep_success (jointP k n) (fixP k n) (rowP n) measurable_restJ measurable_rowJ
    joint_map (measurable_linJ hbh k) h2.meas (fun ω _ => vHat_nonneg bh k ω)
    (fun ω _ => linJ_gauss bh k ω) hv h2.var g
    (fun p => Bn p.1.1 p.1.2.1 p.1.2.2) (fun p => gA p.1.1 p.1.2.1 p.1.2.2)
    (fun p => sdn p.1.1 p.1.2.1 p.1.2.2)
    (fun p hp => by rw [hgE p hp]; exact struct151 hn bh p)
    {p | p.1 ∈ G} h2.sub εW hεA hd
  -- the argument of `Φ̄`
  have harg : (1 / 2 - εW) * √(d₀ * (4 / (n : ℝ))) / √(cV * (4 / (n : ℝ)) / n) =
      (1 / 2 - εW) * √(n * d₀ / cV) := by
    rw [mul_div_assoc, ← Real.sqrt_div (by positivity)]
    congr 2
    field_simp
  -- the three probabilities
  have e1 : (jointP k n).real {p : Joint k n | εW * sdn p.1.1 p.1.2.1 p.1.2.2 <
      |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ≤ p₁ := by
    have := jointP_fst (k := k) {t : Trip n | εW * sdn t.1 t.2.1 t.2.2 <
      |gA t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2|}
    exact (le_of_eq this).trans h1
  have e3 : (jointP k n).real ({p : Joint k n | p.1 ∈ G} ∩
      {p | sdn p.1.1 p.1.2.1 p.1.2.2 < √(d₀ * (4 / (n : ℝ)))}) ≤ p₃ := by
    have hsub : ({p : Joint k n | p.1 ∈ G} ∩
        {p | sdn p.1.1 p.1.2.1 p.1.2.2 < √(d₀ * (4 / (n : ℝ)))}) ⊆
        {p : Joint k n | p.1 ∈ G ∩ {t : Trip n | sdn t.1 t.2.1 t.2.2 ^ 2 <
          d₀ * (4 / (n : ℝ))}} := by
      rintro p ⟨hp1, hp2⟩
      refine ⟨hp1, ?_⟩
      simp only [mem_ofPred_eq] at hp2 ⊢
      have h0 : 0 ≤ sdn p.1.1 p.1.2.1 p.1.2.2 := Real.sqrt_nonneg _
      calc sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 < √(d₀ * (4 / (n : ℝ))) ^ 2 :=
            pow_lt_pow_left₀ hp2 h0 (by norm_num)
        _ = d₀ * (4 / (n : ℝ)) := Real.sq_sqrt (by positivity)
    refine (measureReal_mono hsub).trans ?_
    rw [jointP_fst]
    exact h3
  rw [harg] at hfin
  have hset : {p : Joint k n | |g p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
      (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2} =
      {p | |g p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
    ext p
    simp only [mem_ofPred_eq]
    rw [show (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 = sdn p.1.1 p.1.2.1 p.1.2.2 / 2 by
      ring]
  rw [hset] at hfin
  have h2p := h2.prob
  linarith

/-- **The conditional program theorem** for the estimator `g = gSampH bh k`
(`(1/k)·Σ_j F(A₃b + σ_pη_j)`, `b = bh(W, A₁, A₂)` an arbitrary measurable centre). -/
theorem cond151 (hn : 1 ≤ n) {bh : CMap n} (hbh : Measurable bh) {G : Set (Trip n)}
    {E : Set (Fix k n)} {εW p₁ cV p₂ d₀ p₃ : ℝ} (h1 : H1 n εW p₁) (h2 : H2 n k bh G E cV p₂)
    (h3 : H3 n G d₀ p₃) (hεW : εW < 1 / 2) (hd₀ : 0 < d₀) (hcV : 0 < cV) :
    1 - (p₁ + p₂ + p₃ + 2 * PhiBar ((1 / 2 - εW) * √(n * d₀ / cV))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} :=
  cond151_gen hn hbh h1 h2 h3 hεW hd₀ hcV _ fun _ _ => rfl

/-- **The conditional program theorem for the straight-line program of Part 150**
(`fullProg150 k n J`: one program in the cost model, no forward pass of `A`; its centre is the
arithmetic centre `bTW J` with `J + 1` binomial atoms in both hidden layers of `A`). One more
hypothesis: `τ̃₀ > 0` on `E` (the value lemma of the program needs it). -/
theorem condProg151 (hn : 1 ≤ n) {J : ℕ} {G : Set (Trip n)} {E : Set (Fix k n)}
    {εW p₁ cV p₂ d₀ p₃ : ℝ} (h1 : H1 n εW p₁) (h2 : H2 n k (bTW J) G E cV p₂)
    (h3 : H3 n G d₀ p₃) (hτ : ∀ ω ∈ E, 0 < tauWA ω.1.1) (hεW : εW < 1 / 2) (hd₀ : 0 < d₀)
    (hcV : 0 < cV) :
    1 - (p₁ + p₂ + p₃ + 2 * PhiBar ((1 / 2 - εW) * √(n * d₀ / cV))) ≤
      (jointP k n).real {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hgE : ∀ p : Joint k n, restJ p ∈ E →
      (fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () =
        gSampH (bTW J) k p.1.1 p.1.2.1 p.1.2.2 p.2 := by
    intro p hp
    have hτ' : 0 < tauWA p.1.1 := hτ (restJ p) hp
    exact fullProg150_gSampH (k := k) (J := J) p.1.1 p.1.2.1 p.1.2.2 p.2 hτ'
  exact cond151_gen hn (measurable_bTW J) h1 h2 h3 hεW hd₀ hcV
    (fun p : Joint k n => (fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) ()) hgE

/-! ## The Gaussian tail in closed form -/

/-- `2Φ̄(a) ≤ exp(−a²/2)` for `a ≥ 0`. -/
theorem two_PhiBar_le_exp {a : ℝ} (ha : 0 ≤ a) : 2 * PhiBar a ≤ Real.exp (-(a ^ 2 / 2)) := by
  have := tail_le_exp ha
  unfold PhiBar
  linarith

/-- `2Φ̄(a) ≤ 2φ(a)(1/a − 1/a³ + 3/a⁵)` for `a > 0` (the bound (G4) of the document). -/
theorem two_PhiBar_le_mills {a : ℝ} (ha : 0 < a) :
    2 * PhiBar a ≤ 2 * (gaussianPDFReal 0 1 a * (1 / a - 1 / a ^ 3 + 3 / a ^ 5)) := by
  have := tail_le_mills3 ha
  unfold PhiBar
  linarith

/-- `Φ̄` is nonincreasing. -/
lemma PhiBar_anti {a b : ℝ} (hab : a ≤ b) : PhiBar b ≤ PhiBar a := tail_anti hab

/-- `cond151` with the bound `exp(−a²/2)` of the Gaussian tail,
`a = (1/2 − ε_W)·√(n·d₀/c_V)`. -/
theorem cond151_exp (hn : 1 ≤ n) {bh : CMap n} (hbh : Measurable bh) {G : Set (Trip n)}
    {E : Set (Fix k n)} {εW p₁ cV p₂ d₀ p₃ : ℝ} (h1 : H1 n εW p₁) (h2 : H2 n k bh G E cV p₂)
    (h3 : H3 n G d₀ p₃) (hεW : εW < 1 / 2) (hd₀ : 0 < d₀) (hcV : 0 < cV) :
    1 - (p₁ + p₂ + p₃ + Real.exp (-(((1 / 2 - εW) * √(n * d₀ / cV)) ^ 2 / 2))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have h := cond151 hn hbh h1 h2 h3 hεW hd₀ hcV
  have ha : 0 ≤ (1 / 2 - εW) * √(n * d₀ / cV) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have := two_PhiBar_le_exp ha
  linarith

/-- `cond151` with the bound `2φ(a)(1/a − 1/a³ + 3/a⁵)` of the Gaussian tail,
`a = (1/2 − ε_W)·√(n·d₀/c_V)`. -/
theorem cond151_mills (hn : 1 ≤ n) {bh : CMap n} (hbh : Measurable bh) {G : Set (Trip n)}
    {E : Set (Fix k n)} {εW p₁ cV p₂ d₀ p₃ : ℝ} (h1 : H1 n εW p₁) (h2 : H2 n k bh G E cV p₂)
    (h3 : H3 n G d₀ p₃) (hεW : εW < 1 / 2) (hd₀ : 0 < d₀) (hcV : 0 < cV) :
    1 - (p₁ + p₂ + p₃ + 2 * (gaussianPDFReal 0 1 ((1 / 2 - εW) * √(n * d₀ / cV)) *
        (1 / ((1 / 2 - εW) * √(n * d₀ / cV)) - 1 / ((1 / 2 - εW) * √(n * d₀ / cV)) ^ 3 +
          3 / ((1 / 2 - εW) * √(n * d₀ / cV)) ^ 5))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have h := cond151 hn hbh h1 h2 h3 hεW hd₀ hcV
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < (1 / 2 - εW) * √(n * d₀ / cV) :=
    mul_pos (by linarith) (Real.sqrt_pos.mpr (by positivity))
  have := two_PhiBar_le_mills ha
  linarith

/-! ## `H2` from an event of all variables that does not depend on the last row -/

/-- **`H2` from an event of `((W, A, F), η)` that does not depend on the last row of `F`.**
If `E'` is measurable, if membership of `E'` does not change when the last row is replaced, if
`Pr(E'ᶜ) ≤ p₂`, if `V′ ≤ c_V·S/n` on `E'` and `E'` is inside `G`: then `H2` holds for the event
`{ω | (ω, 0) ∈ E'}` of the fixed variables. -/
theorem H2_of_joint {bh : CMap n} {G : Set (Trip n)} {E' : Set (Joint k n)} {cV p₂ : ℝ}
    (hm : MeasurableSet E') (hinv : ∀ (ω : Fix k n) (w w' : Row n), joinJ ω w ∈ E' →
      joinJ ω w' ∈ E')
    (hp : (jointP k n).real E'ᶜ ≤ p₂)
    (hvar : ∀ p ∈ E', vHat bh k (restJ p) ≤ cV * (4 / (n : ℝ)) / n)
    (hsub : ∀ p ∈ E', p.1 ∈ G) :
    H2 n k bh G {ω | joinJ ω 0 ∈ E'} cV p₂ := by
  have hmE : MeasurableSet {ω : Fix k n | joinJ ω (0 : Row n) ∈ E'} :=
    (measurable_joinJ.comp (measurable_id.prodMk measurable_const)) hm
  have hiff : ∀ p : Joint k n, restJ p ∈ {ω : Fix k n | joinJ ω (0 : Row n) ∈ E'} ↔ p ∈ E' := by
    intro p
    constructor
    · intro h
      have := hinv (restJ p) 0 (rowJ p) h
      rwa [joinJ_rest_row] at this
    · intro h
      have h' : joinJ (restJ p) (rowJ p) ∈ E' := by rwa [joinJ_rest_row]
      exact hinv (restJ p) (rowJ p) 0 h'
  refine ⟨hmE, ?_, ?_, ?_⟩
  · have h1 : fixP k n = (jointP k n).map restJ := by
      have h := congrArg (Measure.map Prod.fst) (joint_map (k := k) (n := n))
      rw [Measure.map_map measurable_fst (measurable_restJ.prodMk measurable_rowJ)] at h
      have e : (Prod.fst ∘ fun p : Joint k n => (restJ p, rowJ p)) = restJ := rfl
      rw [e] at h
      rw [h]; simp
    rw [h1, map_measureReal_apply measurable_restJ hmE.compl]
    have e : restJ ⁻¹' {ω : Fix k n | joinJ ω (0 : Row n) ∈ E'}ᶜ = E'ᶜ := by
      ext p
      simp only [mem_preimage, mem_compl_iff]
      exact not_congr (hiff p)
    rw [e]
    exact hp
  · intro ω hω
    have := hvar (joinJ ω 0) hω
    rwa [restJ_joinJ] at this
  · intro p hp'
    exact hsub p ((hiff p).mp hp')

end BstLean.Part151
