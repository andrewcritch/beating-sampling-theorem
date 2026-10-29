import BstLean.Part151Inputs
import BstLean.Part151Kap

/-!
# Part 151 (file `G`): the Gaussian step in moment form for the `W` term

Role: `delegations/statements/p151-spec.md`, item 5 ("sharper constants").

The error of the `W` stage is also linear in the last row `f₃` of `F`:
`B′ − B = gA W A F − Bn W A F = f₃·Δ_W`, with
`Δ_W = E_{x∼ν′} z_F(A(x)) − E_u z_F(A(x_W(u)))`, a function of `(W, A, F₁, F₂)` only. So the
Chebyshev step for the `W` term can be replaced by the Gaussian step in moment form
(`gaussStepMoment`), which multiplies that term by `κ` (`κ = 1/3`: `two_PhiBar_le_third`).

* `dW ω`: the vector `Δ_W`; `vW ω = t_F·|Δ_W|²`; `linW ω w = w·Δ_W`.
* **`wStruct151`**: `B′ − B = f₃·Δ_W`.
* `lint_vW`: `E[1_G·t_F|Δ_W|²] = E[1_G·(B′ − B)²]` for the good hidden event `G` of `W`.
* **`wStageGauss151`**: `Pr(W good, |B′ − B| > c) ≤ κ·(4849/20000)(1/n)(4/n)/c²`.
* **`condLean151G`**, `condLeanProg151G`: `condLean151`, `condLeanProg151` with the `W` term
  multiplied by `κ`.
* (`theorem5_frameProgG`, the frame for the program with that term, is in `Part151G1`.)
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part138 (cheapIn)
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143 BstLean.Part145
open BstLean.Part149 BstLean.Part150

variable {k n : ℕ}

/-- `Δ_W = E_{x∼ν′} z_F(A(x)) − E_u z_F(A(x_W(u)))`: the feature error of the `W` stage. A
function of `(W, A, F₁, F₂)`; it ignores `η`. -/
noncomputable def dW (ω : Fix k n) : Fin (mF n) → ℝ := fun i =>
  ∫ x, hidF ω.1.2.2.1 ω.1.2.2.2 ω.1.2.1 x i ∂cheapIn (cenA ω.1.1) (tauWA ω.1.1) -
    aVec ω.1.1 ω.1.2.1 ω.1.2.2.1 ω.1.2.2.2 i

/-- `t_F·|Δ_W|²`: the conditional variance of `B′ − B` given all but the last row. -/
noncomputable def vW (ω : Fix k n) : ℝ := 2 / (mF n : ℝ) * normSq (dW ω)

lemma vW_nonneg (ω : Fix k n) : 0 ≤ vW ω := by
  unfold vW
  have : 0 ≤ normSq (dW ω) := Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

/-- The linear form `f₃·Δ_W`. -/
noncomputable def linW (ω : Fix k n) (w : Row n) : ℝ := rowOf 0 w ⬝ᵥ dW ω

/-- **The error of the `W` stage is linear in the last row of `F`**: `B′ − B = f₃·Δ_W`. -/
theorem wStruct151 (hn : 1 ≤ n) (p : Joint k n) :
    gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2 = linW (restJ p) (rowJ p) := by
  obtain ⟨⟨W, A, F₁, F₂, F₃⟩, γ⟩ := p
  have hN : 1 ≤ 2 * n := by omega
  simp only [restJ, rowJ, linW]
  have hg : gA W A (F₁, F₂, F₃) =
      ∑ l, F₃ 0 l * ∫ x, hidF F₁ F₂ A x l ∂cheapIn (cenA W) (tauWA W) := by
    unfold gA
    simp_rw [phiN_last]
    rw [integral_finsetSum _ fun l _ =>
      (hidF_cheap_integrable hn F₁ F₂ A (cenA W) (tauWA W) l).const_mul _]
    simp_rw [integral_const_mul]
  rw [hg, Bn_last hn hN W A F₁ F₂ F₃]
  simp only [dotProduct, rowOf, dW]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

lemma measurable_linW (hn : 1 ≤ n) :
    Measurable (fun q : Fix k n × Row n => linW q.1 q.2) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : (fun q : Fix k n × Row n => linW q.1 q.2) = fun q =>
      gA (joinJ q.1 q.2).1.1 (joinJ q.1 q.2).1.2.1 (joinJ q.1 q.2).1.2.2 -
        Bn (joinJ q.1 q.2).1.1 (joinJ q.1 q.2).1.2.1 (joinJ q.1 q.2).1.2.2 := by
    funext q
    have h := wStruct151 hn (joinJ q.1 q.2)
    rw [restJ_joinJ, rowJ_joinJ] at h
    exact h.symm
  rw [e]
  have hj : Measurable (fun q : Fix k n × Row n => (joinJ q.1 q.2).1) :=
    measurable_fst.comp measurable_joinJ
  have h1 := (measurable_gA (n := n) (mA := mA n) (mF := mF n)).comp hj
  have h2 := (BstLean.Part131.measurable_Bn (mA := mA n) (mF := mF n) hN).comp hj
  exact h1.sub h2

/-- Given all other variables, `f₃·Δ_W` is centred Gaussian with variance `t_F·|Δ_W|²`. -/
theorem linW_gauss (ω : Fix k n) :
    (rowP n).map (linW ω) = gaussianReal 0 (vW ω).toNNReal := by
  unfold rowP linW vW
  exact row_gauss (by positivity) _

/-- The good hidden event of `W` (Part 145) as a set of the fixed variables. -/
def EWg (k n : ℕ) : Set (Fix k n) := {ω | ω.1.1 ∈ goodWAG (Gwin n)}

lemma EWg_meas (hn : 4096 ≤ n) : MeasurableSet (EWg k n) := by
  have hG := (goodEvFR hn).to0
  have hm : Measurable (fun ω : Fix k n => ω.1.1) := measurable_fst.comp measurable_fst
  exact hm (goodWAG0_meas hG (by omega))

/-- **The bridge for the `W` stage**: `E[1_G·t_F|Δ_W|²] = E[1_G·(B′ − B)²]`. -/
theorem lint_vW (hn : 4096 ≤ n) :
    ∫⁻ ω in EWg k n, ENNReal.ofReal (vW ω) ∂fixP k n =
      ∫⁻ t, ENNReal.ofReal (errGAG (Gwin n) t) ∂mlpTriple 2 n := by
  have hn1 : 1 ≤ n := by omega
  have hG := (goodEvFR hn).to0
  have hE := EWg_meas (k := k) hn
  have hlin2 : Measurable (fun q : Fix k n × Row n => ENNReal.ofReal (linW q.1 q.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_linW hn1).pow_const 2)
  set Fn : Fix k n × Row n → ℝ≥0∞ :=
    (EWg k n ×ˢ (univ : Set (Row n))).indicator
      (fun q => ENNReal.ofReal (linW q.1 q.2 ^ 2)) with hFn
  have mFn : Measurable Fn := hlin2.indicator (hE.prod MeasurableSet.univ)
  have e1 : ∀ p : Joint k n, ENNReal.ofReal (errGAG (Gwin n) p.1) = Fn (restJ p, rowJ p) := by
    intro p
    by_cases hp : p.1.1 ∈ goodWAG (Gwin n)
    · have hp' : (restJ p, rowJ p) ∈ EWg k n ×ˢ (univ : Set (Row n)) := ⟨hp, mem_univ _⟩
      have e : errGAG (Gwin n) p.1 =
          (gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2 := by
        unfold errGAG
        rw [indicator_of_mem hp]
      rw [e, hFn, indicator_of_mem hp', wStruct151 hn1 p]
    · have hp' : (restJ p, rowJ p) ∉ EWg k n ×ˢ (univ : Set (Row n)) := fun h => hp h.1
      have e : errGAG (Gwin n) p.1 = 0 := by
        unfold errGAG
        rw [indicator_of_notMem hp]
      rw [e, hFn, indicator_of_notMem hp', ENNReal.ofReal_zero]
  have mG : Measurable (fun t : Trip n => ENNReal.ofReal (errGAG (Gwin n) t)) :=
    ENNReal.measurable_ofReal.comp (measurable_errGAG0 hG hn1)
  have e0 : ∫⁻ t, ENNReal.ofReal (errGAG (Gwin n) t) ∂mlpTriple 2 n =
      ∫⁻ p : Joint k n, ENNReal.ofReal (errGAG (Gwin n) p.1) ∂jointP k n := by
    unfold jointP
    have h := lintegral_prod (μ := mlpTriple 2 n) (ν := gamK k n)
      (fun p : Trip n × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errGAG (Gwin n) p.1))
      (mG.comp measurable_fst).aemeasurable
    rw [h]
    simp
  rw [e0]
  simp_rw [e1]
  have e2 : ∫⁻ p, Fn (restJ p, rowJ p) ∂jointP k n = ∫⁻ q, Fn q ∂(fixP k n).prod (rowP n) := by
    rw [← joint_map, lintegral_map mFn (measurable_restJ.prodMk measurable_rowJ)]
  rw [e2, hFn, lintegral_indicator (hE.prod MeasurableSet.univ), ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hlin2.aemeasurable]
  refine lintegral_congr fun ω => ?_
  unfold linW vW rowP
  exact (row_sq_lintegral (by positivity) _).symm

/-- **The `W` term with the Gaussian step in moment form**: for `n ≥ 4096`, `c > 0`, and every
constant `κ` with `2Φ̄(a) ≤ κ/a²`:
`Pr(W good, |B′ − B| > c) ≤ κ·(4849/20000)·(1/n)·(4/n)/c²`. (Chebyshev: `κ = 1`.) -/
theorem wStageGauss151 {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (hn : 4096 ≤ n) {c : ℝ} (hc : 0 < c) :
    (jointP k n).real {p | p.1.1 ∈ goodWAG (Gwin n) ∧
        c < |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ≤
      κ * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) / c ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  obtain ⟨hΛi, hΛ⟩ := LamVR hn
  have hW := errVecAF_lint (goodEvFR hn) hn (by unfold Lam145R; norm_num) hΛi hΛ
    (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 7) (by norm_num) (η' := 1 / 29)
    (by norm_num)
  have hXA := XA145_R hn
  have hW' : ∫⁻ t, ENNReal.ofReal (errGAG (Gwin n) t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) :=
    hW.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hXA (by positivity)))
  have hI : ∫⁻ ω in EWg k n, ENNReal.ofReal (vW ω) ∂fixP k n ≤
      ENNReal.ofReal (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) := by
    rw [lint_vW hn]; exact hW'
  have hlin := measurable_linW (k := k) hn1
  have hE := EWg_meas (k := k) hn
  have hstep := gaussStepMoment hκ (fixP k n) (rowP n) hlin hE (fun ω _ => vW_nonneg ω)
    (fun ω _ => linW_gauss ω) hc
    (by positivity : (0 : ℝ) ≤ 4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) hI
  have hpair : Measurable fun p : Joint k n => (restJ p, rowJ p) :=
    measurable_restJ.prodMk measurable_rowJ
  have hS : MeasurableSet {q : Fix k n × Row n | q.1 ∈ EWg k n ∧ c < |linW q.1 q.2|} :=
    (measurable_fst hE).inter (measurableSet_lt measurable_const hlin.abs)
  have eset : {p : Joint k n | p.1.1 ∈ goodWAG (Gwin n) ∧
      c < |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} =
      (fun p : Joint k n => (restJ p, rowJ p)) ⁻¹'
        {q : Fix k n × Row n | q.1 ∈ EWg k n ∧ c < |linW q.1 q.2|} := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage]
    rw [← wStruct151 hn1 p]
    rfl
  rw [eset, ← map_measureReal_apply hpair hS, joint_map]
  exact hstep

/-! ## The conditional program theorem with the `W` term in moment form -/

/-- **`condLean151` with the Gaussian step for the `W` term**: the term
`(4849/20000)/(ε_W²θq₀)/n` is multiplied by `κ`, for every constant `κ` with
`2Φ̄(a) ≤ κ/a²` (`κ = 1/3`: `two_PhiBar_le_third`). -/
theorem condLean151G {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (hn : 4096 ≤ n) {bh : CMap n} (hbh : Measurable bh) {E : Set (Fix k n)}
    {cV p₂ : ℝ} (h2 : H2 n k bh univ E cV p₂) (hcV : 0 < cV) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) (gE : Joint k n → ℝ)
    (hgE : ∀ p : Joint k n, restJ p ∈ E → gE p = gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2) :
    1 - (1 / (n : ℝ) + κ * (4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n) + p₂ +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) / cV))) ≤
      (jointP k n).real {p | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  set d : ℝ := √(θ * c₀) with hd
  have hd0 : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = θ * c₀ := Real.sq_sqrt (by positivity)
  have hv : 0 < cV * (4 / (n : ℝ)) / n := by positivity
  have hεA : 0 < 1 / 2 - εW := by linarith
  have hfin := finalStepR (jointP k n) (fixP k n) (rowP n) measurable_restJ measurable_rowJ
    joint_map (measurable_linJ hbh k) h2.meas (fun ω _ => vHat_nonneg bh k ω)
    (fun ω _ => linJ_gauss bh k ω) hv h2.var gE
    (fun p => Bn p.1.1 p.1.2.1 p.1.2.2) (fun p => gA p.1.1 p.1.2.1 p.1.2.2)
    (fun p => sdn p.1.1 p.1.2.1 p.1.2.2)
    (fun p hp => by rw [hgE p hp]; exact struct151 hn1 bh p) εW hεA hd0
  have harg : (1 / 2 - εW) * d / √(cV * (4 / (n : ℝ)) / n) =
      (1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) / cV) := by
    rw [hd, mul_div_assoc, ← Real.sqrt_div (by positivity)]
    congr 2
    rw [hc₀]
    field_simp
  rw [harg] at hfin
  -- the first term
  have t1 : (jointP k n).real {p : Joint k n | restJ p ∈ E ∧ d ≤ sdn p.1.1 p.1.2.1 p.1.2.2 ∧
      εW * sdn p.1.1 p.1.2.1 p.1.2.2 <
        |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ≤
      1 / (n : ℝ) + κ * (4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n) := by
    have h1 := wBad151 hn
    have h3 := wStageGauss151 (k := k) hκ hn (mul_pos hεW0 hd0)
    have hsub : {p : Joint k n | restJ p ∈ E ∧ d ≤ sdn p.1.1 p.1.2.1 p.1.2.2 ∧
        εW * sdn p.1.1 p.1.2.1 p.1.2.2 <
          |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ⊆
        {p : Joint k n | p.1 ∈ {t : Trip n | t.1 ∉ goodWAG (Gwin n)}} ∪
          {p : Joint k n | p.1.1 ∈ goodWAG (Gwin n) ∧
            εW * d < |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} := by
      rintro p ⟨-, hp2, hp3⟩
      by_cases hW : p.1.1 ∈ goodWAG (Gwin n)
      · refine Or.inr ⟨hW, lt_of_le_of_lt ?_ hp3⟩
        exact mul_le_mul_of_nonneg_left hp2 hεW0.le
      · exact Or.inl hW
    refine (measureReal_mono hsub).trans ?_
    refine (measureReal_union_le _ _).trans ?_
    rw [jointP_fst]
    have e3 : 4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ)) / (εW * d) ^ 2 =
        4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n := by
      rw [mul_pow, hd2, hc₀]
      field_simp
    rw [mul_div_assoc, e3] at h3
    linarith
  -- the spread
  have t3 : (jointP k n).real {p : Joint k n | sdn p.1.1 p.1.2.1 p.1.2.2 < d} ≤
      2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n := by
    have h := spreadLean151 hn hθ1
    have hsub : {p : Joint k n | sdn p.1.1 p.1.2.1 p.1.2.2 < d} ⊆
        {p : Joint k n | p.1 ∈ {t : Trip n | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c₀}} := by
      intro p hp
      simp only [mem_ofPred_eq] at hp ⊢
      have h0 : 0 ≤ sdn p.1.1 p.1.2.1 p.1.2.2 := Real.sqrt_nonneg _
      rw [← hd2]
      exact pow_lt_pow_left₀ hp h0 (by norm_num)
    refine (measureReal_mono hsub).trans ?_
    rw [jointP_fst]
    exact h
  have hu : (1 : ℝ) ≤ (jointP k n).real {p | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} +
      (jointP k n).real {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
        |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|} := by
    have e : {p : Joint k n | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
          sdn p.1.1 p.1.2.1 p.1.2.2 / 2} ∪
        {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
          |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|} = univ := by
      ext p
      simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      rw [show (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 =
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2 by ring]
      exact le_or_gt _ _
    have h1 := measureReal_union_le (μ := jointP k n)
      {p : Joint k n | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2}
      {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
        |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|}
    rw [e] at h1
    simpa using h1
  have h2p := h2.prob
  linarith

/-- `condLean151G` for the estimator `gSampH bh k`. -/
theorem condLeanSamp151G {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (hn : 4096 ≤ n) {bh : CMap n} (hbh : Measurable bh) {E : Set (Fix k n)}
    {cV p₂ : ℝ} (h2 : H2 n k bh univ E cV p₂) (hcV : 0 < cV) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + κ * (4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n) + p₂ +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) / cV))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} :=
  condLean151G hκ hn hbh h2 hcV hεW0 hεW hθ0 hθ1
    (fun p : Joint k n => gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2) fun _ _ => rfl

/-- `condLean151G` for the straight-line program `fullProg150 k n J` of Part 150, if
`τ̃₀ > 0` on `E`. -/
theorem condLeanProg151G {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (hn : 4096 ≤ n) {J : ℕ} {E : Set (Fix k n)}
    {cV p₂ : ℝ} (h2 : H2 n k (bTW J) univ E cV p₂) (hτ : ∀ ω ∈ E, 0 < tauWA ω.1.1)
    (hcV : 0 < cV) {εW θ : ℝ} (hεW0 : 0 < εW) (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + κ * (4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n) + p₂ +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) / cV))) ≤
      (jointP k n).real {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hgE : ∀ p : Joint k n, restJ p ∈ E →
      (fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () =
        gSampH (bTW J) k p.1.1 p.1.2.1 p.1.2.2 p.2 := by
    intro p hp
    have hτ' : 0 < tauWA p.1.1 := hτ (restJ p) hp
    exact fullProg150_gSampH (k := k) (J := J) p.1.1 p.1.2.1 p.1.2.2 p.2 hτ'
  exact condLean151G hκ hn (measurable_bTW J) h2 hcV hεW0 hεW hθ0 hθ1
    (fun p : Joint k n => (fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) ()) hgE

end BstLean.Part151
