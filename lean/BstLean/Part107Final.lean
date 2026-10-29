import BstLean.Part107Defs5

/-!
# Part 107: the Cantelli inequality, the variance bound of the realized spread, its lower tail,
and Lemma A — from the interface statements

Every theorem here takes the interface statements of `Part107Defs.lean` / `Part107Defs5.lean` that
it uses as hypotheses. `Part107All.lean` supplies them.

* `cantelli`: `Pr(X ≤ E X − t) ≤ Var X/(Var X + t²)`.
* `lower_tail`: if `n · Var X ≤ a (E X)²` and `E X > 0`, then
  `Pr(X < (1 − θ) E X) ≤ a/(a + n θ²)`.
* `spread_var`: Lemma S and Corollary S with the explicit constants (`vbar`, `aL`).
* `spread_tail`: the lower tail of the spread `X₁`.
* `lemmaA_abs`, `lemmaA`: the failure bound of the program for the linear part.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-- **The Cantelli inequality** (one-sided Chebyshev inequality), lower tail. -/
theorem cantelli {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) {t : ℝ} (ht : 0 < t) :
    P.real {ω | X ω ≤ (∫ ω, X ω ∂P) - t} ≤ Var[X; P] / (Var[X; P] + t ^ 2) := by
  set E := ∫ ω, X ω ∂P with hE
  set v := Var[X; P] with hv
  have hv0 : 0 ≤ v := variance_nonneg _ _
  set s := v / t with hs
  have hs0 : 0 ≤ s := div_nonneg hv0 ht.le
  have hst : s * t = v := div_mul_cancel₀ _ ht.ne'
  have hXi : Integrable X P := hX.integrable (by norm_num)
  have hc : MemLp (fun ω => X ω - E) 2 P := hX.sub (memLp_const E)
  have hcs : MemLp (fun ω => X ω - E - s) 2 P := hc.sub (memLp_const s)
  have hint : Integrable (fun ω => (X ω - E - s) ^ 2) P := hcs.integrable_sq
  have hint0 : Integrable (fun ω => (X ω - E) ^ 2) P := hc.integrable_sq
  have hvE : v = ∫ ω, (X ω - E) ^ 2 ∂P := by
    rw [hv, variance_eq_integral hXi.aemeasurable]
  have hval : ∫ ω, (X ω - E - s) ^ 2 ∂P = v + s ^ 2 := by
    have h1 : ∀ ω, (X ω - E - s) ^ 2 = (X ω - E) ^ 2 - (2 * s) * (X ω - E) + s ^ 2 := by
      intro ω; ring
    simp_rw [h1]
    have hI1 : Integrable (fun ω => X ω - E) P := hXi.sub (integrable_const E)
    have hI2 : Integrable (fun ω => (2 * s) * (X ω - E)) P := hI1.const_mul _
    have hI3 : Integrable (fun ω => (X ω - E) ^ 2 - (2 * s) * (X ω - E)) P := hint0.sub hI2
    have hz : ∫ ω, (X ω - E) ∂P = 0 := by
      rw [integral_sub hXi (integrable_const E)]
      simp [hE]
    rw [integral_add hI3 (integrable_const _), integral_sub hint0 hI2, integral_const_mul, hz,
      ← hvE]
    simp
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => (X ω - E - s) ^ 2)
    (ae_of_all _ fun _ => sq_nonneg _) hint ((t + s) ^ 2)
  rw [hval] at hmk
  have hsub : {ω | X ω ≤ E - t} ⊆ {ω | (t + s) ^ 2 ≤ (X ω - E - s) ^ 2} := by
    intro ω h
    simp only [Set.mem_ofPred_eq] at h ⊢
    nlinarith
  have hle : P.real {ω | X ω ≤ E - t} ≤ P.real {ω | (t + s) ^ 2 ≤ (X ω - E - s) ^ 2} :=
    measureReal_mono hsub
  set p := P.real {ω | X ω ≤ E - t} with hp
  have hp0 : 0 ≤ p := measureReal_nonneg
  have h2 : (t + s) ^ 2 * p ≤ v + s ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) hmk
  have hpos : 0 < v + t ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  -- multiply `h2` by `t²`
  have h3 : (t ^ 2 + v) ^ 2 * p ≤ v * (t ^ 2 + v) := by
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg t)
    have e1 : t ^ 2 * ((t + s) ^ 2 * p) = (t ^ 2 + s * t) ^ 2 * p := by ring
    have e2 : t ^ 2 * (v + s ^ 2) = v * t ^ 2 + (s * t) ^ 2 := by ring
    rw [e1, e2, hst] at this
    nlinarith
  have hpos' : 0 < t ^ 2 + v := by positivity
  have h4 : (t ^ 2 + v) * p ≤ v := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon hpos'
    nlinarith
  nlinarith

/-- **The lower tail from a relative variance bound**: if `n · Var X ≤ a (E X)²` and `E X > 0`,
then `Pr(X < (1 − θ) E X) ≤ a/(a + n θ²)`. -/
theorem lower_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) {a n θ : ℝ} (hn : 0 < n) (ha : 0 ≤ a)
    (hE : 0 < ∫ ω, X ω ∂P) (hvar : n * Var[X; P] ≤ a * (∫ ω, X ω ∂P) ^ 2) (hθ : 0 < θ) :
    P.real {ω | X ω < (1 - θ) * ∫ ω, X ω ∂P} ≤ a / (a + n * θ ^ 2) := by
  set E := ∫ ω, X ω ∂P with hEdef
  set v := Var[X; P] with hv
  have hv0 : 0 ≤ v := variance_nonneg _ _
  have ht : 0 < θ * E := mul_pos hθ hE
  have hc := cantelli P hX ht
  have hsub : {ω | X ω < (1 - θ) * E} ⊆ {ω | X ω ≤ E - θ * E} := by
    intro ω h
    simp only [Set.mem_ofPred_eq] at h ⊢
    nlinarith
  refine le_trans (measureReal_mono hsub) (le_trans hc ?_)
  have hd1 : 0 < v + (θ * E) ^ 2 := by positivity
  have hd2 : 0 < a + n * θ ^ 2 := by positivity
  rw [div_le_div_iff₀ hd1 hd2]
  have hE2 : 0 < E ^ 2 := by positivity
  nlinarith [mul_nonneg hv0 ha, mul_pos (mul_pos hθ hθ) hE2,
    mul_le_mul_of_nonneg_right hvar (sq_nonneg θ)]

/-- `J_* ≥ 0` whenever (P5) holds. -/
theorem Jstar_nonneg_of (h5 : P5_107) (n dA : ℕ) (σ : ℝ) (hn : 3 ≤ n) (hdA : dA = 3 ∨ dA = 4)
    (hσ : σ ≠ 0) : 0 ≤ Jstar dA n := by
  obtain ⟨-, h5b⟩ := h5 n dA σ hn hdA hσ
  refine le_trans ?_ h5b
  have : 0 ≤ twoPt (2 * n) n (2 * dA) σ (fun a => (kap dA a - cStar n dA) ^ 2) := by
    unfold twoPt
    exact integral_nonneg fun W => integral_nonneg fun u => integral_nonneg fun u' => sq_nonneg _
  positivity

/-- `a_L ≥ 2` whenever (P5) holds. -/
theorem aL_ge_two_of (h5 : P5_107) (n dA : ℕ) (σ : ℝ) (hn : 3 ≤ n) (hdA : dA = 3 ∨ dA = 4)
    (hσ : σ ≠ 0) : 2 ≤ aL dA n := by
  have hJ := Jstar_nonneg_of h5 n dA σ hn hdA hσ
  unfold aL
  have : 0 ≤ 3 * Jstar dA n * (1 + 2 / (n : ℝ)) / ((dA : ℝ) + 1 - vbar dA n) ^ 2 := by positivity
  linarith

/-- **Lemma S and Corollary S** (Gaussian versions, `r = 2`, `d_A ∈ {3, 4}`):
`E X₁ ≥ n (K − v̄)` and `n · Var X₁ ≤ a_L (E X₁)²`. -/
theorem spread_var (hC : CorS107) (h5 : P5_107) (n dA : ℕ) (σ : ℝ) (hn : 3 ≤ n)
    (hdA : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0) (hv : vbar dA n < (dA : ℝ) + 1) :
    MemLp (fun ω => X1 ω.1 ω.2.1 ω.2.2) 2 (PP (2 * n) n (2 * dA) dA σ) ∧
    (n : ℝ) * ((dA : ℝ) + 1 - vbar dA n) ≤ ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ ∧
    (n : ℝ) * Var[fun ω => X1 ω.1 ω.2.1 ω.2.2; PP (2 * n) n (2 * dA) dA σ] ≤
      aL dA n * (∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ) ^ 2 := by
  obtain ⟨h5a, h5b⟩ := h5 n dA σ hn hdA hσ
  exact hC (2 * n) n (2 * dA) dA σ (vbar dA n) (Jstar dA n) (cStar n dA) (by omega) (by omega) hσ
    hv h5a h5b

/-- **The lower tail of the spread**: `Pr(X₁ < (1 − θ) E X₁) ≤ a_L/(a_L + n θ²)`. -/
theorem spread_tail (hC : CorS107) (h5 : P5_107) (n dA : ℕ) (σ : ℝ) (hn : 3 ≤ n)
    (hdA : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0) (hv : vbar dA n < (dA : ℝ) + 1) {θ : ℝ} (hθ : 0 < θ) :
    (PP (2 * n) n (2 * dA) dA σ).real
        {ω | X1 ω.1 ω.2.1 ω.2.2 < (1 - θ) * ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ} ≤
      aL dA n / (aL dA n + (n : ℝ) * θ ^ 2) := by
  obtain ⟨hL2, hE, hvar⟩ := spread_var hC h5 n dA σ hn hdA hσ hv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEpos : 0 < ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ :=
    lt_of_lt_of_le (mul_pos hn0 (by linarith)) hE
  have ha : 0 ≤ aL dA n := le_trans (by norm_num) (aL_ge_two_of h5 n dA σ hn hdA hσ)
  exact lower_tail _ hL2 hn0 ha hEpos hvar hθ

/-- `a ↦ a/(a + c)` is monotone for `c > 0`, `a ≥ 0`. -/
theorem frac_mono {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c) :
    a / (a + c) ≤ b / (b + c) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Lemma A in an abstract form.** `X` (the spread) is a function of the first component;
`err` (the error `g − B`) a function of both. If `n · Var X ≤ a (E X)²` and
`(1 − lam) · E err² ≤ c · E X`, then
`Pr(|err| > √X/2) ≤ a/(a + n θ²) + 4c/((1 − θ)(1 − lam))`. -/
theorem lemmaA_abs {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : Ω → ℝ}
    {err : Ω × Ω' → ℝ} (hX : MemLp X 2 P) (hX0 : ∀ ω, 0 ≤ X ω)
    (herr : Integrable (fun ω => err ω ^ 2) (P.prod P')) {a n θ lam c : ℝ} (hn : 0 < n)
    (ha : 0 ≤ a) (hE : 0 < ∫ ω, X ω ∂P) (hvar : n * Var[X; P] ≤ a * (∫ ω, X ω ∂P) ^ 2)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hlam : lam < 1)
    (hEr : (1 - lam) * ∫ ω, err ω ^ 2 ∂P.prod P' ≤ c * ∫ ω, X ω ∂P) :
    (P.prod P').real {ω | Real.sqrt (X ω.1) / 2 < |err ω|} ≤
      a / (a + n * θ ^ 2) + 4 * c / ((1 - θ) * (1 - lam)) := by
  set E := ∫ ω, X ω ∂P with hEdef
  set Q := P.prod P' with hQ
  -- the two events
  set S1 : Set (Ω × Ω') := {ω | X ω.1 < (1 - θ) * E} with hS1
  set S2 : Set (Ω × Ω') := {ω | (1 - θ) * E / 4 ≤ err ω ^ 2} with hS2
  have hsub : {ω : Ω × Ω' | Real.sqrt (X ω.1) / 2 < |err ω|} ⊆ S1 ∪ S2 := by
    intro ω h
    simp only [Set.mem_ofPred_eq] at h
    by_cases h1 : X ω.1 < (1 - θ) * E
    · exact Or.inl h1
    · right
      push Not at h1
      simp only [hS2, Set.mem_ofPred_eq]
      have hsq : X ω.1 = Real.sqrt (X ω.1) ^ 2 := (Real.sq_sqrt (hX0 _)).symm
      have h0 : 0 ≤ Real.sqrt (X ω.1) := Real.sqrt_nonneg _
      have h2 : (Real.sqrt (X ω.1) / 2) ^ 2 < |err ω| ^ 2 :=
        pow_lt_pow_left₀ h (by positivity) (by norm_num)
      rw [sq_abs] at h2
      nlinarith
  have hunion : Q.real (S1 ∪ S2) ≤ Q.real S1 + Q.real S2 := measureReal_union_le _ _
  -- first event: Cantelli on `P`
  have h1 : Q.real S1 ≤ a / (a + n * θ ^ 2) := by
    have hlt := lower_tail P hX hn ha hE hvar hθ
    have hpre : S1 = Prod.fst ⁻¹' {ω : Ω | X ω < (1 - θ) * E} := rfl
    have hnull : NullMeasurableSet {ω : Ω | X ω < (1 - θ) * E} P :=
      nullMeasurableSet_lt hX.aestronglyMeasurable.aemeasurable aemeasurable_const
    have hmp : MeasurePreserving (Prod.fst : Ω × Ω' → Ω) Q P := measurePreserving_fst
    have : Q.real S1 = P.real {ω : Ω | X ω < (1 - θ) * E} := by
      rw [hpre]
      unfold Measure.real
      rw [hmp.measure_preimage hnull]
    rw [this]
    exact hlt
  -- second event: Markov
  have h2 : Q.real S2 ≤ 4 * c / ((1 - θ) * (1 - lam)) := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := Q) (f := fun ω => err ω ^ 2)
      (ae_of_all _ fun _ => sq_nonneg _) herr ((1 - θ) * E / 4)
    have hd : 0 < (1 - θ) * (1 - lam) := mul_pos (by linarith) (by linarith)
    rw [le_div_iff₀ hd]
    have hI0 : 0 ≤ ∫ ω, err ω ^ 2 ∂Q := integral_nonneg fun _ => sq_nonneg _
    have hp0 : 0 ≤ Q.real S2 := measureReal_nonneg
    have hl : 0 < 1 - lam := by linarith
    have hth : 0 < 1 - θ := by linarith
    -- (1-θ) E/4 * p ≤ I, (1-lam) I ≤ c E
    have h3 : (1 - lam) * ((1 - θ) * E / 4 * Q.real S2) ≤ c * E :=
      le_trans (mul_le_mul_of_nonneg_left hmk hl.le) hEr
    have h4 : E * (Q.real S2 * ((1 - θ) * (1 - lam))) ≤ E * (4 * c) := by nlinarith
    exact le_of_mul_le_mul_left h4 hE
  calc Q.real {ω | Real.sqrt (X ω.1) / 2 < |err ω|} ≤ Q.real (S1 ∪ S2) := measureReal_mono hsub
    _ ≤ Q.real S1 + Q.real S2 := hunion
    _ ≤ _ := add_le_add h1 h2

/-- **Lemma A for the linear part** (Gaussian versions, `r = 2`, `d_A ∈ {3, 4}`, `ε = 1/2`): the
probability, over `W`, `A₁`, `ℓ` and the `k` draws of the program, of
`|g − B| > sd_μ/2` (`sd_μ = √X₁`) is at most
`a_L/(a_L + n θ²) + 4(λ_0 + 1/k)/((1 − θ)(1 − λ_0))`. -/
theorem lemmaA (hC : CorS107) (h5 : P5_107) (hE : LemmaE107) (n dA k : ℕ) (σ : ℝ) (hn : 3 ≤ n)
    (hdA : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0) (hk : 1 ≤ k) (hv : vbar dA n < (dA : ℝ) + 1)
    (hlam : lam0 (2 * n) (2 * dA) < 1) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (Full (2 * n) n (2 * dA) dA k σ).real
        {ω | Real.sqrt (X1 ω.1.1 ω.1.2.1 ω.1.2.2) / 2 <
          |gErr (N := 2 * n) (n := n) (dW := 2 * dA) (dA := dA) (k := k) σ ω|} ≤
      aL dA n / (aL dA n + (n : ℝ) * θ ^ 2) +
        4 * (lam0 (2 * n) (2 * dA) + 1 / (k : ℝ)) / ((1 - θ) * (1 - lam0 (2 * n) (2 * dA))) := by
  have : IsProbabilityMeasure (uniformSphere (2 * n)) :=
    BstLean.Part29.uniformSphere_isProbability (2 * n) (by omega)
  obtain ⟨hL2, hEX, hvar⟩ := spread_var hC h5 n dA σ hn hdA hσ hv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEpos : 0 < ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ :=
    lt_of_lt_of_le (mul_pos hn0 (by linarith)) hEX
  have ha : 0 ≤ aL dA n := le_trans (by norm_num) (aL_ge_two_of h5 n dA σ hn hdA hσ)
  obtain ⟨hint, hbd⟩ := hE (2 * n) n (2 * dA) dA k σ (by omega) (by rcases hdA with h | h <;> omega) hk
  exact lemmaA_abs (PP (2 * n) n (2 * dA) dA σ) (Measure.pi fun _ : Fin k => primM (2 * n) n)
    (X := fun ω => X1 ω.1 ω.2.1 ω.2.2) hL2 (fun ω => variance_nonneg _ _) hint hn0 ha hEpos hvar
    hθ hθ1 hlam hbd

end BstLean.Part107
