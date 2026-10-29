import BstLean.Part140Cost
import BstLean.Part140Sample

/-!
# Part 140, item 4: the arithmetic program succeeds, and its operation count

Role: `delegations/statements/p140-spec.md`, item 4. `Part140Cost` has the two straight-line
programs in the model `RProg` of Part 130 (operations `+ − × ÷ √ relu`, one unit each; reads of
inputs are free): `preProg N m` (first pass: `a = M₂ h̄₁` and the smoothing width `s`) and
`hatProg k n m mA mF` (given the centre `b̂`: `ĉ = M₃ b̂`, the scalar `τ̂₀`, and the mean of
`F(A(·))` over `k` points). Between the two programs the centre is `b̂_i = ψ_s(a_i)`: `ψ_s` is NOT
an arithmetic function; it is counted as one oracle operation for each of the `m` coordinates.
The real constants `c_N` and `c₁ = 1/(γκ₁²)` (they depend on `n` only) and the Gaussian vectors
are inputs of the programs.

* `c1Hat N = 1/(γκ₁²)`; `gProg k W A F γ`: the output of `hatProg` at the computed centre.
* `gProg_eq`: `gProg = gSampleH` (the sample mean of `Part140Sample`) if no point `M₃ b̂ + τ̂₀γ_i`
  is zero; `preHat_null`: for `τ̂₀ ≠ 0` this holds for almost every `γ`.
* **`progSucceeds140`**: for `n ≥ 4096`, `k ≥ 1`:
  `Pr(|gProg − B| ≤ sd/2) ≥ 1 − (0.002 + 2022/n + 180/k)` over `(W, A, F)` and the `k` Gaussian
  vectors.
* **`cost140_focus`**, `cost140_vs_sample`: the operation count of the two programs plus the `m`
  oracle operations is at most `2m² + m(6n + 4) + 12 + k·(5n + 2 + cost(A) + cost(F))`, and at
  most the count of ONE direct evaluation of `W` plus `4m + n + 12 + k·(…)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM

section link

variable {N m n mA mF : ℕ}

/-- The constant input `c₁ = 1/(γκ₁²)` of `hatProg` (it depends on `N` only). -/
noncomputable def c1Hat (N : ℕ) : ℝ := 1 / (2 / (N : ℝ) * kap1 N ^ 2)

/-- **The output of the arithmetic program** `hatProg` at the computed centre `b̂` of `W`, with
the `k` Gaussian vectors `γ`. -/
noncomputable def gProg (k : ℕ) (W : MlpParam N m n) (A : MlpParam n mA n) (F : MlpParam n mF 1)
    (γ : Fin k → Fin n → ℝ) : ℝ :=
  (hatProg k n m mA mF).eval (hatVal (bhat (W.1, W.2.1)) W.2.2 (c1Hat N) γ A F) ()

/-- The program computes the sample mean of `Part140Sample` if no point is zero before the
normalization. -/
theorem gProg_eq (k : ℕ) (W : MlpParam N m n) (A : MlpParam n mA n) (F : MlpParam n mF 1)
    (γ : Fin k → Fin n → ℝ) (h : ∀ i, normSq (preHat W (γ i)) ≠ 0) :
    gProg k W A F γ = gSampleH k W A F γ := by
  have e : ∀ g : Fin n → ℝ, W.2.2.mulVec (bhat (W.1, W.2.1)) +
      tauOf m (bhat (W.1, W.2.1)) (c1Hat N) • g = preHat W g := by
    intro g
    unfold c1Hat preHat
    rw [tauOf_bhat]
  unfold gProg
  rw [hatProg_eval_sphPt _ _ _ _ _ _ (fun i => by rw [e]; exact h i)]
  unfold gSampleH phiS
  simp_rw [e]

lemma stdGauss_nullSingleton (hn : 1 ≤ n) : NullSingletonClass (stdGauss (Fin n)) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  unfold stdGauss
  exact Measure.pi_nullSingletonClass (μ := fun _ : Fin n => gaussianReal 0 1) (⟨0, hn⟩ : Fin n)

/-- For `τ̂₀ ≠ 0`, almost no `k`-tuple of Gaussian vectors has a zero point before the
normalization. -/
theorem preHat_null (hn : 1 ≤ n) (k : ℕ) (W : MlpParam N m n)
    (hτ : tauHat N m (W.1, W.2.1) ≠ 0) :
    gamK k n {γ | ∃ i, normSq (preHat W (γ i)) = 0} = 0 := by
  have inst : NullSingletonClass (stdGauss (Fin n)) := stdGauss_nullSingleton (n := n) hn
  set c := W.2.2.mulVec (bhat (W.1, W.2.1)) with hc
  set τ := tauHat N m (W.1, W.2.1) with hτd
  set g₀ : Fin n → ℝ := (-τ⁻¹) • c with hg₀
  have hsub : {γ : Fin k → Fin n → ℝ | ∃ i, normSq (preHat W (γ i)) = 0} ⊆
      ⋃ i : Fin k, {γ | γ i = g₀} := by
    rintro γ ⟨i, hi⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have h0 : preHat W (γ i) = 0 := eq_zero_of_normSq hi
    have h1 : c + τ • γ i = 0 := h0
    change γ i = g₀
    have h2 : τ • γ i = -c := by
      have := eq_neg_of_add_eq_zero_right h1
      exact this
    rw [hg₀]
    funext j
    have h3 := congrFun h2 j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h3 ⊢
    field_simp
    linarith
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun i => ?_
  unfold gamK
  exact Measure.pi_hyperplane (μ := fun _ : Fin k => stdGauss (Fin n)) i g₀

end link

/-! ## The program succeeds -/

/-- The success event of the arithmetic program: `|gProg − B| ≤ sd/2`. -/
def okProg (k n : ℕ) : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
    MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) :=
  {p | |gProg k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
    sdn p.1.1 p.1.2.1 p.1.2.2 / 2}

/-- The event "`W` is good and a point is zero before the normalization" has probability `0`. -/
lemma zeroPt_null {n : ℕ} (hn : 4096 ≤ n) (k : ℕ) :
    ((mlpTriple 2 n).prod (gamK k n))
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWH n ∧ ∃ i, normSq (preHat p.1.1 (p.2 i)) = 0} = 0 := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWH n ∧ ∃ i, normSq (preHat p.1.1 (p.2 i)) = 0} with hZ
  have mZ : MeasurableSet Z := by
    have m1 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWH n} :=
      (measurable_fst.comp measurable_fst) (goodWH_meas hn1)
    have m2 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        ∃ i, normSq (preHat p.1.1 (p.2 i)) = 0} := by
      have e : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
          ∃ i, normSq (preHat p.1.1 (p.2 i)) = 0} =
          ⋃ i : Fin k, {p | normSq (preHat p.1.1 (p.2 i)) = 0} := by
        ext p; simp
      rw [e]
      refine MeasurableSet.iUnion fun i => ?_
      have hm : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => normSq (preHat p.1.1 (p.2 i))) :=
        measurable_normSq.comp ((measurable_preHat hN).comp
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_pi_apply i).comp measurable_snd)))
      exact hm (measurableSet_singleton 0)
    exact m1.inter m2
  rw [Measure.measure_prod_null mZ]
  refine Filter.Eventually.of_forall fun t => ?_
  change gamK k n (Prod.mk t ⁻¹' Z) = 0
  by_cases hg : t.1 ∈ goodWH n
  · have hτ : tauHat (2 * n) (mW n) (t.1.1, t.1.2.1) ≠ 0 := (tauHat_pos hn hg).ne'
    refine measure_mono_null ?_ (preHat_null hn1 k t.1 hτ)
    rintro γ ⟨-, h⟩
    exact h
  · have e : Prod.mk t ⁻¹' Z = ∅ := by
      ext γ
      simp only [Set.mem_preimage, hZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro h
      exact absurd h hg
    rw [e]
    simp

/-- **`progSucceeds140`: the arithmetic program succeeds.** For every `n ≥ 4096` and `k ≥ 1`,
with `gProg` the output of `hatProg` (the straight-line program of `Part140Cost`) at the
computed centre `b̂ = ψ_s(M₂ h̄₁)` of `W`, the constant `c₁ = 1/(γκ₁²)` and `k` independent
standard Gaussian vectors: `Pr(|gProg − B| ≤ sd/2) ≥ 1 − (0.002 + 2022/n + 180/k)`, the
probability over `(W, A, F)` and the `k` Gaussian vectors. -/
theorem progSucceeds140 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 2022 / (n : ℝ) + 180 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProg k n) := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hs0 : (0 : ℝ) < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 := by
    have : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
    positivity
  set μ := (mlpTriple 2 n).prod (gamK k n) with hμ
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWH n ∧ ∃ i, normSq (preHat p.1.1 (p.2 i)) = 0} with hZ
  have hZ0 : μ.real Z = 0 := by
    rw [measureReal_def, zeroPt_null hn k]
    rfl
  have h1 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWH n}ᶜ ≤ 2 / 1000 + 70 / (n : ℝ) :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWH n}).trans_le (badHat_prob hn)
  have h2 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWH n} ∧
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤
          (gProg k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (21 / 20 * (183 / 100 / (n : ℝ)) + 84 * EHH n (1 / 20) + (k : ℝ)⁻¹) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) := by
    have hT := errSampleTailHat hn (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
      (by norm_num) hk hs0
    have e84 : (4 : ℝ) * (1 + 1 / (1 / 20)) = 84 := by norm_num
    have e105 : (1 : ℝ) + 1 / 20 = 21 / 20 := by norm_num
    rw [e84, e105] at hT
    have hsub : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWH n} ∧
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤
          (gProg k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ⊆
        {p | 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤ errSH k n p} ∪ Z := by
      rintro p ⟨hg, he⟩
      by_cases hz : ∃ i, normSq (preHat p.1.1 (p.2 i)) = 0
      · exact Or.inr ⟨hg, hz⟩
      · left
        push Not at hz
        change _ ≤ errSH k n p
        unfold errSH
        rw [Set.indicator_of_mem (show p.1.1 ∈ goodWH n from hg),
          ← gProg_eq k p.1.1 p.1.2.1 p.1.2.2 p.2 hz]
        exact he
    calc _ ≤ μ.real ({p | 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤ errSH k n p} ∪ Z) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ μ.real {p | 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤ errSH k n p} +
          μ.real Z := measureReal_union_le _ _
      _ ≤ _ := by rw [hZ0, add_zero]; exact hT
  have h3 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 <
          4 * (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4)} ≤
      vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 := by
    have e : (4 : ℝ) * (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) =
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by ring
    rw [e]
    exact (prod_fst_real (mlpTriple 2 n) (gamK k n)
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0))}).trans_le
      (spreadLow139 hn (by norm_num))
  have h := ok_of_three μ
    (d := fun p => gProg k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (fun p => sdn_nonneg' _ _ _) h1 h2 h3
  have ha := rateHat_arith hn hk
  exact le_trans (by linarith) h

/-! ## The operation count at the widths of the Focus -/

/-- **`cost140_focus`.** For `N = 2n` inputs: the operation count of `preProg`, the `m` oracle
operations `ψ_s`, and `hatProg` with `k` points is at most
`2m² + m(6n + 4) + 12 + k·(5n + 2 + mlpCost n mA n + mlpCost n mF 1)`. -/
theorem cost140_focus (k n m mA mF : ℕ) (hn : 1 ≤ n) :
    (preProg (2 * n) m).cost + m + (hatProg k n m mA mF).cost ≤
      2 * m ^ 2 + m * (6 * n + 4) + 12 +
        k * (5 * n + 2 + mlpCost n mA n + mlpCost n mF 1) := by
  have h1 := costHat_ge k (N := 2 * n) n m mA mF (by omega)
  have h2 := cost140 k (2 * n) n m mA mF
  have e : m * (2 * (2 * n) + 2 * n + 4) = m * (6 * n + 4) := by ring_nf
  rw [e] at h2
  omega

/-- **Against direct sampling.** One direct evaluation of the World network costs
`mlpCost (2n) m n` operations. The two programs with the `m` oracle operations and `k` points
cost at most ONE such evaluation plus `4m + n + 12 + k·(5n + 2 + mlpCost n mA n + mlpCost n mF 1)`.
(A sample mean of `k₀` exact samples costs at least `k₀·mlpCost (2n) m n`.) -/
theorem cost140_vs_sample (k n m mA mF : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (preProg (2 * n) m).cost + m + (hatProg k n m mA mF).cost ≤
      mlpCost (2 * n) m n + (4 * m + n + 12) +
        k * (5 * n + 2 + mlpCost n mA n + mlpCost n mF 1) := by
  have h := cost140_focus k n m mA mF hn
  have e : 2 * m ^ 2 + 6 * (m * n) ≤ mlpCost (2 * n) m n + n := by
    unfold mlpCost
    have a1 : m * (2 * (2 * n) - 1) + m = 4 * (m * n) := by
      have : 2 * (2 * n) - 1 + 1 = 4 * n := by omega
      calc m * (2 * (2 * n) - 1) + m = m * (2 * (2 * n) - 1 + 1) := by ring
        _ = 4 * (m * n) := by rw [this]; ring
    have a2 : m * (2 * m - 1) + m = 2 * m ^ 2 := by
      have : 2 * m - 1 + 1 = 2 * m := by omega
      calc m * (2 * m - 1) + m = m * (2 * m - 1 + 1) := by ring
        _ = 2 * m ^ 2 := by rw [this]; ring
    have a3 : n * (2 * m - 1) + n = 2 * (m * n) := by
      have : 2 * m - 1 + 1 = 2 * m := by omega
      calc n * (2 * m - 1) + n = n * (2 * m - 1 + 1) := by ring
        _ = 2 * (m * n) := by rw [this]; ring
    omega
  have e2 : m * (6 * n + 4) = 6 * (m * n) + 4 * m := by ring
  rw [e2] at h
  omega

end BstLean.Part140

open BstLean.Part140 in
#print axioms gProg_eq
open BstLean.Part140 in
#print axioms preHat_null
open BstLean.Part140 in
#print axioms progSucceeds140
open BstLean.Part140 in
#print axioms cost140_focus
open BstLean.Part140 in
#print axioms cost140_vs_sample
