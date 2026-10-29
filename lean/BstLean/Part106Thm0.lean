import BstLean.Part106Defs

/-!
# Part 106: Theorem 0 of round oaW2 for the Gaussian version of the World polynomial

Paper source: `delegations/answers/oaW2-opus-prover.md`, Section 2 (Theorem 0).

`W : ℝ^N → ℝⁿ` of degree `d`; the coefficients of degree `0` and `1` are fixed (`b0`), the
coefficients `c` of degree `2` to `d` have the Gaussian version of the Bombieri–Weyl distribution
(`W = mixW b0 c`). The program `g` returns `gVal b0 τ φ ω`, the mean of `φ` over `k` independent
samples of the stand-in `ν_W` (noise level `τ = tauOf d σ = √(d−1)·σ`).

* `gVal_second_moment`: `E (g − E_ν φ)² = Var_ν φ / k`.
* `sample_cheb`: Chebyshev for the mean of `k` samples.
* `thm0_general`: except with probability `δ₁ + δ₃` over `(c, ω)`:
  `(E_μ φ − E_ν φ)² ≤ (λ_0/δ₁) Var_ν φ` and `(g − E_ν φ)² ≤ Var_ν φ/(k δ₃)`.
* `thm0_r2_dA3`, `thm0_r2_dA4`: the headlines at `r = 2`, `d_A = 3` and `d_A = 4`, every `d_F`,
  every `n ≥ 4096`, every `k ≥ 834`: `|g − B(W, A, F)| ≤ (1/2)·sd_ν` with probability `≥ 99/100`.
* `lam0_eight`, `lam0_bound8`: the value of `λ_0` at degree `8` and `λ_0 ≤ (1/(14n))(1 + 3/n)`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

variable {N n d : ℕ}

/-! ## `φ = F ∘ A` and its truncation to the unit ball -/

lemma continuous_monoVal {k d : ℕ} (m : MonoIdx k d) :
    Continuous (fun x : Fin k → ℝ => monoVal x m) := by
  simp_rw [monoVal_eq_prod]
  exact continuous_finsetProd _ (fun l _ => (continuous_apply l).pow _)

lemma continuous_bwEval {k q d : ℕ} (b : CoefIdx k q d → ℝ) :
    Continuous (fun x : Fin k → ℝ => bwEval b x) := by
  refine continuous_pi fun a => ?_
  unfold bwEval
  exact continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_monoVal m)

lemma continuous_phiAF {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    Continuous (phiAF A F) := by
  unfold phiAF
  exact (continuous_apply 0).comp ((continuous_bwEval F).comp (continuous_bwEval A))

/-- `F ∘ A` on the closed unit ball, `0` outside. It is bounded and measurable, and it agrees
with `F ∘ A` at every point `y/|y|`. -/
noncomputable def phiT {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  if ∑ i, x i ^ 2 ≤ 1 then phiAF A F x else 0

lemma bm_phiT {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) : BM (phiT A F) := by
  refine ⟨?_, ?_⟩
  · unfold phiT
    refine Measurable.ite ?_ (continuous_phiAF A F).measurable measurable_const
    exact measurableSet_le
      (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2) measurable_const
  · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
      (fun _ => 1))).exists_bound_of_continuousOn (continuous_phiAF A F).continuousOn
    refine ⟨|C|, fun x => ?_⟩
    unfold phiT
    split_ifs with h
    · have hx : x ∈ Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1) := by
        have hi : ∀ i, |x i| ≤ 1 := by
          intro i
          have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
            Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _)
              (Finset.mem_univ i)
          have h2 : x i ^ 2 ≤ 1 := h1.trans h
          exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
        exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
      have := hC x hx
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self C)
    · simp

lemma sphProj_sq_le (y : Fin n → ℝ) : ∑ i, (sphProj y i) ^ 2 ≤ 1 := by
  unfold sphProj
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  set s := ∑ i, y i ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hs0.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [one_div, inv_pow, Real.sq_sqrt hs0, inv_mul_cancel₀ h.ne']

lemma phiT_sphProj {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (y : Fin n → ℝ) : phiT A F (sphProj y) = phiAF A F (sphProj y) :=
  if_pos (sphProj_sq_le y)

lemma muInt_phiT {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (W : CoefIdx N n d → ℝ) :
    ∫ x, phiAF A F x ∂muW W = ∫ x, phiT A F x ∂muW W := by
  unfold muW
  rw [integral_map (measurable_muMap W).aemeasurable
      (continuous_phiAF A F).measurable.aestronglyMeasurable,
    integral_map (measurable_muMap W).aemeasurable (bm_phiT A F).meas.aestronglyMeasurable]
  simp only [phiT_sphProj]

lemma nuVar_phiT {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (b0 : CoefIdx N n d → ℝ) (τ : ℝ) :
    Var[phiAF A F; nuW b0 τ] = Var[phiT A F; nuW b0 τ] := by
  unfold nuW
  rw [variance_map (continuous_phiAF A F).measurable.aemeasurable
      (measurable_nuMap b0 τ).aemeasurable,
    variance_map (bm_phiT A F).meas.aemeasurable (measurable_nuMap b0 τ).aemeasurable]
  congr 1
  funext p
  simp only [Function.comp, phiT_sphProj]

lemma gVal_phiT {dA dF k : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (b0 : CoefIdx N n d → ℝ) (τ : ℝ) (ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ)) :
    gVal b0 τ (phiAF A F) ω = gVal b0 τ (phiT A F) ω := by
  simp only [gVal, standIn, phiT_sphProj]

/-- **What `B` is**: `∫ φ dμ_W = E_u F(A(W(u)/|W(u)|))`, `u` uniform on the unit sphere of
`ℝ^N`. This is `B(W, A, F)` of `MM.md`. -/
theorem B_eq {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (W : CoefIdx N n d → ℝ) :
    ∫ x, phiAF A F x ∂muW W =
      ∫ u, bwEval F (bwEval A (sphProj (bwEval W u))) 0 ∂uniformSphere N := by
  unfold muW
  rw [integral_map (measurable_muMap W).aemeasurable
      (continuous_phiAF A F).measurable.aestronglyMeasurable]
  rfl

/-- **What `sd_ν²` is**: the variance of `F(A(y/|y|))`, `y = W_0 + W_1 u + τ g`, over one block
`(u, g)` of random inputs. -/
theorem sdNu_eq {dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (b0 : CoefIdx N n d → ℝ) (τ : ℝ) :
    Var[phiAF A F; nuW b0 τ] =
      Var[fun p : (Fin N → ℝ) × (Fin n → ℝ) =>
          bwEval F (bwEval A (sphProj (bwEval (mixW b0 0) p.1 + τ • p.2))) 0;
        (uniformSphere N).prod (stdGauss (Fin n))] := by
  unfold nuW
  rw [variance_map (continuous_phiAF A F).measurable.aemeasurable
      (measurable_nuMap b0 τ).aemeasurable]
  rfl

/-! ## A Markov inequality in the strict form -/

/-- For `Y ≥ 0` bounded measurable with `E Y ≤ A` and `δ > 0`: `P(A < δ Y) ≤ δ`. (This form has
no hypothesis `A > 0`.) -/
lemma markov_strict {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (bY : BM Y) (hY0 : ∀ ω, 0 ≤ Y ω) {A δ : ℝ} (hI : ∫ ω, Y ω ∂P ≤ A)
    (hδ : 0 < δ) : P.real {ω | A < δ * Y ω} ≤ δ := by
  have hI0 : 0 ≤ ∫ ω, Y ω ∂P := integral_nonneg hY0
  rcases (hI0.trans hI).eq_or_lt with h0 | hpos
  · have hz : ∫ ω, Y ω ∂P = 0 := le_antisymm (h0 ▸ hI) hI0
    have hae := (integral_eq_zero_iff_of_nonneg hY0 (bY.integrable _)).mp hz
    have hnull : P {ω | A < δ * Y ω} = 0 := by
      refine measure_mono_null ?_ hae
      intro c hc
      simp only [Set.mem_setOf_eq] at hc
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Pi.zero_apply]
      intro hc0
      rw [hc0, mul_zero, ← h0] at hc
      exact lt_irrefl _ hc
    rw [measureReal_def, hnull]
    simpa using hδ.le
  · have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall hY0) (bY.integrable _) (A / δ)
    have hsub : {ω | A < δ * Y ω} ⊆ {ω | A / δ ≤ Y ω} := by
      intro c hc
      simp only [Set.mem_setOf_eq] at hc ⊢
      rw [div_le_iff₀ hδ]
      linarith
    have hle : P.real {ω | A < δ * Y ω} ≤ P.real {ω | A / δ ≤ Y ω} := measureReal_mono hsub
    have h2 : A / δ * P.real {ω | A / δ ≤ Y ω} ≤ A := hm.trans hI
    have h3 : P.real {ω | A / δ ≤ Y ω} ≤ δ := by
      have hAδ : 0 < A / δ := div_pos hpos hδ
      have := (le_div_iff₀' hAδ).mpr h2
      rwa [div_div_cancel₀ hpos.ne'] at this
    exact hle.trans h3

/-! ## The mean of `k` independent samples of the stand-in -/

section sample

variable (hN : 1 ≤ N) (b0 : CoefIdx N n d → ℝ) (τ : ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ)
  {k : ℕ}

lemma measurable_standIn : Measurable (standIn (N := N) b0 τ) := measurable_nuMap b0 τ

lemma measurable_gVal_right (hφ : BM φ) :
    Measurable (fun ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ) => gVal b0 τ φ ω) := by
  unfold gVal
  exact (Finset.measurable_sum _ fun i _ =>
    hφ.meas.comp ((measurable_standIn b0 τ).comp (measurable_pi_apply i))).div_const _

lemma bm_gVal_right (hφ : BM φ) :
    BM (fun ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ) => gVal b0 τ φ ω) := by
  obtain ⟨M, hM⟩ := hφ.bdd
  refine ⟨measurable_gVal_right b0 τ hφ, |M|, fun ω => ?_⟩
  unfold gVal
  rw [abs_div, Nat.abs_cast]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [div_le_iff₀ hk']
    calc |∑ i, φ (standIn b0 τ (ω i))| ≤ ∑ i : Fin k, |φ (standIn b0 τ (ω i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, |M| :=
          Finset.sum_le_sum fun i _ => (hM _).trans (le_abs_self M)
      _ = |M| * k := by simp [mul_comm]

include hN hφ in
/-- **The second moment of the sample mean**: `E (g − E_ν φ)² = Var_ν φ / k`. -/
theorem gVal_second_moment (hk : 1 ≤ k) :
    ∫ ω, (gVal b0 τ φ ω - ∫ x, φ x ∂nuW b0 τ) ^ 2
        ∂(Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n))) =
      Var[φ; nuW b0 τ] / k := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  set ρ : Measure ((Fin N → ℝ) × (Fin n → ℝ)) := (uniformSphere N).prod (stdGauss (Fin n))
    with hρ
  set π : Measure (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) := Measure.pi fun _ : Fin k => ρ with hπ
  set Y : (Fin N → ℝ) × (Fin n → ℝ) → ℝ := fun p => φ (standIn b0 τ p) with hY
  have bY : BM Y := hφ.comp (measurable_standIn b0 τ)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  -- the mean and the variance of one sample
  have hm : ∫ x, φ x ∂nuW b0 τ = ∫ p, Y p ∂ρ := by
    rw [nuW_eq_map, integral_map (measurable_standIn b0 τ).aemeasurable
      hφ.meas.aestronglyMeasurable]
  have hv : Var[φ; nuW b0 τ] = Var[Y; ρ] := by
    rw [nuW_eq_map, variance_map hφ.meas.aemeasurable (measurable_standIn b0 τ).aemeasurable]
    rfl
  have hmap : ∀ i : Fin k, π.map (Function.eval i) = ρ := fun i =>
    (measurePreserving_eval (fun _ : Fin k => ρ) i).map_eq
  -- one coordinate
  have hXint : ∀ i : Fin k, ∫ ω, Y (ω i) ∂π = ∫ p, Y p ∂ρ := by
    intro i
    have := integral_map (μ := π) (φ := Function.eval i) (measurable_pi_apply i).aemeasurable
      (f := Y) (by rw [hmap i]; exact bY.meas.aestronglyMeasurable)
    rw [hmap i] at this
    exact this.symm
  have hXvar : ∀ i : Fin k, Var[fun ω => Y (ω i); π] = Var[Y; ρ] := by
    intro i
    have := variance_map (μ := π) (Y := Function.eval i) (X := Y)
      (by rw [hmap i]; exact bY.meas.aemeasurable) (measurable_pi_apply i).aemeasurable
    rw [hmap i] at this
    exact this.symm
  have hL2 : ∀ i : Fin k, MemLp (fun ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ) => Y (ω i)) 2 π := by
    intro i
    obtain ⟨M, hM⟩ := bY.bdd
    exact MemLp.of_bound (bY.meas.comp (measurable_pi_apply i)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hM _)
  have hind : iIndepFun (fun (i : Fin k) (ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ)) => Y (ω i)) π :=
    iIndepFun_pi (fun _ => bY.meas.aemeasurable)
  -- the sum
  set S : (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) → ℝ := fun ω => ∑ i, Y (ω i) with hS
  have hSfun : S = ∑ i ∈ (Finset.univ : Finset (Fin k)), fun ω => Y (ω i) := by
    funext ω
    simp [hS]
  have hSvar : Var[S; π] = k * Var[Y; ρ] := by
    rw [hSfun, IndepFun.variance_sum (fun i _ => hL2 i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp [hXvar]
  have hSint : ∫ ω, S ω ∂π = k * ∫ p, Y p ∂ρ := by
    simp only [hS]
    rw [integral_finsetSum _ (fun i _ => ((bY.comp (measurable_pi_apply i)).integrable π))]
    simp [hXint]
  have hSm : Measurable S :=
    Finset.measurable_sum _ fun i _ => bY.meas.comp (measurable_pi_apply i)
  have hVe := variance_eq_integral (μ := π) hSm.aemeasurable
  rw [hSint] at hVe
  have e : ∀ ω, (gVal b0 τ φ ω - ∫ x, φ x ∂nuW b0 τ) ^ 2 =
      (1 / (k : ℝ) ^ 2) * (S ω - k * ∫ p, Y p ∂ρ) ^ 2 := by
    intro ω
    rw [hm]
    simp only [gVal, hS, hY]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, ← hVe, hSvar, hv]
  field_simp

include hN hφ in
/-- **Chebyshev for the mean of `k` samples of the stand-in**: for `δ > 0`, the event
`Var_ν φ < k δ (g − E_ν φ)²` has probability at most `δ` over the `k` blocks of random inputs. -/
theorem sample_cheb (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n))).real
      {ω | Var[φ; nuW b0 τ] < k * δ * (gVal b0 τ φ ω - ∫ x, φ x ∂nuW b0 τ) ^ 2} ≤ δ := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have bY : BM (fun ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ) =>
      (gVal b0 τ φ ω - ∫ x, φ x ∂nuW b0 τ) ^ 2) :=
    ((bm_gVal_right b0 τ hφ).sub (BM.const _)).sq
  have h := markov_strict (Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)))
    bY (fun ω => sq_nonneg _) (gVal_second_moment hN b0 τ hφ hk).le hδ
  refine le_trans (measureReal_mono ?_) h
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [div_lt_iff₀ hk']
  linarith

end sample

/-! ## Theorem 0, general form -/

/-- **Theorem 0, general form** (Gaussian version of `W : ℝ^N → ℝⁿ` of degree `d ≥ 2`; fixed
coefficients `b0` of degree `0` and `1`; bounded measurable `φ`; `k ≥ 1` samples; `δ₁, δ₃ > 0`).
Except with probability `δ₁ + δ₃` over the coefficients `c` of degree `2` to `d` and the `k`
blocks of random inputs:
`δ₁ (E_{μ_W} φ − E_ν φ)² ≤ λ_0 Var_ν φ` and `k δ₃ (g − E_ν φ)² ≤ Var_ν φ`. -/
theorem thm0_general (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (b0 : CoefIdx N n d → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) {k : ℕ} (hk : 1 ≤ k) {δ₁ δ₃ : ℝ} (h1 : 0 < δ₁)
    (h3 : 0 < δ₃) :
    1 - (δ₁ + δ₃) ≤
      ((bwGauss N n d σ).prod
        (Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)))).real
        {p | δ₁ * (∫ x, φ x ∂muW (mixW b0 p.1) - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2 ≤
              lam0 N d * Var[φ; nuW b0 (tauOf d σ)] ∧
            k * δ₃ * (gVal b0 (tauOf d σ) φ p.2 - ∫ x, φ x ∂nuW b0 (tauOf d σ)) ^ 2 ≤
              Var[φ; nuW b0 (tauOf d σ)]} := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  set G := bwGauss N n d σ with hG
  set π : Measure (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) :=
    Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)) with hπ
  set τ := tauOf d σ with hτ
  set E1 : Set (CoefIdx N n d → ℝ) := {c | lam0 N d * Var[φ; nuW b0 τ] <
    δ₁ * (∫ x, φ x ∂muW (mixW b0 c) - ∫ x, φ x ∂nuW b0 τ) ^ 2} with hE1
  set E3 : Set (Fin k → (Fin N → ℝ) × (Fin n → ℝ)) :=
    {ω | Var[φ; nuW b0 τ] < k * δ₃ * (gVal b0 τ φ ω - ∫ x, φ x ∂nuW b0 τ) ^ 2} with hE3
  set Good : Set ((CoefIdx N n d → ℝ) × (Fin k → (Fin N → ℝ) × (Fin n → ℝ))) :=
    {p | δ₁ * (∫ x, φ x ∂muW (mixW b0 p.1) - ∫ x, φ x ∂nuW b0 τ) ^ 2 ≤
          lam0 N d * Var[φ; nuW b0 τ] ∧
        k * δ₃ * (gVal b0 τ φ p.2 - ∫ x, φ x ∂nuW b0 τ) ^ 2 ≤ Var[φ; nuW b0 τ]} with hGood
  have hP1 : G.real E1 ≤ δ₁ := thm1_prob hN hd σ b0 hφ h1
  have hP3 : π.real E3 ≤ δ₃ := sample_cheb hN b0 τ hφ hk h3
  have hcov : (Set.univ : Set ((CoefIdx N n d → ℝ) × (Fin k → (Fin N → ℝ) × (Fin n → ℝ)))) ⊆
      Good ∪ (E1 ×ˢ Set.univ ∪ Set.univ ×ˢ E3) := by
    intro p _
    by_cases hp : p ∈ Good
    · exact Or.inl hp
    · right
      simp only [hGood, Set.mem_setOf_eq, not_and_or, not_le] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, hp⟩
  have hu : (G.prod π).real Set.univ ≤
      (G.prod π).real Good + ((G.prod π).real (E1 ×ˢ Set.univ) +
        (G.prod π).real (Set.univ ×ˢ E3)) :=
    (measureReal_mono hcov).trans ((measureReal_union_le _ _).trans
      (add_le_add le_rfl (measureReal_union_le _ _)))
  have e1 : (G.prod π).real (E1 ×ˢ Set.univ) = G.real E1 := by
    simp [measureReal_def, Measure.prod_prod]
  have e3 : (G.prod π).real (Set.univ ×ˢ E3) = π.real E3 := by
    simp [measureReal_def, Measure.prod_prod]
  rw [e1, e3] at hu
  have h1' : (G.prod π).real Set.univ = 1 := by simp
  linarith

/-! ## The numeric step -/

/-- The triangle step: from `δ₁ a² ≤ λ V` and `k δ₃ b² ≤ V`, with `λ/δ₁ ≤ c₁²` and
`1/(k δ₃) ≤ c₃²`: `|b − a| ≤ (c₁ + c₃) √V`. -/
lemma tri_step {a b V lam δ₁ δ₃ κ c₁ c₃ : ℝ} (hV : 0 ≤ V) (h1 : 0 < δ₁) (h3 : 0 < κ * δ₃)
    (hc1 : 0 ≤ c₁) (hc3 : 0 ≤ c₃) (hl : lam ≤ c₁ ^ 2 * δ₁) (hk : 1 ≤ c₃ ^ 2 * (κ * δ₃))
    (ha : δ₁ * a ^ 2 ≤ lam * V) (hb : κ * δ₃ * b ^ 2 ≤ V) :
    |b - a| ≤ (c₁ + c₃) * Real.sqrt V := by
  have ha2 : a ^ 2 ≤ c₁ ^ 2 * V := by
    have : δ₁ * a ^ 2 ≤ δ₁ * (c₁ ^ 2 * V) := by
      calc δ₁ * a ^ 2 ≤ lam * V := ha
        _ ≤ c₁ ^ 2 * δ₁ * V := mul_le_mul_of_nonneg_right hl hV
        _ = δ₁ * (c₁ ^ 2 * V) := by ring
    exact le_of_mul_le_mul_left this h1
  have hb2 : b ^ 2 ≤ c₃ ^ 2 * V := by
    have : κ * δ₃ * b ^ 2 ≤ κ * δ₃ * (c₃ ^ 2 * V) := by
      calc κ * δ₃ * b ^ 2 ≤ V := hb
        _ = 1 * V := (one_mul V).symm
        _ ≤ c₃ ^ 2 * (κ * δ₃) * V := mul_le_mul_of_nonneg_right hk hV
        _ = κ * δ₃ * (c₃ ^ 2 * V) := by ring
    exact le_of_mul_le_mul_left this h3
  have hsq : ∀ {x c : ℝ}, 0 ≤ c → x ^ 2 ≤ c ^ 2 * V → |x| ≤ c * Real.sqrt V := by
    intro x c hc hx
    have := Real.abs_le_sqrt hx
    rwa [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc] at this
  have h := abs_sub b a
  calc |b - a| ≤ |b| + |a| := abs_sub b a
    _ ≤ c₃ * Real.sqrt V + c₁ * Real.sqrt V := add_le_add (hsq hc3 hb2) (hsq hc1 ha2)
    _ = (c₁ + c₃) * Real.sqrt V := by ring

/-- The bound `(1/(10n))(1 + 2/n) ≤ (108/1000)² · (21/10000)` for `n ≥ 4096`. -/
lemma lam_num {n : ℕ} (hn : 4096 ≤ n) :
    1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) ≤ (108 / 1000 : ℝ) ^ 2 * (21 / 10000) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) < n := by linarith
  have h2 : 2 / (n : ℝ) ≤ 2 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
  have h1 : 1 / (10 * (n : ℝ)) ≤ 1 / (10 * 4096) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (10 * (n : ℝ)) := by positivity
  calc 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) ≤ 1 / (10 * 4096) * (1 + 2 / 4096) :=
        mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
    _ ≤ (108 / 1000 : ℝ) ^ 2 * (21 / 10000) := by norm_num

/-! ## `λ_0` at degree `8` (the case `d_A = 4`) -/

/-- The value of `λ_0` at degree `8`. -/
theorem lam0_eight (N : ℕ) (hN : 1 ≤ N) :
    lam0 N 8 = (1 / (N : ℝ) + 3 / ((N : ℝ) * (N + 2)) + 15 / ((N : ℝ) * (N + 2) * (N + 4)) +
      105 / ((N : ℝ) * (N + 2) * (N + 4) * (N + 6))) / 7 := by
  rw [lam0_eq N 8 hN]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hI : Finset.Icc 2 8 = {2, 3, 4, 5, 6, 7, 8} := by decide
  rw [hI]
  simp only [sphMom, BstLean.Part29.gaussMom, BstLean.Part36.rhoD]
  norm_num [Finset.prod_range_succ, Nat.doubleFactorial, Nat.even_iff]
  ring

/-- `λ_0 ≤ (1/(14n))(1 + 3/n)` at `r = 2`, `d = 8`, every `n ≥ 1`. (With `2/n` in place of
`3/n` the inequality is false at `n = 2`.) -/
theorem lam0_bound8 (n : ℕ) (hn : 1 ≤ n) :
    lam0 (2 * n) 8 ≤ 1 / (14 * (n : ℝ)) * (1 + 3 / (n : ℝ)) := by
  rw [lam0_eight (2 * n) (by omega)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0 : ℝ) < n := by linarith
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  rw [show 1 / (14 * (n : ℝ)) * (1 + 3 / (n : ℝ)) * 7 = (n + 3) / (2 * (n : ℝ) ^ 2) by
    field_simp; norm_num]
  rw [show 1 / (2 * (n : ℝ)) + 3 / (2 * (n : ℝ) * (2 * n + 2)) +
      15 / (2 * (n : ℝ) * (2 * n + 2) * (2 * n + 4)) +
      105 / (2 * (n : ℝ) * (2 * n + 2) * (2 * n + 4) * (2 * n + 6)) =
      (8 * ((n : ℝ) + 1) * (n + 2) * (n + 3) + 12 * ((n : ℝ) + 2) * (n + 3) +
        30 * ((n : ℝ) + 3) + 105) / (16 * n * (n + 1) * (n + 2) * (n + 3)) by
    field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h1 h1, mul_pos (mul_pos h1 h1) h1, mul_pos (mul_pos h1 h1) (mul_pos h1 h1),
    mul_pos (mul_pos (mul_pos h1 h1) (mul_pos h1 h1)) h1]

lemma tauOf_eight (σ : ℝ) : tauOf 8 σ = Real.sqrt 7 * σ := by
  unfold tauOf
  norm_num

/-- The bound `(1/(14n))(1 + 3/n) ≤ (108/1000)² · (21/10000)` for `n ≥ 4096`. -/
lemma lam_num8 {n : ℕ} (hn : 4096 ≤ n) :
    1 / (14 * (n : ℝ)) * (1 + 3 / (n : ℝ)) ≤ (108 / 1000 : ℝ) ^ 2 * (21 / 10000) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) < n := by linarith
  have h2 : 3 / (n : ℝ) ≤ 3 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
  have h1 : 1 / (14 * (n : ℝ)) ≤ 1 / (14 * 4096) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  calc 1 / (14 * (n : ℝ)) * (1 + 3 / (n : ℝ)) ≤ 1 / (14 * 4096) * (1 + 3 / 4096) :=
        mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
    _ ≤ (108 / 1000 : ℝ) ^ 2 * (21 / 10000) := by norm_num

/-! ## The headlines -/

/-- **Theorem 0, core form.** Gaussian version of `W : ℝ^N → ℝⁿ` of degree `d ≥ 2` with
`λ_0 ≤ (108/1000)²·(21/10000)`; every fixed `b0`, `A`, `F`; `k ≥ 834` samples. With probability
at least `99/100` over the coefficients of degree `2` to `d` of `W` and the random inputs of the
program: `|g − B(W, A, F)| ≤ (1/2)·sd_ν`. -/
theorem thm0_core (hN : 1 ≤ N) (hd : 2 ≤ d) (σ : ℝ) (b0 : CoefIdx N n d → ℝ) {dA dF k : ℕ}
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) (hk : 834 ≤ k)
    (hlam : lam0 N d ≤ (108 / 1000 : ℝ) ^ 2 * (21 / 10000)) :
    99 / 100 ≤
      ((bwGauss N n d σ).prod
        (Measure.pi fun _ : Fin k => (uniformSphere N).prod (stdGauss (Fin n)))).real
        {p | |gVal b0 (tauOf d σ) (phiAF A F) p.2 - ∫ x, phiAF A F x ∂muW (mixW b0 p.1)| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW b0 (tauOf d σ)])} := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have hk1 : 1 ≤ k := by omega
  have hk' : (834 : ℝ) ≤ k := by exact_mod_cast hk
  have h := thm0_general hN hd σ b0 (bm_phiT A F) hk1 (δ₁ := 21 / 10000) (δ₃ := 79 / 10000)
    (by norm_num) (by norm_num)
  refine le_trans (by norm_num) (h.trans (measureReal_mono ?_))
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [gVal_phiT, muInt_phiT, nuVar_phiT]
  set V := Var[phiT A F; nuW b0 (tauOf d σ)] with hV
  have hV0 : 0 ≤ V := variance_nonneg _ _
  have ht := tri_step (c₁ := 108 / 1000) (c₃ := 39 / 100) hV0 (by norm_num : (0 : ℝ) < 21 / 10000)
    (by positivity : (0 : ℝ) < (k : ℝ) * (79 / 10000)) (by norm_num) (by norm_num) hlam
    (by nlinarith) hp.1 hp.2
  have e : gVal b0 (tauOf d σ) (phiT A F) p.2 - ∫ x, phiT A F x ∂muW (mixW b0 p.1) =
      (gVal b0 (tauOf d σ) (phiT A F) p.2 - ∫ x, phiT A F x ∂nuW b0 (tauOf d σ)) -
        (∫ x, phiT A F x ∂muW (mixW b0 p.1) - ∫ x, phiT A F x ∂nuW b0 (tauOf d σ)) := by ring
  rw [e]
  refine ht.trans ?_
  have := Real.sqrt_nonneg V
  nlinarith

/-- **Theorem 0 at `r = 2`, `d_A = 3`** (`W : ℝ^{2n} → ℝⁿ` of degree `6`, Gaussian version with
parameter `σ`; every `d_F`). For every `n ≥ 4096`, every `k ≥ 834`, every fixed coefficients `b0`
of degree `0` and `1` of `W`, every `A` and `F`: with probability at least `99/100` over the
coefficients of degree `2` to `6` of `W` and the `k` blocks of random inputs of the program `g`,
`|g − B(W, A, F)| ≤ (1/2)·sd_ν`, with `sd_ν² = Var_{ν_W}(F ∘ A)` and noise level `τ = √5·σ`. -/
theorem thm0_r2_dA3 (n k dF : ℕ) (hn : 4096 ≤ n) (hk : 834 ≤ k) (σ : ℝ)
    (b0 : CoefIdx (2 * n) n 6 → ℝ) (A : CoefIdx n n 3 → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    99 / 100 ≤
      ((bwGauss (2 * n) n 6 σ).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |gVal b0 (Real.sqrt 5 * σ) (phiAF A F) p.2 -
              ∫ x, phiAF A F x ∂muW (mixW b0 p.1)| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW b0 (Real.sqrt 5 * σ)])} := by
  have h := thm0_core (N := 2 * n) (d := 6) (by omega) (by norm_num) σ b0 A F hk
    ((lam0_bound n (by omega)).trans (lam_num hn))
  rwa [tauOf_six] at h

/-- **Theorem 0 at `r = 2`, `d_A = 4`** (`W : ℝ^{2n} → ℝⁿ` of degree `8`; noise level
`τ = √7·σ`). The statement is that of `thm0_r2_dA3`. -/
theorem thm0_r2_dA4 (n k dF : ℕ) (hn : 4096 ≤ n) (hk : 834 ≤ k) (σ : ℝ)
    (b0 : CoefIdx (2 * n) n 8 → ℝ) (A : CoefIdx n n 4 → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    99 / 100 ≤
      ((bwGauss (2 * n) n 8 σ).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |gVal b0 (Real.sqrt 7 * σ) (phiAF A F) p.2 -
              ∫ x, phiAF A F x ∂muW (mixW b0 p.1)| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW b0 (Real.sqrt 7 * σ)])} := by
  have h := thm0_core (N := 2 * n) (d := 8) (by omega) (by norm_num) σ b0 A F hk
    ((lam0_bound8 n (by omega)).trans (lam_num8 hn))
  rwa [tauOf_eight] at h

end BstLean.Part106

#print axioms BstLean.Part106.B_eq
#print axioms BstLean.Part106.sdNu_eq
#print axioms BstLean.Part106.gVal_second_moment
#print axioms BstLean.Part106.sample_cheb
#print axioms BstLean.Part106.thm0_general
#print axioms BstLean.Part106.lam0_eight
#print axioms BstLean.Part106.lam0_bound8
#print axioms BstLean.Part106.thm0_core
#print axioms BstLean.Part106.thm0_r2_dA3
#print axioms BstLean.Part106.thm0_r2_dA4
