import BstLean.Part157Gp

/-!
# Part 157, items 3 and 4: the two means over the residual matrices (Fubini and regression)

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-02-world.tex`, the paragraph after Lemma `t7:p02:regression`
("Fubini and regression give `E_{G_W}(p | Θ_W, ĉ, f) = q_W`"); `theorem7-03-composition.tex`,
"Two-stage composition" ("Fubini and regression give the retained-data value `Q = …`").

* `frame_mean`: `E_M μ{x | (x, M r(x)) ∈ S} = (μ ⊗ γ){(x, γ) | (x, √v·|r(x)|·γ) ∈ S}`.
* `nuW D c`: the distribution `ν` of `sphPt (λ_W(u)·ĉ + σ_W(u)·γ)`; `nuStand D c`: the stand-in
  input distribution `ν'` of `sphPt (ĉ + τ₀ ξ)`.
* `mean_pRes`: `E_{ω_W} p = ν{x | c(A(x))}`; `PStand_eq_nu`: `P = ν'{x | c(A(x))}`.
* `REPLW_test_hyp`: the World replacement, uniform over all measurable test sets (no residual
  matrix occurs); `replw_of_test`: it gives `REPL_W_hyp`.
* `QStand D t c`: the retained-data value `Q`; `mean_PStand`: `E_{ω_A} P = Q`.
* `REPLA_mix_hyp`: the Agent replacement with `Q` (no residual matrix occurs);
  `repla_of_mix`: it gives `REPL_A_hyp`.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part156

/-- **Fubini and the Gaussian residual.** `μ` a probability measure on the inputs, `r` a
measurable field of vectors, `M` a Gaussian matrix with entry variance `v`, `S` a measurable set:
`E_M μ{x | (x, M r(x)) ∈ S} = (μ ⊗ γ){(x, γ) | (x, (√v·|r(x)|)·γ) ∈ S}`, `γ` standard
Gaussian. -/
theorem frame_mean {N q m : ℕ} (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ] (v : ℝ)
    {r : (Fin N → ℝ) → Fin m → ℝ} (hr : Measurable r)
    {S : Set ((Fin N → ℝ) × (Fin q → ℝ))} (hS : MeasurableSet S) :
    ∫ M, μ.real {x | (x, M.mulVec (r x)) ∈ S} ∂gaussMat q m v =
      (μ.prod (stdGauss (Fin q))).real {p | (p.1, (√v * √(normSq (r p.1))) • p.2) ∈ S} := by
  set f : (Fin N → ℝ) × (Fin q → ℝ) → ℝ := S.indicator 1 with hf
  have mf : Measurable f := measurable_one.indicator hS
  have bf : ∀ y, ‖f y‖ ≤ 1 := by
    intro y
    by_cases h : y ∈ S
    · simp [hf, h]
    · simp [hf, h]
  -- the left side as a double integral
  have mJ : Measurable (fun z : Matrix (Fin q) (Fin m) ℝ × (Fin N → ℝ) =>
      (z.2, z.1.mulVec (r z.2))) :=
    measurable_snd.prodMk (measurable_mulVec_joint.comp
      (measurable_fst.prodMk (hr.comp measurable_snd)))
  have e1 : ∀ M : Matrix (Fin q) (Fin m) ℝ,
      μ.real {x | (x, M.mulVec (r x)) ∈ S} = ∫ x, f (x, M.mulVec (r x)) ∂μ := by
    intro M
    have hs : MeasurableSet {x : Fin N → ℝ | (x, M.mulVec (r x)) ∈ S} :=
      (mJ.comp measurable_prodMk_left) hS
    rw [← integral_indicator_one hs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases h : (x, M.mulVec (r x)) ∈ S
    · have h' : x ∈ {x : Fin N → ℝ | (x, M.mulVec (r x)) ∈ S} := h
      simp [hf, h, h']
    · have h' : x ∉ {x : Fin N → ℝ | (x, M.mulVec (r x)) ∈ S} := h
      simp [hf, h, h']
  simp_rw [e1]
  have hint : Integrable (fun z : Matrix (Fin q) (Fin m) ℝ × (Fin N → ℝ) =>
      f (z.2, z.1.mulVec (r z.2))) ((gaussMat q m v).prod μ) :=
    Integrable.of_bound (mf.comp mJ).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => bf _)
  rw [integral_integral_swap
    (f := fun (M : Matrix (Fin q) (Fin m) ℝ) (x : Fin N → ℝ) => f (x, M.mulVec (r x))) hint]
  -- the right side as a double integral
  have mK : Measurable (fun p : (Fin N → ℝ) × (Fin q → ℝ) =>
      (p.1, (√v * √(normSq (r p.1))) • p.2)) :=
    measurable_fst.prodMk
      ((measurable_const.mul ((measurable_normSq.comp (hr.comp measurable_fst)).sqrt)).smul
        measurable_snd)
  have hs2 : MeasurableSet {p : (Fin N → ℝ) × (Fin q → ℝ) |
      (p.1, (√v * √(normSq (r p.1))) • p.2) ∈ S} := mK hS
  have e2 : (μ.prod (stdGauss (Fin q))).real
      {p | (p.1, (√v * √(normSq (r p.1))) • p.2) ∈ S} =
      ∫ p, f (p.1, (√v * √(normSq (r p.1))) • p.2) ∂(μ.prod (stdGauss (Fin q))) := by
    rw [← integral_indicator_one hs2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    by_cases h : (p.1, (√v * √(normSq (r p.1))) • p.2) ∈ S
    · have h' : p ∈ {p : (Fin N → ℝ) × (Fin q → ℝ) |
          (p.1, (√v * √(normSq (r p.1))) • p.2) ∈ S} := h
      simp [hf, h, h']
    · have h' : p ∉ {p : (Fin N → ℝ) × (Fin q → ℝ) |
          (p.1, (√v * √(normSq (r p.1))) • p.2) ∈ S} := h
      simp [hf, h, h']
  have hint2 : Integrable (fun p : (Fin N → ℝ) × (Fin q → ℝ) =>
      f (p.1, (√v * √(normSq (r p.1))) • p.2)) (μ.prod (stdGauss (Fin q))) :=
    Integrable.of_bound (mf.comp mK).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => bf _)
  rw [e2, integral_prod _ hint2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact layer_transfer v (r x) (g := fun y => f (x, y)) (mf.comp measurable_prodMk_left)

variable {n : ℕ}

/-! ## The World stage -/

/-- The map `(u, γ) ↦ sphPt (λ_W(u)·ĉ + σ_W(u)·γ)`. -/
noncomputable def nuWmap (D : Centres n) (c : Ret n) (p : (Fin (2 * n) → ℝ) × (Fin n → ℝ)) :
    Fin n → ℝ :=
  sphPt (lam (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 p.1) • c.1.2 +
    sig (2 / (mW n : ℝ)) (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 p.1) • p.2)

/-- **The distribution `ν`** of `sphPt (λ_W(u)·ĉ + σ_W(u)·γ)`: `u` uniform on the unit sphere of
`ℝ^{2n}`, `γ` an independent standard Gaussian vector of `ℝⁿ`,
`λ_W(u) = ⟨a₂^W(u), b_W⟩/|b_W|²`, `σ_W(u) = √(2/m_W)·|r_W(u)|`. -/
noncomputable def nuW (D : Centres n) (c : Ret n) : Measure (Fin n → ℝ) :=
  ((uniformSphere (2 * n)).prod (stdGauss (Fin n))).map (nuWmap D c)

/-- **The stand-in input distribution `ν'`**: the distribution of `sphPt (ĉ + τ₀ ξ)`. -/
noncomputable def nuStand (D : Design n) (c : Ret n) : Measure (Fin n → ℝ) :=
  (stdGauss (Fin n)).map (fun ξ => sphPt (c.1.2 + D.tau0 c • ξ))

lemma measurable_nuWmap (D : Centres n) (c : Ret n) : Measurable (nuWmap D c) := by
  have hh : Measurable (fun p : (Fin (2 * n) → ℝ) × (Fin n → ℝ) => hid2 c.1.1.1 c.1.1.2 p.1) :=
    (continuous_hid2 c.1.1.1 c.1.1.2).measurable.comp measurable_fst
  exact measurable_sphPt.comp
    ((((measurable_lam (D.bW c.1.1)).comp hh).smul_const c.1.2).add
      (((measurable_sig _ (D.bW c.1.1)).comp hh).smul measurable_snd))

lemma measurableSet_test (F : MlpParam n (mF n) 1) (t : ℝ) (A : MlpParam n (mA n) n) :
    MeasurableSet {x : Fin n → ℝ | classifier F t (mlpEval A x)} :=
  measurableSet_lt measurable_const ((measurable_pi_apply 0).comp
    ((continuous_mlpEval F).measurable.comp (continuous_mlpEval A).measurable))

/-- **The mean of the target over the residual of `W₃`**: `E_{ω_W} p = ν{x | c(A(x))}`. -/
theorem mean_pRes (hn : 1 ≤ n) (D : Centres n) (t : ℝ) (c : Ret n) (ωA : ResA n) :
    ∫ ωW, pRes D t c (ωW, ωA) ∂resW n =
      (nuW D c).real {x | classifier c.2.2 t (mlpEval (agentOf D c ωA) x)} := by
  have hprob := BstLean.Part29.uniformSphere_isProbability (2 * n) (by omega)
  have e : ∀ ωW : ResW n, pRes D t c (ωW, ωA) = (uniformSphere (2 * n)).real
        {u | (u, ωW.mulVec (res (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u))) ∈
          setW D t c (agentOf D c ωA)} := fun ωW => pRes_eq_frame D t c (ωW, ωA)
  simp only [e]
  have hr : Measurable (fun u : Fin (2 * n) → ℝ => res (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u)) :=
    (measurable_res _).comp (continuous_hid2 c.1.1.1 c.1.1.2).measurable
  have h1 := frame_mean (uniformSphere (2 * n)) (2 / (mW n : ℝ)) hr
    (measurableSet_setW D t c (agentOf D c ωA))
  unfold resW
  rw [h1]
  unfold nuW
  rw [map_measureReal_apply (measurable_nuWmap D c) (measurableSet_test c.2.2 t _)]
  rfl

/-- **The stand-in probability is a probability under `ν'`**: `P = ν'{x | c(A(x))}`. -/
theorem PStand_eq_nu (D : Design n) (t : ℝ) (c : Ret n) (ωA : ResA n) :
    PStand D t c ωA =
      (nuStand D c).real {x | classifier c.2.2 t (mlpEval (agentOf D.toCentres c ωA) x)} := by
  have hm : Measurable (fun ξ : Fin n → ℝ => sphPt (c.1.2 + D.tau0 c • ξ)) :=
    measurable_sphPt.comp (measurable_const.add (measurable_const_smul (D.tau0 c)))
  unfold nuStand
  rw [map_measureReal_apply hm (measurableSet_test c.2.2 t _)]
  rfl

/-- **(REPL-W) in the form of the paper: uniform over all tests.** For every retained value `c`
in `E` and every measurable set `T` of `ℝⁿ`: `|√(ν(T)) − √(ν'(T))| ≤ h_W`. A statement about the
retained World data only (no residual matrix, no Agent network, no `F`).

Paper statement that proves it: `theorem7-02-world.tex`, Lemma `t7:p02:replacement`, formula
`t7:p02:replacement-conclusions` (on the event `K_W(h_W) = H_W ∩ {H̄_W ≤ h_W}`). -/
def REPLW_test_hyp (D : Design n) (hW : ℝ) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, ∀ T : Set (Fin n → ℝ), MeasurableSet T →
    |√((nuW D.toCentres c).real T) - √((nuStand D c).real T)| ≤ hW

/-- The uniform World replacement gives `REPL_W_hyp`. -/
theorem replw_of_test (hn : 1 ≤ n) (D : Design n) (t : ℝ) {hW : ℝ} {E : Set (Ret n)}
    (h : REPLW_test_hyp D hW E) : REPL_W_hyp D t hW E := by
  intro c hc ωA
  rw [mean_pRes hn D.toCentres t c ωA, PStand_eq_nu D t c ωA]
  exact h c hc _ (measurableSet_test c.2.2 t _)

/-! ## The Agent stage -/

/-- **The retained-data value `Q`**: the probability, over the stand-in input `x = sphPt (ĉ + τ₀ ξ)`
and an independent standard Gaussian vector `η`, that `F(λ(x)·c_A + σ(x)·η) > t`, with
`λ(x) = ⟨a₂(x), b⟩/|b|²` and `σ(x) = √(2/m_A)·|r(x)|`. -/
noncomputable def QStand (D : Design n) (t : ℝ) (c : Ret n) : ℝ :=
  ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
    {p | classifier c.2.2 t (lam (D.bA c.1 c.2.1.1) (hStand D c p.1) • c.2.1.2 +
      sig (2 / (mA n : ℝ)) (D.bA c.1 c.2.1.1) (hStand D c p.1) • p.2)}

/-- **The mean of the stand-in probability over the residual of `A₃`**: `E_{ω_A} P = Q`. -/
theorem mean_PStand (D : Design n) (t : ℝ) (c : Ret n) :
    ∫ ωA, PStand D t c ωA ∂resA n = QStand D t c := by
  have e : ∀ ωA : ResA n, PStand D t c ωA = (stdGauss (Fin n)).real
        {ξ | (ξ, ωA.mulVec (res (D.bA c.1 c.2.1.1) (hStand D c ξ))) ∈ setA D t c} :=
    fun ωA => PStand_eq_frame D t c ωA
  simp only [e]
  have hr : Measurable (fun ξ : Fin n → ℝ => res (D.bA c.1 c.2.1.1) (hStand D c ξ)) :=
    (measurable_res _).comp (measurable_hStand D c)
  have h1 := frame_mean (stdGauss (Fin n)) (2 / (mA n : ℝ)) hr (measurableSet_setA D t c)
  unfold resA
  rw [h1]
  rfl

/-- **(REPL-A) with the retained-data value `Q`.** For every retained value `c` in `E`:
`|√Q − √q̃| ≤ h_A`. No residual matrix occurs.

Paper statement that proves it: `theorem7-09-assembly.tex`, Lemma `t7:p09:bias-junction`,
formula `t7:p09:root` (Parts 04 to 08). -/
def REPLA_mix_hyp (D : Design n) (t hA : ℝ) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, |√(QStand D t c) - √(qTilde D t c)| ≤ hA

theorem repla_of_mix (D : Design n) (t : ℝ) {hA : ℝ} {E : Set (Ret n)}
    (h : REPLA_mix_hyp D t hA E) : REPL_A_hyp D t hA E := by
  intro c hc
  rw [mean_PStand D t c]
  exact h c hc

/-! ## The second form of the conditional theorem -/

/-- **The conditional classifier theorem for the actual networks, with hypotheses on the retained
data only (every `n ≥ 16 384`).** IF the Gaussian frame inequality `GaussFrameMGF` (no network)
holds, and there are retained-data events with the charges of the ledger (`EVENTS_hyp`) such that
on `H ∩ {Hbar ≤ h_W} ∩ E₁`: the World frame bound `c_W/n` (`FRAME_W_hyp`), the Agent frame bound
`c_frame/n` (`FRAME_A_hyp`), the uniform World replacement (`REPLW_test_hyp`) and the Agent
replacement (`REPLA_mix_hyp`) hold, THEN the program succeeds with probability at least
`99/100`. -/
theorem classifier_networks_conditional_frame (hn : 16384 ≤ n) (hG : GaussFrameMGF)
    (D : Design n) (t : ℝ) {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhidL vWL δextraL)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ Hbar hWL))
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet H E₁ Hbar hWL))
    (hRW : REPLW_test_hyp D hWL (goodSet H E₁ Hbar hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ Hbar hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hLW : 0 < cWL / (n : ℝ) := div_pos (by unfold cWL; norm_num) hnpos
  have hLA : 0 < cfL / (n : ℝ) := div_pos (by unfold cfL; norm_num) hnpos
  exact classifier_networks_conditional_ge_success hn D t hEv
    (gpw_of_frame hn1 hG D.toCentres t hLW hFW) (gpa_of_frame hn1 hG D t hLA hFA)
    (replw_of_test hn1 D t hRW) (repla_of_mix D t hRA)

end BstLean.Part157

open BstLean.Part157 in
#print axioms frame_mean
open BstLean.Part157 in
#print axioms mean_pRes
open BstLean.Part157 in
#print axioms mean_PStand
open BstLean.Part157 in
#print axioms classifier_networks_conditional_frame
