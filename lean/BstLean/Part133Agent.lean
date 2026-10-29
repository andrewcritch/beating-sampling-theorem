import BstLean.Part133Relu

/-!
# Part 133: the `L²` bounds of the three kernels over `(A, A′, F)`, for fixed unit inputs

Role: `delegations/statements/p133-spec.md`, item 3. Paper source: `onW4c-cx.md` §4 (links `F`,
`A_3`, `A_2`, `A_1`; the cross term; `e_V`).

For unit vectors `x, x′` and the kernel `k = (2/m_F)⟨H_A(x), H_{A′}(x′)⟩`, with `S = 4/n`:

* `kern_same_L2_of`: `‖k_{A,A}(x, x′) − S·κ^{∘4}(⟨x, x′⟩)‖₂ ≤ S·(cF·(1+5/m_A)√(1+2/n) + cAg)` from a
  bound `cF` of the link `F` and a bound `cAg` of the links of `A`.
* `kern_cross_L2_of`: `‖k_{A,A′}(x, x′) − S·κ(κ(0))‖₂ ≤ S·(cF + 1/√n + κ(κ(0))·2√δ)` for independent
  `A`, `A′`, from `cF` and a deficit `δ` of `E|A(x)|` below `√2`.
* `kern_diag_L2`: `‖k_{A,A}(x, x) − S‖₂ ≤ S·eV`, `eV² = (1+5/m_F)²(1+5/m_A)²(1+2/n) − 1` (exact).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

/-! ## More `L²` tools -/

section Kit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ} {a : ℝ}

lemma L2le.congr_ae (h : L2le μ f a) (hfg : f =ᵐ[μ] g) : L2le μ g a := by
  have h2 : (fun ω => f ω ^ 2) =ᵐ[μ] fun ω => g ω ^ 2 := hfg.fun_comp (· ^ 2)
  refine ⟨h.1.congr hfg, h.2.1.congr h2, ?_⟩
  rw [← integral_congr_ae h2]
  exact h.2.2

lemma L2le.of_abs_le_ae (hf : AEStronglyMeasurable f μ) (hg : L2le μ g a)
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ |g ω|) : L2le μ f a := by
  have h2 : ∀ᵐ ω ∂μ, f ω ^ 2 ≤ g ω ^ 2 := h.mono fun ω hω => by
    rw [← sq_abs (f ω), ← sq_abs (g ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hi : Integrable (fun ω => f ω ^ 2) μ := by
    refine Integrable.mono' hg.int_sq (hf.pow 2) (h2.mono fun ω hω => ?_)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ⟨hf, hi, (integral_mono_ae hi hg.int_sq h2).trans hg.le⟩

lemma L2le.of_comp_map {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {φ : Ω' → Ω}
    {f : Ω → ℝ} (hφ : Measurable φ) (hf : AEStronglyMeasurable f (P.map φ))
    (h : L2le P (fun ω => f (φ ω)) a) : L2le (P.map φ) f a := by
  refine ⟨hf, (integrable_map_measure (hf.pow 2) hφ.aemeasurable).2 h.2.1, ?_⟩
  have := integral_map hφ.aemeasurable (f := fun ω => f ω ^ 2) (hf.pow 2)
  rw [this]
  exact h.2.2

end Kit

/-! ## Pointwise tools -/

lemma sqrt_ge_quad {x : ℝ} (hx : 0 ≤ x) : 1 + (x - 1) / 2 - (x - 1) ^ 2 / 2 ≤ √x := by
  set s := √x with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hsx : x = s ^ 2 := (Real.sq_sqrt hx).symm
  rw [hsx]
  have e : s - (1 + (s ^ 2 - 1) / 2 - (s ^ 2 - 1) ^ 2 / 2) = (s - 1) ^ 2 * (s ^ 2 + 2 * s) / 2 := by
    ring
  have : 0 ≤ (s - 1) ^ 2 * (s ^ 2 + 2 * s) / 2 := by positivity
  linarith

lemma psi_sub_const_abs {ι : Type*} [Fintype ι] {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) :
    |psi G y y' - G 0 * (nrm y * nrm y')| ≤ |dotp y y'| := by
  have ht := cosv_mem y y'
  have hp := nrm_mul_nonneg y y'
  have hl : |G (cosv y y') - G 0| ≤ |cosv y y'| := by
    rcases le_total 0 (cosv y y') with h | h
    · have h1 := hG.lip (t := 0) (s := cosv y y') (by norm_num) h ht.2
      have h2 := hG.mono KGood.zero_mem ht h
      rw [abs_of_nonneg (by linarith), abs_of_nonneg h]
      linarith
    · have h1 := hG.lip (t := cosv y y') (s := 0) ht.1 h (by norm_num)
      have h2 := hG.mono ht KGood.zero_mem h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos h]
      linarith
  have e : psi G y y' - G 0 * (nrm y * nrm y') = nrm y * nrm y' * (G (cosv y y') - G 0) := by
    unfold psi; ring
  rw [e, dotp_eq_cosv_mul, abs_mul (nrm y * nrm y'), abs_mul (cosv y y'), abs_of_nonneg hp,
    mul_comm]
  exact mul_le_mul_of_nonneg_right hl hp

variable {n mA mF : ℕ}

lemma kappa2_zero_pos : 0 < kappa (kappa 0) := by
  have h0 : (0 : ℝ) < kappa 0 := by rw [kappa_zero]; positivity
  have h1 : kappa 0 ≤ 1 := (kappa_mem (by norm_num) (by norm_num)).2
  have := kGood_kappa.self_le (t := kappa 0) ⟨by linarith, h1⟩
  linarith

/-! ## The constants -/

/-- The exact relative standard deviation of the diagonal kernel. -/
noncomputable def eV (n mA mF : ℕ) : ℝ :=
  √((1 + 5 / (mF : ℝ)) ^ 2 * (1 + 5 / (mA : ℝ)) ^ 2 * (1 + 2 / (n : ℝ)) - 1)

/-! ## Norm factors -/

/-- `‖|A(z)|·|A(z′)|‖₂ ≤ (2q/k)·(1 + 5/m)·√(1 + 2/q)` for unit `z, z′`. -/
lemma mlp_nrm_pair_L2 {k m q : ℕ} (hm : 1 ≤ m) {z z' : Fin k → ℝ} (hz : normSq z = 1)
    (hz' : normSq z' = 1) :
    L2le (mlpGauss k m q) (fun θ : MlpParam k m q => nrm (mlpEval θ z) * nrm (mlpEval θ z'))
      (2 * (q : ℝ) / k * ((1 + 5 / (m : ℝ)) * √(1 + 2 / (q : ℝ)))) := by
  have i4 := mlp_normSq_sq_integrable (m := m) (q := q) z
  have i4' := mlp_normSq_sq_integrable (m := m) (q := q) z'
  have e4 := mlp_fourth_moment (q := q) hm z
  have e4' := mlp_fourth_moment (q := q) hm z'
  have hmeas : Measurable (fun θ : MlpParam k m q => nrm (mlpEval θ z) * nrm (mlpEval θ z')) :=
    (continuous_nrm.measurable.comp (measurable_mlpEval_param z)).mul
      (continuous_nrm.measurable.comp (measurable_mlpEval_param z'))
  refine L2le.of_sq_le (G := fun θ : MlpParam k m q =>
    (normSq (mlpEval θ z) ^ 2 + normSq (mlpEval θ z') ^ 2) / 2) hmeas.aestronglyMeasurable
    ((i4.add i4').div_const 2) (fun θ => ?_) ?_
  · have e : (nrm (mlpEval θ z) * nrm (mlpEval θ z')) ^ 2 =
        normSq (mlpEval θ z) * normSq (mlpEval θ z') := by
      rw [mul_pow, nrm_sq, nrm_sq]
    rw [e]
    nlinarith [sq_nonneg (normSq (mlpEval θ z) - normSq (mlpEval θ z'))]
  · rw [integral_div, integral_add i4 i4', e4, e4', hz, hz']
    have hq0 : (0 : ℝ) ≤ 1 + 2 / (q : ℝ) := by positivity
    have hs := Real.sq_sqrt hq0
    have hs2 : ((1 + 5 / (m : ℝ)) * √(1 + 2 / (q : ℝ))) ^ 2 =
        (1 + 5 / (m : ℝ)) ^ 2 * (1 + 2 / (q : ℝ)) := by rw [mul_pow, hs]
    have hs3 : (2 * (q : ℝ) / k * ((1 + 5 / (m : ℝ)) * √(1 + 2 / (q : ℝ)))) ^ 2 =
        (2 * (q : ℝ) / k) ^ 2 * ((1 + 5 / (m : ℝ)) ^ 2 * (1 + 2 / (q : ℝ))) := by
      rw [mul_pow, hs2]
    apply le_of_eq
    rw [hs3]
    ring

/-- `‖|A(z)|‖₂ = √2`-type bound: `E|N(z)|² = (2q/k)|z|²`. -/
lemma mlp_nrm_L2 {k m q : ℕ} (hm : 1 ≤ m) (z : Fin k → ℝ) :
    L2le (mlpGauss k m q) (fun θ : MlpParam k m q => nrm (mlpEval θ z))
      (√(2 * (q : ℝ) / k * normSq z)) := by
  have hmeas : Measurable (fun θ : MlpParam k m q => nrm (mlpEval θ z)) :=
    continuous_nrm.measurable.comp (measurable_mlpEval_param z)
  refine L2le.of_sq_le (G := fun θ : MlpParam k m q => normSq (mlpEval θ z))
    hmeas.aestronglyMeasurable (mlp_normSq_integrable z) (fun θ => (nrm_sq _).le) ?_
  rw [mlp_second_moment hm z, Real.sq_sqrt (by have := normSq_nonneg z; positivity)]

/-! ## The same-`A` kernel -/

lemma iter4_eq (t : ℝ) : ((kappa ∘ kappa) ∘ kappa ∘ kappa) t = kappa^[4] t := rfl

/-- **The same-`A` kernel**, from a bound `cF` of the link `F` and a bound `cAg` of the links of
`A`: for unit `x, x′`,
`‖(2/m_F)⟨H_A(x), H_A(x′)⟩ − (4/n)·κ^{∘4}(⟨x, x′⟩)‖_{L²(A, A′, F)} ≤ (4/n)·(cF·(1+5/m_A)√(1+2/n) + cAg)`.
-/
theorem kern_same_L2_of (hn : 1 ≤ n) (hmA : 1 ≤ mA) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {cF cAg : ℝ} (hcF : 0 < cF) (hcA : 0 < cAg)
    (hKF : ∀ y y' : Fin n → ℝ, L2le (mlpGauss n mF 1)
      (fun F : MlpParam n mF 1 => 2 / (mF : ℝ) * dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') -
        2 / (n : ℝ) * psi (kappa ∘ kappa) y y')
      (cF * (2 / (n : ℝ) * (nrm y * nrm y'))))
    (hAg : L2le (mlpGauss n mA n)
      (fun θ : MlpParam n mA n => psi (kappa ∘ kappa) (mlpEval θ x) (mlpEval θ x') -
        2 * (n : ℝ) / n * psi ((kappa ∘ kappa) ∘ kappa ∘ kappa) x x')
      (cAg * (2 * (n : ℝ) / n * (nrm x * nrm x')))) :
    L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        kern p.2.2 p.1 p.1 x x' - 4 / (n : ℝ) * kappa^[4] (dotp x x'))
      (4 / (n : ℝ) * (cF * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))) + cAg)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA' : (0 : ℝ) < mA := by exact_mod_cast hmA
  have hGc : Continuous (kappa ∘ kappa) := continuous_kappa.comp continuous_kappa
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  -- the part of `F`
  have m1 : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x') :=
    measurable_kern_comp (measurable_snd.comp measurable_snd) measurable_fst measurable_fst
      measurable_const measurable_const
  have m2 : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      psi (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.1 x')) :=
    (measurable_psi_mlp hGc x x').comp measurable_fst
  have hg : L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n =>
        cF * (2 / (n : ℝ) * (nrm (mlpEval A x) * nrm (mlpEval A x'))))
      (4 / (n : ℝ) * (cF * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))))) := by
    have h0 := ((mlp_nrm_pair_L2 (q := n) hmA hx hx').const_mul_nonneg
      (c := cF * (2 / (n : ℝ))) (by positivity))
    refine (h0.congr_fun fun A => by ring).congr_bound ?_
    field_simp
    ring
  have h1 : L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        kern p.2.2 p.1 p.1 x x' -
          2 / (n : ℝ) * psi (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.1 x'))
      (4 / (n : ℝ) * (cF * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))))) := by
    refine L2le.prod' (m1.sub (m2.const_mul _)).aestronglyMeasurable hg
      (Filter.Eventually.of_forall fun A => ?_)
    exact (hKF (mlpEval A x) (mlpEval A x')).comp_snd
  -- the part of `A`
  have h2 : L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        2 / (n : ℝ) * (psi (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.1 x') -
          2 * (n : ℝ) / n * psi ((kappa ∘ kappa) ∘ kappa ∘ kappa) x x'))
      (4 / (n : ℝ) * cAg) := by
    have h0 := (hAg.const_mul_nonneg
      (c := 2 / (n : ℝ)) (by positivity)).comp_fst
      (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1))
    refine h0.congr_bound ?_
    rw [nrm_of_normSq_one hx, nrm_of_normSq_one hx']
    field_simp
    ring
  have h3 := h1.add h2 (by positivity)
    (by positivity)
  refine (h3.congr_fun fun p => ?_).congr_bound (by ring)
  rw [psi_unit _ hx hx', iter4_eq]
  field_simp
  ring

/-! ## The cross kernel -/

/-- `E|A(x)| ≥ √2·(1 − eps4/2)` for a unit `x`. -/
lemma agent_nrm_lower (hn : 1 ≤ n) (hmA : 1 ≤ mA) {x : Fin n → ℝ} (hx : normSq x = 1) :
    Integrable (fun a : MlpParam n mA n => nrm (mlpEval a x)) (mlpGauss n mA n) ∧
    √2 * (1 - eps4 n mA / 2) ≤ ∫ a : MlpParam n mA n, nrm (mlpEval a x) ∂mlpGauss n mA n := by
  have i2 := mlp_normSq_integrable (m := mA) (q := n) x
  have e2 := agent_second_moment hn hmA x
  obtain ⟨iv, ev⟩ := agent_sq_var hn hmA hx
  have hi := (mlp_nrm_single (q := n) hmA x).1
  refine ⟨hi, ?_⟩
  have hlow : Integrable (fun a : MlpParam n mA n =>
      √2 * (1 + (normSq (mlpEval a x) - 2) / 4 - (normSq (mlpEval a x) - 2) ^ 2 / 8))
      (mlpGauss n mA n) :=
    ((((integrable_const 1).add ((i2.sub (integrable_const 2)).div_const 4)).sub
      (iv.div_const 8)).const_mul _)
  have hpt : ∀ a : MlpParam n mA n,
      √2 * (1 + (normSq (mlpEval a x) - 2) / 4 - (normSq (mlpEval a x) - 2) ^ 2 / 8) ≤
        nrm (mlpEval a x) := by
    intro a
    set X := normSq (mlpEval a x) with hX
    have hX0 : 0 ≤ X := normSq_nonneg _
    have h1 := sqrt_ge_quad (x := X / 2) (by positivity)
    have h2 : nrm (mlpEval a x) = √2 * √(X / 2) := by
      unfold nrm
      rw [← Real.sqrt_mul (by norm_num), ← hX]
      congr 1
      ring
    rw [h2]
    have h3 : 1 + (X - 2) / 4 - (X - 2) ^ 2 / 8 = 1 + (X / 2 - 1) / 2 - (X / 2 - 1) ^ 2 / 2 := by
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 2)
  have hmono := integral_mono hlow hi hpt
  have hval : ∫ a : MlpParam n mA n,
      √2 * (1 + (normSq (mlpEval a x) - 2) / 4 - (normSq (mlpEval a x) - 2) ^ 2 / 8)
      ∂mlpGauss n mA n = √2 * (1 - eps4 n mA / 2) := by
    have hA : Integrable (fun a : MlpParam n mA n => (1 : ℝ) + (normSq (mlpEval a x) - 2) / 4)
        (mlpGauss n mA n) := (integrable_const 1).add ((i2.sub (integrable_const 2)).div_const 4)
    have hB : Integrable (fun a : MlpParam n mA n => (normSq (mlpEval a x) - 2) / 4)
        (mlpGauss n mA n) := (i2.sub (integrable_const 2)).div_const 4
    rw [integral_const_mul, integral_sub hA (iv.div_const 8), integral_add (integrable_const 1) hB,
      integral_div, integral_div, integral_sub i2 (integrable_const 2), ev, e2, hx]
    simp
    ring
  linarith

lemma agent_nrm_nonneg (x : Fin n → ℝ) :
    0 ≤ ∫ a : MlpParam n mA n, nrm (mlpEval a x) ∂mlpGauss n mA n :=
  integral_nonneg fun a => nrm_nonneg _

/-- `‖|A(x)|·|A′(x′)| − 2‖₂ ≤ 4·√δ` for independent `A`, `A′` and unit `x`, `x′`, if
`E|A(x)| ≥ √2·(1 − δ)` and the same at `x′`. -/
lemma agent_nrm_prod_L2_of (hn : 1 ≤ n) (hmA : 1 ≤ mA) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hl : √2 * (1 - δ) ≤ ∫ a : MlpParam n mA n, nrm (mlpEval a x) ∂mlpGauss n mA n)
    (hl' : √2 * (1 - δ) ≤ ∫ a : MlpParam n mA n, nrm (mlpEval a x') ∂mlpGauss n mA n) :
    L2le ((mlpGauss n mA n).prod (mlpGauss n mA n))
      (fun z : MlpParam n mA n × MlpParam n mA n =>
        nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x') - 2) (4 * √δ) := by
  have i2 := mlp_normSq_integrable (m := mA) (q := n) x
  have i2' := mlp_normSq_integrable (m := mA) (q := n) x'
  have e2 := agent_second_moment hn hmA x
  have e2' := agent_second_moment hn hmA x'
  have hi := (mlp_nrm_single (q := n) hmA x).1
  have hi' := (mlp_nrm_single (q := n) hmA x').1
  have h0 := agent_nrm_nonneg (mA := mA) x
  have h0' := agent_nrm_nonneg (mA := mA) x'
  have hmeas : Measurable (fun z : MlpParam n mA n × MlpParam n mA n =>
      nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x') - 2) :=
    (((continuous_nrm.measurable.comp (measurable_mlpEval_param x)).comp measurable_fst).mul
      ((continuous_nrm.measurable.comp (measurable_mlpEval_param x')).comp measurable_snd)).sub
      measurable_const
  have I1 : Integrable (fun z : MlpParam n mA n × MlpParam n mA n =>
      normSq (mlpEval z.1 x) * normSq (mlpEval z.2 x'))
      ((mlpGauss n mA n).prod (mlpGauss n mA n)) := i2.mul_prod i2'
  have I2 : Integrable (fun z : MlpParam n mA n × MlpParam n mA n =>
      nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x'))
      ((mlpGauss n mA n).prod (mlpGauss n mA n)) := hi.mul_prod hi'
  have E1 : ∫ z : MlpParam n mA n × MlpParam n mA n,
      normSq (mlpEval z.1 x) * normSq (mlpEval z.2 x')
      ∂((mlpGauss n mA n).prod (mlpGauss n mA n)) = 4 := by
    rw [integral_prod_mul (fun a : MlpParam n mA n => normSq (mlpEval a x))
      (fun a : MlpParam n mA n => normSq (mlpEval a x')), e2, e2', hx, hx']
    norm_num
  have E2 : ∫ z : MlpParam n mA n × MlpParam n mA n,
      nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x')
      ∂((mlpGauss n mA n).prod (mlpGauss n mA n)) =
      (∫ a : MlpParam n mA n, nrm (mlpEval a x) ∂mlpGauss n mA n) *
        ∫ a : MlpParam n mA n, nrm (mlpEval a x') ∂mlpGauss n mA n :=
    integral_prod_mul (fun a : MlpParam n mA n => nrm (mlpEval a x))
      (fun a : MlpParam n mA n => nrm (mlpEval a x'))
  have hG : Integrable (fun z : MlpParam n mA n × MlpParam n mA n =>
      normSq (mlpEval z.1 x) * normSq (mlpEval z.2 x') -
        4 * (nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x')) + 4)
      ((mlpGauss n mA n).prod (mlpGauss n mA n)) :=
    (I1.sub (I2.const_mul 4)).add (integrable_const 4)
  refine L2le.of_sq_le hmeas.aestronglyMeasurable hG (fun z => ?_) ?_
  · have : (nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x') - 2) ^ 2 =
        nrm (mlpEval z.1 x) ^ 2 * nrm (mlpEval z.2 x') ^ 2 -
          4 * (nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x')) + 4 := by ring
    rw [this, nrm_sq, nrm_sq]
  · have hA : Integrable (fun z : MlpParam n mA n × MlpParam n mA n =>
        normSq (mlpEval z.1 x) * normSq (mlpEval z.2 x') -
          4 * (nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x')))
        ((mlpGauss n mA n).prod (mlpGauss n mA n)) := I1.sub (I2.const_mul 4)
    rw [integral_add hA (integrable_const 4), integral_sub I1 (I2.const_mul 4),
      integral_const_mul, E1, E2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [mul_pow, Real.sq_sqrt hδ]
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs2 : 0 < √2 := by positivity
    set a := ∫ a : MlpParam n mA n, nrm (mlpEval a x) ∂mlpGauss n mA n
    set a' := ∫ a : MlpParam n mA n, nrm (mlpEval a x') ∂mlpGauss n mA n
    by_cases hc : δ ≤ 1
    · have hL : 0 ≤ √2 * (1 - δ) := mul_nonneg hs2.le (by linarith)
      have hp : (√2 * (1 - δ)) * (√2 * (1 - δ)) ≤ a * a' :=
        mul_le_mul hl hl' hL h0
      have e : (√2 * (1 - δ)) * (√2 * (1 - δ)) = 2 * (1 - δ) ^ 2 := by
        calc (√2 * (1 - δ)) * (√2 * (1 - δ)) = (√2 * √2) * (1 - δ) ^ 2 := by ring
          _ = 2 * (1 - δ) ^ 2 := by rw [h2]
      nlinarith
    · have : 0 ≤ a * a' := mul_nonneg h0 h0'
      nlinarith

/-- **The cross kernel**, from a bound `cF` of the link `F` and a deficit `δ` of `E|A(x)|`: for
unit `x, x′` and independent `A`, `A′`,
`‖(2/m_F)⟨H_A(x), H_{A′}(x′)⟩ − (4/n)·κ(κ(0))‖_{L²(A, A′, F)} ≤ (4/n)·(cF + 1/√n + κ(κ(0))·2√δ)`. -/
theorem kern_cross_L2_of (hn : 1 ≤ n) (hmA : 1 ≤ mA) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {cF δ : ℝ} (hcF : 0 < cF) (hδ : 0 < δ)
    (hKF : ∀ y y' : Fin n → ℝ, L2le (mlpGauss n mF 1)
      (fun F : MlpParam n mF 1 => 2 / (mF : ℝ) * dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') -
        2 / (n : ℝ) * psi (kappa ∘ kappa) y y')
      (cF * (2 / (n : ℝ) * (nrm y * nrm y'))))
    (hl : ∀ z : Fin n → ℝ, normSq z = 1 →
      √2 * (1 - δ) ≤ ∫ a : MlpParam n mA n, nrm (mlpEval a z) ∂mlpGauss n mA n) :
    L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        kern p.2.2 p.1 p.2.1 x x' - 4 / (n : ℝ) * kappa (kappa 0))
      (4 / (n : ℝ) * (cF + 1 / √(n : ℝ) + kappa (kappa 0) * (2 * √δ))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hGc : Continuous (kappa ∘ kappa) := continuous_kappa.comp continuous_kappa
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hq := kappa2_zero_pos
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- measurability
  have m1 : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.2.1 x x') :=
    measurable_kern_comp (measurable_snd.comp measurable_snd) measurable_fst
      (measurable_fst.comp measurable_snd) measurable_const measurable_const
  have mpsi : Measurable (fun z : MlpParam n mA n × MlpParam n mA n =>
      psi (kappa ∘ kappa) (mlpEval z.1 x) (mlpEval z.2 x')) :=
    Measurable.comp (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) => psi (kappa ∘ kappa) p.1 p.2)
      (f := fun z : MlpParam n mA n × MlpParam n mA n => (mlpEval z.1 x, mlpEval z.2 x'))
      (measurable_psi hGc)
      (((measurable_mlpEval_param x).comp measurable_fst).prodMk
        ((measurable_mlpEval_param x').comp measurable_snd))
  have mnn : Measurable (fun z : MlpParam n mA n × MlpParam n mA n =>
      nrm (mlpEval z.1 x) * nrm (mlpEval z.2 x')) :=
    ((continuous_nrm.measurable.comp (measurable_mlpEval_param x)).comp measurable_fst).mul
      ((continuous_nrm.measurable.comp (measurable_mlpEval_param x')).comp measurable_snd)
  have mdot : Measurable (fun z : MlpParam n mA n × MlpParam n mA n =>
      dotp (mlpEval z.1 x) (mlpEval z.2 x')) :=
    measurable_dotp_comp ((measurable_mlpEval_param x).comp measurable_fst)
      ((measurable_mlpEval_param x').comp measurable_snd)
  have mdrop : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      (p.1, p.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  -- link F
  have h1 : L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        kern p.2.2 p.1 p.2.1 x x' -
          2 / (n : ℝ) * psi (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.2.1 x'))
      (4 / (n : ℝ) * cF) := by
    have hg : L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => cF * (2 / (n : ℝ)) * √2 * nrm (mlpEval A x))
        (4 / (n : ℝ) * cF) := by
      have h0 := (mlp_nrm_L2 (q := n) hmA x).const_mul_nonneg
        (c := cF * (2 / (n : ℝ)) * √2) (by positivity)
      refine h0.congr_bound ?_
      rw [hx]
      have : 2 * (n : ℝ) / n * 1 = 2 := by field_simp
      rw [this]
      calc cF * (2 / (n : ℝ)) * √2 * √2 = cF * (2 / (n : ℝ)) * (√2 * √2) := by ring
        _ = 4 / (n : ℝ) * cF := by rw [h22]; ring
    refine L2le.prod' (m1.sub ((mpsi.comp mdrop).const_mul _)).aestronglyMeasurable hg
      (Filter.Eventually.of_forall fun A => ?_)
    have hg' : L2le (mlpGauss n mA n)
        (fun A' : MlpParam n mA n =>
          cF * (2 / (n : ℝ) * (nrm (mlpEval A x) * nrm (mlpEval A' x'))))
        (cF * (2 / (n : ℝ)) * √2 * nrm (mlpEval A x)) := by
      have h0 := (mlp_nrm_L2 (q := n) hmA x').const_mul_nonneg
        (c := cF * (2 / (n : ℝ)) * nrm (mlpEval A x))
        (by have := nrm_nonneg (mlpEval A x); positivity)
      refine (h0.congr_fun fun A' => by ring).congr_bound ?_
      rw [hx']
      have : 2 * (n : ℝ) / n * 1 = 2 := by field_simp
      rw [this]
      ring
    have msec : Measurable (fun y : MlpParam n mA n × MlpParam n mF 1 =>
        kern y.2 A y.1 x x' -
          2 / (n : ℝ) * psi (kappa ∘ kappa) (mlpEval A x) (mlpEval y.1 x')) :=
      (measurable_kern_comp measurable_snd measurable_const measurable_fst measurable_const
        measurable_const).sub
        (((measurable_psi hGc).comp
          (measurable_const.prodMk ((measurable_mlpEval_param x').comp measurable_fst))).const_mul
          _)
    refine L2le.prod' msec.aestronglyMeasurable hg' (Filter.Eventually.of_forall fun A' => ?_)
    exact hKF (mlpEval A x) (mlpEval A' x')
  -- the inner product of two independent outputs
  have hdot : L2le ((mlpGauss n mA n).prod (mlpGauss n mA n))
      (fun z : MlpParam n mA n × MlpParam n mA n => dotp (mlpEval z.1 x) (mlpEval z.2 x'))
      (2 / √(n : ℝ)) := by
    have hg : L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => √(2 / (n : ℝ)) * nrm (mlpEval A x)) (2 / √(n : ℝ)) := by
      have h0 := (mlp_nrm_L2 (q := n) hmA x).const_mul_nonneg
        (c := √(2 / (n : ℝ))) (by positivity)
      refine h0.congr_bound ?_
      rw [hx]
      have : 2 * (n : ℝ) / n * 1 = 2 := by field_simp
      rw [this, Real.sqrt_div (by norm_num), div_mul_eq_mul_div, h22]
    refine L2le.prod mdot.aestronglyMeasurable hg (Filter.Eventually.of_forall fun A => ?_)
    obtain ⟨hi, he⟩ := mlp_form_sq (q := n) hmA (mlpEval A x) x'
    refine ⟨hi, ?_⟩
    rw [he, hx', mul_pow, Real.sq_sqrt (by positivity), nrm_sq]
    apply le_of_eq
    ring
  have hdrop : ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))).map
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 => (p.1, p.2.1)) =
      (mlpGauss n mA n).prod (mlpGauss n mA n) := map_drop3
  have h2 : L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        2 / (n : ℝ) * (psi (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.2.1 x') -
          kappa (kappa 0) * (nrm (mlpEval p.1 x) * nrm (mlpEval p.2.1 x'))))
      (4 / (n : ℝ) * (1 / √(n : ℝ))) := by
    have h0 := ((hdot.comp_map mdrop hdrop).const_mul_nonneg (c := 2 / (n : ℝ)) (by positivity))
    refine L2le.of_abs_le
      ((((mpsi.sub (mnn.const_mul _)).comp mdrop).const_mul _).aestronglyMeasurable)
      (h0.congr_bound (by ring)) (fun p => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (psi_sub_const_abs hG _ _) (abs_nonneg _)
  have h3 : L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        2 / (n : ℝ) * kappa (kappa 0) * (nrm (mlpEval p.1 x) * nrm (mlpEval p.2.1 x') - 2))
      (4 / (n : ℝ) * (kappa (kappa 0) * (2 * √δ))) := by
    have h0 := (((agent_nrm_prod_L2_of hn hmA hx hx' hδ.le (hl x hx) (hl x' hx')).comp_map mdrop hdrop).const_mul_nonneg
      (c := 2 / (n : ℝ) * kappa (kappa 0)) (by positivity))
    exact h0.congr_bound (by ring)
  have h12 := h1.add h2 (by positivity) (by positivity)
  have h123 := h12.add h3 (by positivity) (by positivity)
  refine (h123.congr_fun fun p => ?_).congr_bound (by ring)
  field_simp
  ring

/-! ## The diagonal kernel -/

/-- `E_F |H(y)|⁴` for the hidden map of `F`. -/
lemma F_hid_four (y : Fin n → ℝ) :
    Integrable (fun F : MlpParam n mF 1 => normSq (hid2 F.1 F.2.1 y) ^ 2) (mlpGauss n mF 1) ∧
    ∫ F : MlpParam n mF 1, normSq (hid2 F.1 F.2.1 y) ^ 2 ∂mlpGauss n mF 1 =
      ((mF : ℝ) ^ 2 / 4 + 5 * mF / 4) * (2 / (mF : ℝ)) ^ 2 *
        (((mF : ℝ) ^ 2 / 4 + 5 * mF / 4) * (2 / (n : ℝ)) ^ 2) * normSq y ^ 2 := by
  obtain ⟨hi, he⟩ := hid2_four (m₁ := mF) (m₂ := mF) (two_div_nonneg n) (two_div_nonneg mF) y
  unfold mlpGauss
  exact ⟨integrable_drop3 hi, by rw [integral_drop3 hi.aestronglyMeasurable, he]⟩

/-- `E k(x, x)² = (4/n)²·(1+5/m_F)²(1+5/m_A)²(1+2/n)` for a unit `x`. -/
lemma kern_diag_sq (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {x : Fin n → ℝ}
    (hx : normSq x = 1) :
    Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x ^ 2)
      ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ∧
    ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kern p.2.2 p.1 p.1 x x ^ 2
      ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) =
      (4 / (n : ℝ)) ^ 2 * ((1 + 5 / (mF : ℝ)) ^ 2 * (1 + 5 / (mA : ℝ)) ^ 2 * (1 + 2 / (n : ℝ))) := by
  have hmF' : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hmA' : (0 : ℝ) < mA := by exact_mod_cast hmA
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : ∀ (F : MlpParam n mF 1) (a : MlpParam n mA n),
      kern F a a x x ^ 2 = (2 / (mF : ℝ)) ^ 2 * normSq (hid2 F.1 F.2.1 (mlpEval a x)) ^ 2 := by
    intro F a
    unfold kern hidF
    rw [dotp_self, mul_pow]
  have inner : ∀ a : MlpParam n mA n,
      Integrable (fun y : MlpParam n mA n × MlpParam n mF 1 => kern y.2 a a x x ^ 2)
        ((mlpGauss n mA n).prod (mlpGauss n mF 1)) ∧
      ∫ y : MlpParam n mA n × MlpParam n mF 1, kern y.2 a a x x ^ 2
        ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) =
        (2 / (n : ℝ)) ^ 2 * (1 + 5 / (mF : ℝ)) ^ 2 * normSq (mlpEval a x) ^ 2 := by
    intro a
    obtain ⟨hi, he⟩ := F_hid_four (mF := mF) (mlpEval a x)
    simp_rw [hk]
    refine ⟨(hi.const_mul _).comp_snd _, ?_⟩
    rw [integral_fun_snd (fun F : MlpParam n mF 1 =>
      (2 / (mF : ℝ)) ^ 2 * normSq (hid2 F.1 F.2.1 (mlpEval a x)) ^ 2), integral_const_mul, he]
    simp
    field_simp
    ring
  have hmeas : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x ^ 2) :=
    (measurable_kern_comp (measurable_snd.comp measurable_snd) measurable_fst measurable_fst
      measurable_const measurable_const).pow_const 2
  have step := prod_step (μ := mlpGauss n mA n)
    (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1)) hmeas
    (fun p => sq_nonneg _)
    (fun a => (2 / (n : ℝ)) ^ 2 * (1 + 5 / (mF : ℝ)) ^ 2 * normSq (mlpEval a x) ^ 2) inner
    ((mlp_normSq_sq_integrable x).const_mul _)
  refine ⟨step.1, ?_⟩
  rw [step.2, integral_const_mul, mlp_fourth_moment (q := n) hmA x, hx]
  field_simp
  ring

lemma eV_sq (n mA mF : ℕ) :
    eV n mA mF ^ 2 = (1 + 5 / (mF : ℝ)) ^ 2 * (1 + 5 / (mA : ℝ)) ^ 2 * (1 + 2 / (n : ℝ)) - 1 := by
  unfold eV
  apply Real.sq_sqrt
  have h1 : (0 : ℝ) ≤ 5 / (mF : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ 5 / (mA : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have a1 : (1 : ℝ) ≤ (1 + 5 / (mF : ℝ)) ^ 2 := by nlinarith
  have a2 : (1 : ℝ) ≤ (1 + 5 / (mA : ℝ)) ^ 2 := by nlinarith
  have a3 : (1 : ℝ) ≤ (1 + 5 / (mF : ℝ)) ^ 2 * (1 + 5 / (mA : ℝ)) ^ 2 := by nlinarith
  nlinarith

/-- **The diagonal kernel**: for a unit `x`,
`‖(2/m_F)|H_A(x)|² − 4/n‖_{L²(A, A′, F)} ≤ (4/n)·eV` (an equality of the second moments). -/
theorem kern_diag_L2 (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {x : Fin n → ℝ}
    (hx : normSq x = 1) :
    L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
      (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        kern p.2.2 p.1 p.1 x x - 4 / (n : ℝ))
      (4 / (n : ℝ) * eV n mA mF) := by
  obtain ⟨i1, _⟩ := kern_diag_gen hn hmA hmF x
  have e1 := kern_diag_mean hn hmA hmF hx
  obtain ⟨i2, e2⟩ := kern_diag_sq hn hmA hmF hx
  have hmeas : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x - 4 / (n : ℝ)) :=
    (measurable_kern_comp (measurable_snd.comp measurable_snd) measurable_fst measurable_fst
      measurable_const measurable_const).sub measurable_const
  have hG : Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x ^ 2 - 2 * (4 / (n : ℝ)) * kern p.2.2 p.1 p.1 x x + (4 / (n : ℝ)) ^ 2)
      ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) :=
    (i2.sub (i1.const_mul _)).add (integrable_const _)
  refine L2le.of_sq_le hmeas.aestronglyMeasurable hG (fun p => le_of_eq (by ring)) ?_
  have hA : Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x ^ 2 - 2 * (4 / (n : ℝ)) * kern p.2.2 p.1 p.1 x x)
      ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) :=
    i2.sub (i1.const_mul _)
  rw [integral_add hA (integrable_const _), integral_sub i2 (i1.const_mul _), integral_const_mul,
    e1, e2, mul_pow, eV_sq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  apply le_of_eq
  ring

end BstLean.Part133
