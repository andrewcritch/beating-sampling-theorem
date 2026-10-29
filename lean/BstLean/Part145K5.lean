import BstLean.Part145K3

/-!
# Part 145 (K5): one more orthogonal block in the assembly of the distance kernel

`kernDist145_of` adds the remainder `kX2` of the first layer of `F` (the function `rF`, bound
`asmE2`) by the triangle inequality. Here `kX2 = kX2c + kX2b`:

* `rFb y y′ = ∫ rF0 F₁ y y′ dF₁`: the mean of `rF0` over the first matrix `F₁` of `F` (the
  distribution of `F₁` is `gaussMat mF n (2/n)`).
* `kX2b ω = rFb (yA ω) (yA' ω)`: it does not read `F`. `kX2c = kX2 − kX2b`.
* `L2le_sub_mean`: `‖f − ∫ f‖₂ ≤ ‖f‖₂` on a probability space; `kX2c_L2`: `‖kX2c‖₂ ≤ S·asmE2`.
* `kX2b_L2`: `‖kX2b‖₂ ≤ S·bK·((1 + 5/mA)·√(1 + 2/n))` from the bias hypothesis
  `|rFb y y′| ≤ (2/n)·bK·(|y|² + |y′|²)/2`.
* `crossC`: `∫ kX2c·(kX2b + X4 + (X3 + X5)) = 0` (mean zero over `F₁`).
* `kernDistB_of`, **`kernB`**:
  `‖kD − S(1 − Q)‖₂ ≤ S·√(E1² + E2² + (B2 + E4 + √(E3x² + pW²))²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143

/-! ## Abstract tools -/

section tools

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma L2le_integrableK [IsFiniteMeasure μ] {f : Ω → ℝ} {a : ℝ} (h : L2le μ f a) :
    Integrable f μ :=
  ((memLp_two_iff_integrable_sq h.aesm).2 h.int_sq).integrable one_le_two

/-- **The variance is at most the second moment**: `‖f − ∫ f‖₂ ≤ ‖f‖₂`. -/
theorem L2le_sub_mean [IsProbabilityMeasure μ] {f : Ω → ℝ} {a : ℝ} (h : L2le μ f a) :
    L2le μ (fun ω => f ω - ∫ x, f x ∂μ) a := by
  have hi := L2le_integrableK h
  set c : ℝ := ∫ x, f x ∂μ with hc
  have hA : Integrable (fun ω => f ω ^ 2 - 2 * c * f ω) μ := h.int_sq.sub (hi.const_mul _)
  have hG : Integrable (fun ω => f ω ^ 2 - 2 * c * f ω + c ^ 2) μ :=
    hA.add (integrable_const _)
  refine L2le.of_sq_le (h.aesm.sub aestronglyMeasurable_const) hG
    (fun ω => le_of_eq (by ring)) ?_
  rw [integral_add hA (integrable_const _), integral_sub h.int_sq (hi.const_mul _),
    integral_const_mul, integral_const, ← hc]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have := h.le
  nlinarith [sq_nonneg c]

end tools

section General

variable {N mW n mA mF : ℕ}

/-! ## The mean of `rF0` over the first matrix of `F` -/

/-- The mean of `rF0` over the first matrix `F₁` of `F`. -/
noncomputable def rFb (mF : ℕ) (y y' : Fin n → ℝ) : ℝ :=
  ∫ F₁ : Matrix (Fin mF) (Fin n) ℝ, rF0 F₁ y y' ∂gaussMat mF n (2 / (n : ℝ))

lemma measurable_rFb :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => rFb mF q.1 q.2) := by
  have h := (measurable_rF0 (n := n) (mF := mF)).stronglyMeasurable
  exact (h.integral_prod_left' (μ := gaussMat mF n (2 / (n : ℝ)))).measurable

/-- `rF − rFb` in `L²`, over the weights of `F`: the bound of `rF_L2`. -/
theorem rFc_L2 (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    L2le (mlpGauss n mF 1) (fun F : MlpParam n mF 1 => rF F y y' - rFb mF y y')
      (2 / (n : ℝ) * (f1b mF * normSq (y - y') + f2 mF * (normSq y + normSq y') +
        f3 mF * |normSq y - normSq y'| + f4 * dlt y y')) := by
  unfold mlpGauss
  exact ((L2le_sub_mean (rF0_L2 hn hmF y y')).comp_fst).congr_fun fun F => rfl

lemma rF0_sub_mean (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    ∫ F₁ : Matrix (Fin mF) (Fin n) ℝ, (rF0 F₁ y y' - rFb mF y y')
      ∂gaussMat mF n (2 / (n : ℝ)) = 0 := by
  have hi := L2le_integrableK (rF0_L2 hn hmF y y')
  rw [integral_sub hi (integrable_const _), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold rFb
  ring

/-! ## The two parts of `X2` -/

/-- `X2b`: the mean of `X2` over the first matrix of `F`. It does not read `F`. -/
noncomputable def kX2b (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  rFb mF (yA ω) (yA' ω)

/-- `X2c = X2 − X2b`: mean zero over the first matrix of `F`. -/
noncomputable def kX2c (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  kX2 ω - kX2b ω

/-- `‖X2c‖₂ ≤ S·E2`. -/
theorem kX2c_L2 (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    {d0 d1 d2 δ2 τ : ℝ} (h0 : 0 ≤ d0) (h1 : 0 ≤ d1)
    (h2 : 0 ≤ d2) (hδ2 : 0 ≤ δ2) (hτ : 0 ≤ τ)
    (hDiff : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => normSq (mlpEval A x - mlpEval A x'))
      (4 * (d0 + d1 * (1 - kappa (kappa (dotp x x'))) + d2 * (1 - dotp x x'))))
    (hDlt : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => dlt (mlpEval A x) (mlpEval A x')) (2 * δ2))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (kX2c (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))
      (4 / (n : ℝ) * asmE2 n mA mF d0 d1 d2 δ2 τ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA' : (0 : ℝ) < mA := by exact_mod_cast hmA
  have hf1 := f1b_nonneg mF
  have hf2 := f2_nonneg mF
  have hf3 := f3_nonneg mF
  have hf4 := f4_nonneg
  have a4 := one_sub_k4_nonneg
  have a2 := a2_nonneg
  have he4 := Real.sqrt_nonneg (eps4 n mA)
  set N0 : ℝ := (1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ)) with hN0
  have hN00 : 0 ≤ N0 := by rw [hN0]; positivity
  have hb := tX_lin_L2 (mW := mW) hn hN
    (g0 := 2 * f1b mF * d0 + 2 * f2 mF * N0 + 2 * f3 mF * √(eps4 n mA) + f4 * δ2)
    (g1 := 2 * f1b mF * d1) (g2 := 2 * f1b mF * d2) (g3 := 0) (by positivity) le_rfl hτ
    (lin_nonneg (by positivity) (by positivity) (by positivity) le_rfl) hT
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * f1b mF * d1)] at hb
  have hXm : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) (x x' : Fin n → ℝ) =>
        rF p.2.2 (mlpEval p.1 x) (mlpEval p.1 x') -
          rFb mF (mlpEval p.1 x) (mlpEval p.1 x')) z.1 z.2.1 z.2.2) :=
    (measurable_rF.comp (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (z.1.2.2, (mlpEval z.1.1 z.2.1, mlpEval z.1.1 z.2.2)))
      (((measurable_snd.comp measurable_snd).comp measurable_fst).prodMk
        (measurable_ev1.prodMk measurable_ev2))).sub
    (measurable_rFb.comp (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (mlpEval z.1.1 z.2.1, mlpEval z.1.1 z.2.2))
      (measurable_ev1.prodMk measurable_ev2))
  have key := lift_L2 (mW := mW) hn hN hXm hb (fun x x' hx hx' => by
    have ht := dotp_unit_mem hx hx'
    have hkt := kk_memIcc ht
    have u1 : 0 ≤ 1 - kappa (kappa (dotp x x')) := by linarith [hkt.2]
    have u2 : 0 ≤ 1 - dotp x x' := by linarith [ht.2]
    set δ1 : ℝ := d0 + d1 * (1 - kappa (kappa (dotp x x'))) + d2 * (1 - dotp x x') with hδ1d
    have hδ1 : 0 ≤ δ1 := by rw [hδ1d]; positivity
    have nS := agent_normSq_L2 hn hmA hx
    have nS' := agent_normSq_L2 hn hmA hx'
    have dS := agent_normSq_dev_L2 hn hmA hx
    have dS' := agent_normSq_dev_L2 hn hmA hx'
    have sSum := nS.add0 nS' (by positivity) (by positivity)
    have sDif : L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => |normSq (mlpEval A x) - normSq (mlpEval A x')|)
        (2 * √(eps4 n mA) + 2 * √(eps4 n mA)) := by
      have h0 := dS.add0 dS'.neg (by positivity) (by positivity)
      exact L2le.abs' (h0.congr_fun fun A => by ring)
    have hg : L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => 2 / (n : ℝ) *
          (f1b mF * normSq (mlpEval A x - mlpEval A x') +
          f2 mF * (normSq (mlpEval A x) + normSq (mlpEval A x')) +
          f3 mF * |normSq (mlpEval A x) - normSq (mlpEval A x')| +
          f4 * dlt (mlpEval A x) (mlpEval A x')))
        (2 / (n : ℝ) * (f1b mF * (4 * δ1) + f2 mF * (2 * N0 + 2 * N0) +
          f3 mF * (2 * √(eps4 n mA) + 2 * √(eps4 n mA)) + f4 * (2 * δ2))) := by
      have a1 := (hDiff x x' hx hx').const_mul_nonneg hf1
      have a2 := sSum.const_mul_nonneg hf2
      have a3 := sDif.const_mul_nonneg hf3
      have a4 := (hDlt x x' hx hx').const_mul_nonneg hf4
      have s12 := a1.add0 a2 (by positivity) (by positivity)
      have s123 := s12.add0 a3 (by positivity) (by positivity)
      have s1234 := s123.add0 a4 (by positivity) (by positivity)
      exact s1234.const_mul_nonneg (by positivity)
    have m1 : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        rF p.2.2 (mlpEval p.1 x) (mlpEval p.1 x') -
          rFb mF (mlpEval p.1 x) (mlpEval p.1 x')) :=
      hXm.comp (f := fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        (p, (x, x'))) (by fun_prop)
    refine (L2le.prod' m1.aestronglyMeasurable hg (Filter.Eventually.of_forall fun A =>
      (rFc_L2 hn hmF (mlpEval A x) (mlpEval A x')).comp_snd)).congr_bound ?_
    rw [hδ1d]
    unfold linB
    ring)
  refine (key.congr_fun fun ω => rfl).congr_bound ?_
  unfold asmE2
  rw [← hN0]
  ring

/-- `‖X2b‖₂ ≤ S·bK·((1 + 5/mA)·√(1 + 2/n))` from the bias hypothesis. -/
theorem kX2b_L2 (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) {bK : ℝ} (hbK : 0 ≤ bK)
    (hB : ∀ y y' : Fin n → ℝ,
      Integrable (fun F₁ : Matrix (Fin mF) (Fin n) ℝ => rF0 F₁ y y')
        (gaussMat mF n (2 / (n : ℝ))) ∧
      |∫ F₁, rF0 F₁ y y' ∂gaussMat mF n (2 / (n : ℝ))| ≤
        2 / (n : ℝ) * (bK * ((normSq y + normSq y') / 2))) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (kX2b (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))
      (4 / (n : ℝ) * (bK * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))))) := by
  have := lawU2_prob hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA' : (0 : ℝ) < mA := by exact_mod_cast hmA
  set N0 : ℝ := (1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ)) with hN0
  have hN00 : 0 ≤ N0 := by rw [hN0]; positivity
  have hc0 : 0 ≤ 4 / (n : ℝ) * (bK * N0) := by positivity
  have hb : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        (fun _ : ℝ => 4 / (n : ℝ) * (bK * N0)) (tX z)) (4 / (n : ℝ) * (bK * N0)) := by
    have h := L2le.const (μ := (lawU2 N).prod (mlpGauss N mW n)) (4 / (n : ℝ) * (bK * N0))
    rwa [abs_of_nonneg hc0] at h
  have hXm : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) (x x' : Fin n → ℝ) =>
        rFb mF (mlpEval p.1 x) (mlpEval p.1 x')) z.1 z.2.1 z.2.2) :=
    measurable_rFb.comp (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (mlpEval z.1.1 z.2.1, mlpEval z.1.1 z.2.2))
      (measurable_ev1.prodMk measurable_ev2)
  have key := lift_L2 (mW := mW) (mA := mA) (mF := mF)
    (X := fun (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) (x x' : Fin n → ℝ) =>
      rFb mF (mlpEval p.1 x) (mlpEval p.1 x'))
    (b := fun _ : ℝ => 4 / (n : ℝ) * (bK * N0)) hn hN hXm hb
    (fun x x' hx hx' => by
    have nS := agent_normSq_L2 hn hmA hx
    have nS' := agent_normSq_L2 hn hmA hx'
    rw [← hN0] at nS nS'
    have sSum := nS.add0 nS' (by positivity) (by positivity)
    have hg := (sSum.const_mul_nonneg (c := 2 / (n : ℝ) * (bK / 2)) (by positivity))
    have mA1 : Measurable (fun A : MlpParam n mA n => rFb mF (mlpEval A x) (mlpEval A x')) :=
      (measurable_rFb (n := n) (mF := mF)).comp
        (f := fun A : MlpParam n mA n => (mlpEval A x, mlpEval A x'))
        ((measurable_mlpEval_param x).prodMk (measurable_mlpEval_param x'))
    have hh := L2le.of_abs_le mA1.aestronglyMeasurable hg (fun A => by
      have h1 := (hB (mlpEval A x) (mlpEval A x')).2
      have h2 : 0 ≤ 2 / (n : ℝ) * (bK / 2) *
          (normSq (mlpEval A x) + normSq (mlpEval A x')) :=
        mul_nonneg (by positivity) (add_nonneg (normSq_nonneg _) (normSq_nonneg _))
      rw [abs_of_nonneg h2]
      exact h1.trans (le_of_eq (by ring)))
    refine (hh.comp_fst (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1))).congr_bound ?_
    ring)
  exact key.congr_fun fun ω => rfl

/-! ## The orthogonality steps -/

/-- **Orthogonality (iii)**: `∫ X2c·(X2b + X4 + (X3 + X5)) = 0`. -/
theorem crossC (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF)
    (cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hI : Integrable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      kX2c ω * (kX2b ω + kX4 cA ω + (kX3 cA ω + kX5 ω))) ((lawU2 N).prod (lawR N mW n mA mF))) :
    ∫ ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF,
      kX2c ω * (kX2b ω + kX4 cA ω + (kX3 cA ω + kX5 ω))
      ∂((lawU2 N).prod (lawR N mW n mA mF)) = 0 := by
  have := lawU2_prob hN
  refine integral_prod_zero hI fun uu h1 => ?_
  refine integral_prod_zero (μ := mlpGauss N mW n)
    (ν := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) h1 fun W h2 => ?_
  refine integral_prod_zero (μ := mlpGauss n mA n)
    (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1)) h2 fun A h3 => ?_
  refine integral_prod_zero (μ := mlpGauss n mA n) (ν := mlpGauss n mF 1) h3 fun A' _ => ?_
  exact integral_fst_mul_zero (μ := gaussMat mF n (2 / (n : ℝ)))
    (ν := (gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ))))
    (g := fun F₁ : Matrix (Fin mF) (Fin n) ℝ =>
      rF0 F₁ (mlpEval A (xW W uu.1)) (mlpEval A (xW W uu.2)) -
        rFb mF (mlpEval A (xW W uu.1)) (mlpEval A (xW W uu.2)))
    (rF0_sub_mean hn hmF _ _)
    (rFb mF (mlpEval A (xW W uu.1)) (mlpEval A (xW W uu.2)) +
      2 / (n : ℝ) * (phiD (kappa ∘ kappa) (mlpEval A (xW W uu.1)) (mlpEval A (xW W uu.2)) -
        2 * (1 - kappa^[4] (dotp (xW W uu.1) (xW W uu.2))) -
        cA A (xW W uu.1) (xW W uu.2)) +
      (2 / (n : ℝ) * cA A (xW W uu.1) (xW W uu.2) +
        4 / (n : ℝ) * (kappa^[6] 0 - kappa^[4] (dotp (xW W uu.1) (xW W uu.2)))))

/-- **Orthogonality (i)** in the new split: `∫ X1·(X2c + (X2b + X4 + (X3 + X5))) = 0`. -/
theorem cross1B (hN : 1 ≤ N) (hmF : 1 ≤ mF)
    (cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hI : Integrable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      kX1 ω * (kX2c ω + (kX2b ω + kX4 cA ω + (kX3 cA ω + kX5 ω))))
      ((lawU2 N).prod (lawR N mW n mA mF))) :
    ∫ ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF,
      kX1 ω * (kX2c ω + (kX2b ω + kX4 cA ω + (kX3 cA ω + kX5 ω)))
      ∂((lawU2 N).prod (lawR N mW n mA mF)) = 0 := by
  have e : ∀ ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF,
      kX1 ω * (kX2c ω + (kX2b ω + kX4 cA ω + (kX3 cA ω + kX5 ω))) =
        kX1 ω * (kX2 ω + kX4 cA ω + (kX3 cA ω + kX5 ω)) := fun ω => by
    unfold kX2c; ring
  have hI' := hI.congr (Filter.Eventually.of_forall e)
  rw [integral_congr_ae (Filter.Eventually.of_forall e)]
  exact cross1 hN hmF cA hI'

/-! ## The assembly -/

/-- **The distance kernel with three orthogonal blocks.** The copy of `kernDist145_of` with the
split `X2 = X2c + X2b` and the bias hypothesis `hB`. -/
theorem kernDistB_of (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    {cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hcAm : Measurable (fun p : MlpParam n mA n × (Fin n → ℝ) × (Fin n → ℝ) =>
      cA p.1 p.2.1 p.2.2))
    {c0 c1 c1' c2 r0 r1 r1' r2 τ pW bK : ℝ}
    (hc1 : 0 ≤ c1) (hc1' : 0 ≤ c1') (hc2 : 0 ≤ c2) (hr1 : 0 ≤ r1) (hr1' : 0 ≤ r1')
    (hr2 : 0 ≤ r2) (hτ : 0 ≤ τ) (hbK : 0 ≤ bK)
    (hcC : 0 ≤ c0 + c1 * (1 - kappa^[6] 0) - c1' * (1 - kappa^[4] 0) +
      c2 * (1 - kappa (kappa 0)))
    (hrC : 0 ≤ r0 + r1 * (1 - kappa^[6] 0) - r1' * (1 - kappa^[4] 0) +
      r2 * (1 - kappa (kappa 0)))
    (hcI : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      Integrable (fun A : MlpParam n mA n => cA A x x') (mlpGauss n mA n) ∧
        ∫ A, cA A x x' ∂mlpGauss n mA n = 0)
    (hcL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n) (fun A : MlpParam n mA n => cA A x x')
        (2 * (c0 + c1 * (1 - kappa^[4] (dotp x x')) - c1' * (1 - kappa (kappa (dotp x x'))) +
          c2 * (1 - dotp x x'))))
    (hrL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
          2 * (1 - kappa^[4] (dotp x x')) - cA A x x')
        (2 * (r0 + r1 * (1 - kappa^[4] (dotp x x')) - r1' * (1 - kappa (kappa (dotp x x'))) +
          r2 * (1 - dotp x x'))))
    {d0 d1 d2 δ2 : ℝ} (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hδ2 : 0 ≤ δ2)
    (hDiff : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => normSq (mlpEval A x - mlpEval A x'))
      (4 * (d0 + d1 * (1 - kappa (kappa (dotp x x'))) + d2 * (1 - dotp x x'))))
    (hDlt : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => dlt (mlpEval A x) (mlpEval A x')) (2 * δ2))
    (hB : ∀ y y' : Fin n → ℝ,
      Integrable (fun F₁ : Matrix (Fin mF) (Fin n) ℝ => rF0 F₁ y y')
        (gaussMat mF n (2 / (n : ℝ))) ∧
      |∫ F₁, rF0 F₁ y y' ∂gaussMat mF n (2 / (n : ℝ))| ≤
        2 / (n : ℝ) * (bK * ((normSq y + normSq y') / 2)))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ)
    (hW5 : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        kappa^[4] (tX z) - kappa^[6] 0) pW) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * √(asmE1 mF d0 d1 d2 τ ^ 2 + asmE2 n mA mF d0 d1 d2 δ2 τ ^ 2 +
        (bK * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))) + asmE4 r0 r1 r1' r2 τ +
          √(asmE3x c0 c1 c1' c2 τ ^ 2 + pW ^ 2)) ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA' : (0 : ℝ) < mA := by exact_mod_cast hmA
  have hS0 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
  have g1 := kX1_L2 (mW := mW) (mA := mA) hn hN hmF hd0 hd1 hd2 hτ hDiff hT
  have g2c := kX2c_L2 (mW := mW) hn hN hmA hmF hd0 hd1 hd2 hδ2 hτ hDiff hDlt hT
  have g2b := kX2b_L2 (N := N) (mW := mW) (mF := mF) hn hN hmA hbK hB
  have g3 := kX3_L2x (mW := mW) (mF := mF) hn hN hcAm hc1 hc1' hc2 hτ hcC hcL hT
  have g4 := kX4_L2 (mW := mW) (mF := mF) hn hN hcAm hr1 hr1' hr2 hτ hrC hrL hT
  have g5 := kX5_L2 (mA := mA) (mF := mF) hN hn hW5
  set B2 : ℝ := bK * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))) with hB2
  have hB20 : 0 ≤ B2 := by rw [hB2]; positivity
  have e2 := asmE2_nonneg n mA mF hd0 hd1 hd2 hδ2 hτ
  have e4 : 0 ≤ asmE4 r0 r1 r1' r2 τ := by
    have := sig4_nonneg
    have : 0 ≤ (r1 * sig4 + r1' + r2) * τ := by positivity
    unfold asmE4; linarith
  have g35 := L2le.add_orth g3 g5 (cross35 hN hcI hn)
  have gZ := (g2b.add0 g4 (by positivity) (by positivity)).add0 g35 (by positivity)
    (Real.sqrt_nonneg _)
  have gY := L2le.add_orth g2c gZ (crossC hn hN hmF cA)
  have gAll := L2le.add_orth g1 gY (cross1B hN hmF cA)
  refine (gAll.congr_fun fun ω => ?_).congr_bound ?_
  · rw [kD_split cA ω]
    unfold kX2c
    ring
  have q1 : √((4 / (n : ℝ) * asmE3x c0 c1 c1' c2 τ) ^ 2 + (4 / (n : ℝ) * pW) ^ 2) =
      4 / (n : ℝ) * √(asmE3x c0 c1 c1' c2 τ ^ 2 + pW ^ 2) := by
    have e : (4 / (n : ℝ) * asmE3x c0 c1 c1' c2 τ) ^ 2 + (4 / (n : ℝ) * pW) ^ 2 =
        (4 / (n : ℝ)) ^ 2 * (asmE3x c0 c1 c1' c2 τ ^ 2 + pW ^ 2) := by ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS0]
  rw [q1]
  set R : ℝ := √(asmE3x c0 c1 c1' c2 τ ^ 2 + pW ^ 2) with hR
  rw [Real.sq_sqrt (by positivity)]
  have e : (4 / (n : ℝ) * asmE1 mF d0 d1 d2 τ) ^ 2 +
      ((4 / (n : ℝ) * asmE2 n mA mF d0 d1 d2 δ2 τ) ^ 2 +
        (4 / (n : ℝ) * B2 + 4 / (n : ℝ) * asmE4 r0 r1 r1' r2 τ + 4 / (n : ℝ) * R) ^ 2) =
      (4 / (n : ℝ)) ^ 2 * (asmE1 mF d0 d1 d2 τ ^ 2 + asmE2 n mA mF d0 d1 d2 δ2 τ ^ 2 +
        (B2 + asmE4 r0 r1 r1' r2 τ + R) ^ 2) := by ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS0]

end General

/-! ## The Focus widths -/

/-- The kernel constant with three orthogonal blocks, at a general `τ` and bias constant `bK`. -/
noncomputable def eDB (bK τ : ℝ) (n : ℕ) : ℝ :=
  √(asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) τ ^ 2 +
    asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (cAdlt n (mA n)) τ ^ 2 +
    (bK * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) +
      asmE4 (rR0 n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) τ +
      √(asmE3x (cC0x n (mA n)) (cC1 n) (cC1x' n) (cC2x n (mA n)) τ ^ 2 + (sig4 * τ) ^ 2)) ^ 2)

lemma eDB_nonneg (bK τ : ℝ) (n : ℕ) : 0 ≤ eDB bK τ n := Real.sqrt_nonneg _

/-- **The kernel bound with three orthogonal blocks**, `n ≥ 4096`, from the bias hypothesis. -/
theorem kernB {n : ℕ} (hn : 4096 ≤ n) {bK : ℝ} (hbK : 0 ≤ bK)
    (hB : ∀ y y' : Fin n → ℝ,
      Integrable (fun F₁ : Matrix (Fin (mF n)) (Fin n) ℝ => rF0 F₁ y y')
        (gaussMat (mF n) n (2 / (n : ℝ))) ∧
      |∫ F₁, rF0 F₁ y y' ∂gaussMat (mF n) n (2 / (n : ℝ))| ≤
        2 / (n : ℝ) * (bK * ((normSq y + normSq y') / 2)))
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hT : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * eDB bK τ n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  unfold eDB
  exact kernDistB_of (cA := cAg) hn1 hN hmA hmF measurable_cAg
    (cC1_nonneg n) (cC1x'_nonneg n) (cC2x_nonneg n (mA n)) (rR1_nonneg n) (rR1'_nonneg n)
    (rR2_nonneg n (mA n)) hτ hbK (cC_ref_nonneg n (mA n)) (rR_ref_nonneg n (mA n))
    (fun x x' hx hx' => cAg_integral hn1 hmA hx hx')
    (fun x x' hx hx' => cAg_L2x hn1 hmA hx hx')
    (fun x x' hx hx' => agent_rem_L2 hn1 hmA hx hx')
    (dA0_nonneg n (mA n)) (dA1_nonneg n (mA n)) (dA2_nonneg n (mA n)) (cAdlt_nonneg n (mA n))
    (fun x x' hx hx' => agent_diff_L2_of reluEDStmt reluPhiStmt hn1 hmA hx hx')
    (fun x x' hx hx' => agent_dlt_L2_of reluSqStmt reluDltStmt linDltStmt hn1 hmA hx hx')
    hB hT (chord_pW hn1 hT)

end BstLean.Part145

open BstLean.Part145 in
#print axioms kernDistB_of
open BstLean.Part145 in
#print axioms kernB
