import BstLean.Part132Mean

/-!
# Part 132, item 3: the lower bound of the kernel through `F` and `A`

Role: `delegations/statements/p132-spec.md`. Paper source: `onW4c-cx.md` §3, the display
`E_{A,F}[F(A(x))F(A(x′))] ≥ S·[κ⁴(t_x) − 6q/n − 17(h₀ + q)/m_A − 17/(π m_F)]`
(`onW4-opus-prover.md` (M1)).

* `KF_lower`: for fixed outputs `y, y′` of `A`:
  `E_F (2/m_F)⟨H(y), H(y′)⟩ ≥ (2/n)·[Ψ_{κ∘κ}(y, y′) − (10/m_F)κ(0)|y||y′|]`.
* `eA n mA mF = (4/n)·κ(κ(0)) + 20/m_A + (10/m_F)·κ(0)`.
* **`kern_pair_lower`** (the Lean form of (M1)): for unit vectors `x, x′`,
  `E_{A,F} kern F A A x x′ ≥ (4/n)·[κ^{∘4}(⟨x, x′⟩) − eA]`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131

variable {N mW n mA mF : ℕ}

/-- The two hidden layers of `F`, for fixed inputs `y, y′`. -/
theorem KF_lower (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    Integrable (fun F : MlpParam n mF 1 =>
      2 / (mF : ℝ) * dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y')) (mlpGauss n mF 1) ∧
    2 / (n : ℝ) * (psi (kappa ∘ kappa) y y' - 10 / (mF : ℝ) * kappa 0 * (nrm y * nrm y')) ≤
      ∫ F : MlpParam n mF 1, 2 / (mF : ℝ) * dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y')
        ∂mlpGauss n mF 1 := by
  have hmF' : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi := hid2_dot_integrable (m₁ := mF) (m₂ := mF) (two_div_nonneg n) (two_div_nonneg mF) y y'
  have hl := hid2_dot_lower (m₁ := mF) (m₂ := mF) (two_div_nonneg n) (two_div_nonneg mF) hmF y y'
  have hi' : Integrable (fun F : MlpParam n mF 1 => dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y'))
      (mlpGauss n mF 1) := by
    unfold mlpGauss; exact integrable_drop3 hi
  have he : ∫ F : MlpParam n mF 1, dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') ∂mlpGauss n mF 1 =
      ∫ θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ,
        dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y')
        ∂((gaussMat mF n (2 / (n : ℝ))).prod (gaussMat mF mF (2 / (mF : ℝ)))) := by
    unfold mlpGauss; exact integral_drop3 hi.aestronglyMeasurable
  refine ⟨hi'.const_mul _, ?_⟩
  rw [integral_const_mul, he]
  have h2 := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 2 / (mF : ℝ))
  refine le_trans (le_of_eq ?_) h2
  field_simp

/-- The error of the lower bound through `A` and `F`. -/
noncomputable def eA (n mA mF : ℕ) : ℝ :=
  4 / (n : ℝ) * kappa (kappa 0) + 20 / (mA : ℝ) + 10 / (mF : ℝ) * kappa 0

lemma kern_abs_le_diag (F : MlpParam n mF 1) (a : MlpParam n mA n) (x x' : Fin n → ℝ) :
    |kern F a a x x'| ≤ kern F a a x x + kern F a a x' x' := by
  unfold kern
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (mF : ℝ)), dotp_self, dotp_self,
    ← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_dotp_le _ _) (by positivity)

lemma kern_pair_integrable (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) (x x' : Fin n → ℝ) :
    Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x')
      ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) := by
  have hmeas : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x') :=
    measurable_kern_comp (measurable_snd.comp measurable_snd) measurable_fst measurable_fst
      measurable_const measurable_const
  exact Integrable.mono' ((kern_diag_gen hn hmA hmF x).1.add (kern_diag_gen hn hmA hmF x').1)
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => kern_abs_le_diag _ _ _ _)

lemma agent_arith {n' I1 I2 Ψ q c d a : ℝ} (hn : 0 < n') (hc : 0 ≤ c)
    (h1 : 2 * n' / n' * (Ψ - (4 / n' * q + a) * (1 * 1)) ≤ I1)
    (h2 : I2 ≤ 2 * n' / n' * (1 * 1)) (hd : d = 2 / n' * (I1 - c * I2)) :
    4 / n' * (Ψ - (4 / n' * q + a + c)) ≤ d := by
  have e : 2 * n' / n' = 2 := by field_simp
  rw [e] at h1 h2
  have h3 := mul_le_mul_of_nonneg_left h2 hc
  have h4 : 2 * (Ψ - (4 / n' * q + a) - c) ≤ I1 - c * I2 := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 / n')
  rw [hd]
  calc 4 / n' * (Ψ - (4 / n' * q + a + c)) = 2 / n' * (2 * (Ψ - (4 / n' * q + a) - c)) := by ring
    _ ≤ _ := h5

/-- **The lower bound through `A` and `F`** (paper (M1)): for unit vectors `x, x′`,
`E_{A,F} (2/m_F)⟨H_A(x), H_A(x′)⟩ ≥ (4/n)·[κ^{∘4}(⟨x, x′⟩) − eA n m_A m_F]`. -/
theorem kern_pair_lower (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    4 / (n : ℝ) * (kappa^[4] (dotp x x') - eA n mA mF) ≤
      ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kern p.2.2 p.1 p.1 x x'
        ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmF' : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  obtain ⟨hPi, hPl⟩ := mlp_psi_lower (k := n) (q := n) hG hmA hn x x'
  obtain ⟨hNi, hNu⟩ := mlp_nrm_upper (k := n) (q := n) hmA x x'
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (by norm_num) (by norm_num)).1
  have hgi : Integrable (fun a : MlpParam n mA n => 2 / (n : ℝ) *
      (psi (kappa ∘ kappa) (mlpEval a x) (mlpEval a x') - 10 / (mF : ℝ) * kappa 0 *
        (nrm (mlpEval a x) * nrm (mlpEval a x')))) (mlpGauss n mA n) :=
    (hPi.sub (hNi.const_mul _)).const_mul _
  have key := integral_prod_ge (kern_pair_integrable hn hmA hmF x x') hgi (fun a => by
    have h := (KF_lower (mF := mF) hn hmF (mlpEval a x) (mlpEval a x')).2
    have e : ∫ y : MlpParam n mA n × MlpParam n mF 1, kern y.2 a a x x'
        ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) =
        ∫ F : MlpParam n mF 1, kern F a a x x' ∂mlpGauss n mF 1 := by
      rw [integral_fun_snd (fun F : MlpParam n mF 1 => kern F a a x x')]
      simp
    rw [e]
    exact h)
  refine le_trans ?_ key
  have a1 : ∫ a : MlpParam n mA n, 2 / (n : ℝ) *
      (psi (kappa ∘ kappa) (mlpEval a x) (mlpEval a x') - 10 / (mF : ℝ) * kappa 0 *
        (nrm (mlpEval a x) * nrm (mlpEval a x'))) ∂mlpGauss n mA n =
      2 / (n : ℝ) * ∫ a : MlpParam n mA n,
      (psi (kappa ∘ kappa) (mlpEval a x) (mlpEval a x') - 10 / (mF : ℝ) * kappa 0 *
        (nrm (mlpEval a x) * nrm (mlpEval a x'))) ∂mlpGauss n mA n := integral_const_mul _ _
  have a2 := integral_sub hPi (hNi.const_mul (10 / (mF : ℝ) * kappa 0))
  have a3 : ∫ a : MlpParam n mA n, 10 / (mF : ℝ) * kappa 0 *
      (nrm (mlpEval a x) * nrm (mlpEval a x')) ∂mlpGauss n mA n =
      10 / (mF : ℝ) * kappa 0 * ∫ a : MlpParam n mA n,
      nrm (mlpEval a x) * nrm (mlpEval a x') ∂mlpGauss n mA n := integral_const_mul _ _
  beta_reduce at a2
  rw [a2, a3] at a1
  rw [nrm_of_normSq_one hx, nrm_of_normSq_one hx'] at hPl hNu
  have hpsi : psi (kappa ∘ kappa ∘ kappa ∘ kappa) x x' = kappa^[4] (dotp x x') :=
    psi_unit _ hx hx'
  have hq : (kappa ∘ kappa) 0 = kappa (kappa 0) := rfl
  have hPl' : 2 * (n : ℝ) / n * (psi (kappa ∘ kappa ∘ kappa ∘ kappa) x x' -
      (4 / (n : ℝ) * (kappa ∘ kappa) 0 + 20 / (mA : ℝ)) * (1 * 1)) ≤ _ := hPl
  rw [hpsi, hq] at hPl'
  have := agent_arith hn' (by positivity : (0 : ℝ) ≤ 10 / (mF : ℝ) * kappa 0) hPl' hNu a1
  unfold eA
  exact this

end BstLean.Part132

open BstLean.Part132 in
#print axioms kern_pair_lower
