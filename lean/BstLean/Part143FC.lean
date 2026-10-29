import BstLean.Part142FD
import BstLean.Part142ReluD

/-!
# Part 143: the split of the link of `F` into a centred part and a remainder

For `y, y′ : ℝⁿ`, `h₁ = ReLU(F₁ y)`, `H(y) = hid2 F₁ F₂ y = ReLU(F₂ h₁)`:

* `cF0 F₁ F₂ y y′ = (2/m_F)·[e(H(y), H(y′)) − Φ_κ(h₁, h₁′)]` (the centred part: its mean over
  `F₂` is exactly `0`, `cF0_integral`), with
  `‖cF0‖_{L²(F₁, F₂)} ≤ (2/n)·f1a·|y − y′|²`, `f1a = √3/√m_F + 6/m_F` (`cF0_L2`, `cF_L2`).
* `rF0 F₁ y y′ = (2/m_F)·Φ_κ(h₁, h₁′) − (2/n)·Φ_{κ∘κ}(y, y′)` (reads `F₁` only), with
  `‖rF0‖_{L²(F₁)} ≤ (2/n)·(f1b·|y − y′|² + f2·(|y|² + |y′|²) + f3·||y|² − |y′|²| + f4·δ(y, y′))`,
  `f1b = √3/√m_F` (`rF0_L2`, `rF_L2`).
* `cF_add_rF`: the sum is `(2/m_F)·e(H(y), H(y′)) − (2/n)·Φ_{κ∘κ}(y, y′)`; `f1a + f1b = f1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142

/-- The coefficient of `|y − y′|²` in the centred part of the link of `F`. -/
noncomputable def f1a (mF : ℕ) : ℝ := √3 / √(mF : ℝ) + 6 / (mF : ℝ)

/-- The coefficient of `|y − y′|²` in the remainder of the link of `F`. -/
noncomputable def f1b (mF : ℕ) : ℝ := √3 / √(mF : ℝ)

lemma f1a_nonneg (mF : ℕ) : 0 ≤ f1a mF := by unfold f1a; positivity

lemma f1b_nonneg (mF : ℕ) : 0 ≤ f1b mF := by unfold f1b; positivity

lemma f1a_add_f1b (mF : ℕ) : f1a mF + f1b mF = f1 mF := by
  unfold f1a f1b f1; ring

variable {n mF : ℕ}

/-- The centred part of the link of `F`: `(2/m_F)·[e(H(y), H(y′)) − Φ_κ(h₁, h₁′)]`. -/
noncomputable def cF0 (F₁ : Matrix (Fin mF) (Fin n) ℝ) (F₂ : Matrix (Fin mF) (Fin mF) ℝ)
    (y y' : Fin n → ℝ) : ℝ :=
  2 / (mF : ℝ) * (eD (hid2 F₁ F₂ y) (hid2 F₁ F₂ y') -
    phiD kappa (reluV (F₁.mulVec y)) (reluV (F₁.mulVec y')))

/-- The remainder of the link of `F`: `(2/m_F)·Φ_κ(h₁, h₁′) − (2/n)·Φ_{κ∘κ}(y, y′)`. -/
noncomputable def rF0 (F₁ : Matrix (Fin mF) (Fin n) ℝ) (y y' : Fin n → ℝ) : ℝ :=
  2 / (mF : ℝ) * phiD kappa (reluV (F₁.mulVec y)) (reluV (F₁.mulVec y')) -
    2 / (n : ℝ) * phiD (kappa ∘ kappa) y y'

/-- `cF0` as a function of the weights of `F` (it does not read the last matrix). -/
noncomputable def cF (F : MlpParam n mF 1) (y y' : Fin n → ℝ) : ℝ := cF0 F.1 F.2.1 y y'

/-- `rF0` as a function of the weights of `F` (it reads the first matrix only). -/
noncomputable def rF (F : MlpParam n mF 1) (y y' : Fin n → ℝ) : ℝ := rF0 F.1 y y'

lemma cF_add_rF (F : MlpParam n mF 1) (y y' : Fin n → ℝ) :
    cF F y y' + rF F y y' =
      2 / (mF : ℝ) * eD (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') -
        2 / (n : ℝ) * phiD (kappa ∘ kappa) y y' := by
  unfold cF rF cF0 rF0; ring

/-! ## Measurability -/

lemma measurable_phiD_pair {ι : Type*} [Fintype ι] {G : ℝ → ℝ} (hG : Continuous G) :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) => phiD G p.1 p.2) := by
  unfold phiD
  exact (((continuous_normSq.comp continuous_fst).add
    (continuous_normSq.comp continuous_snd)).measurable.div_const 2).sub (measurable_psi hG)

lemma continuous_eD_pair {ι : Type*} [Fintype ι] :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => eD p.1 p.2) := by
  have e : (fun p : (ι → ℝ) × (ι → ℝ) => eD p.1 p.2) =
      fun p => normSq (p.1 - p.2) / 2 := by
    funext p; exact eD_eq _ _
  rw [e]
  exact (continuous_normSq.comp (continuous_fst.sub continuous_snd)).div_const 2

lemma continuous_hid1_joint :
    Continuous (fun p : Matrix (Fin mF) (Fin n) ℝ × (Fin n → ℝ) => reluV (p.1.mulVec p.2)) :=
  continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_snd)

lemma measurable_rF0 :
    Measurable (fun p : Matrix (Fin mF) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      rF0 p.1 p.2.1 p.2.2) := by
  unfold rF0
  have c1 : Continuous (fun p : Matrix (Fin mF) (Fin n) ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      (reluV (p.1.mulVec p.2.1), reluV (p.1.mulVec p.2.2))) :=
    (continuous_hid1_joint.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_hid1_joint.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  exact (((measurable_phiD_pair continuous_kappa).comp c1.measurable).const_mul _).sub
    (((measurable_phiD_pair (continuous_kappa.comp continuous_kappa)).comp
      measurable_snd).const_mul _)

lemma measurable_cF0 :
    Measurable (fun p : (Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
      (Fin n → ℝ) × (Fin n → ℝ) => cF0 p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold cF0
  have h1 : ∀ g : (Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
      (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ), Continuous g →
      Continuous (fun p : (Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
        (Fin n → ℝ) × (Fin n → ℝ) => reluV (p.1.1.mulVec (g p))) := fun g hg =>
    continuous_reluV.comp (Continuous.matrix_mulVec (continuous_fst.comp continuous_fst) hg)
  have h2 : ∀ g : (Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
      (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ), Continuous g →
      Continuous (fun p : (Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
        (Fin n → ℝ) × (Fin n → ℝ) => hid2 p.1.1 p.1.2 (g p)) := fun g hg => by
    unfold hid2
    exact continuous_reluV.comp
      (Continuous.matrix_mulVec (continuous_snd.comp continuous_fst) (h1 g hg))
  have cy : Continuous (fun p : (Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
      (Fin n → ℝ) × (Fin n → ℝ) => p.2.1) := continuous_fst.comp continuous_snd
  have cy' : Continuous (fun p : (Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ) ×
      (Fin n → ℝ) × (Fin n → ℝ) => p.2.2) := continuous_snd.comp continuous_snd
  exact (((continuous_eD_pair.comp ((h2 _ cy).prodMk (h2 _ cy'))).measurable).sub
    ((measurable_phiD_pair continuous_kappa).comp
      ((h1 _ cy).prodMk (h1 _ cy')).measurable)).const_mul _

lemma measurable_cF :
    Measurable (fun p : MlpParam n mF 1 × (Fin n → ℝ) × (Fin n → ℝ) => cF p.1 p.2.1 p.2.2) :=
  measurable_cF0.comp (f := fun p : MlpParam n mF 1 × (Fin n → ℝ) × (Fin n → ℝ) =>
    ((p.1.1, p.1.2.1), p.2)) (by fun_prop)

lemma measurable_rF :
    Measurable (fun p : MlpParam n mF 1 × (Fin n → ℝ) × (Fin n → ℝ) => rF p.1 p.2.1 p.2.2) :=
  measurable_rF0.comp (f := fun p : MlpParam n mF 1 × (Fin n → ℝ) × (Fin n → ℝ) =>
    (p.1.1, p.2)) (by fun_prop)

/-! ## The exact mean of the centred part -/

/-- **The centred part has mean zero over `F₂`**, for every `F₁`, `y`, `y′`. -/
theorem cF0_integral (hmF : 1 ≤ mF) (F₁ : Matrix (Fin mF) (Fin n) ℝ) (y y' : Fin n → ℝ) :
    Integrable (fun F₂ : Matrix (Fin mF) (Fin mF) ℝ => cF0 F₁ F₂ y y')
        (gaussMat mF mF (2 / (mF : ℝ))) ∧
      ∫ F₂, cF0 F₁ F₂ y y' ∂gaussMat mF mF (2 / (mF : ℝ)) = 0 := by
  have hm0 : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hv : (0 : ℝ) ≤ 2 / (mF : ℝ) := by positivity
  set h := reluV (F₁.mulVec y) with hh
  set h' := reluV (F₁.mulVec y') with hh'
  obtain ⟨iD, eDd⟩ := layer_dot_relu (m := mF) hv h h'
  obtain ⟨i1, e1⟩ := layer_relu_sq (m := mF) hv h
  obtain ⟨i2, e2⟩ := layer_relu_sq (m := mF) hv h'
  have iE : Integrable (fun F₂ : Matrix (Fin mF) (Fin mF) ℝ =>
      (normSq (reluV (F₂.mulVec h)) + normSq (reluV (F₂.mulVec h'))) / 2 -
        dotp (reluV (F₂.mulVec h)) (reluV (F₂.mulVec h'))) (gaussMat mF mF (2 / (mF : ℝ))) :=
    ((i1.add i2).div_const 2).sub iD
  have s1 : ∫ F₂ : Matrix (Fin mF) (Fin mF) ℝ,
      ((normSq (reluV (F₂.mulVec h)) + normSq (reluV (F₂.mulVec h'))) / 2 -
        dotp (reluV (F₂.mulVec h)) (reluV (F₂.mulVec h'))) ∂gaussMat mF mF (2 / (mF : ℝ)) =
      ((mF : ℝ) / 2 * (2 / (mF : ℝ) * normSq h) + (mF : ℝ) / 2 * (2 / (mF : ℝ) * normSq h')) / 2 -
        (mF : ℝ) / 2 * (2 / (mF : ℝ) * kernelPhi h h') := by
    have iS : Integrable (fun F₂ : Matrix (Fin mF) (Fin mF) ℝ =>
        normSq (reluV (F₂.mulVec h)) + normSq (reluV (F₂.mulVec h')))
        (gaussMat mF mF (2 / (mF : ℝ))) := i1.add i2
    have iH : Integrable (fun F₂ : Matrix (Fin mF) (Fin mF) ℝ =>
        (normSq (reluV (F₂.mulVec h)) + normSq (reluV (F₂.mulVec h'))) / 2)
        (gaussMat mF mF (2 / (mF : ℝ))) := iS.div_const 2
    rw [integral_sub iH iD, integral_div, integral_add i1 i2, e1, e2, eDd]
  have efun : (fun F₂ : Matrix (Fin mF) (Fin mF) ℝ => cF0 F₁ F₂ y y') =
      fun F₂ => 2 / (mF : ℝ) * (((normSq (reluV (F₂.mulVec h)) +
        normSq (reluV (F₂.mulVec h'))) / 2 -
        dotp (reluV (F₂.mulVec h)) (reluV (F₂.mulVec h'))) - phiD kappa h h') := by
    funext F₂; rfl
  rw [efun]
  refine ⟨(iE.sub (integrable_const _)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub iE (integrable_const _), s1, integral_const,
    kernelPhi_eq_psi]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold phiD
  field_simp
  ring

/-- The same, over the last two matrices of `F`. -/
theorem cF_integral_tail (hmF : 1 ≤ mF) (F₁ : Matrix (Fin mF) (Fin n) ℝ) (y y' : Fin n → ℝ) :
    ∫ θ : Matrix (Fin mF) (Fin mF) ℝ × Matrix (Fin 1) (Fin mF) ℝ, cF (F₁, θ) y y'
      ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) = 0 := by
  have h := integral_fun_fst (μ := gaussMat mF mF (2 / (mF : ℝ)))
    (ν := gaussMat 1 mF (2 / (mF : ℝ))) (fun F₂ : Matrix (Fin mF) (Fin mF) ℝ => cF0 F₁ F₂ y y')
  rw [(cF0_integral hmF F₁ y y').2] at h
  refine Eq.trans h ?_
  simp

/-! ## The two `L²` bounds -/

/-- **The centred part in `L²`**, on the product of the two Gaussian matrices. -/
theorem cF0_L2 (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    L2le ((gaussMat mF n (2 / (n : ℝ))).prod (gaussMat mF mF (2 / (mF : ℝ))))
      (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ => cF0 θ.1 θ.2 y y')
      (2 / (n : ℝ) * (f1a mF * normSq (y - y'))) := by
  have hRE : ReluEDStmt := reluEDStmt
  have hm0 : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hv2 : (0 : ℝ) < 2 / (mF : ℝ) := by positivity
  set s : ℝ := √(mF : ℝ) with hsd
  set t : ℝ := √3 with htd
  have hs0 : 0 < s := Real.sqrt_pos.mpr hm0
  have hss : s * s = (mF : ℝ) := Real.mul_self_sqrt hm0.le
  have htt : t * t = 3 := Real.mul_self_sqrt (by norm_num)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  set N : ℝ := normSq (y - y') with hN
  have hN0 : 0 ≤ N := normSq_nonneg _
  have hE1 := hRE (m := mF) (k := n) hv1 hmF y y'
  set c : ℝ := (mF : ℝ) / 2 * (2 / (n : ℝ)) * phiD kappa y y' with hc
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (phiD_kappa_nonneg y y')
  have hcle : c ≤ (mF : ℝ) / 2 * (2 / (n : ℝ)) * (N / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hN, ← eD_eq]
    exact phiD_kappa_le_eD y y'
  have hcc : L2le (gaussMat mF n (2 / (n : ℝ))) (fun _ : Matrix (Fin mF) (Fin n) ℝ => c) |c| :=
    L2le.const c
  rw [abs_of_nonneg hc0] at hcc
  set K : ℝ := t / 2 * s * (2 / (mF : ℝ)) * 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hE1' : L2le (gaussMat mF n (2 / (n : ℝ)))
      (fun M : Matrix (Fin mF) (Fin n) ℝ =>
        eD (reluV (M.mulVec y)) (reluV (M.mulVec y')) - c)
      (t / 2 * s * (2 / (n : ℝ)) * N) := hE1
  have hg0 := ((hE1'.add0 hcc (by positivity) hc0).const_mul_nonneg hK0).mono
    (by positivity)
    (show K * (t / 2 * s * (2 / (n : ℝ)) * N + c) ≤
      K * (t / 2 * s * (2 / (n : ℝ)) * N + (mF : ℝ) / 2 * (2 / (n : ℝ)) * (N / 2)) from
      mul_le_mul_of_nonneg_left (by linarith) hK0)
  have eK : K * (t / 2 * s * (2 / (n : ℝ)) * N + (mF : ℝ) / 2 * (2 / (n : ℝ)) * (N / 2)) =
      6 * (N / (n : ℝ)) + t * s * (N / (n : ℝ)) := by
    have e : K * (t / 2 * s * (2 / (n : ℝ)) * N + (mF : ℝ) / 2 * (2 / (n : ℝ)) * (N / 2)) =
        (t * t) * ((s * s) / (mF : ℝ)) * (2 * (N / (n : ℝ))) +
          t * s * (N / (n : ℝ)) * ((mF : ℝ) / (mF : ℝ)) := by
      rw [hK]; ring
    rw [e, htt, hss, div_self hm0.ne']
    ring
  have hg : L2le (gaussMat mF n (2 / (n : ℝ)))
      (fun M₁ : Matrix (Fin mF) (Fin n) ℝ => t / 2 * s * (2 / (mF : ℝ)) *
        normSq (reluV (M₁.mulVec y) - reluV (M₁.mulVec y')))
      (6 * (N / (n : ℝ)) + t * s * (N / (n : ℝ))) := by
    refine (hg0.congr_fun fun M₁ => ?_).congr_bound eK
    rw [eD_eq, hK]
    ring
  have mA : Measurable (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
      cF0 θ.1 θ.2 y y') :=
    measurable_cF0.comp (f := fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
      (θ, (y, y'))) (by fun_prop)
  have hA : L2le ((gaussMat mF n (2 / (n : ℝ))).prod (gaussMat mF mF (2 / (mF : ℝ))))
      (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
        eD (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
          (mF : ℝ) / 2 * (2 / (mF : ℝ)) *
            phiD kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y')))
      (6 * (N / (n : ℝ)) + t * s * (N / (n : ℝ))) := by
    have mA' : Measurable (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
        eD (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
          (mF : ℝ) / 2 * (2 / (mF : ℝ)) *
            phiD kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y'))) := by
      have e : (fun θ : Matrix (Fin mF) (Fin n) ℝ × Matrix (Fin mF) (Fin mF) ℝ =>
          eD (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
            (mF : ℝ) / 2 * (2 / (mF : ℝ)) *
              phiD kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y'))) =
          fun θ => (mF : ℝ) / 2 * cF0 θ.1 θ.2 y y' := by
        funext θ
        unfold cF0
        field_simp
      rw [e]
      exact mA.const_mul _
    refine L2le.prod' mA'.aestronglyMeasurable hg (Filter.Eventually.of_forall fun M₁ => ?_)
    exact hRE (m := mF) (k := mF) hv2 hmF (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))
  have h := hA.const_mul_nonneg (c := 2 / (mF : ℝ)) (by positivity)
  refine (h.congr_fun fun θ => ?_).congr_bound ?_
  · unfold cF0
    field_simp
  · unfold f1a
    rw [← hsd, ← htd]
    have hm2 : (mF : ℝ) = s ^ 2 := by rw [← hss]; ring
    rw [hm2]
    field_simp
    ring

/-- **The remainder in `L²`**, over the first matrix of `F`. -/
theorem rF0_L2 (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    L2le (gaussMat mF n (2 / (n : ℝ)))
      (fun F₁ : Matrix (Fin mF) (Fin n) ℝ => rF0 F₁ y y')
      (2 / (n : ℝ) * (f1b mF * normSq (y - y') + f2 mF * (normSq y + normSq y') +
        f3 mF * |normSq y - normSq y'| + f4 * dlt y y')) := by
  have hm0 : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv1 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs0 : 0 < √(mF : ℝ) := Real.sqrt_pos.mpr hm0
  have hB := (reluPhiStmt (m := mF) (k := n) kGood_kappa hv1 hmF y y').const_mul_nonneg
    (c := 2 / (mF : ℝ)) (by positivity)
  refine (hB.congr_fun fun F₁ => ?_).congr_bound ?_
  · unfold rF0
    field_simp
  · unfold f1b f2 f3 f4
    field_simp
    ring

/-- **The centred part in `L²`**, over the weights of `F`. -/
theorem cF_L2 (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    L2le (mlpGauss n mF 1) (fun F : MlpParam n mF 1 => cF F y y')
      (2 / (n : ℝ) * (f1a mF * normSq (y - y'))) :=
  (cF0_L2 hn hmF y y').comp_map (P := mlpGauss n mF 1)
    (φ := fun θ : MlpParam n mF 1 => (θ.1, θ.2.1)) (by fun_prop)
    (by unfold mlpGauss; exact map_drop3)

/-- **The remainder in `L²`**, over the weights of `F`. -/
theorem rF_L2 (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    L2le (mlpGauss n mF 1) (fun F : MlpParam n mF 1 => rF F y y')
      (2 / (n : ℝ) * (f1b mF * normSq (y - y') + f2 mF * (normSq y + normSq y') +
        f3 mF * |normSq y - normSq y'| + f4 * dlt y y')) := by
  unfold mlpGauss
  exact (rF0_L2 hn hmF y y').comp_fst

end BstLean.Part143

open BstLean.Part143 in
#print axioms cF0_integral
open BstLean.Part143 in
#print axioms cF_integral_tail
open BstLean.Part143 in
#print axioms cF_L2
open BstLean.Part143 in
#print axioms rF_L2
open BstLean.Part143 in
#print axioms measurable_cF
