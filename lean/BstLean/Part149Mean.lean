import BstLean.Part149Defs

/-!
# Part 149, helper `Mean`: the means of the kernel error and of the diagonal error

Role: `delegations/statements/p149-spec.md`.

Do not use `sorry`, `native_decide` or `axiom`.

* `measurable_errKc`, `measurable_errDc`, `measurable_bbar`, `measurable_tauOut`: the joint
  measurability of the four quantities of `Part149Defs` in the centre, the scalar and the hidden
  weights.
* `errD_mean`: `E_θ errDc c τ θ ≤ ((m/n)·cF2o m)²` for every centre `c` and every scalar `τ`.
* `errK_mean`: `E_ξ E_θ errKc ((m/n)·κ(κ(q))) (β·ξ) τ θ ≤ ((m/n)·(cF2o m + (1 − q²)/√n + jCosC n))²`
  with `q = β²/(β² + τ²)`; the centre is the Gaussian vector `β·ξ`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 BstLean.Part145

variable {n m : ℕ}

/-! ## Joint measurability -/

/-- The last hidden vector is jointly measurable in the centre, the scalar, the hidden weights
and the Gaussian vector. -/
lemma measurable_hA_joint :
    Measurable (fun z : (((Fin n → ℝ) × ℝ) × HidParam n m) × (Fin n → ℝ) =>
      hA z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have h1 : Measurable (fun z : (((Fin n → ℝ) × ℝ) × HidParam n m) × (Fin n → ℝ) =>
      z.1.1.1 + z.1.1.2 • z.2) :=
    (by fun_prop : Continuous fun z : (((Fin n → ℝ) × ℝ) × HidParam n m) × (Fin n → ℝ) =>
      z.1.1.1 + z.1.1.2 • z.2).measurable
  exact continuous_hid2_joint.measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp h1))

lemma measurable_errKc :
    Measurable (fun x : (ℝ × (Fin n → ℝ) × ℝ) × HidParam n m =>
      errKc x.1.1 x.1.2.1 x.1.2.2 x.2) := by
  have e1 : Measurable (fun z : ((ℝ × (Fin n → ℝ) × ℝ) × HidParam n m) ×
      ((Fin n → ℝ) × (Fin n → ℝ)) => hA z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.1) :=
    measurable_hA_joint.comp
      ((((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)).comp
        (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)
        |>.prodMk (measurable_fst.comp measurable_snd))
  have e2 : Measurable (fun z : ((ℝ × (Fin n → ℝ) × ℝ) × HidParam n m) ×
      ((Fin n → ℝ) × (Fin n → ℝ)) => hA z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.2) :=
    measurable_hA_joint.comp
      ((((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)).comp
        (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)
        |>.prodMk (measurable_snd.comp measurable_snd))
  have mf : Measurable (fun z : ((ℝ × (Fin n → ℝ) × ℝ) × HidParam n m) ×
      ((Fin n → ℝ) × (Fin n → ℝ)) =>
      (∑ k, hA z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.1 k * hA z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.2 k -
        z.1.1.1) ^ 2) :=
    ((Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp e1).mul ((measurable_pi_apply k).comp e2)).sub
        (measurable_fst.comp (measurable_fst.comp measurable_fst))).pow_const 2
  exact (mf.stronglyMeasurable.integral_prod_right'
    (ν := (stdGauss (Fin n)).prod (stdGauss (Fin n)))).measurable

lemma measurable_errDc :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => errDc x.1.1 x.1.2 x.2) := by
  have mf : Measurable (fun z : (((Fin n → ℝ) × ℝ) × HidParam n m) × (Fin n → ℝ) =>
      (normSq (hA z.1.1.1 z.1.1.2 z.1.2 z.2) - (m : ℝ) / n) ^ 2) :=
    ((continuous_normSq.measurable.comp measurable_hA_joint).sub measurable_const).pow_const 2
  exact (mf.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

lemma measurable_bbar :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => bbar x.1.1 x.1.2 x.2) := by
  refine measurable_pi_iff.mpr fun j => ?_
  have mf : Measurable (fun z : (((Fin n → ℝ) × ℝ) × HidParam n m) × (Fin n → ℝ) =>
      hA z.1.1.1 z.1.1.2 z.1.2 z.2 j) := (measurable_pi_apply j).comp measurable_hA_joint
  exact (mf.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

lemma measurable_tauOut :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => tauOut x.1.1 x.1.2 x.2) := by
  unfold tauOut
  exact Real.continuous_sqrt.measurable.comp (measurable_const.max
    (measurable_const.sub (measurable_const.mul
      (continuous_normSq.measurable.comp measurable_bbar))))

/-! ## From real integrals to lower integrals -/

/-- For a nonnegative real function, `ofReal` of the Bochner integral is at most the lower
integral (with equality if the function is integrable). -/
lemma ofReal_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ)
    (h : ∀ x, 0 ≤ g x) :
    ENNReal.ofReal (∫ x, g x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  by_cases hi : Integrable g μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall h)).le
  · rw [integral_undef hi]
    simp

/-! ## The mean of the diagonal error -/

/-- **The mean of the diagonal error over the hidden weights**, for every centre and scalar. -/
theorem errD_mean (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) :
    ∫⁻ θ, ENNReal.ofReal (errDc c τ θ) ∂hidGauss n m ≤
      ENNReal.ofReal (((m : ℝ) / n * cF2o m) ^ 2) := by
  have g := gramD_L2 (stdGauss (Fin n)) hn hm (m := m) (X := fun γ => sphPt (c + τ • γ))
    (measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ)))
    (fun _ => normSq_sphPt hn _)
  have mG : AEMeasurable (fun z : (Fin n → ℝ) × HidParam n m =>
      ENNReal.ofReal ((normSq (hid2 z.2.1 z.2.2 (sphPt (c + τ • z.1))) - (m : ℝ) / n) ^ 2))
      ((stdGauss (Fin n)).prod (hidGauss n m)) :=
    (g.aesm.aemeasurable.pow_const 2).ennreal_ofReal
  calc ∫⁻ θ, ENNReal.ofReal (errDc c τ θ) ∂hidGauss n m
      ≤ ∫⁻ θ, ∫⁻ γ, ENNReal.ofReal
          ((normSq (hid2 θ.1 θ.2 (sphPt (c + τ • γ))) - (m : ℝ) / n) ^ 2)
            ∂stdGauss (Fin n) ∂hidGauss n m :=
        lintegral_mono fun θ => ofReal_integral_le _ _ fun _ => sq_nonneg _
    _ = ∫⁻ z, ENNReal.ofReal
          ((normSq (hid2 z.2.1 z.2.2 (sphPt (c + τ • z.1))) - (m : ℝ) / n) ^ 2)
            ∂((stdGauss (Fin n)).prod (hidGauss n m)) := (lintegral_prod_symm _ mG).symm
    _ = ENNReal.ofReal (∫ z, (normSq (hid2 z.2.1 z.2.2 (sphPt (c + τ • z.1))) - (m : ℝ) / n) ^ 2
            ∂((stdGauss (Fin n)).prod (hidGauss n m))) :=
        (ofReal_integral_eq_lintegral_ofReal g.int_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (((m : ℝ) / n * cF2o m) ^ 2) := ENNReal.ofReal_le_ofReal g.le

/-! ## The mean of the kernel error -/

/-- **The mean of the kernel error over the hidden weights and over a Gaussian centre** `β·ξ`;
`q = β²/(β² + τ²)`. -/
theorem errK_mean (hn : 1 ≤ n) (hm : 1 ≤ m) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal
        (errKc ((m : ℝ) / n * kappa (kappa (β ^ 2 / (β ^ 2 + τ ^ 2)))) (β • ξ) τ θ)
          ∂hidGauss n m) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (((m : ℝ) / n *
        (cF2o m + ((1 - (β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) / √(n : ℝ) + jCosC n))) ^ 2) := by
  have g := errK_L2 (m := m) hn hm hβ hτ
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (m : ℝ) / n * kappa (kappa (β ^ 2 / (β ^ 2 + τ ^ 2))) := ⟨_, rfl⟩
  rw [← ha] at g ⊢
  obtain ⟨G, hG⟩ : ∃ G : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m → ENNReal,
      G = fun z => ENNReal.ofReal
        ((dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
          (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) - a) ^ 2) := ⟨_, rfl⟩
  have mG : Measurable G := by
    rw [hG]
    have m1 : Measurable (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1))) :=
      continuous_hid2_joint.measurable.comp
        (measurable_snd.prodMk ((measurable_cheapPt β τ).1.comp measurable_fst))
    have m2 : Measurable (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) :=
      continuous_hid2_joint.measurable.comp
        (measurable_snd.prodMk ((measurable_cheapPt β τ).2.comp measurable_fst))
    exact (((continuous_dotp.measurable.comp (m1.prodMk m2)).sub measurable_const).pow_const
      2).ennreal_ofReal
  have step : ∀ ξ : Fin n → ℝ, ∀ θ : HidParam n m,
      ENNReal.ofReal (errKc a (β • ξ) τ θ) ≤
        ∫⁻ p, G ((ξ, p), θ) ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
    intro ξ θ
    rw [hG]
    exact ofReal_integral_le _ _ fun _ => sq_nonneg _
  calc ∫⁻ ξ, (∫⁻ θ, ENNReal.ofReal (errKc a (β • ξ) τ θ) ∂hidGauss n m) ∂stdGauss (Fin n)
      ≤ ∫⁻ ξ, (∫⁻ θ, ∫⁻ p, G ((ξ, p), θ) ∂((stdGauss (Fin n)).prod (stdGauss (Fin n)))
          ∂hidGauss n m) ∂stdGauss (Fin n) :=
        lintegral_mono fun ξ => lintegral_mono fun θ => step ξ θ
    _ = ∫⁻ ξ, (∫⁻ p, ∫⁻ θ, G ((ξ, p), θ) ∂hidGauss n m
          ∂((stdGauss (Fin n)).prod (stdGauss (Fin n)))) ∂stdGauss (Fin n) := by
        refine lintegral_congr fun ξ => ?_
        exact lintegral_lintegral_swap
          (f := fun (θ : HidParam n m) (p : (Fin n → ℝ) × (Fin n → ℝ)) => G ((ξ, p), θ))
          (mG.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aemeasurable
    _ = ∫⁻ w, (∫⁻ θ, G (w, θ) ∂hidGauss n m)
          ∂((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n)))) :=
        (lintegral_prod (fun w => ∫⁻ θ, G (w, θ) ∂hidGauss n m)
          mG.lintegral_prod_right'.aemeasurable).symm
    _ = ∫⁻ z, G z ∂(((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n)))).prod
          (hidGauss n m)) := (lintegral_prod _ mG.aemeasurable).symm
    _ = ENNReal.ofReal (∫ z, (dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
          (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) - a) ^ 2
          ∂(((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n)))).prod
            (hidGauss n m))) := by
        rw [hG]
        exact (ofReal_integral_eq_lintegral_ofReal g.int_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal g.le

end BstLean.Part149

open BstLean.Part149 in
#print axioms measurable_errKc
open BstLean.Part149 in
#print axioms measurable_errDc
open BstLean.Part149 in
#print axioms measurable_bbar
open BstLean.Part149 in
#print axioms measurable_tauOut
open BstLean.Part149 in
#print axioms errD_mean
open BstLean.Part149 in
#print axioms errK_mean
