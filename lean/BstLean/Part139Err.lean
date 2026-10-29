import BstLean.Part138All

/-!
# Part 139, item 1: the error of the mean over the cheap stand-in, joint over `(W, A, F)`

Role: `delegations/statements/p139-spec.md`, item 1. Paper sources: `onW6c-cx.md` §§4, 6,
`onW17c-cx.md` §§5–6. The centre is the exact mean hidden vector `h̄` (NOT the arithmetic centre
of the programs).

* `gCheap W A F = E_{ν′_W} F(A(x))`: the exact mean of `F∘A` over the cheap stand-in `cheapW W`
  of Part 138 (the distribution of `sphPt(M₃h̄ + τ₀γ)`). No sampling.
* `phiS A F x = F(A(sphPt x))`: a bounded measurable function on `ℝⁿ` that is equal to `F∘A` on
  the unit sphere.
* `lint_phi_sq`: for a unit vector `x`: `E_{A,F} F(A(x))² = 4/n`.
* **`errFixed139`**: for fixed `(M₁, M₂) ∈ good136 n`:
  `E_{A,F} E_{M₃} (Bn − gCheap)² ≤ (2·(0.99/n) + 8·Hbar n ζ θ)·(4/n)`.
* **`errVec139_lint`**, **`errVec139`**: `E_{W,A,F}[1_good(W)·(gCheap − Bn)²] ≤
  (2·(0.99/n) + 8·EH n ζ)·(4/n)`; **`errVec139_num`**: with `3760·n/m_W` (at `ζ = 1/20`).
* **`errTail139`**: `Pr(W good and (gCheap − Bn)² ≥ s) ≤ (2·(0.99/n) + 8·EH n ζ)·(4/n)/s`.

The proof does not use a supremum norm of `F∘A`: `cheapStandIn138` of Part 138 with the free
constant `a = 0` has second moments on its right side, and the second moment of `F(A(x))` over
`(A, F)` is `4/n` for every unit vector `x`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138

/-! ## The bounded form of `F∘A` and the cheap estimate -/

section defs

variable {N m n mA mF : ℕ}

/-- `x ↦ F(A(x/|x|))`: equal to `F∘A` on the unit sphere, and bounded. -/
noncomputable def phiS (A : MlpParam n mA n) (F : MlpParam n mF 1) (x : Fin n → ℝ) : ℝ :=
  phiN A F (sphPt x)

/-- **The cheap estimate** `g₀(W, A, F) = E_{ν′_W} F(A(x))`: the exact mean of `F∘A` over the
cheap stand-in of `W` (Part 138: the distribution of `sphPt(M₃h̄ + τ₀γ)`). -/
noncomputable def gCheap (W : MlpParam N m n) (A : MlpParam n mA n) (F : MlpParam n mF 1) : ℝ :=
  ∫ x, phiN A F x ∂cheapW W

lemma sphPt_idem (hn : 1 ≤ n) (y : Fin n → ℝ) : sphPt (sphPt y) = sphPt y := by
  have h := normSq_sphPt hn y
  have h' : ∑ i, sphPt y i ^ 2 = 1 := h
  rw [sphPt_of_ne _ (by rw [h]; exact one_ne_zero)]
  unfold BstLean.Part105.sphProj
  rw [h']
  simp

lemma bm_phiS (hn : 1 ≤ n) (A : MlpParam n mA n) (F : MlpParam n mF 1) : BM (phiS A F) := by
  obtain ⟨C, hC⟩ := isCompact_unit.exists_bound_of_continuousOn
    (continuous_phiN A F).continuousOn
  refine ⟨(continuous_phiN A F).measurable.comp measurable_sphPt, C, fun x => ?_⟩
  have := hC (sphPt x) (normSq_sphPt hn x)
  rwa [Real.norm_eq_abs] at this

lemma integral_phiS_muWn (hn : 1 ≤ n) (W : MlpParam N m n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) : ∫ x, phiS A F x ∂muWn W = Bn W A F := by
  unfold Bn muWn
  rw [integral_map (measurable_sphPt_mlpEval W).aemeasurable
      (bm_phiS hn A F).meas.aestronglyMeasurable,
    integral_map (measurable_sphPt_mlpEval W).aemeasurable
      (continuous_phiN A F).measurable.aestronglyMeasurable]
  simp only [phiS, sphPt_idem hn]

lemma integral_phiS_cheapIn (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) :
    ∫ x, phiS A F x ∂cheapIn c τ = ∫ x, phiN A F x ∂cheapIn c τ := by
  rw [integral_cheapIn _ _ (bm_phiS hn A F).meas,
    integral_cheapIn _ _ (continuous_phiN A F).measurable]
  simp only [phiS, sphPt_idem hn]

/-- `g₀` is jointly measurable in `(W, A, F)`. -/
lemma measurable_gCheap (hN : 1 ≤ N) :
    Measurable (fun t : MlpParam N m n × MlpParam n mA n × MlpParam n mF 1 =>
      gCheap t.1 t.2.1 t.2.2) := by
  have hθ : Measurable (fun W : MlpParam N m n => ((W.1, W.2.1) : HidParam N m)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun W : MlpParam N m n => W.2.2.mulVec (hbarW (W.1, W.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp measurable_snd).prodMk ((measurable_hbarW hN).comp hθ))
  have hτ : Measurable (fun W : MlpParam N m n => tau0 N m (W.1, W.2.1)) :=
    (measurable_tau0 hN).comp hθ
  have hW : Measurable (fun q : (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) => q.1.1) := measurable_fst.comp measurable_fst
  have hj : Measurable (fun q : (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) => phiN q.1.2.1 q.1.2.2
        (sphPt (q.1.1.2.2.mulVec (hbarW (q.1.1.1, q.1.1.2.1)) +
          tau0 N m (q.1.1.1, q.1.1.2.1) • q.2))) :=
    BstLean.Part131.continuous_phiN_all.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_sphPt.comp ((hc.comp hW).add ((hτ.comp hW).smul measurable_snd))))
  have e : (fun t : MlpParam N m n × MlpParam n mA n × MlpParam n mF 1 =>
      gCheap t.1 t.2.1 t.2.2) = fun t => ∫ γ, phiN t.2.1 t.2.2
        (sphPt (t.1.2.2.mulVec (hbarW (t.1.1, t.1.2.1)) + tau0 N m (t.1.1, t.1.2.1) • γ))
        ∂stdGauss (Fin n) := by
    funext t
    unfold gCheap cheapW
    exact integral_cheapIn _ _ (continuous_phiN _ _).measurable
  rw [e]
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

end defs

/-! ## The second moment of `F(A(x))` over `(A, F)` -/

section second

variable {n mA mF : ℕ}

/-- **For a unit vector `x`: `E_{A,F} F(A(x))² = 4/n`** (as an integral of a nonnegative
function). -/
lemma lint_phi_sq (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {x : Fin n → ℝ}
    (hx : normSq x = 1) :
    ∫⁻ p : MlpParam n mA n × MlpParam n mF 1, ENNReal.ofReal (phiN p.1 p.2 x ^ 2)
      ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) = ENNReal.ofReal (4 / (n : ℝ)) := by
  have hm : Measurable (fun p : MlpParam n mA n × MlpParam n mF 1 =>
      ENNReal.ofReal (phiN p.1 p.2 x ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
      (measurable_id.prodMk measurable_const)).pow_const 2)
  rw [lintegral_prod _ hm.aemeasurable]
  have inner : ∀ A : MlpParam n mA n,
      ∫⁻ F : MlpParam n mF 1, ENNReal.ofReal (phiN A F x ^ 2) ∂mlpGauss n mF 1 =
        ENNReal.ofReal (2 * normSq (mlpEval A x) / n) := by
    intro A
    rw [← F_second_moment hmF (mlpEval A x)]
    exact (ofReal_integral_eq_lintegral_ofReal (F_sq_integrable (mlpEval A x))
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
  simp_rw [inner]
  have hi : Integrable (fun A : MlpParam n mA n => 2 * normSq (mlpEval A x) / n)
      (mlpGauss n mA n) := ((mlp_normSq_integrable x).const_mul 2).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun A => by
      have : 0 ≤ normSq (mlpEval A x) := Finset.sum_nonneg fun i _ => sq_nonneg _
      positivity)]
  congr 1
  have e : ∫ A : MlpParam n mA n, 2 * normSq (mlpEval A x) / n ∂mlpGauss n mA n =
      2 * (∫ A : MlpParam n mA n, normSq (mlpEval A x) ∂mlpGauss n mA n) / n := by
    rw [← integral_const_mul, ← integral_div]
  rw [e, agent_second_moment hn hmA x, hx]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

lemma measurable_phiS_out {o : Ω → Fin n → ℝ} (ho : Measurable o) :
    Measurable (fun q : (MlpParam n mA n × MlpParam n mF 1) × Ω => phiS q.1.1 q.1.2 (o q.2)) :=
  BstLean.Part131.continuous_phiN_all.measurable.comp
    (measurable_fst.prodMk (measurable_sphPt.comp (ho.comp measurable_snd)))

/-- The second moment of `F∘A` at the random point `o(ω)/|o(ω)|`, `ω ~ P`, as a function of
`(A, F)`. -/
noncomputable def Lout (o : Ω → Fin n → ℝ) (p : MlpParam n mA n × MlpParam n mF 1) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (phiS p.1 p.2 (o ω) ^ 2) ∂P

variable [IsProbabilityMeasure P]

lemma measurable_Lout {o : Ω → Fin n → ℝ} (ho : Measurable o) :
    Measurable (Lout (mA := mA) (mF := mF) P o) :=
  Measurable.lintegral_prod_right'
    (f := fun q : (MlpParam n mA n × MlpParam n mF 1) × Ω =>
      ENNReal.ofReal (phiS q.1.1 q.1.2 (o q.2) ^ 2))
    (ENNReal.measurable_ofReal.comp ((measurable_phiS_out ho).pow_const 2))

/-- The mean over `(A, F)` of the second moment is `4/n`, for every distribution of the
point. -/
lemma lintegral_Lout (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {o : Ω → Fin n → ℝ}
    (ho : Measurable o) :
    ∫⁻ p, Lout (mA := mA) (mF := mF) P o p ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) =
      ENNReal.ofReal (4 / (n : ℝ)) := by
  unfold Lout
  rw [lintegral_lintegral_swap
    (f := fun (p : MlpParam n mA n × MlpParam n mF 1) (ω : Ω) =>
      ENNReal.ofReal (phiS p.1 p.2 (o ω) ^ 2))
    (ENNReal.measurable_ofReal.comp ((measurable_phiS_out ho).pow_const 2)).aemeasurable]
  have h : ∀ ω : Ω, ∫⁻ p : MlpParam n mA n × MlpParam n mF 1,
      ENNReal.ofReal (phiS p.1 p.2 (o ω) ^ 2) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) =
      ENNReal.ofReal (4 / (n : ℝ)) := fun ω =>
    lint_phi_sq hn hmA hmF (normSq_sphPt hn (o ω))
  simp_rw [h]
  simp

lemma ofReal_integral_out (hn : 1 ≤ n) (A : MlpParam n mA n) (F : MlpParam n mF 1)
    {o : Ω → Fin n → ℝ} (ho : Measurable o) :
    ENNReal.ofReal (∫ ω, phiS A F (o ω) ^ 2 ∂P) = Lout P o (A, F) := by
  have hb : BM (fun ω => phiS A F (o ω) ^ 2) := ((bm_phiS hn A F).comp ho).sq
  exact ofReal_integral_eq_lintegral_ofReal (hb.integrable P)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

end second

/-! ## The two mixed integrals of `cheapStandIn138` in explicit form -/

section mixed

variable {n m : ℕ} {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]

lemma J1_eq (v : ℝ) (b : Fin m → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ c, (∫ x, φ x ∂standIn μ h v b c) ∂cDist n v b =
      ∫ ω : (Fin n → ℝ) × (U × (Fin n → ℝ)),
        φ (sphPt (lam b (h ω.2.1) • ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1) +
          sig v b (h ω.2.1) • ω.2.2))
        ∂((stdGauss (Fin n)).prod (μ.prod (stdGauss (Fin n)))) := by
  have hm : Measurable (fun ω : (Fin n → ℝ) × (U × (Fin n → ℝ)) =>
      sphPt (lam b (h ω.2.1) • ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1) +
          sig v b (h ω.2.1) • ω.2.2)) :=
    measurable_sphPt.comp
      ((((measurable_lam b).comp (hh.comp (measurable_fst.comp measurable_snd))).smul
        ((measurable_const_smul (Real.sqrt v * Real.sqrt (normSq b))).comp measurable_fst)).add
        (((measurable_sig v b).comp (hh.comp (measurable_fst.comp measurable_snd))).smul
          (measurable_snd.comp measurable_snd)))
  have hG : BM (fun ω : (Fin n → ℝ) × (U × (Fin n → ℝ)) =>
      φ (sphPt (lam b (h ω.2.1) • ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1) +
          sig v b (h ω.2.1) • ω.2.2))) := hφ.comp hm
  unfold cDist
  rw [integral_map (measurable_const_smul _).aemeasurable
    (bm_standIn μ v b hh hφ).meas.aestronglyMeasurable, integral_prod _ (hG.integrable _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  unfold standIn
  exact integral_map (measurable_sphPt.comp (measurable_standOut hh v b _)).aemeasurable
    hφ.meas.aestronglyMeasurable

omit [MeasurableSpace U] in
lemma J2_eq (v : ℝ) (b : Fin m → ℝ) (τ₀ : ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ c, (∫ x, φ x ∂cheapIn c τ₀) ∂cDist n v b =
      ∫ ω : (Fin n → ℝ) × (Fin n → ℝ),
        φ (sphPt ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1 + τ₀ • ω.2))
        ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
  have hm : Measurable (fun ω : (Fin n → ℝ) × (Fin n → ℝ) =>
      sphPt ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1 + τ₀ • ω.2)) :=
    measurable_sphPt.comp
      (((measurable_const_smul (Real.sqrt v * Real.sqrt (normSq b))).comp measurable_fst).add
        ((measurable_const_smul τ₀).comp measurable_snd))
  have hG : BM (fun ω : (Fin n → ℝ) × (Fin n → ℝ) =>
      φ (sphPt ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1 + τ₀ • ω.2))) := hφ.comp hm
  unfold cDist
  rw [integral_map (measurable_const_smul _).aemeasurable
    (bm_cheapIn (cc := fun c : Fin n → ℝ => c) (tt := fun _ => τ₀) measurable_id
      measurable_const hφ).meas.aestronglyMeasurable,
    integral_prod _ (hG.integrable _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  exact integral_cheapIn _ _ hφ.meas

end mixed

/-! ## Fixed `(M₁, M₂)` -/

/-- **The error for fixed `(M₁, M₂)` on the good event.** For `n ≥ 4096`,
`θ = (M₁, M₂) ∈ good136 n` and `0 ≤ ζ < 1`:
`E_{A,F} E_{M₃} (B − g₀)² ≤ (2·(0.99/n) + 8·Hbar n ζ θ)·(4/n)`. -/
theorem errFixed139 {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ good136 n) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gCheap ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)))
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal ((2 * (99 / 100 / (n : ℝ)) + 8 * Hbar n ζ θ) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have hH := Hbar_nonneg n ζ θ
  set b := hbarW θ with hb
  set v : ℝ := 2 / (mW n : ℝ) with hv
  set τ₀ := tau0 (2 * n) (mW n) θ with hτ₀
  set h := hid2 θ.1 θ.2 with hh'
  have hh : Measurable h := (continuous_hid2 θ.1 θ.2).measurable
  set o₁ : (Fin n → ℝ) × ((Fin (2 * n) → ℝ) × (Fin n → ℝ)) → Fin n → ℝ := fun ω =>
    sphPt (lam b (h ω.2.1) • ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1) +
      sig v b (h ω.2.1) • ω.2.2) with ho₁d
  set o₂ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ := fun ω =>
    sphPt ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1 + τ₀ • ω.2) with ho₂d
  have ho₁ : Measurable o₁ :=
    measurable_sphPt.comp
      ((((measurable_lam b).comp (hh.comp (measurable_fst.comp measurable_snd))).smul
        ((measurable_const_smul (Real.sqrt v * Real.sqrt (normSq b))).comp measurable_fst)).add
        (((measurable_sig v b).comp (hh.comp (measurable_fst.comp measurable_snd))).smul
          (measurable_snd.comp measurable_snd)))
  have ho₂ : Measurable o₂ :=
    measurable_sphPt.comp
      (((measurable_const_smul (Real.sqrt v * Real.sqrt (normSq b))).comp measurable_fst).add
        ((measurable_const_smul τ₀).comp measurable_snd))
  set P₁ := (stdGauss (Fin n)).prod ((uniformSphere (2 * n)).prod (stdGauss (Fin n))) with hP₁
  set P₂ := (stdGauss (Fin n)).prod (stdGauss (Fin n)) with hP₂
  set a₁ : ℝ := 2 * (99 / 100 / (n : ℝ)) + 4 * Hbar n ζ θ with ha₁
  set a₂ : ℝ := 4 * Hbar n ζ θ with ha₂
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; positivity
  have ha₂0 : 0 ≤ a₂ := by rw [ha₂]; positivity
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gCheap ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))) ≤
      ENNReal.ofReal a₁ * Lout P₁ o₁ p + ENNReal.ofReal a₂ * Lout P₂ o₂ p := by
    rintro ⟨A, F⟩
    have hφ : BM (phiS A F) := bm_phiS hn1 A F
    have h0 := cheapStandIn138 hn hθ hζ0 hζ1 hφ 0
    simp only [sub_zero] at h0
    -- the left side
    have eL : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
        ((∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
          ∫ x, phiS A F x ∂cheapIn (M₃.mulVec (hbarW θ)) (tau0 (2 * n) (mW n) θ)) ^ 2 =
        (Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
          gCheap ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2 := by
      intro M₃
      rw [integral_phiS_muWn hn1, integral_phiS_cheapIn hn1]
      rfl
    simp_rw [eL] at h0
    -- the right side
    have bV := bm_var_standIn (n := n) (uniformSphere (2 * n)) v b hh hφ
    have b1 := bm_standIn (n := n) (uniformSphere (2 * n)) v b hh hφ.sq
    have b2 : BM (fun c : Fin n → ℝ => ∫ x, phiS A F x ^ 2 ∂cheapIn c τ₀) :=
      bm_cheapIn measurable_id measurable_const hφ.sq
    have hVle : ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) h v b c] ∂cDist n v b ≤
        ∫ c, (∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) h v b c) ∂cDist n v b := by
      refine integral_mono (bV.integrable _) (b1.integrable _) fun c => ?_
      have := standIn_prob (n := n) (uniformSphere (2 * n)) hh v b c
      rw [var_bm (standIn (uniformSphere (2 * n)) h v b c) hφ]
      nlinarith [sq_nonneg (∫ x, phiS A F x ∂standIn (uniformSphere (2 * n)) h v b c)]
    have hsplit : ∫ c, ((∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) h v b c) +
          ∫ x, phiS A F x ^ 2 ∂cheapIn c τ₀) ∂cDist n v b =
        (∫ c, (∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) h v b c) ∂cDist n v b) +
          ∫ c, (∫ x, phiS A F x ^ 2 ∂cheapIn c τ₀) ∂cDist n v b :=
      integral_add (b1.integrable _) (b2.integrable _)
    rw [hsplit] at h0
    have e1 := J1_eq (n := n) (uniformSphere (2 * n)) v b hh hφ.sq
    have e2 := J2_eq (n := n) v b τ₀ hφ.sq
    rw [e1] at hVle h0
    rw [e2] at h0
    have i1 : 0 ≤ ∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁ := integral_nonneg fun _ => sq_nonneg _
    have i2 : 0 ≤ ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂ := integral_nonneg fun _ => sq_nonneg _
    rw [← ofReal_integral_out P₁ hn1 A F ho₁, ← ofReal_integral_out P₂ hn1 A F ho₂,
      ← ENNReal.ofReal_mul ha₁0, ← ENNReal.ofReal_mul ha₂0,
      ← ENNReal.ofReal_add (mul_nonneg ha₁0 i1) (mul_nonneg ha₂0 i2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc : (0 : ℝ) ≤ 99 / 100 / (n : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hVle hc
    rw [ha₁, ha₂]
    change _ ≤ (2 * (99 / 100 / (n : ℝ)) + 4 * Hbar n ζ θ) * (∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) +
      4 * Hbar n ζ θ * ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂
    change _ ≤ 2 * (99 / 100 / (n : ℝ) *
        ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) h v b c] ∂cDist n v b) +
      4 * Hbar n ζ θ * ((∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) + ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂) at h0
    change 99 / 100 / (n : ℝ) *
        ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) h v b c] ∂cDist n v b ≤
      99 / 100 / (n : ℝ) * ∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁ at this
    linarith
  calc _ ≤ ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
        (ENNReal.ofReal a₁ * Lout P₁ o₁ p + ENNReal.ofReal a₂ * Lout P₂ o₂ p)
        ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := lintegral_mono key
    _ = ENNReal.ofReal a₁ * ENNReal.ofReal (4 / (n : ℝ)) +
        ENNReal.ofReal a₂ * ENNReal.ofReal (4 / (n : ℝ)) := by
      rw [lintegral_add_left ((measurable_Lout P₁ ho₁).const_mul _),
        lintegral_const_mul _ (measurable_Lout P₁ ho₁),
        lintegral_const_mul _ (measurable_Lout P₂ ho₂),
        lintegral_Lout P₁ hn1 hmA hmF ho₁, lintegral_Lout P₂ hn1 hmA hmF ho₂]
    _ = _ := by
      have h4 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
      rw [← ENNReal.ofReal_mul ha₁0, ← ENNReal.ofReal_mul ha₂0,
        ← ENNReal.ofReal_add (mul_nonneg ha₁0 h4) (mul_nonneg ha₂0 h4)]
      congr 1
      rw [ha₁, ha₂]
      ring

/-! ## Joint over `(W, A, F)` -/

/-- The squared error of the cheap estimate on the good event of `W`:
`1_good(W)·(g₀ − B)²`, a function of `(W, A, F)`. -/
noncomputable def errG (n : ℕ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodW n).indicator (fun W => (gCheap W t.2.1 t.2.2 - Part130.Bn W t.2.1 t.2.2) ^ 2) t.1

lemma errG_nonneg (n : ℕ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ errG n t :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_errG {n : ℕ} (hn : 1 ≤ n) : Measurable (errG n) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errG n = ({t | t.1 ∈ goodW n} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gCheap t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    by_cases ht : t.1 ∈ goodW n
    · rw [Set.indicator_of_mem (show t ∈ {t : MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1 | t.1 ∈ goodW n} from ht)]
      unfold errG
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem (show t ∉ {t : MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1 | t.1 ∈ goodW n} from ht)]
      unfold errG
      rw [Set.indicator_of_notMem ht]
  rw [e]
  exact (((measurable_gCheap hN).sub (BstLean.Part131.measurable_Bn hN)).pow_const 2).indicator
    (measurable_fst (goodW_meas hn))

instance (r n : ℕ) : IsProbabilityMeasure (mlpTriple r n) := by
  unfold mlpTriple; infer_instance

section joint

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)

include hn hζ0 hζ1

/-- **Item 1 (`errVec139`), as an integral of a nonnegative function.** For `n ≥ 4096` and
`0 < ζ < 1`: `E_{W,A,F}[1_good(W)·(g₀ − B)²] ≤ (2·(0.99/n) + 8·EH n ζ)·(4/n)`. -/
theorem errVec139_lint :
    ∫⁻ t, ENNReal.ofReal (errG n t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal ((2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have mE := good136_meas (n := n) hn1
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (errG n t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_errG hn1)
  set G : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hG
  have mG : Measurable G := mf.lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, G W ∂mlpGauss (2 * n) (mW n) n = _
    rw [e, lintegral_map mG MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => G (MeasurableEquiv.prodAssoc a))
      (mG.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  -- the bound for fixed θ
  set a : ℝ := 2 * (99 / 100 / (n : ℝ)) with ha
  set S : ℝ := 4 / (n : ℝ) with hS
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    a * S * (good136 n).indicator (fun _ => (1 : ℝ)) θ +
      8 * S * (good136 n).indicator (Hbar n ζ) θ with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have h1 : 0 ≤ (good136 n).indicator (fun _ => (1 : ℝ)) θ :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h2 : 0 ≤ (good136 n).indicator (Hbar n ζ) θ :=
      Set.indicator_nonneg (fun θ _ => Hbar_nonneg n ζ θ) _
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    have msec : Measurable (fun q : Matrix (Fin n) (Fin (mW n)) ℝ ×
        (MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
        (((θ.1, θ.2, q.1) : MlpParam (2 * n) (mW n) n), q.2)) :=
      ((measurable_const.prodMk (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
    have hswap : ∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM =
        ∫⁻ p, (∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM) ∂PAF :=
      lintegral_lintegral_swap
        (f := fun (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) (mf.comp msec).aemeasurable
    rw [hswap]
    by_cases hθ : θ ∈ good136 n
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodW n := fun M₃ => hθ
      have hin : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM =
          ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)
            p.1 p.2 - gCheap ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2 ∂gM) := by
        rintro ⟨A, F⟩
        have hφ : BM (phiS A F) := bm_phiS hn1 A F
        have hb : BM (fun W : MlpParam (2 * n) (mW n) n =>
            ((∫ x, phiS A F x ∂muWn W) - ∫ x, phiS A F x ∂cheapW W) ^ 2) :=
          ((bm_muW hN hφ).sub (bm_cheapW hN hφ)).sq
        have hb' : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
              gCheap ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2) := by
          have h1 := hb.comp (g := fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n))
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))
          refine ⟨?_, h1.bdd.imp fun M hM M₃ => ?_⟩
          · convert h1.meas using 2 with M₃
            rw [integral_phiS_muWn hn1]
            unfold cheapW gCheap
            rw [integral_phiS_cheapIn hn1]
            rfl
          · have := hM M₃
            rw [integral_phiS_muWn hn1] at this
            unfold cheapW at this
            rw [integral_phiS_cheapIn hn1] at this
            exact this
        rw [ofReal_integral_eq_lintegral_ofReal (hb'.integrable gM)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        refine lintegral_congr fun M₃ => ?_
        simp only [hf, errG, Set.indicator_of_mem (hW M₃)]
        congr 1
        ring
      simp_rw [hin]
      refine (errFixed139 hn hθ hζ0.le hζ1).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hk]
      simp only [Set.indicator_of_mem hθ]
      rw [ha, hS]
      apply le_of_eq
      ring
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodW n := fun M₃ => hθ
      have hz : ∀ (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
          (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ),
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) = 0 := by
        intro p M₃
        simp only [hf, errG, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero]
      simp_rw [hz]
      simp
  obtain ⟨iH, hH⟩ := Hbar_mean hn hζ0 hζ1
  have i1 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      a * S * (good136 n).indicator (fun _ => (1 : ℝ)) θ) (hidGauss (2 * n) (mW n)) :=
    ((integrable_const (1 : ℝ)).indicator mE).const_mul _
  have i2 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      8 * S * (good136 n).indicator (Hbar n ζ) θ) (hidGauss (2 * n) (mW n)) := iH.const_mul _
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := i1.add i2
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_add i1 i2, integral_const_mul, integral_const_mul]
        have e1 : ∫ θ, (good136 n).indicator (fun _ => (1 : ℝ)) θ ∂hidGauss (2 * n) (mW n) ≤ 1 := by
          rw [integral_indicator mE, setIntegral_const, smul_eq_mul, mul_one]
          exact measureReal_le_one
        have h1 := mul_le_mul_of_nonneg_left e1 (mul_nonneg ha0 hS0)
        have h2 := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 8 * S)
        nlinarith

/-- **Item 1 (`errVec139`).** For `n ≥ 4096` and `0 < ζ < 1`: `1_good(W)·(g₀ − B)²` is
integrable over `(W, A, F)`, and
`E_{W,A,F}[1_good(W)·(g₀ − B)²] ≤ (2·(0.99/n) + 8·EH n ζ)·(4/n)`. -/
theorem errVec139 :
    Integrable (errG n) (mlpTriple 2 n) ∧
      ∫ t, errG n t ∂mlpTriple 2 n ≤ (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) * (4 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := errVec139_lint hn hζ0 hζ1
  have hEH := (EH_pos hn hζ0).le
  have hc : (0 : ℝ) ≤ (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) * (4 / (n : ℝ)) := by positivity
  have h0 : 0 ≤ᵐ[mlpTriple 2 n] errG n := Filter.Eventually.of_forall (errG_nonneg n)
  have hm := (measurable_errG hn1).aestronglyMeasurable (μ := mlpTriple 2 n)
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
  exact ENNReal.toReal_le_of_le_ofReal hc h

/-- **The tail form of item 1.** For `s > 0`:
`Pr_{W,A,F}(W good and (g₀ − B)² ≥ s) ≤ (2·(0.99/n) + 8·EH n ζ)·(4/n)/s`. -/
theorem errTail139 {s : ℝ} (hs : 0 < s) :
    (mlpTriple 2 n).real {t | s ≤ errG n t} ≤
      (2 * (99 / 100 / (n : ℝ)) + 8 * EH n ζ) * (4 / (n : ℝ)) / s := by
  obtain ⟨hi, hb⟩ := errVec139 hn hζ0 hζ1
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := mlpTriple 2 n) (f := errG n)
    (Filter.Eventually.of_forall (errG_nonneg n)) hi s
  rw [le_div_iff₀ hs]
  linarith

end joint

/-- **Item 1 with explicit constants** (`ζ = 1/20`). For `n ≥ 4096`:
`E_{W,A,F}[1_good(W)·(g₀ − B)²] ≤ (1.98/n + 3760·n/m_W)·(4/n)`. -/
theorem errVec139_num {n : ℕ} (hn : 4096 ≤ n) :
    Integrable (errG n) (mlpTriple 2 n) ∧
      ∫ t, errG n t ∂mlpTriple 2 n ≤
        (198 / 100 / (n : ℝ) + 3760 * ((n : ℝ) / (mW n : ℝ))) * (4 / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hi, hb⟩ := errVec139 hn (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num)
  refine ⟨hi, hb.trans ?_⟩
  have h := EH_le hn
  have h4 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_right ?_ h4
  have e : 470 * (n : ℝ) / (mW n : ℝ) = 470 * ((n : ℝ) / (mW n : ℝ)) := by ring
  rw [e] at h
  have e2 : 2 * (99 / 100 / (n : ℝ)) = 198 / 100 / (n : ℝ) := by ring
  rw [e2]
  linarith

end BstLean.Part139

open BstLean.Part139 in
#print axioms errFixed139
open BstLean.Part139 in
#print axioms errVec139_lint
open BstLean.Part139 in
#print axioms errVec139
open BstLean.Part139 in
#print axioms errTail139
open BstLean.Part139 in
#print axioms errVec139_num
