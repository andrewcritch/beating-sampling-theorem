import BstLean.Part139Explicit

/-!
# Part 139, item 4 (optional, second half): the scalar from one uniform input

Role: `delegations/statements/p139-spec.md`, item 4, "the same for the scalar from one input
(`cheapTwo138`)". The cheap stand-in has the scalar `τ₁² = t|h̄|²·max(0, w(u₁))` of Part 138
(`tau1`), from one uniform input `u₁` that is independent of `(W, A, F)`. The centre is still
the exact mean hidden vector `h̄`.

* `errFixedGen`: the second-moment argument of `errFixed139` for every constant scalar `τ` and
  every inequality of the form of `cheapStandIn138`.
* `cheapFixed2`: `cheap_fixed` of Part 138 with second moments in the place of `B²`.
* `gTwo u₁ W A F`: the exact mean of `F∘A` over the cheap stand-in with the scalar from `u₁`.
* **`errTwo139_lint`**: `E[1_{good, u₁ good}·(g₁ − B)²] ≤ (2·(0.99/n) + 8·EH1 n ζ)·(4/n)`.
* **`standInTwo139_rate`**: for every `n ≥ 4096`:
  `Pr(|g₁ − B| ≤ sd/2) ≥ 1 − (0.002 + 1977/n)`, the probability over `u₁` and `(W, A, F)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138

/-! ## The second-moment argument for a general constant scalar -/

/-- **The error for fixed `(M₁, M₂)` and a constant scalar `τ`, from an inequality of the form of
`cheapStandIn138`** with the factor `κ` in the second term:
`E_{A,F} E_{M₃}(B − E_{ν′(M₃h̄, τ)} F∘A)² ≤ (2·(0.99/n) + 2κ)·(4/n)`. -/
theorem errFixedGen {n : ℕ} (hn : 4096 ≤ n) (θ : HidParam (2 * n) (mW n)) (τ : ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ)
    (H : ∀ {φ : (Fin n → ℝ) → ℝ}, BstLean.Part105.BM φ →
      ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
          ∫ x, φ x ∂cheapIn (M₃.mulVec (hbarW θ)) τ) ^ 2
          ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
        2 * (99 / 100 / (n : ℝ) *
          ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
            (hbarW θ) c] ∂cDist n (2 / (mW n : ℝ)) (hbarW θ)) +
        κ * ∫ c, (∫ x, φ x ^ 2
              ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c +
            ∫ x, φ x ^ 2 ∂cheapIn c τ) ∂cDist n (2 / (mW n : ℝ)) (hbarW θ)) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          ∫ x, phiN p.1 p.2 x ∂cheapIn (M₃.mulVec (hbarW θ)) τ) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)))
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal ((2 * (99 / 100 / (n : ℝ)) + 2 * κ) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  set b := hbarW θ with hb
  set v : ℝ := 2 / (mW n : ℝ) with hv
  set h := hid2 θ.1 θ.2 with hh'
  have hh : Measurable h := (continuous_hid2 θ.1 θ.2).measurable
  set o₁ : (Fin n → ℝ) × ((Fin (2 * n) → ℝ) × (Fin n → ℝ)) → Fin n → ℝ := fun ω =>
    sphPt (lam b (h ω.2.1) • ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1) +
      sig v b (h ω.2.1) • ω.2.2) with ho₁d
  set o₂ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ := fun ω =>
    sphPt ((Real.sqrt v * Real.sqrt (normSq b)) • ω.1 + τ • ω.2) with ho₂d
  have ho₁ : Measurable o₁ :=
    measurable_sphPt.comp
      ((((measurable_lam b).comp (hh.comp (measurable_fst.comp measurable_snd))).smul
        ((measurable_const_smul (Real.sqrt v * Real.sqrt (normSq b))).comp measurable_fst)).add
        (((measurable_sig v b).comp (hh.comp (measurable_fst.comp measurable_snd))).smul
          (measurable_snd.comp measurable_snd)))
  have ho₂ : Measurable o₂ :=
    measurable_sphPt.comp
      (((measurable_const_smul (Real.sqrt v * Real.sqrt (normSq b))).comp measurable_fst).add
        ((measurable_const_smul τ).comp measurable_snd))
  set P₁ := (stdGauss (Fin n)).prod ((uniformSphere (2 * n)).prod (stdGauss (Fin n))) with hP₁
  set P₂ := (stdGauss (Fin n)).prod (stdGauss (Fin n)) with hP₂
  set a₁ : ℝ := 2 * (99 / 100 / (n : ℝ)) + κ with ha₁
  have ha₁0 : 0 ≤ a₁ := by
    have : (0 : ℝ) ≤ 99 / 100 / (n : ℝ) := by positivity
    rw [ha₁]; linarith
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          ∫ x, phiN p.1 p.2 x ∂cheapIn (M₃.mulVec b) τ) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))) ≤
      ENNReal.ofReal a₁ * Lout P₁ o₁ p + ENNReal.ofReal κ * Lout P₂ o₂ p := by
    rintro ⟨A, F⟩
    have hφ : BstLean.Part105.BM (phiS A F) := bm_phiS hn1 A F
    have h0 := H hφ
    -- the left side
    have eL : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
        ((∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
          ∫ x, phiS A F x ∂cheapIn (M₃.mulVec b) τ) ^ 2 =
        (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
          ∫ x, phiN A F x ∂cheapIn (M₃.mulVec b) τ) ^ 2 := by
      intro M₃
      rw [integral_phiS_muWn hn1, integral_phiS_cheapIn hn1]
    simp_rw [eL] at h0
    -- the right side
    have bV := bm_var_standIn (n := n) (uniformSphere (2 * n)) v b hh hφ
    have b1 := bm_standIn (n := n) (uniformSphere (2 * n)) v b hh hφ.sq
    have b2 : BstLean.Part105.BM (fun c : Fin n → ℝ => ∫ x, phiS A F x ^ 2 ∂cheapIn c τ) :=
      bm_cheapIn measurable_id measurable_const hφ.sq
    have hVle : ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) h v b c] ∂cDist n v b ≤
        ∫ c, (∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) h v b c) ∂cDist n v b := by
      refine integral_mono (bV.integrable _) (b1.integrable _) fun c => ?_
      have := standIn_prob (n := n) (uniformSphere (2 * n)) hh v b c
      rw [var_bm (standIn (uniformSphere (2 * n)) h v b c) hφ]
      nlinarith [sq_nonneg (∫ x, phiS A F x ∂standIn (uniformSphere (2 * n)) h v b c)]
    have hsplit : ∫ c, ((∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) h v b c) +
          ∫ x, phiS A F x ^ 2 ∂cheapIn c τ) ∂cDist n v b =
        (∫ c, (∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) h v b c) ∂cDist n v b) +
          ∫ c, (∫ x, phiS A F x ^ 2 ∂cheapIn c τ) ∂cDist n v b :=
      integral_add (b1.integrable _) (b2.integrable _)
    rw [hsplit] at h0
    have e1 := J1_eq (n := n) (uniformSphere (2 * n)) v b hh hφ.sq
    have e2 := J2_eq (n := n) v b τ hφ.sq
    rw [e1] at hVle h0
    rw [e2] at h0
    have i1 : 0 ≤ ∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁ := integral_nonneg fun _ => sq_nonneg _
    have i2 : 0 ≤ ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂ := integral_nonneg fun _ => sq_nonneg _
    rw [← ofReal_integral_out P₁ hn1 A F ho₁, ← ofReal_integral_out P₂ hn1 A F ho₂,
      ← ENNReal.ofReal_mul ha₁0, ← ENNReal.ofReal_mul hκ,
      ← ENNReal.ofReal_add (mul_nonneg ha₁0 i1) (mul_nonneg hκ i2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc : (0 : ℝ) ≤ 99 / 100 / (n : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hVle hc
    rw [ha₁]
    change _ ≤ (2 * (99 / 100 / (n : ℝ)) + κ) * (∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) +
      κ * ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂
    change _ ≤ 2 * (99 / 100 / (n : ℝ) *
        ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) h v b c] ∂cDist n v b) +
      κ * ((∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) + ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂) at h0
    change 99 / 100 / (n : ℝ) *
        ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) h v b c] ∂cDist n v b ≤
      99 / 100 / (n : ℝ) * ∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁ at this
    linarith
  calc _ ≤ ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
        (ENNReal.ofReal a₁ * Lout P₁ o₁ p + ENNReal.ofReal κ * Lout P₂ o₂ p)
        ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := lintegral_mono key
    _ = ENNReal.ofReal a₁ * ENNReal.ofReal (4 / (n : ℝ)) +
        ENNReal.ofReal κ * ENNReal.ofReal (4 / (n : ℝ)) := by
      rw [lintegral_add_left ((measurable_Lout P₁ ho₁).const_mul _),
        lintegral_const_mul _ (measurable_Lout P₁ ho₁),
        lintegral_const_mul _ (measurable_Lout P₂ ho₂),
        lintegral_Lout P₁ hn1 hmA hmF ho₁, lintegral_Lout P₂ hn1 hmA hmF ho₂]
    _ = _ := by
      have h4 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
      rw [← ENNReal.ofReal_mul ha₁0, ← ENNReal.ofReal_mul hκ,
        ← ENNReal.ofReal_add (mul_nonneg ha₁0 h4) (mul_nonneg hκ h4)]
      congr 1
      rw [ha₁]
      ring

/-- **`cheap_fixed` of Part 138 with second moments.** For `θ ∈ good136 n`, a constant `τ > 0`
and a bound `K` of the Hellinger distance (as in `cheap_mix`), for bounded measurable `φ`:
`E_{M₃}(E_{μ_W} φ − E_{ν′} φ)² ≤ 2·(0.99/n)·E_c Var_{ν_c} φ
   + 4·E_u K·E_c(E_{ν_c} φ² + E_{ν′_c} φ²)`. -/
theorem cheapFixed2 {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ good136 n) {τ : ℝ} (hτ : 0 < τ) {K : (Fin (2 * n) → ℝ) → ℝ} (hKm : Measurable K)
    (hKi : Integrable K (uniformSphere (2 * n)))
    (hK : ∀ u, (0 < lam (hbarW θ) (hid2 θ.1 θ.2 u) ∧
        hellG n (sig (2 / (mW n : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) /
          lam (hbarW θ) (hid2 θ.1 θ.2 u)) τ ≤ K u) ∨ 1 ≤ K u)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BstLean.Part105.BM φ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec (hbarW θ)) τ) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbarW θ) c] ∂cDist n (2 / (mW n : ℝ)) (hbarW θ)) +
      4 * (∫ u, K u ∂uniformSphere (2 * n)) *
        ∫ c, (∫ x, φ x ^ 2
              ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c +
            ∫ x, φ x ^ 2 ∂cheapIn c τ) ∂cDist n (2 / (mW n : ℝ)) (hbarW θ) := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  set P := gaussMat n (mW n) (2 / (mW n : ℝ)) with hP
  set b := hbarW θ with hb
  set IK : ℝ := ∫ u, K u ∂uniformSphere (2 * n) with hIK
  have bX : BstLean.Part105.BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      ∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) :=
    (bm_muW hN hφ).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have bYc : BstLean.Part105.BM (fun c : Fin n → ℝ =>
      ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c) :=
    bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) b hh hφ
  have bZc : BstLean.Part105.BM (fun c : Fin n → ℝ => ∫ x, φ x ∂cheapIn c τ) :=
    bm_cheapIn (cc := fun c : Fin n → ℝ => c) (tt := fun _ => τ) measurable_id
      measurable_const hφ
  have bSc : BstLean.Part105.BM (fun c : Fin n → ℝ =>
      ∫ x, φ x ^ 2
          ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c +
        ∫ x, φ x ^ 2 ∂cheapIn c τ) :=
    (bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) b hh hφ.sq).add
      (bm_cheapIn (cc := fun c : Fin n → ℝ => c) (tt := fun _ => τ) measurable_id
        measurable_const hφ.sq)
  have mb : Measurable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ => M₃.mulVec b) :=
    measurable_mulVec_right b
  have bY := bYc.comp mb
  have bZ := bZc.comp mb
  have bS := bSc.comp mb
  have hpt : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec b) τ) ^ 2 ≤
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      4 * IK *
        (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, φ x ^ 2 ∂cheapIn (M₃.mulVec b) τ) := by
    intro M₃
    have h1 := cheap_mix (uniformSphere (2 * n)) (by omega : 2 ≤ n) (2 / (mW n : ℝ)) b
      (M₃.mulVec b) hh hτ hKm hKi hK hφ
    nlinarith [sq_nonneg ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
      2 * ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b) + ∫ x, φ x ∂cheapIn (M₃.mulVec b) τ)]
  have i1 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2) P :=
    ((BstLean.Part105.BM.const 2).mul (bX.sub bY).sq).integrable P
  have i2 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      4 * IK *
        (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, φ x ^ 2 ∂cheapIn (M₃.mulVec b) τ)) P :=
    ((BstLean.Part105.BM.const (4 * IK)).mul bS).integrable P
  have i12 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      4 * IK *
        (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, φ x ^ 2 ∂cheapIn (M₃.mulVec b) τ)) P := i1.add i2
  have hmono := integral_mono ((bX.sub bZ).sq.integrable P) i12 hpt
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hmono
  have h136 := standIn136 hn hθ hφ
  have ecd : ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, φ x ^ 2 ∂cheapIn (M₃.mulVec b) τ) ∂P =
      ∫ c, (∫ x, φ x ^ 2
              ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c +
            ∫ x, φ x ^ 2 ∂cheapIn c τ) ∂cDist n (2 / (mW n : ℝ)) b := by
    rw [← cDist_eq, integral_map mb.aemeasurable bSc.meas.aestronglyMeasurable]
  rw [ecd] at hmono
  have h136' : ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 ∂P ≤
      99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c]
          ∂cDist n (2 / (mW n : ℝ)) b := h136
  linarith

/-! ## The estimate with the scalar from one input -/

section defs

variable {N m n mA mF : ℕ}

/-- **The cheap estimate with the scalar from the input `u₁`**: the exact mean of `F∘A` over the
distribution of `sphPt(M₃h̄ + τ₁γ)`, `τ₁² = t|h̄|²·max(0, w(u₁))` (`tau1` of Part 138). -/
noncomputable def gTwo (u₁ : Fin N → ℝ) (W : MlpParam N m n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) : ℝ :=
  ∫ x, phiN A F x ∂cheapIn (W.2.2.mulVec (hbarW (W.1, W.2.1))) (tau1 N m u₁ (W.1, W.2.1))

/-- The mean of `F∘A` over the cheap stand-in is jointly measurable in the centre, the scalar
and `(A, F)`. -/
lemma measurable_cheapMean :
    Measurable (fun z : ((Fin n → ℝ) × ℝ) × (MlpParam n mA n × MlpParam n mF 1) =>
      ∫ x, phiN z.2.1 z.2.2 x ∂cheapIn z.1.1 z.1.2) := by
  have hj : Measurable (fun y : (((Fin n → ℝ) × ℝ) × (MlpParam n mA n × MlpParam n mF 1)) ×
      (Fin n → ℝ) => phiN y.1.2.1 y.1.2.2 (sphPt (y.1.1.1 + y.1.1.2 • y.2))) := by
    have h1 : Measurable (fun y : (((Fin n → ℝ) × ℝ) × (MlpParam n mA n × MlpParam n mF 1)) ×
        (Fin n → ℝ) => sphPt (y.1.1.1 + y.1.1.2 • y.2)) :=
      measurable_sphPt.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).add
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd))
    have h2 := BstLean.Part131.continuous_phiN_all.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk h1)
    simp only [Function.comp_def] at h2
    exact h2
  have e : (fun z : ((Fin n → ℝ) × ℝ) × (MlpParam n mA n × MlpParam n mF 1) =>
      ∫ x, phiN z.2.1 z.2.2 x ∂cheapIn z.1.1 z.1.2) = fun z => ∫ γ, phiN z.2.1 z.2.2
        (sphPt (z.1.1 + z.1.2 • γ)) ∂stdGauss (Fin n) := by
    funext z
    exact integral_cheapIn _ _ (continuous_phiN _ _).measurable
  rw [e]
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

/-- `g₁` is jointly measurable in `(u₁, (W, A, F))`. -/
lemma measurable_gTwo (hN : 1 ≤ N) :
    Measurable (fun q : (Fin N → ℝ) × (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) =>
      gTwo q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hθ : Measurable (fun W : MlpParam N m n => ((W.1, W.2.1) : HidParam N m)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun W : MlpParam N m n => W.2.2.mulVec (hbarW (W.1, W.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp measurable_snd).prodMk ((measurable_hbarW hN).comp hθ))
  have hg : Measurable (fun r : (Fin N → ℝ) × MlpParam N m n =>
      (r.1, ((r.2.1, r.2.2.1) : HidParam N m))) :=
    measurable_fst.prodMk (hθ.comp measurable_snd)
  have hτ0 := (measurable_tau1 (m := m) hN).comp hg
  have hτ : Measurable (fun r : (Fin N → ℝ) × MlpParam N m n =>
      tau1 N m r.1 (r.2.1, r.2.2.1)) := hτ0
  have hW : Measurable (fun q : (Fin N → ℝ) × (MlpParam N m n × MlpParam n mA n ×
      MlpParam n mF 1) => q.2.1) := measurable_fst.comp measurable_snd
  have hmap : Measurable (fun q : (Fin N → ℝ) × (MlpParam N m n × MlpParam n mA n ×
      MlpParam n mF 1) =>
      (((q.2.1.2.2.mulVec (hbarW (q.2.1.1, q.2.1.2.1)),
        tau1 N m q.1 (q.2.1.1, q.2.1.2.1)) : (Fin n → ℝ) × ℝ), q.2.2)) :=
    ((hc.comp hW).prodMk (hτ.comp (measurable_fst.prodMk hW))).prodMk
      (measurable_snd.comp measurable_snd)
  have h3 := (measurable_cheapMean (n := n) (mA := mA) (mF := mF)).comp hmap
  simp only [Function.comp_def] at h3
  unfold gTwo
  exact h3

end defs

/-- The good event of `(u₁, (W, A, F))`: `(M₁, M₂) ∈ good136 n` and `u₁` a good input. -/
def goodQ (n : ℕ) (ζ : ℝ) : Set ((Fin (2 * n) → ℝ) ×
    (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1)) :=
  {q | (q.1, ((q.2.1.1, q.2.1.2.1) : HidParam (2 * n) (mW n))) ∈ goodS (good136 n) ζ}

lemma measurable_piQ (n : ℕ) :
    Measurable (fun q : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
      (q.1, ((q.2.1.1, q.2.1.2.1) : HidParam (2 * n) (mW n)))) :=
  measurable_fst.prodMk (((measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
    (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))))

lemma goodQ_meas {n : ℕ} (hn : 1 ≤ n) (ζ : ℝ) : MeasurableSet (goodQ n ζ) :=
  (measurable_piQ n) (goodS_meas (by omega) (good136_meas hn) ζ)

/-- `1_{good}·(g₁ − B)²`, a function of `(u₁, (W, A, F))`. -/
noncomputable def errG2 (n : ℕ) (ζ : ℝ) (q : (Fin (2 * n) → ℝ) ×
    (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1)) : ℝ :=
  (goodQ n ζ).indicator (fun q => (gTwo q.1 q.2.1 q.2.2.1 q.2.2.2 -
    Part130.Bn q.2.1 q.2.2.1 q.2.2.2) ^ 2) q

lemma errG2_nonneg (n : ℕ) (ζ : ℝ) (q : (Fin (2 * n) → ℝ) ×
    (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1)) :
    0 ≤ errG2 n ζ q :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_errG2 {n : ℕ} (hn : 1 ≤ n) (ζ : ℝ) : Measurable (errG2 n ζ) := by
  have hN : 1 ≤ 2 * n := by omega
  exact (((measurable_gTwo hN).sub
    ((BstLean.Part131.measurable_Bn hN).comp measurable_snd)).pow_const 2).indicator
    (goodQ_meas hn ζ)

/-- Tonelli for the three networks: first `(M₁, M₂)`, then `M₃`, then `(A, F)`. -/
lemma lintegral_triple_split {n : ℕ}
    {f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞}
    (mf : Measurable f) :
    ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ : HidParam (2 * n) (mW n), (∫⁻ M₃, (∫⁻ p, f (((θ.1, θ.2, M₃) :
        MlpParam (2 * n) (mW n) n), p) ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)))
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))) ∂hidGauss (2 * n) (mW n) := by
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set G : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hG
  have mG : Measurable G := mf.lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
  rw [e0, lintegral_prod _ mf.aemeasurable]
  change ∫⁻ W, G W ∂mlpGauss (2 * n) (mW n) n = _
  rw [e, lintegral_map mG MeasurableEquiv.prodAssoc.measurable]
  exact lintegral_prod (fun a => G (MeasurableEquiv.prodAssoc a))
    (mG.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable

section two

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (hz : zetaP ζ < wLow)

include hn hζ0 hζ1 hz

/-- **The error of the estimate with the scalar from one input.** For `n ≥ 4096`, `0 < ζ < 1`
with `ζ′ < wLow`: `E[1_{good, u₁ good}·(g₁ − B)²] ≤ (2·(0.99/n) + 8·EH1 n ζ)·(4/n)`, the mean
over the uniform input `u₁` and `(W, A, F)`. -/
theorem errTwo139_lint :
    ∫⁻ q, ENNReal.ofReal (errG2 n ζ q) ∂((uniformSphere (2 * n)).prod (mlpTriple 2 n)) ≤
      ENNReal.ofReal ((2 * (99 / 100 / (n : ℝ)) + 8 * EH1 n ζ) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := uniformSphere_isProbability (2 * n) hN
  have hC := C1_nonneg (n := n) hζ0.le hζ1 hz
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  set f : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) → ℝ≥0∞ := fun q => ENNReal.ofReal (errG2 n ζ q) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_errG2 hn1 ζ)
  set a : ℝ := 2 * (99 / 100 / (n : ℝ)) with ha
  set S : ℝ := 4 / (n : ℝ) with hS
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  set k : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ := fun p =>
    a * S + 8 * S * (Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p) with hk
  have hk0 : ∀ p, 0 ≤ k p := by
    intro p
    have h2 := Gm_nonneg n ζ (by positivity : (0 : ℝ) ≤ 2 * C1 n ζ) p.2
    have h3 := Fsq_nonneg n ζ p
    rw [hk]
    positivity
  -- the bound for fixed `(u₁, θ)`
  have step2 : ∀ (u₁ : Fin (2 * n) → ℝ) (θ : HidParam (2 * n) (mW n)),
      ∫⁻ M₃, (∫⁻ p, f (u₁, (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) ∂PAF) ∂gM ≤
        ENNReal.ofReal (k (u₁, θ)) := by
    intro u₁ θ
    have msec : Measurable (fun z : Matrix (Fin n) (Fin (mW n)) ℝ ×
        (MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
        (u₁, (((θ.1, θ.2, z.1) : MlpParam (2 * n) (mW n) n), z.2))) :=
      measurable_const.prodMk
        ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
          measurable_snd)
    have hswap : ∫⁻ M₃, (∫⁻ p, f (u₁, (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p))
          ∂PAF) ∂gM =
        ∫⁻ p, (∫⁻ M₃, f (u₁, (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) ∂gM) ∂PAF :=
      lintegral_lintegral_swap
        (f := fun (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          f (u₁, (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p))) (mf.comp msec).aemeasurable
    rw [hswap]
    by_cases hp : (u₁, θ) ∈ goodS (good136 n) ζ
    · obtain ⟨hθ, hu₁⟩ := hp
      have hq : ∀ (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1),
          (u₁, (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) ∈ goodQ n ζ :=
        fun M₃ p => ⟨hθ, hu₁⟩
      set d : ℝ := (wn (2 * n) (mW n) u₁ θ - wbar (2 * n) (mW n) θ) ^ 2 with hd
      have hd0 : 0 ≤ d := sq_nonneg _
      have hFd : Fsq n ζ (u₁, θ) = d := by
        unfold Fsq
        rw [Set.indicator_of_mem (show (u₁, θ) ∈ goodS (good136 n) ζ from ⟨hθ, hu₁⟩)]
      obtain ⟨iK, hKle⟩ := K1fun_int hn hθ hζ0.le hζ1 hz hd0
      set τ : ℝ := tau1 (2 * n) (mW n) u₁ θ with hτ
      have hτpos : 0 < τ :=
        (good_pt1 hn hθ hζ0.le hζ1 hz (u := u₁) (u₁ := u₁) hu₁ hu₁).1
      have hK : ∀ u : Fin (2 * n) → ℝ,
          (0 < lam (hbarW θ) (hid2 θ.1 θ.2 u) ∧
            hellG n (sig (2 / (mW n : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) /
              lam (hbarW θ) (hid2 θ.1 θ.2 u)) τ ≤ K1fun n ζ d (u, θ)) ∨
            1 ≤ K1fun n ζ d (u, θ) := by
        intro u
        by_cases hu : (u, θ) ∈ goodU (2 * n) (mW n) ζ
        · left
          obtain ⟨-, h2, h3⟩ := good_pt1 hn hθ hζ0.le hζ1 hz hu hu₁
          refine ⟨h2, ?_⟩
          unfold K1fun
          rw [Set.indicator_of_mem hu, Set.indicator_of_notMem (by simpa using hu), add_zero]
          exact h3
        · right
          unfold K1fun
          rw [Set.indicator_of_notMem hu, Set.indicator_of_mem (by simpa using hu), zero_add]
      set IK : ℝ := ∫ u, K1fun n ζ d (u, θ) ∂uniformSphere (2 * n) with hIK
      have hIK0 : 0 ≤ IK := integral_nonneg fun u => K1fun_nonneg hζ0.le hζ1 hz hd0 (u, θ)
      have hgen := errFixedGen hn θ τ (κ := 4 * IK) (by positivity)
        (fun {φ} hφ => cheapFixed2 hn hθ hτpos
          ((measurable_K1fun hn1 ζ d).comp measurable_prodMk_right) iK hK hφ)
      have hin : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ∫⁻ M₃, f (u₁, (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) ∂gM =
          ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)
            p.1 p.2 - ∫ x, phiN p.1 p.2 x ∂cheapIn (M₃.mulVec (hbarW θ)) τ) ^ 2 ∂gM) := by
        rintro ⟨A, F⟩
        have hφ : BstLean.Part105.BM (phiS A F) := bm_phiS hn1 A F
        have hb : BstLean.Part105.BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            ((∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
              ∫ x, phiS A F x ∂cheapIn (M₃.mulVec (hbarW θ)) τ) ^ 2) :=
          (((bm_muW hN hφ).comp (measurable_const.prodMk (measurable_const.prodMk
            measurable_id))).sub (bm_cheapIn (cc := fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
              M₃.mulVec (hbarW θ)) (tt := fun _ => τ) (measurable_mulVec_right _)
              measurable_const hφ)).sq
        have hb' : BstLean.Part105.BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
              ∫ x, phiN A F x ∂cheapIn (M₃.mulVec (hbarW θ)) τ) ^ 2) := by
          have e : (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
              (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
                ∫ x, phiN A F x ∂cheapIn (M₃.mulVec (hbarW θ)) τ) ^ 2) =
              fun M₃ => ((∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) :
                MlpParam (2 * n) (mW n) n)) -
                ∫ x, phiS A F x ∂cheapIn (M₃.mulVec (hbarW θ)) τ) ^ 2 := by
            funext M₃
            rw [integral_phiS_muWn hn1, integral_phiS_cheapIn hn1]
          rw [e]
          exact hb
        rw [ofReal_integral_eq_lintegral_ofReal (hb'.integrable gM)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        refine lintegral_congr fun M₃ => ?_
        simp only [hf, errG2, Set.indicator_of_mem (hq M₃ (A, F))]
        congr 1
        have : gTwo u₁ ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F =
            ∫ x, phiN A F x ∂cheapIn (M₃.mulVec (hbarW θ)) τ := rfl
        rw [this]
        ring
      simp_rw [hin]
      refine hgen.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hk]
      simp only
      rw [hFd, ← ha, ← hS]
      have h1 : (a + 2 * (4 * IK)) * S = a * S + 8 * S * IK := by ring
      rw [h1]
      have h2 := mul_le_mul_of_nonneg_left hKle (by positivity : (0 : ℝ) ≤ 8 * S)
      linarith
    · have hq : ∀ (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1),
          (u₁, (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) ∉ goodQ n ζ :=
        fun M₃ p => hp
      have hzero : ∀ (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
          (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ),
          f (u₁, (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) = 0 := by
        intro p M₃
        simp only [hf, errG2, Set.indicator_of_notMem (hq M₃ p), ENNReal.ofReal_zero]
      simp_rw [hzero]
      simp
  -- the mean of the bound
  obtain ⟨iGm, hGm⟩ := Gm_mean hn hζ0 hζ1 (C := 2 * C1 n ζ) (by positivity)
  obtain ⟨iFs, hFs⟩ := Fsq_int hn hζ0 hζ1
  have j2 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      Gm n ζ (2 * C1 n ζ) p.2) μP := iGm.comp_snd _
  have j3 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      2 * C1 n ζ * Fsq n ζ p) μP := iFs.const_mul _
  have j23 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p) μP := j2.add j3
  have j4 : Integrable (fun p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) =>
      8 * S * (Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p)) μP := j23.const_mul _
  have j0 : Integrable (fun _ : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) => a * S) μP :=
    integrable_const _
  have ik : Integrable k μP := j0.add j4
  have hkint : ∫ p, k p ∂μP ≤ (a + 8 * EH1 n ζ) * S := by
    have ea : ∫ _p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n), a * S ∂μP = a * S := by
      simp
    have eb : ∫ p, 8 * S * (Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p) ∂μP =
        8 * S * ∫ p, (Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p) ∂μP :=
      integral_const_mul _ _
    have ec : ∫ p, (Gm n ζ (2 * C1 n ζ) p.2 + 2 * C1 n ζ * Fsq n ζ p) ∂μP =
        ∫ p, Gm n ζ (2 * C1 n ζ) p.2 ∂μP + ∫ p, 2 * C1 n ζ * Fsq n ζ p ∂μP :=
      integral_add j2 j3
    have ed : ∫ p, Gm n ζ (2 * C1 n ζ) p.2 ∂μP =
        ∫ θ, Gm n ζ (2 * C1 n ζ) θ ∂hidGauss (2 * n) (mW n) := by
      rw [hμP, integral_fun_snd]
      simp
    have ee : ∫ p, 2 * C1 n ζ * Fsq n ζ p ∂μP = 2 * C1 n ζ * ∫ p, Fsq n ζ p ∂μP :=
      integral_const_mul _ _
    have e0 : ∫ p, k p ∂μP = a * S + 8 * S * (∫ θ, Gm n ζ (2 * C1 n ζ) θ
        ∂hidGauss (2 * n) (mW n) + 2 * C1 n ζ * ∫ p, Fsq n ζ p ∂μP) := by
      rw [hk, integral_add j0 j4, ea, eb, ec, ed, ee]
    rw [e0]
    have h5 : ∫ θ, Gm n ζ (2 * C1 n ζ) θ ∂hidGauss (2 * n) (mW n) +
        2 * C1 n ζ * ∫ p, Fsq n ζ p ∂μP ≤ EH1 n ζ := by
      unfold EH1
      have := mul_le_mul_of_nonneg_left hFs (by positivity : (0 : ℝ) ≤ 2 * C1 n ζ)
      linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 8 * S)
    linarith
  rw [lintegral_prod _ mf.aemeasurable]
  have hsec : ∀ u₁ : Fin (2 * n) → ℝ, ∫⁻ t, f (u₁, t) ∂mlpTriple 2 n ≤
      ∫⁻ θ, ENNReal.ofReal (k (u₁, θ)) ∂hidGauss (2 * n) (mW n) := by
    intro u₁
    rw [lintegral_triple_split (f := fun t => f (u₁, t)) (mf.comp measurable_prodMk_left)]
    exact lintegral_mono fun θ => step2 u₁ θ
  calc ∫⁻ u₁, (∫⁻ t, f (u₁, t) ∂mlpTriple 2 n) ∂uniformSphere (2 * n)
      ≤ ∫⁻ u₁, (∫⁻ θ, ENNReal.ofReal (k (u₁, θ)) ∂hidGauss (2 * n) (mW n))
          ∂uniformSphere (2 * n) := lintegral_mono hsec
    _ = ∫⁻ p, ENNReal.ofReal (k p) ∂μP :=
        (lintegral_prod (fun p => ENNReal.ofReal (k p))
          ik.aestronglyMeasurable.aemeasurable.ennreal_ofReal).symm
    _ = ENNReal.ofReal (∫ p, k p ∂μP) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hkint

end two

/-! ## The headline for the scalar from one input -/

/-- From a bound of the integral of a nonnegative function to a tail bound (Markov). -/
lemma tail_of_lint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {f : Ω → ℝ}
    (hf : Measurable f) (h0 : ∀ ω, 0 ≤ f ω) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal c) {s : ℝ} (hs : 0 < s) :
    μ.real {ω | s ≤ f ω} ≤ c / s := by
  have h0' : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall h0
  have hm := hf.aestronglyMeasurable (μ := μ)
  have hi : Integrable f μ :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal h0').2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  have hb : ∫ ω, f ω ∂μ ≤ c := by
    rw [integral_eq_lintegral_of_nonneg_ae h0' hm]
    exact ENNReal.toReal_le_of_le_ofReal hc h
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := f) h0' hi s
  rw [le_div_iff₀ hs]
  linarith

/-- An event of the second coordinate has the same probability under a product with a
probability measure. -/
lemma prod_snd_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsProbabilityMeasure μ] [SFinite ν] (E : Set β) :
    (μ.prod ν).real {p | p.2 ∈ E} = ν.real E := by
  have e : {p : α × β | p.2 ∈ E} = (Set.univ : Set α) ×ˢ E := by ext p; simp
  rw [e, measureReal_def, Measure.prod_prod, measure_univ, one_mul, measureReal_def]

/-- `(u₁, (W, A, F)) ↦ (u₁, (M₁, M₂))` maps the joint distribution to
`uniformSphere ⊗ hidGauss`. -/
lemma map_piQ {n : ℕ} (hn : 1 ≤ n) :
    ((uniformSphere (2 * n)).prod (mlpTriple 2 n)).map
        (fun q : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          (q.1, ((q.2.1.1, q.2.1.2.1) : HidParam (2 * n) (mW n)))) =
      (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) := by
  have := uniformSphere_isProbability (2 * n) (by omega)
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  have a : (mlpTriple 2 n).map Prod.fst = mlpGauss (2 * n) (mW n) n := by
    rw [e0, Measure.map_fst_prod, measure_univ, one_smul]
  have b : (mlpGauss (2 * n) (mW n) n).map
      (fun W : MlpParam (2 * n) (mW n) n => ((W.1, W.2.1) : HidParam (2 * n) (mW n))) =
      hidGauss (2 * n) (mW n) := by
    unfold mlpGauss hidGauss
    exact BstLean.Part132.map_drop3
  have mθ : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ((W.1, W.2.1) : HidParam (2 * n) (mW n))) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have c : (mlpTriple 2 n).map (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ((t.1.1, t.1.2.1) : HidParam (2 * n) (mW n))) =
      hidGauss (2 * n) (mW n) := by
    rw [← b, ← a, Measure.map_map mθ measurable_fst]
    rfl
  have h2 := Measure.map_prod_map (uniformSphere (2 * n)) (mlpTriple 2 n) (f := id)
    (g := fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ((t.1.1, t.1.2.1) : HidParam (2 * n) (mW n)))
    measurable_id (mθ.comp measurable_fst)
  rw [Measure.map_id, c] at h2
  rw [h2]
  rfl

/-- The probability that `(M₁, M₂)` is not good or `u₁` is not a good input. -/
lemma badQ_prob {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) :
    ((uniformSphere (2 * n)).prod (mlpTriple 2 n)).real (goodQ n ζ)ᶜ ≤
      2 / 1000 + Beta n ζ := by
  have hn1 : 1 ≤ n := by omega
  have := uniformSphere_isProbability (2 * n) (by omega)
  set μQ := (uniformSphere (2 * n)).prod (mlpTriple 2 n) with hμQ
  have hsub : (goodQ n ζ)ᶜ ⊆
      {q : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) | q.2 ∈ {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1 | t.1 ∉ goodW n}} ∪
      (fun q : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          (q.1, ((q.2.1.1, q.2.1.2.1) : HidParam (2 * n) (mW n)))) ⁻¹' (badS n ζ) := by
    intro q hq
    by_cases hθ : ((q.2.1.1, q.2.1.2.1) : HidParam (2 * n) (mW n)) ∈ good136 n
    · right
      refine ⟨hθ, fun hu => hq ⟨hθ, hu⟩⟩
    · left
      exact hθ
  have h1 : μQ.real {q : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1) | q.2 ∈ {t : MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1 | t.1 ∉ goodW n}} ≤ 2 / 1000 :=
    (prod_snd_real (uniformSphere (2 * n)) (mlpTriple 2 n) {t | t.1 ∉ goodW n}).trans_le
      (bad_prob hn)
  have h2 : μQ.real ((fun q : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          (q.1, ((q.2.1.1, q.2.1.2.1) : HidParam (2 * n) (mW n)))) ⁻¹' (badS n ζ)) ≤
      Beta n ζ := by
    rw [← map_measureReal_apply (measurable_piQ n) (badS_meas hn1 ζ), map_piQ hn1]
    exact tauBad137 hn hζ0
  calc μQ.real (goodQ n ζ)ᶜ ≤ μQ.real (_ ∪ _) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add h1 h2)

/-- The arithmetic of the terms at `θ = 1/10`, `ζ = 1/20`, for the scalar from one input. -/
lemma rate_arith2 {n : ℕ} (hn : 4096 ≤ n) :
    2 / 1000 + Beta n (1 / 20) + (2 * (99 / 100 / (n : ℝ)) + 8 * EH1 n (1 / 20)) *
        (4 / (n : ℝ)) / (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) +
      vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤
    2 / 1000 + 1977 / (n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have e : (2 * (99 / 100 / (n : ℝ)) + 8 * EH1 n (1 / 20)) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) =
      4 * (2 * (99 / 100 / (n : ℝ)) + 8 * EH1 n (1 / 20)) / (1 / 10 * (1 - kappa^[6] 0)) := by
    field_simp
  rw [e]
  have hv := vSpread_scale hn
  have hv0 : 0 ≤ vSpread n := by unfold vSpread; positivity
  have hEH := EH1_le hn
  have hB := Beta_le hn
  have hnm := n_div_mW_scale hn
  have hmsq := mW_ge_sq hn
  have hm0 : (0 : ℝ) < mW n := by nlinarith
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hEH' : EH1 n (1 / 20) ≤ 5200 / 262144 * t := by
    have e : 5200 * (n : ℝ) / (mW n : ℝ) = 5200 * ((n : ℝ) / (mW n : ℝ)) := by ring
    rw [e] at hEH
    have e2 : (1 : ℝ) / 262144 / (n : ℝ) = 1 / 262144 * t := by rw [ht]; ring
    rw [e2] at hnm
    linarith
  have hB' : Beta n (1 / 20) ≤ 1 / 10 * t := by
    refine hB.trans ?_
    rw [ht, div_le_iff₀ hm0]
    have : 1 / 10 * (1 / (n : ℝ)) * (mW n : ℝ) = (mW n : ℝ) / (10 * (n : ℝ)) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith
  have e99 : 99 / 100 / (n : ℝ) = 99 / 100 * t := by rw [ht]; ring
  have e64 : 64 / (n : ℝ) = 64 * t := by rw [ht]; ring
  have e1977 : 1977 / (n : ℝ) = 1977 * t := by rw [ht]; ring
  rw [e64] at hv
  have t1 : 4 * (2 * (99 / 100 / (n : ℝ)) + 8 * EH1 n (1 / 20)) /
      (1 / 10 * (1 - kappa^[6] 0)) ≤ 3841 / 10 * t := by
    rw [e99, div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hy)]
  have t2 : vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤ 15924 / 10 * t := by
    have hden : ((1 - 1 / 10) * (222757 / 1000000 : ℝ)) ^ 2 ≤
        ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  rw [e1977]
  linarith

/-- The success event of the estimate with the scalar from one input: `|g₁ − B| ≤ sd/2`. -/
def okTwo (n : ℕ) : Set ((Fin (2 * n) → ℝ) ×
    (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1)) :=
  {q | |gTwo q.1 q.2.1 q.2.2.1 q.2.2.2 - Part130.Bn q.2.1 q.2.2.1 q.2.2.2| ≤
    sdn q.2.1 q.2.2.1 q.2.2.2 / 2}

/-- **The estimate with the scalar from one uniform input succeeds (item 4, second half).** For
every `n ≥ 4096`, with `u₁` uniform on the unit sphere of `ℝ^{2n}` and independent of
`(W, A, F)`, and `g₁` the exact mean of `F∘A` over the distribution of `sphPt(M₃h̄ + τ₁γ)`,
`τ₁² = (2/m)|h̄|²·max(0, w(u₁))`:
`Pr(|g₁ − B| ≤ sd/2) ≥ 1 − (0.002 + 1977/n)`. -/
theorem standInTwo139_rate {n : ℕ} (hn : 4096 ≤ n) :
    1 - (2 / 1000 + 1977 / (n : ℝ)) ≤
      ((uniformSphere (2 * n)).prod (mlpTriple 2 n)).real (okTwo n) := by
  have hn1 : 1 ≤ n := by omega
  have := uniformSphere_isProbability (2 * n) (by omega)
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hs0 : (0 : ℝ) < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 := by
    have : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
    positivity
  have hEH1 : 0 ≤ EH1 n (1 / 20) := by
    have hC := C1_nonneg (n := n) (by norm_num : (0 : ℝ) ≤ 1 / 20) (by norm_num) zetaP_lt
    have h1 := Omega2_nonneg n (1 / 20)
    have h2 := (Beta_pos hn (by norm_num : (0 : ℝ) < 1 / 20)).le
    unfold EH1
    positivity
  have h1 := badQ_prob hn (ζ := 1 / 20) (by norm_num)
  have hlint := errTwo139_lint hn (ζ := 1 / 20) (by norm_num) (by norm_num) zetaP_lt
  have h2 : ((uniformSphere (2 * n)).prod (mlpTriple 2 n)).real
      {q : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) | q ∈ goodQ n (1 / 20) ∧
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 ≤
          (gTwo q.1 q.2.1 q.2.2.1 q.2.2.2 - Part130.Bn q.2.1 q.2.2.1 q.2.2.2) ^ 2} ≤
      (2 * (99 / 100 / (n : ℝ)) + 8 * EH1 n (1 / 20)) * (4 / (n : ℝ)) /
        (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      (tail_of_lint _ (measurable_errG2 hn1 (1 / 20)) (errG2_nonneg n (1 / 20))
        (by positivity) hlint hs0)
    rintro q ⟨hg, he⟩
    change _ ≤ errG2 n (1 / 20) q
    unfold errG2
    rw [Set.indicator_of_mem hg]
    exact he
  have h3 : ((uniformSphere (2 * n)).prod (mlpTriple 2 n)).real
      {q : (Fin (2 * n) → ℝ) × (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) | sdn q.2.1 q.2.2.1 q.2.2.2 ^ 2 <
          4 * (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4)} ≤
      vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 := by
    have e : (4 : ℝ) * (1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4) =
        1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by ring
    rw [e]
    exact (prod_snd_real (uniformSphere (2 * n)) (mlpTriple 2 n)
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < 1 / 10 * (4 / (n : ℝ) * (1 - kappa^[6] 0))}).trans_le
      (spreadLow139 hn (by norm_num))
  have h := ok_of_three ((uniformSphere (2 * n)).prod (mlpTriple 2 n))
    (d := fun q => gTwo q.1 q.2.1 q.2.2.1 q.2.2.2 - Part130.Bn q.2.1 q.2.2.1 q.2.2.2)
    (sd := fun q => sdn q.2.1 q.2.2.1 q.2.2.2) (fun q => sdn_nonneg' _ _ _) h1 h2 h3
  have ha := rate_arith2 hn
  exact le_trans (by linarith) h

end BstLean.Part139

open BstLean.Part139 in
#print axioms errFixedGen
open BstLean.Part139 in
#print axioms cheapFixed2
open BstLean.Part139 in
#print axioms errTwo139_lint
open BstLean.Part139 in
#print axioms standInTwo139_rate
