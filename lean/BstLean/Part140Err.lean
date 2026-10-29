import BstLean.Part140Cheap
import BstLean.Part139All

/-!
# Part 140, item 3: the error of the mean over the cheap stand-in with the computed centre

Role: `delegations/statements/p140-spec.md`, item 3. Paper sources: `onW17c-cx.md` §§5–6,
`MM-best-result.md` Theorem 3(a). The centre is the COMPUTED centre `b̂ = ψ_s(M₂ h̄₁)` of Part 137
and the scalar is `τ̂₀ = tauHat` (a function of `|b̂|²` and `n`): no exact `h̄` is used.

* `cheapHat W`: the cheap stand-in of `W = (M₁, M₂, M₃)` with the computed centre: the
  distribution of `sphPt(M₃ b̂ + τ̂₀γ)`.
* `gHat W A F = E_{cheapHat W} F(A(x))`: the estimate `ĝ` (an exact mean; no sampling).
* `goodWH n`: the good hidden event `goodHat n` as an event of `W`; `goodWH_prob`.
* **`errFixedHat`**: for fixed `(M₁, M₂) ∈ goodHat n`:
  `E_{A,F} E_{M₃} (Bn − gHat)² ≤ ((1 + η)·(1.83/n) + 4(1 + 1/η)·HbarH n ζ θ)·(4/n)`.
* **`errVecHat_lint`**, **`errVecHat`**: `E_{W,A,F}[1_good(W)·(gHat − Bn)²] ≤
  ((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ)·(4/n)`; **`errTailHat`**: the tail form.
The proofs are those of `Part139Err` with the centre `b̂`, the scalar `τ̂₀`, the event `goodHat n`
and the factor `1.83/n` of `standInHat140`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM

/-! ## The cheap stand-in of `W` with the computed centre, and the estimate -/

section defs

variable {N m n mA mF : ℕ}

/-- **The cheap stand-in of `W = (M₁, M₂, M₃)` with the computed centre**: the distribution of
`sphPt(M₃ b̂ + τ̂₀γ)`, `b̂ = ψ_s(M₂ h̄₁)`, `τ̂₀² = t|b̂|²·max(0, t|b̂|²/(γκ₁²) − 1)`. -/
noncomputable def cheapHat (W : MlpParam N m n) : Measure (Fin n → ℝ) :=
  cheapIn (W.2.2.mulVec (bhat (W.1, W.2.1))) (tauHat N m (W.1, W.2.1))

lemma cheapHat_prob (W : MlpParam N m n) : IsProbabilityMeasure (cheapHat W) := cheapIn_prob _ _

/-- `W ↦ E_{cheapHat W} φ` is bounded and measurable. -/
lemma bm_cheapHat (hN : 1 ≤ N) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    BM (fun W : MlpParam N m n => ∫ x, φ x ∂cheapHat W) := by
  have hθ : Measurable (fun W : MlpParam N m n => ((W.1, W.2.1) : HidParam N m)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun W : MlpParam N m n => W.2.2.mulVec (bhat (W.1, W.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp measurable_snd).prodMk ((measurable_bhat hN).comp hθ))
  exact bm_cheapIn hc ((measurable_tauHat hN).comp hθ) hφ

/-- **The estimate** `ĝ(W, A, F) = E_{cheapHat W} F(A(x))`: the exact mean of `F∘A` over the
cheap stand-in with the computed centre. -/
noncomputable def gHat (W : MlpParam N m n) (A : MlpParam n mA n) (F : MlpParam n mF 1) : ℝ :=
  ∫ x, phiN A F x ∂cheapHat W

/-- `ĝ` is jointly measurable in `(W, A, F)`. -/
lemma measurable_gHat (hN : 1 ≤ N) :
    Measurable (fun t : MlpParam N m n × MlpParam n mA n × MlpParam n mF 1 =>
      gHat t.1 t.2.1 t.2.2) := by
  have hθ : Measurable (fun W : MlpParam N m n => ((W.1, W.2.1) : HidParam N m)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun W : MlpParam N m n => W.2.2.mulVec (bhat (W.1, W.2.1))) :=
    measurable_mulVec_joint.comp
      ((measurable_snd.comp measurable_snd).prodMk ((measurable_bhat hN).comp hθ))
  have hτ : Measurable (fun W : MlpParam N m n => tauHat N m (W.1, W.2.1)) :=
    (measurable_tauHat hN).comp hθ
  have hW : Measurable (fun q : (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) => q.1.1) := measurable_fst.comp measurable_fst
  have hj : Measurable (fun q : (MlpParam N m n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) => phiN q.1.2.1 q.1.2.2
        (sphPt (q.1.1.2.2.mulVec (bhat (q.1.1.1, q.1.1.2.1)) +
          tauHat N m (q.1.1.1, q.1.1.2.1) • q.2))) :=
    BstLean.Part131.continuous_phiN_all.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_sphPt.comp ((hc.comp hW).add ((hτ.comp hW).smul measurable_snd))))
  have e : (fun t : MlpParam N m n × MlpParam n mA n × MlpParam n mF 1 =>
      gHat t.1 t.2.1 t.2.2) = fun t => ∫ γ, phiN t.2.1 t.2.2
        (sphPt (t.1.2.2.mulVec (bhat (t.1.1, t.1.2.1)) + tauHat N m (t.1.1, t.1.2.1) • γ))
        ∂stdGauss (Fin n) := by
    funext t
    unfold gHat cheapHat
    exact integral_cheapIn _ _ (continuous_phiN _ _).measurable
  rw [e]
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

end defs

/-! ## The good hidden event as an event of `W` -/

/-- The good hidden event `goodHat n` as an event of the whole World network. -/
def goodWH (n : ℕ) : Set (MlpParam (2 * n) (mW n) n) := {W | (W.1, W.2.1) ∈ goodHat n}

lemma goodWH_meas {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (goodWH n) :=
  (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) (goodHat_meas hn)

/-- `Pr_W(goodWH n) ≥ 1 − (0.002 + 70/n)` for `n ≥ 4096`. -/
theorem goodWH_prob {n : ℕ} (hn : 4096 ≤ n) :
    1 - (2 / 1000 + 70 / (n : ℝ)) ≤ (mlpGauss (2 * n) (mW n) n).real (goodWH n) := by
  have hmS := goodHat_meas (n := n) (by omega)
  have e : goodWH n =
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) ⁻¹' goodHat n := rfl
  have hmap : (mlpGauss (2 * n) (mW n) n).map
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) = hidGauss (2 * n) (mW n) := by
    unfold mlpGauss hidGauss
    have h1 : (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) =
        Prod.map id Prod.fst := by
      funext W; rfl
    rw [h1, ← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id,
      Measure.map_fst_prod]
    simp
  have hf : Measurable (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  rw [e, ← map_measureReal_apply hf hmS, hmap]
  exact goodHat_prob hn

/-! ## Fixed `(M₁, M₂)` -/

/-- **The error for fixed `(M₁, M₂)` on the good event.** For `n ≥ 4096`,
`θ = (M₁, M₂) ∈ goodHat n` and `0 ≤ ζ < 1`:
`E_{A,F} E_{M₃} (B − g₀)² ≤ ((1 + η)·(1.83/n) + 4(1 + 1/η)·HbarH n ζ θ)·(4/n)`. -/
theorem errFixedHat {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ goodHat n) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)))
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal (((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * HbarH n ζ θ) *
      (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have hH := HbarH_nonneg n ζ θ
  set b := bhat θ with hb
  set v : ℝ := 2 / (mW n : ℝ) with hv
  set τ₀ := tauHat (2 * n) (mW n) θ with hτ₀
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
  set a₁ : ℝ := (1 + η) * (183 / 100 / (n : ℝ)) + 2 * (1 + 1 / η) * HbarH n ζ θ with ha₁
  set a₂ : ℝ := 2 * (1 + 1 / η) * HbarH n ζ θ with ha₂
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; positivity
  have ha₂0 : 0 ≤ a₂ := by rw [ha₂]; positivity
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))) ≤
      ENNReal.ofReal a₁ * Lout P₁ o₁ p + ENNReal.ofReal a₂ * Lout P₂ o₂ p := by
    rintro ⟨A, F⟩
    have hφ : BM (phiS A F) := bm_phiS hn1 A F
    have h0 := cheapStandInHat hn hθ hζ0 hζ1 hη hφ 0
    simp only [sub_zero] at h0
    -- the left side
    have eL : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
        ((∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
          ∫ x, phiS A F x ∂cheapIn (M₃.mulVec (bhat θ)) (tauHat (2 * n) (mW n) θ)) ^ 2 =
        (Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2 := by
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
    have hc : (0 : ℝ) ≤ 183 / 100 / (n : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hVle hc
    rw [ha₁, ha₂]
    change _ ≤ ((1 + η) * (183 / 100 / (n : ℝ)) + 2 * (1 + 1 / η) * HbarH n ζ θ) *
        (∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) +
      2 * (1 + 1 / η) * HbarH n ζ θ * ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂
    change _ ≤ (1 + η) * (183 / 100 / (n : ℝ) *
        ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) h v b c] ∂cDist n v b) +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        ((∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) + ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂) at h0
    change 183 / 100 / (n : ℝ) *
        ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) h v b c] ∂cDist n v b ≤
      183 / 100 / (n : ℝ) * ∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁ at this
    have this' := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 + η)
    have e3 : ((1 + η) * (183 / 100 / (n : ℝ)) + 2 * (1 + 1 / η) * HbarH n ζ θ) *
        (∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) +
      2 * (1 + 1 / η) * HbarH n ζ θ * ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂ =
      (1 + η) * (183 / 100 / (n : ℝ) * ∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        ((∫ ω, phiS A F (o₁ ω) ^ 2 ∂P₁) + ∫ ω, phiS A F (o₂ ω) ^ 2 ∂P₂) := by ring
    rw [e3]
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
noncomputable def errGH (n : ℕ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodWH n).indicator (fun W => (gHat W t.2.1 t.2.2 - Part130.Bn W t.2.1 t.2.2) ^ 2) t.1

lemma errGH_nonneg (n : ℕ)
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ errGH n t :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_errGH {n : ℕ} (hn : 1 ≤ n) : Measurable (errGH n) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errGH n = ({t | t.1 ∈ goodWH n} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gHat t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    by_cases ht : t.1 ∈ goodWH n
    · rw [Set.indicator_of_mem (show t ∈ {t : MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1 | t.1 ∈ goodWH n} from ht)]
      unfold errGH
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem (show t ∉ {t : MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1 | t.1 ∈ goodWH n} from ht)]
      unfold errGH
      rw [Set.indicator_of_notMem ht]
  rw [e]
  exact (((measurable_gHat hN).sub (BstLean.Part131.measurable_Bn hN)).pow_const 2).indicator
    (measurable_fst (goodWH_meas hn))

section joint

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η)

include hn hζ0 hζ1 hη

/-- **Item 1 (`errVecHat`), as an integral of a nonnegative function.** For `n ≥ 4096` and
`0 < ζ < 1`: `E_{W,A,F}[1_good(W)·(g₀ − B)²] ≤ ((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ)·(4/n)`. -/
theorem errVecHat_lint :
    ∫⁻ t, ENNReal.ofReal (errGH n t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have mE := goodHat_meas (n := n) hn1
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (errGH n t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_errGH hn1)
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
  set a : ℝ := (1 + η) * (183 / 100 / (n : ℝ)) with ha
  set S : ℝ := 4 / (n : ℝ) with hS
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    a * S * (goodHat n).indicator (fun _ => (1 : ℝ)) θ +
      4 * (1 + 1 / η) * S * (goodHat n).indicator (HbarH n ζ) θ with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have h1 : 0 ≤ (goodHat n).indicator (fun _ => (1 : ℝ)) θ :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h2 : 0 ≤ (goodHat n).indicator (HbarH n ζ) θ :=
      Set.indicator_nonneg (fun θ _ => HbarH_nonneg n ζ θ) _
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
    by_cases hθ : θ ∈ goodHat n
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWH n := fun M₃ => hθ
      have hin : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM =
          ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)
            p.1 p.2 - gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2 ∂gM) := by
        rintro ⟨A, F⟩
        have hφ : BM (phiS A F) := bm_phiS hn1 A F
        have hb : BM (fun W : MlpParam (2 * n) (mW n) n =>
            ((∫ x, phiS A F x ∂muWn W) - ∫ x, phiS A F x ∂cheapHat W) ^ 2) :=
          ((bm_muW hN hφ).sub (bm_cheapHat hN hφ)).sq
        have hb' : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
              gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2) := by
          have h1 := hb.comp (g := fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n))
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))
          refine ⟨?_, h1.bdd.imp fun M hM M₃ => ?_⟩
          · convert h1.meas using 2 with M₃
            rw [integral_phiS_muWn hn1]
            unfold cheapHat gHat
            rw [integral_phiS_cheapIn hn1]
            rfl
          · have := hM M₃
            rw [integral_phiS_muWn hn1] at this
            unfold cheapHat at this
            rw [integral_phiS_cheapIn hn1] at this
            exact this
        rw [ofReal_integral_eq_lintegral_ofReal (hb'.integrable gM)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        refine lintegral_congr fun M₃ => ?_
        simp only [hf, errGH, Set.indicator_of_mem (hW M₃)]
        congr 1
        ring
      simp_rw [hin]
      refine (errFixedHat hn hθ hζ0.le hζ1 hη).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hk]
      simp only [Set.indicator_of_mem hθ]
      rw [ha, hS]
      apply le_of_eq
      ring
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWH n := fun M₃ => hθ
      have hz : ∀ (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
          (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ),
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) = 0 := by
        intro p M₃
        simp only [hf, errGH, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero]
      simp_rw [hz]
      simp
  obtain ⟨iH, hH⟩ := HbarH_mean hn hζ0 hζ1
  have i1 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      a * S * (goodHat n).indicator (fun _ => (1 : ℝ)) θ) (hidGauss (2 * n) (mW n)) :=
    ((integrable_const (1 : ℝ)).indicator mE).const_mul _
  have i2 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      4 * (1 + 1 / η) * S * (goodHat n).indicator (HbarH n ζ) θ) (hidGauss (2 * n) (mW n)) := iH.const_mul _
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := i1.add i2
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_add i1 i2, integral_const_mul, integral_const_mul]
        have e1 : ∫ θ, (goodHat n).indicator (fun _ => (1 : ℝ)) θ ∂hidGauss (2 * n) (mW n) ≤ 1 := by
          rw [integral_indicator mE, setIntegral_const, smul_eq_mul, mul_one]
          exact measureReal_le_one
        have h1 := mul_le_mul_of_nonneg_left e1 (mul_nonneg ha0 hS0)
        have h2 := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 4 * (1 + 1 / η) * S)
        nlinarith

/-- **Item 1 (`errVecHat`).** For `n ≥ 4096` and `0 < ζ < 1`: `1_good(W)·(g₀ − B)²` is
integrable over `(W, A, F)`, and
`E_{W,A,F}[1_good(W)·(g₀ − B)²] ≤ ((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ)·(4/n)`. -/
theorem errVecHat :
    Integrable (errGH n) (mlpTriple 2 n) ∧
      ∫ t, errGH n t ∂mlpTriple 2 n ≤ ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := errVecHat_lint hn hζ0 hζ1 hη
  have hEH := EHH_nonneg hn ζ
  have hc : (0 : ℝ) ≤ ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ)) := by positivity
  have h0 : 0 ≤ᵐ[mlpTriple 2 n] errGH n := Filter.Eventually.of_forall (errGH_nonneg n)
  have hm := (measurable_errGH hn1).aestronglyMeasurable (μ := mlpTriple 2 n)
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
  exact ENNReal.toReal_le_of_le_ofReal hc h

/-- **The tail form of item 1.** For `s > 0`:
`Pr_{W,A,F}(W good and (g₀ − B)² ≥ s) ≤ ((1 + η)·(1.83/n) + 4(1 + 1/η)·EHH n ζ)·(4/n)/s`. -/
theorem errTailHat {s : ℝ} (hs : 0 < s) :
    (mlpTriple 2 n).real {t | s ≤ errGH n t} ≤
      ((1 + η) * (183 / 100 / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ)) / s := by
  obtain ⟨hi, hb⟩ := errVecHat hn hζ0 hζ1 hη
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := mlpTriple 2 n) (f := errGH n)
    (Filter.Eventually.of_forall (errGH_nonneg n)) hi s
  rw [le_div_iff₀ hs]
  linarith

end joint

end BstLean.Part140

open BstLean.Part140 in
#print axioms goodWH_prob
open BstLean.Part140 in
#print axioms errFixedHat
open BstLean.Part140 in
#print axioms errVecHat_lint
open BstLean.Part140 in
#print axioms errVecHat
open BstLean.Part140 in
#print axioms errTailHat
