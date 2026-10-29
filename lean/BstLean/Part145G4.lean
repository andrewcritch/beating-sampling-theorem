import BstLean.Part145G3
import BstLean.Part142Spread

/-!
# Part 145 (abstract good hidden event), file 4: the variance constant from the distance kernel

`XALV Lc e n ζ η η′`: `XAL Lc n ζ η η′` of Part 143 with `1 − κ^{∘6}(0) + e` in the place of
`1 − κ^{∘6}(0) + σ₄·(eWr + sU) + eAFr`. The number `e` is a bound of the `L²` distance of the
distance kernel `kD` of Part 142 from `(4/n)(1 − κ^{∘6}(0))` (the hypothesis `hD`).

* `lint_phi_dk`: `E_{A,F}(F(A(x)) − F(A(x′)))²/2 = E_{A,F} dk F A x x′`.
* `LDV n θ`, `DKV n θ = (n/4)·LDV n θ`: for fixed `θ = (M₁, M₂)`, the mean over `M₃`, `(u, u′)`,
  `A`, `F` of `(F(A(x(u))) − F(A(x(u′))))²/2`. `lint_LDV_kD`: `E_θ LDV = E kD`.
* `DKV_mean`: `E_θ DKV ≤ 1 − κ^{∘6}(0) + e`.
* **`errSampleAGV_lint`**: `errSampleAG_lint` with `XALV Lc e`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open BstLean.Part143
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-! ## The distance kernel as a mean squared difference -/

section kernel

variable {N mW n mA mF : ℕ}

/-- The mean over `(A, F)` of half the squared difference is the mean of the distance kernel
`dk` (the mean over the last matrix of `F` is `F3_diff`). -/
lemma lint_phi_dk (x x' : Fin n → ℝ) :
    ∫⁻ p : MlpParam n mA n × MlpParam n mF 1,
      ENNReal.ofReal ((phiN p.1 p.2 x - phiN p.1 p.2 x') ^ 2 / 2)
      ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) =
    ∫⁻ p : MlpParam n mA n × MlpParam n mF 1, ENNReal.ofReal (dk p.2 p.1 x x')
      ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) := by
  set Gf : MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((phiN p.1 p.2 x - phiN p.1 p.2 x') ^ 2 / 2) with hGf
  set H : MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (dk p.2 p.1 x x') with hH
  have mphi : ∀ y : Fin n → ℝ, Measurable (fun p : MlpParam n mA n × MlpParam n mF 1 =>
      phiN p.1 p.2 y) := fun y =>
    BstLean.Part131.continuous_phiN_all.measurable.comp (measurable_id.prodMk measurable_const)
  have mG : Measurable Gf :=
    ENNReal.measurable_ofReal.comp ((((mphi x).sub (mphi x')).pow_const 2).div_const 2)
  have mH : Measurable H := ENNReal.measurable_ofReal.comp (measurable_dk x x')
  rw [lintegral_prod _ mG.aemeasurable, lintegral_prod _ mH.aemeasurable]
  refine lintegral_congr fun A => ?_
  have mGA : Measurable (fun F : MlpParam n mF 1 => Gf (A, F)) :=
    mG.comp (measurable_const.prodMk measurable_id)
  have mHA : Measurable (fun F : MlpParam n mF 1 => H (A, F)) :=
    mH.comp (measurable_const.prodMk measurable_id)
  change ∫⁻ F, Gf (A, F) ∂((gaussMat mF n (2 / (n : ℝ))).prod
      ((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ))))) =
    ∫⁻ F, H (A, F) ∂((gaussMat mF n (2 / (n : ℝ))).prod
      ((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))))
  rw [lintegral_prod _ mGA.aemeasurable, lintegral_prod _ mHA.aemeasurable]
  refine lintegral_congr fun F₁ => ?_
  have mGF : Measurable (fun q : Matrix (Fin mF) (Fin mF) ℝ × Matrix (Fin 1) (Fin mF) ℝ =>
      Gf (A, (F₁, q))) := mGA.comp (measurable_const.prodMk measurable_id)
  have mHF : Measurable (fun q : Matrix (Fin mF) (Fin mF) ℝ × Matrix (Fin 1) (Fin mF) ℝ =>
      H (A, (F₁, q))) := mHA.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ mGF.aemeasurable, lintegral_prod _ mHF.aemeasurable]
  refine lintegral_congr fun F₂ => ?_
  obtain ⟨hi, he⟩ := F3_diff A F₁ F₂ 0 x x'
  have eL : ∫⁻ F₃, Gf (A, (F₁, (F₂, F₃))) ∂gaussMat 1 mF (2 / (mF : ℝ)) =
      ENNReal.ofReal (dk (F₁, F₂, 0) A x x') := by
    rw [← he]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => by positivity)).symm
  have eR : ∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ, H (A, (F₁, (F₂, F₃))) =
      ENNReal.ofReal (dk (F₁, F₂, 0) A x x') := fun F₃ => rfl
  rw [eL]
  simp_rw [eR]
  simp

/-- The distance kernel `dk` at the points `x(u)`, `x(u′)` is measurable in
`((A, F), (W, (u, u′)))`. -/
lemma measurable_dkW :
    Measurable (fun q : (MlpParam n mA n × MlpParam n mF 1) ×
        (MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) =>
      ENNReal.ofReal (dk q.1.2 q.1.1 (xW q.2.1 q.2.2.1) (xW q.2.1 q.2.2.2))) := by
  have hF : Measurable (fun q : (MlpParam n mA n × MlpParam n mF 1) ×
      (MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hA : Measurable (fun q : (MlpParam n mA n × MlpParam n mF 1) ×
      (MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hx : Measurable (fun q : (MlpParam n mA n × MlpParam n mF 1) ×
      (MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) => xW q.2.1 q.2.2.1) :=
    measurable_xW_comp (measurable_fst.comp measurable_snd)
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hx' : Measurable (fun q : (MlpParam n mA n × MlpParam n mF 1) ×
      (MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) => xW q.2.1 q.2.2.2) :=
    measurable_xW_comp (measurable_fst.comp measurable_snd)
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  unfold dk
  exact ENNReal.measurable_ofReal.comp
    ((((measurable_kern_comp hF hA hA hx hx).add
      (measurable_kern_comp hF hA hA hx' hx')).div_const 2).sub
      (measurable_kern_comp hF hA hA hx hx'))

/-- The mean over `(A, F)` of the distance kernel at the points `x(u)`, `x(u′)`, a function of
`(W, (u, u′))`. -/
noncomputable def KW (z : MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) : ℝ≥0∞ :=
  ∫⁻ p : MlpParam n mA n × MlpParam n mF 1,
    ENNReal.ofReal (dk p.2 p.1 (xW z.1 z.2.1) (xW z.1 z.2.2))
    ∂((mlpGauss n mA n).prod (mlpGauss n mF 1))

lemma measurable_KW :
    Measurable (KW (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) :=
  (measurable_dkW (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)).lintegral_prod_left'

/-- The mean of the distance kernel `kD` under `(u, u′) ⊗ (W, A, A′, F)` is the mean of `KW`
under `W ⊗ (u, u′)`. -/
lemma lint_kD_eq (hN : 1 ≤ N) :
    ∫⁻ ω, ENNReal.ofReal (kD ω) ∂((lawU2 N).prod (lawR N mW n mA mF)) =
      ∫⁻ z, KW (mA := mA) (mF := mF) z ∂((mlpGauss N mW n).prod (lawU2 N)) := by
  have := lawU2_prob hN
  have mk : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      ENNReal.ofReal (kD ω)) := ENNReal.measurable_ofReal.comp measurable_kD
  rw [lintegral_prod_symm _ mk.aemeasurable,
    lintegral_prod _ (measurable_KW (mA := mA) (mF := mF)).aemeasurable]
  set g : Rest N mW n mA mF → ℝ≥0∞ := fun r => ∫⁻ uu, ENNReal.ofReal (kD (uu, r)) ∂lawU2 N
    with hg
  have mg : Measurable g := mk.lintegral_prod_left'
  unfold lawR
  rw [lintegral_prod g mg.aemeasurable]
  refine lintegral_congr fun W => ?_
  obtain ⟨h, hh⟩ : ∃ h : MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞, h = fun p =>
    ∫⁻ uu, ENNReal.ofReal (dk p.2 p.1 (xW W uu.1) (xW W uu.2)) ∂lawU2 N := ⟨_, rfl⟩
  have mΨ : Measurable (fun q : ((Fin N → ℝ) × (Fin N → ℝ)) ×
      (MlpParam n mA n × MlpParam n mF 1) =>
      ENNReal.ofReal (dk q.2.2 q.2.1 (xW W q.1.1) (xW W q.1.2))) :=
    Measurable.comp (f := fun q : ((Fin N → ℝ) × (Fin N → ℝ)) ×
        (MlpParam n mA n × MlpParam n mF 1) => (q.2, (W, q.1)))
      (measurable_dkW (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))
      (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))
  have mh : Measurable h := by rw [hh]; exact mΨ.lintegral_prod_left'
  have mdrop : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      (p.1, p.2.2)) := measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have e1 : ∀ q : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1,
      g (W, q) = h (q.1, q.2.2) := fun q => by
    rw [hh]
    exact lintegral_congr fun uu => by rw [kD_eq]; rfl
  rw [lintegral_congr e1]
  have e2 := lintegral_map (μ := (mlpGauss n mA n).prod
    ((mlpGauss n mA n).prod (mlpGauss n mF 1))) mh mdrop
  rw [map_dropMid] at e2
  rw [← e2, hh]
  exact lintegral_lintegral_swap
    (f := fun (p : MlpParam n mA n × MlpParam n mF 1) (uu : (Fin N → ℝ) × (Fin N → ℝ)) =>
      ENNReal.ofReal (dk p.2 p.1 (xW W uu.1) (xW W uu.2)))
    (Measurable.comp (f := Prod.swap) mΨ measurable_swap).aemeasurable

end kernel

/-! ## Fixed `(M₁, M₂)` -/

/-- For fixed `θ = (M₁, M₂)`: the mean over `(A, F)`, `M₃` and `(u, u′)` of
`(F(A(x(u))) − F(A(x(u′))))²/2`. -/
noncomputable def LDV (n : ℕ) (θ : HidParam (2 * n) (mW n)) : ℝ≥0∞ :=
  ∫⁻ p, LoutD (mA := mA n) (mF := mF n)
      ((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n))) (oD1 θ) (oD2 θ) p
    ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1))

lemma LDV_eq_KW {n : ℕ} (hn : 1 ≤ n) (θ : HidParam (2 * n) (mW n)) :
    LDV n θ = ∫⁻ ω : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)),
      KW (mA := mA n) (mF := mF n) (((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n), ω.2)
      ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n))) := by
  have := lawU2_prob (N := 2 * n) (by omega)
  unfold LDV LoutD
  rw [lintegral_lintegral_swap
    (f := fun (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
      (ω : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ))) =>
      ENNReal.ofReal ((phiS p.1 p.2 (oD1 θ ω) - phiS p.1 p.2 (oD2 θ ω)) ^ 2 / 2))
    (ENNReal.measurable_ofReal.comp ((((measurable_phiS_out (measurable_oD1 θ)).sub
      (measurable_phiS_out (measurable_oD2 θ))).pow_const 2).div_const 2)).aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact lint_phi_dk (sphPt (oD1 θ ω)) (sphPt (oD2 θ ω))

lemma measurable_LDV {n : ℕ} (hn : 1 ≤ n) : Measurable (LDV n) := by
  have := lawU2_prob (N := 2 * n) (by omega)
  have e : LDV n = fun θ : HidParam (2 * n) (mW n) =>
      ∫⁻ ω : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)),
      KW (mA := mA n) (mF := mF n) (((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n), ω.2)
      ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n))) :=
    funext fun θ => LDV_eq_KW hn θ
  rw [e]
  exact Measurable.lintegral_prod_right'
    (f := fun q : HidParam (2 * n) (mW n) ×
      (Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ))) =>
      KW (mA := mA n) (mF := mF n)
        (((q.1.1, q.1.2, q.2.1) : MlpParam (2 * n) (mW n) n), q.2.2))
    (measurable_KW.comp ((((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))).prodMk
        (measurable_snd.comp measurable_snd)))

/-- **`E_θ LDV = E kD`.** -/
theorem lint_LDV_kD {n : ℕ} (hn : 1 ≤ n) :
    ∫⁻ θ, LDV n θ ∂hidGauss (2 * n) (mW n) =
      ∫⁻ ω, ENNReal.ofReal (kD ω)
        ∂((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n))) := by
  have hN : 1 ≤ 2 * n := by omega
  have := lawU2_prob hN
  rw [lint_kD_eq hN]
  simp_rw [LDV_eq_KW hn]
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set K2 : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W =>
    ∫⁻ uu, KW (mA := mA n) (mF := mF n) (W, uu) ∂lawU2 (2 * n) with hK2
  have mK2 : Measurable K2 :=
    (measurable_KW (mA := mA n) (mF := mF n)).lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  rw [lintegral_prod _ (measurable_KW (mA := mA n) (mF := mF n)).aemeasurable]
  change _ = ∫⁻ W, K2 W ∂mlpGauss (2 * n) (mW n) n
  rw [e, lintegral_map mK2 MeasurableEquiv.prodAssoc.measurable,
    lintegral_prod (fun a => K2 (MeasurableEquiv.prodAssoc a))
      (mK2.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable]
  refine lintegral_congr fun θ => ?_
  rw [lintegral_prod (fun ω : Matrix (Fin n) (Fin (mW n)) ℝ ×
      ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) => KW (mA := mA n) (mF := mF n)
        (((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n), ω.2))
    ((measurable_KW (mA := mA n) (mF := mF n)).comp
    ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
      measurable_snd)).aemeasurable]
  rfl

/-- `DKV n θ = (n/4)·LDV n θ`: the mean squared difference for fixed `θ`, in units of `4/n`. -/
noncomputable def DKV (n : ℕ) (θ : HidParam (2 * n) (mW n)) : ℝ :=
  (n : ℝ) / 4 * (LDV n θ).toReal

lemma DKV_nonneg (n : ℕ) (θ : HidParam (2 * n) (mW n)) : 0 ≤ DKV n θ := by
  unfold DKV
  positivity

lemma LDV_eq_ofReal {n : ℕ} (hn : 4096 ≤ n) (θ : HidParam (2 * n) (mW n)) :
    LDV n θ = ENNReal.ofReal (4 / (n : ℝ) * DKV n θ) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hne : LDV n θ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lint_LoutD_theta (mA := mA n) (mF := mF n) hn1 hmA hmF θ)
  unfold DKV
  rw [← mul_assoc, show 4 / (n : ℝ) * ((n : ℝ) / 4) = 1 by field_simp, one_mul,
    ENNReal.ofReal_toReal hne]

/-- **The mean of `DKV`** from the `L²` bound of the distance kernel:
`E_θ DKV ≤ 1 − κ^{∘6}(0) + e`. -/
theorem DKV_mean {n : ℕ} (hn : 4096 ≤ n) {e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e)) :
    Integrable (DKV n) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, DKV n θ ∂hidGauss (2 * n) (mW n) ≤ 1 - kappa^[6] 0 + e := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := lawU2_prob hN
  set μ := (lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)) with hμ
  have iK : Integrable (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
      Rest (2 * n) (mW n) n (mA n) (mF n) => kD ω) μ :=
    (memLp_of_L2le_sub hD).integrable one_le_two
  have hK0 : ∀ ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
      Rest (2 * n) (mW n) n (mA n) (mF n), 0 ≤ kD ω := fun ω =>
    (show 0 ≤ kD ω from dk_nonneg ω.2.2.2.2 ω.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2))
  have hKle : ∫ ω, kD ω ∂μ ≤ 4 / (n : ℝ) * (1 - kappa^[6] 0 + e) := by
    have h1 := sq_integral_le hD.int_sq
    have h2 := h1.trans hD.le
    have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
    have h4 : ∫ ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
        Rest (2 * n) (mW n) n (mA n) (mF n), (kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) ∂μ =
        (∫ ω, kD ω ∂μ) - 4 / (n : ℝ) * (1 - kappa^[6] 0) := by
      rw [integral_sub iK (integrable_const _)]
      simp
    rw [h4] at h3
    linarith [h3.2]
  have hL : ∫⁻ θ, LDV n θ ∂hidGauss (2 * n) (mW n) = ENNReal.ofReal (∫ ω, kD ω ∂μ) := by
    rw [lint_LDV_kD hn1, ofReal_integral_eq_lintegral_ofReal iK
      (Filter.Eventually.of_forall hK0)]
  have hfin : ∀ θ : HidParam (2 * n) (mW n), LDV n θ < ⊤ := fun θ => by
    rw [LDV_eq_ofReal hn θ]
    exact ENNReal.ofReal_lt_top
  have iT : Integrable (fun θ : HidParam (2 * n) (mW n) => (LDV n θ).toReal)
      (hidGauss (2 * n) (mW n)) :=
    integrable_toReal_of_lintegral_ne_top (measurable_LDV hn1).aemeasurable
      (by rw [hL]; exact ENNReal.ofReal_ne_top)
  have eT : ∫ θ, (LDV n θ).toReal ∂hidGauss (2 * n) (mW n) = ∫ ω, kD ω ∂μ := by
    rw [integral_toReal (measurable_LDV hn1).aemeasurable (Filter.Eventually.of_forall hfin), hL,
      ENNReal.toReal_ofReal (integral_nonneg hK0)]
  refine ⟨iT.const_mul _, ?_⟩
  unfold DKV
  rw [integral_const_mul, eT]
  have h5 := mul_le_mul_of_nonneg_left hKle (by positivity : (0 : ℝ) ≤ (n : ℝ) / 4)
  have e5 : (n : ℝ) / 4 * (4 / (n : ℝ) * (1 - kappa^[6] 0 + e)) = 1 - kappa^[6] 0 + e := by
    field_simp
  linarith

/-! ## The numbers -/

/-- `VbL Lc n` of Part 143 with `e` in the place of `σ₄·(eWr + sU) + eAFr`. -/
noncomputable def VbV (Lc e : ℝ) (n : ℕ) : ℝ :=
  1 - kappa^[6] 0 + e + Lc / (n : ℝ)

/-- `XAL Lc n ζ η η′` of Part 143 with `e` in the place of `σ₄·(eWr + sU) + eAFr`. -/
noncomputable def XALV (Lc e : ℝ) (n : ℕ) (ζ η η' : ℝ) : ℝ :=
  (1 + η') * ((1 + η) * (Lc / (n : ℝ)) * (1 - kappa^[6] 0 + e + Lc / (n : ℝ)) +
    4 * (1 + 1 / η) * EHH n ζ) + (1 + 1 / η') * pertA n

lemma XALV_eq (Lc e : ℝ) (n : ℕ) (ζ η η' : ℝ) :
    XALV Lc e n ζ η η' = (1 + η') * ((1 + η) * (Lc / (n : ℝ)) * VbV Lc e n +
      4 * (1 + 1 / η) * EHH n ζ) + (1 + 1 / η') * pertA n := rfl

lemma VbV_nonneg {n : ℕ} {Lc : ℝ} (hLc0 : 0 ≤ Lc) {e : ℝ} (he : 0 ≤ e) : 0 ≤ VbV Lc e n := by
  have h1 : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have h2 : (0 : ℝ) ≤ Lc / (n : ℝ) := by positivity
  unfold VbV
  linarith

lemma XALV_nonneg {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) {e : ℝ} (he : 0 ≤ e)
    (ζ : ℝ) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') : 0 ≤ XALV Lc e n ζ η η' := by
  have hV := VbV_nonneg (n := n) hLc0 he
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  rw [XALV_eq]
  positivity

/-! ## The chain with `DKV` -/

section fixedV

variable {n : ℕ} {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)

include hG

/-- **The error for fixed `(M₁, M₂)` on the good event, with the variance of the stand-in.**
For `n ≥ 4096`, `θ = (M₁, M₂) ∈ G` and `0 ≤ ζ < 1`:
`E_{A,F} E_{M₃}(Bn − gHat)² ≤
  ((1 + η)(Lc/n)(DKV n θ + Lc/n) + 4(1 + 1/η)·HbarH n ζ θ)·(4/n)`. -/
theorem errFixedHatLGV (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ G) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)))
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal (((1 + η) * (Lc / (n : ℝ)) *
        (DKV n θ + Lc / (n : ℝ)) +
      4 * (1 + 1 / η) * HbarH n ζ θ) * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have := lawU2_prob hN
  have hH := HbarH_nonneg n ζ θ
  have hD0 := DKV_nonneg n θ
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set Pa := gM.prod (uniformSphere (2 * n)) with hPa
  set Pd := gM.prod (lawU2 (2 * n)) with hPd
  set P₁ := (stdGauss (Fin n)).prod ((uniformSphere (2 * n)).prod (stdGauss (Fin n))) with hP₁
  set P₂ := (stdGauss (Fin n)).prod (stdGauss (Fin n)) with hP₂
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set c : ℝ := (1 + η) * ((l ^ 2) / (n : ℝ)) with hc
  set δ : ℝ := (l ^ 2) / (n : ℝ) with hδ
  set a₂ : ℝ := 2 * (1 + 1 / η) * HbarH n ζ θ with ha₂
  set S : ℝ := 4 / (n : ℝ) with hS
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have ha₂0 : 0 ≤ a₂ := by rw [ha₂]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  set Lf : MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ := fun p =>
    ∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
      gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2 ∂gM with hLf
  have m1 := measurable_Lout (mA := mA n) (mF := mF n) P₁ (measurable_o1 θ)
  have m2 := measurable_Lout (mA := mA n) (mF := mF n) P₂ (measurable_o2 θ)
  have ma := measurable_Lout (mA := mA n) (mF := mF n) Pa (measurable_oA θ)
  have md := measurable_LoutD (mA := mA n) (mF := mF n) Pd (measurable_oD1 θ) (measurable_oD2 θ)
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (Lf p) + ENNReal.ofReal c * Lout Pa (oA θ) p ≤
        ENNReal.ofReal (c * (1 + δ)) * Lout P₁ (o1 θ) p +
          ENNReal.ofReal c * LoutD Pd (oD1 θ) (oD2 θ) p +
          ENNReal.ofReal a₂ * (Lout P₁ (o1 θ) p + Lout P₂ (o2 θ) p) := by
    rintro ⟨A, F⟩
    have hr := fixedG_realL hG hn hLc0 hθ hζ0 hζ1 hη A F
    have iL : 0 ≤ Lf (A, F) := integral_nonneg fun _ => sq_nonneg _
    have ia : 0 ≤ ∫ ω, phiS A F (oA θ ω) ^ 2 ∂Pa := integral_nonneg fun _ => sq_nonneg _
    have i1 : 0 ≤ ∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁ := integral_nonneg fun _ => sq_nonneg _
    have i2 : 0 ≤ ∫ ω, phiS A F (o2 θ ω) ^ 2 ∂P₂ := integral_nonneg fun _ => sq_nonneg _
    have id' : 0 ≤ ∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2 ∂Pd :=
      integral_nonneg fun _ => by positivity
    rw [← ofReal_integral_out Pa hn1 A F (measurable_oA θ),
      ← ofReal_integral_out P₁ hn1 A F (measurable_o1 θ),
      ← ofReal_integral_out P₂ hn1 A F (measurable_o2 θ),
      ← ofReal_integral_outD Pd hn1 A F (measurable_oD1 θ) (measurable_oD2 θ)]
    have eLHS : ENNReal.ofReal (Lf (A, F)) +
        ENNReal.ofReal c * ENNReal.ofReal (∫ ω, phiS A F (oA θ ω) ^ 2 ∂Pa) =
        ENNReal.ofReal (Lf (A, F) + c * ∫ ω, phiS A F (oA θ ω) ^ 2 ∂Pa) := by
      rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add iL (mul_nonneg hc0 ia)]
    have eRHS : ENNReal.ofReal (c * (1 + δ)) * ENNReal.ofReal (∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁) +
        ENNReal.ofReal c *
          ENNReal.ofReal (∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2 ∂Pd) +
        ENNReal.ofReal a₂ * (ENNReal.ofReal (∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁) +
          ENNReal.ofReal (∫ ω, phiS A F (o2 θ ω) ^ 2 ∂P₂)) =
        ENNReal.ofReal (c * (1 + δ) * (∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁) +
          c * (∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2 ∂Pd) +
          a₂ * ((∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁) + ∫ ω, phiS A F (o2 θ ω) ^ 2 ∂P₂)) := by
      have hcd : 0 ≤ c * (1 + δ) := by positivity
      rw [← ENNReal.ofReal_add i1 i2, ← ENNReal.ofReal_mul hcd, ← ENNReal.ofReal_mul hc0,
        ← ENNReal.ofReal_mul ha₂0, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [eLHS, eRHS]
    exact ENNReal.ofReal_le_ofReal hr
  have hSa := lintegral_Lout (mA := mA n) (mF := mF n) Pa hn1 hmA hmF (measurable_oA θ)
  have hS1 := lintegral_Lout (mA := mA n) (mF := mF n) P₁ hn1 hmA hmF (measurable_o1 θ)
  have hS2 := lintegral_Lout (mA := mA n) (mF := mF n) P₂ hn1 hmA hmF (measurable_o2 θ)
  have hSd : LDV n θ ≤ ENNReal.ofReal (S * DKV n θ) := (LDV_eq_ofReal hn θ).le
  have hint := lintegral_mono (μ := PAF) key
  have mX2 : Measurable (fun a : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      ENNReal.ofReal c * LoutD Pd (oD1 θ) (oD2 θ) a) := md.const_mul _
  have mS : Measurable (fun a : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      Lout P₁ (o1 θ) a + Lout P₂ (o2 θ) a) := m1.add m2
  have mX3 : Measurable (fun a : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      ENNReal.ofReal a₂ * (Lout P₁ (o1 θ) a + Lout P₂ (o2 θ) a)) := mS.const_mul _
  have mXa : Measurable (fun a : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      ENNReal.ofReal c * Lout Pa (oA θ) a) := ma.const_mul _
  rw [lintegral_add_right _ mXa, lintegral_const_mul _ ma, hSa,
    lintegral_add_right _ mX3, lintegral_add_right _ mX2, lintegral_const_mul _ m1,
    lintegral_const_mul _ md, lintegral_const_mul _ mS, lintegral_add_right _ m2, hS1, hS2]
    at hint
  have hfin : ∫⁻ p, ENNReal.ofReal (Lf p) ∂PAF + ENNReal.ofReal (c * S) ≤
      ENNReal.ofReal (c * (1 + δ) * S + c * (S * DKV n θ) +
        a₂ * (S + S)) := by
    rw [ENNReal.ofReal_mul (q := S) hc0]
    refine hint.trans ?_
    have hD0' : 0 ≤ S * DKV n θ := by positivity
    have hcd : 0 ≤ c * (1 + δ) := by positivity
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (q := S) hcd,
      ENNReal.ofReal_mul (q := S * DKV n θ) hc0,
      ENNReal.ofReal_mul (q := S + S) ha₂0, ENNReal.ofReal_add hS0 hS0]
    exact add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hSd)) le_rfl
  have h2 := ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hfin
  rw [← ENNReal.ofReal_sub _ (mul_nonneg hc0 hS0)] at h2
  refine h2.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [ha₂]
  ring

end fixedV

/-- **`errVecHatG_lint` with the variance constant from the distance kernel.** -/
theorem errVecHatGV_lint {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc) {e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e))
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) :
    ∫⁻ t, ENNReal.ofReal (errGHG G t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (((1 + η) * (Lc / (n : ℝ)) * VbV Lc e n +
        4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have mE := hG.meas
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (errGHG G t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_errGHG hG hn1)
  set Gf : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hGf
  have mGf : Measurable Gf := mf.lintegral_prod_right'
  have eW : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, Gf W ∂mlpGauss (2 * n) (mW n) n = _
    rw [eW, lintegral_map mGf MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => Gf (MeasurableEquiv.prodAssoc a))
      (mGf.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  -- the bound for fixed θ
  set a : ℝ := (1 + η) * ((l ^ 2) / (n : ℝ)) with ha
  set S : ℝ := 4 / (n : ℝ) with hS
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  set δ : ℝ := (l ^ 2) / (n : ℝ) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  set dd : HidParam (2 * n) (mW n) → ℝ := fun θ => DKV n θ + δ with hdd
  have hdd0 : ∀ θ, 0 ≤ dd θ := fun θ => by
    have := DKV_nonneg n θ
    rw [hdd]; positivity
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    a * S * G.indicator dd θ +
      4 * (1 + 1 / η) * S * G.indicator (HbarH n ζ) θ with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have h1 : 0 ≤ G.indicator dd θ :=
      Set.indicator_nonneg (fun θ _ => hdd0 θ) _
    have h2 : 0 ≤ G.indicator (HbarH n ζ) θ :=
      Set.indicator_nonneg (fun θ _ => HbarH_nonneg n ζ θ) _
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    have msec : Measurable (fun q : Matrix (Fin n) (Fin (mW n)) ℝ ×
        (MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
        (((θ.1, θ.2, q.1) : MlpParam (2 * n) (mW n) n), q.2)) :=
      ((measurable_const.prodMk (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
    have hswap : ∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM =
        ∫⁻ p, (∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM) ∂PAF :=
      lintegral_lintegral_swap
        (f := fun (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) (mf.comp msec).aemeasurable
    rw [hswap]
    by_cases hθ : θ ∈ G
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWHG G := fun M₃ => hθ
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
        simp only [hf, errGHG, Set.indicator_of_mem (hW M₃)]
        congr 1
        ring
      simp_rw [hin]
      refine (errFixedHatLGV hG hn hLc0 hθ hζ0.le hζ1 hη).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hk]
      simp only [Set.indicator_of_mem hθ]
      rw [ha, hS, hdd, hδ]
      apply le_of_eq
      ring
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWHG G := fun M₃ => hθ
      have hz : ∀ (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
          (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ),
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) = 0 := by
        intro p M₃
        simp only [hf, errGHG, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero]
      simp_rw [hz]
      simp
  obtain ⟨iH, hH⟩ := HbarHG_mean hG hn hζ0 hζ1
  obtain ⟨iD, hDb⟩ := DKV_mean hn he hD
  have idd : Integrable dd (hidGauss (2 * n) (mW n)) :=
    iD.add (integrable_const _)
  have i1 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      a * S * G.indicator dd θ) (hidGauss (2 * n) (mW n)) :=
    (idd.indicator mE).const_mul _
  have i2 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      4 * (1 + 1 / η) * S * G.indicator (HbarH n ζ) θ) (hidGauss (2 * n) (mW n)) := iH.const_mul _
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := i1.add i2
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_add i1 i2, integral_const_mul, integral_const_mul]
        have e1 : ∫ θ, G.indicator dd θ ∂hidGauss (2 * n) (mW n) ≤ VbV (l ^ 2) e n := by
          have h0 : ∫ θ, G.indicator dd θ ∂hidGauss (2 * n) (mW n) ≤
              ∫ θ, dd θ ∂hidGauss (2 * n) (mW n) :=
            integral_mono (idd.indicator mE) idd
              (fun θ => Set.indicator_le_self' (fun θ _ => hdd0 θ) θ)
          have h1 : ∫ θ, dd θ ∂hidGauss (2 * n) (mW n) =
              (∫ θ, DKV n θ ∂hidGauss (2 * n) (mW n)) + δ := by
            have e' : dd = fun θ => DKV n θ + (fun _ => δ) θ := by rw [hdd]
            rw [e', integral_add (f := fun θ => DKV n θ) iD (integrable_const _)]
            simp
          unfold VbV
          rw [h1] at h0
          linarith
        have h1 := mul_le_mul_of_nonneg_left e1 (mul_nonneg ha0 hS0)
        have h2 := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 4 * (1 + 1 / η) * S)
        rw [ha, hS] at h1
        rw [hS] at h2
        rw [ha, hS]
        linarith

/-- **`errVecAG_lint` with the variance constant from the distance kernel.** -/
theorem errVecAGV_lint {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc) {e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e))
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (XALV Lc e n ζ η η' * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hVb := VbV_nonneg (n := n) hLc0 he
  rw [XALV_eq]
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (errGHG G t)) :=
    ENNReal.measurable_ofReal.comp (measurable_errGHG hG hn1)
  have m2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dGAG G t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dGAG hG hn1)
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (errGAG G t) ≤
        ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGHG G t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGAG G t) := by
    intro t
    have h0 := errGHG_nonneg G t
    have h0' := dGAG_nonneg G t
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases ht : t.1 ∈ goodWAG G
    · have ht' : t.1 ∈ goodWHG G := goodWAG_sub G ht
      simp only [errGAG, errGHG, dGAG, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      have hs := sq_split (η := 1 / η') (by positivity) (gA t.1 t.2.1 t.2.2)
        (gHat t.1 t.2.1 t.2.2) (Part130.Bn t.1 t.2.1 t.2.2)
      rw [one_div_one_div] at hs
      linarith
    · simp only [errGAG, Set.indicator_of_notMem ht]
      positivity
  calc ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGHG G t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGAG G t)) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ENNReal.ofReal (1 + η') * ∫⁻ t, ENNReal.ofReal (errGHG G t) ∂mlpTriple 2 n +
          ENNReal.ofReal (1 + 1 / η') * ∫⁻ t, ENNReal.ofReal (dGAG G t) ∂mlpTriple 2 n := by
        rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
          lintegral_const_mul _ m2]
    _ ≤ ENNReal.ofReal (1 + η') * ENNReal.ofReal (((1 + η) * ((l ^ 2) / (n : ℝ)) * VbV (l ^ 2) e n +
            4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (pertA n * (4 / (n : ℝ))) :=
        add_le_add (mul_le_mul' le_rfl (errVecHatGV_lint hG hn hLc0 he hD hζ0 hζ1 hη))
          (mul_le_mul' le_rfl (diffVecAG_lint hG hn))
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **`errSampleAG_lint` with the variance constant from the distance kernel.** For `n ≥ 4096`,
`0 < ζ < 1`, `k ≥ 1`: `E[1_good(W)·(g̃_k − B)²] ≤ (XALV (l ^ 2) e n ζ η η′ + 1/k)·(4/n)`. -/
theorem errSampleAGV_lint {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc)
    {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G) {e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e))
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η')
    {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (errSAG G k p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((XALV Lc e n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hX := XALV_nonneg hn hLc0 he ζ hη hη'
  set PW := mlpGauss (2 * n) (mW n) n with hPW
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  have e0 : mlpTriple 2 n = PW.prod PAF := rfl
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errSAG G k p)) :=
    ENNReal.measurable_ofReal.comp (measurable_errSAG hG hn1 k)
  rw [lintegral_prod _ mf.aemeasurable]
  -- the second moment term, as a function of `(W, (A, F))`
  set Lo : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => Lout (stdGauss (Fin n)) (preA t.1) t.2 with hLo
  have mL : Measurable Lo := by
    have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) =>
        ENNReal.ofReal (phiS q.1.2.1 q.1.2.2 (preA q.1.1 q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp
          (measurable_preA.comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))).pow_const 2)
    exact hj.lintegral_prod_right'
  have hLint : ∫⁻ t, Lo t ∂mlpTriple 2 n = ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [e0, lintegral_prod _ mL.aemeasurable]
    have h : ∀ W : MlpParam (2 * n) (mW n) n,
        ∫⁻ q, Lo (W, q) ∂PAF = ENNReal.ofReal (4 / (n : ℝ)) := by
      intro W
      have := lintegral_Lout (mA := mA n) (mF := mF n) (stdGauss (Fin n)) hn1 hmA hmF
        (measurable_preA_W W)
      exact this
    simp_rw [h]
    simp
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (errSAG G k (t, γ)) ∂gamK k n ≤
        ENNReal.ofReal (errGAG G t) + ENNReal.ofReal ((k : ℝ)⁻¹) * Lo t := by
    rintro ⟨W, A, F⟩
    have ho : Measurable (preA W) := measurable_preA_W W
    have hφ : BstLean.Part105.BM (fun γ : Fin n → ℝ => phiS A F (preA W γ)) :=
      (bm_phiS hn1 A F).comp ho
    obtain ⟨hi, he⟩ := iid_mean_sq (stdGauss (Fin n)) hφ hk (Part130.Bn W A F)
    by_cases hW : W ∈ goodWAG G
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSAG G k ((W, A, F), γ) =
          ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (γ i)) - Part130.Bn W A F) ^ 2 := by
        intro γ
        simp only [errSAG, Set.indicator_of_mem hW, gSampleA]
      simp_rw [e1]
      rw [show gamK k n = Measure.pi (fun _ : Fin k => stdGauss (Fin n)) from rfl,
        ← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      have he' : ∫ x : Fin k → Fin n → ℝ, ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (x i)) -
          Part130.Bn W A F) ^ 2 ∂Measure.pi (fun _ : Fin k => stdGauss (Fin n)) =
          (∫ x, phiS A F (preA W x) ∂stdGauss (Fin n) - Part130.Bn W A F) ^ 2 +
            (k : ℝ)⁻¹ * Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] := he
      rw [he', ← gA_eq hn1]
      have hv : Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] ≤
          ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) := by
        rw [BstLean.Part134.var_bm (stdGauss (Fin n)) hφ]
        nlinarith [sq_nonneg (∫ γ, phiS A F (preA W γ) ∂stdGauss (Fin n))]
      have hGf : errGAG G (W, A, F) = (gA W A F - Part130.Bn W A F) ^ 2 := by
        simp only [errGAG, Set.indicator_of_mem hW]
      have i0 : 0 ≤ ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) :=
        integral_nonneg fun _ => sq_nonneg _
      rw [hLo]
      simp only
      rw [← ofReal_integral_out (stdGauss (Fin n)) hn1 A F ho, hGf,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg (by positivity) i0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
      linarith
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSAG G k ((W, A, F), γ) = 0 := by
        intro γ
        simp only [errSAG, Set.indicator_of_notMem hW]
      simp_rw [e1]
      simp
  calc ∫⁻ t, (∫⁻ γ, ENNReal.ofReal (errSAG G k (t, γ)) ∂gamK k n) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (errGAG G t) + ENNReal.ofReal ((k : ℝ)⁻¹) * Lo t) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) := by
        have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1 => ENNReal.ofReal (errGAG G t)) :=
          ENNReal.measurable_ofReal.comp (measurable_errGAG hG hn1)
        rw [lintegral_add_left m1, lintegral_const_mul _ mL, hLint]
    _ ≤ ENNReal.ofReal (XALV (l ^ 2) e n ζ η η' * (4 / (n : ℝ))) +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) :=
        add_le_add (errVecAGV_lint hG hn hLc0 he hD hζ0 hζ1 hη hη') le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

end BstLean.Part145

open BstLean.Part145 in
#print axioms errSampleAGV_lint
