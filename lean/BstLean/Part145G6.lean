import BstLean.Part145G5

/-!
# Part 145 (abstract good hidden event), file 6: the `L²` norm of `DKV`

`DKV n θ` is `n/4` times the mean of the distance kernel `kD` for fixed `θ = (M₁, M₂)`. Thus
`E_θ DKV² ≤ (n/4)²·E kD²` (the Cauchy–Schwarz inequality in the inner mean), and
`E kD² ≤ ((4/n)(1 − κ^{∘6}(0) + e))²` from the kernel hypothesis.

* `sq_lintegral_le`: `(∫⁻ f)² ≤ ∫⁻ f²` for a probability measure.
* `KW2`, `lint_kD2_eq`, `lint_KW2`: the identities of file 4 for the square of the kernel.
* **`DKV_L2`**: `‖DKV‖₂ ≤ 1 − κ^{∘6}(0) + e` over `θ`.
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

/-- `(∫⁻ f)² ≤ ∫⁻ f²` for a probability measure. -/
lemma sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ 2 ≤ ∫⁻ a, f a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, measure_univ, ENNReal.rpow_two, one_pow,
    ENNReal.one_rpow] at h
  calc (∫⁻ a, f a ∂μ) ^ 2 ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
    _ = ∫⁻ a, f a ^ 2 ∂μ := by
        rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
        norm_num

section kernel

variable {N mW n mA mF : ℕ}

/-- The mean over `(A, F)` of the square of the distance kernel at the points `x(u)`, `x(u′)`,
a function of `(W, (u, u′))`. -/
noncomputable def KW2 (z : MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) : ℝ≥0∞ :=
  ∫⁻ p : MlpParam n mA n × MlpParam n mF 1,
    ENNReal.ofReal (dk p.2 p.1 (xW z.1 z.2.1) (xW z.1 z.2.2)) ^ 2
    ∂((mlpGauss n mA n).prod (mlpGauss n mF 1))

lemma measurable_dkW2 :
    Measurable (fun q : (MlpParam n mA n × MlpParam n mF 1) ×
        (MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) =>
      ENNReal.ofReal (dk q.1.2 q.1.1 (xW q.2.1 q.2.2.1) (xW q.2.1 q.2.2.2)) ^ 2) :=
  (measurable_dkW (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)).pow_const 2

lemma measurable_KW2 :
    Measurable (KW2 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) :=
  (measurable_dkW2 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)).lintegral_prod_left'

/-- `KW² ≤ KW2`. -/
lemma KW_sq_le (z : MlpParam N mW n × ((Fin N → ℝ) × (Fin N → ℝ))) :
    KW (mA := mA) (mF := mF) z ^ 2 ≤ KW2 (mA := mA) (mF := mF) z :=
  sq_lintegral_le _ (Measurable.comp
    (f := fun p : MlpParam n mA n × MlpParam n mF 1 => (p, z))
    (measurable_dkW (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))
    (measurable_id.prodMk measurable_const)).aemeasurable

/-- The mean of the square of `kD` under `(u, u′) ⊗ (W, A, A′, F)` is the mean of `KW2` under
`W ⊗ (u, u′)`. -/
lemma lint_kD2_eq (hN : 1 ≤ N) :
    ∫⁻ ω, ENNReal.ofReal (kD ω) ^ 2 ∂((lawU2 N).prod (lawR N mW n mA mF)) =
      ∫⁻ z, KW2 (mA := mA) (mF := mF) z ∂((mlpGauss N mW n).prod (lawU2 N)) := by
  have := lawU2_prob hN
  have mk : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      ENNReal.ofReal (kD ω) ^ 2) :=
    (ENNReal.measurable_ofReal.comp measurable_kD).pow_const 2
  rw [lintegral_prod_symm _ mk.aemeasurable,
    lintegral_prod _ (measurable_KW2 (mA := mA) (mF := mF)).aemeasurable]
  set g : Rest N mW n mA mF → ℝ≥0∞ := fun r =>
    ∫⁻ uu, ENNReal.ofReal (kD (uu, r)) ^ 2 ∂lawU2 N with hg
  have mg : Measurable g := mk.lintegral_prod_left'
  unfold lawR
  rw [lintegral_prod g mg.aemeasurable]
  refine lintegral_congr fun W => ?_
  obtain ⟨h, hh⟩ : ∃ h : MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞, h = fun p =>
    ∫⁻ uu, ENNReal.ofReal (dk p.2 p.1 (xW W uu.1) (xW W uu.2)) ^ 2 ∂lawU2 N := ⟨_, rfl⟩
  have mΨ : Measurable (fun q : ((Fin N → ℝ) × (Fin N → ℝ)) ×
      (MlpParam n mA n × MlpParam n mF 1) =>
      ENNReal.ofReal (dk q.2.2 q.2.1 (xW W q.1.1) (xW W q.1.2)) ^ 2) :=
    Measurable.comp (f := fun q : ((Fin N → ℝ) × (Fin N → ℝ)) ×
        (MlpParam n mA n × MlpParam n mF 1) => (q.2, (W, q.1)))
      (measurable_dkW2 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))
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
      ENNReal.ofReal (dk p.2 p.1 (xW W uu.1) (xW W uu.2)) ^ 2)
    (Measurable.comp (f := Prod.swap) mΨ measurable_swap).aemeasurable

end kernel

/-- The mean of `KW2` over `θ`, `M₃` and `(u, u′)` is its mean under `W ⊗ (u, u′)`. -/
lemma lint_KW2 {n : ℕ} (hn : 1 ≤ n) :
    ∫⁻ θ : HidParam (2 * n) (mW n),
      (∫⁻ ω : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)),
        KW2 (mA := mA n) (mF := mF n) (((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n), ω.2)
        ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n))))
      ∂hidGauss (2 * n) (mW n) =
    ∫⁻ z, KW2 (mA := mA n) (mF := mF n) z
      ∂((mlpGauss (2 * n) (mW n) n).prod (lawU2 (2 * n))) := by
  have hN : 1 ≤ 2 * n := by omega
  have := lawU2_prob hN
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set K2 : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W =>
    ∫⁻ uu, KW2 (mA := mA n) (mF := mF n) (W, uu) ∂lawU2 (2 * n) with hK2
  have mK2 : Measurable K2 :=
    (measurable_KW2 (mA := mA n) (mF := mF n)).lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  rw [lintegral_prod _ (measurable_KW2 (mA := mA n) (mF := mF n)).aemeasurable]
  change _ = ∫⁻ W, K2 W ∂mlpGauss (2 * n) (mW n) n
  rw [e, lintegral_map mK2 MeasurableEquiv.prodAssoc.measurable,
    lintegral_prod (fun a => K2 (MeasurableEquiv.prodAssoc a))
      (mK2.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable]
  refine lintegral_congr fun θ => ?_
  rw [lintegral_prod (fun ω : Matrix (Fin n) (Fin (mW n)) ℝ ×
      ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) => KW2 (mA := mA n) (mF := mF n)
        (((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n), ω.2))
    ((measurable_KW2 (mA := mA n) (mF := mF n)).comp
    ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
      measurable_snd)).aemeasurable]
  rfl

/-- **The `L²` norm of `DKV`** from the `L²` bound of the distance kernel:
`E_θ DKV² ≤ (1 − κ^{∘6}(0) + e)²`. -/
theorem DKV_L2 {n : ℕ} (hn : 4096 ≤ n) {e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e)) :
    L2le (hidGauss (2 * n) (mW n)) (DKV n) (1 - kappa^[6] 0 + e) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := lawU2_prob hN
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  set μ := (lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)) with hμ
  set c : ℝ := 4 / (n : ℝ) * (1 - kappa^[6] 0) with hc
  set s : ℝ := 4 / (n : ℝ) * e with hs
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg (by positivity) (by linarith)
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have iK : Integrable (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
      Rest (2 * n) (mW n) n (mA n) (mF n) => kD ω) μ :=
    (memLp_of_L2le_sub hD).integrable one_le_two
  have iK2 : Integrable (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
      Rest (2 * n) (mW n) n (mA n) (mF n) => kD ω ^ 2) μ :=
    (memLp_of_L2le_sub hD).integrable_sq
  have hK0 : ∀ ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
      Rest (2 * n) (mW n) n (mA n) (mF n), 0 ≤ kD ω := fun ω =>
    (show 0 ≤ kD ω from dk_nonneg ω.2.2.2.2 ω.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2))
  -- `E kD² ≤ (c + s)²`
  have hK2le : ∫ ω, kD ω ^ 2 ∂μ ≤ (c + s) ^ 2 := by
    have h1 := sq_integral_le hD.int_sq
    have h2 := h1.trans hD.le
    have h3 := abs_le_of_sq_le_sq' h2 hs0
    have iS : Integrable (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
        Rest (2 * n) (mW n) n (mA n) (mF n) => kD ω - c) μ := iK.sub (integrable_const _)
    have e2 : ∫ ω, kD ω ^ 2 ∂μ = (∫ ω, (kD ω - c) ^ 2 ∂μ) + 2 * c * (∫ ω, (kD ω - c) ∂μ) +
        c ^ 2 := by
      have e3 : (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
          Rest (2 * n) (mW n) n (mA n) (mF n) => kD ω ^ 2) =
          fun ω => ((kD ω - c) ^ 2 + 2 * c * (kD ω - c)) + c ^ 2 := by
        funext ω; ring
      rw [e3, integral_add (f := fun ω => (kD ω - c) ^ 2 + 2 * c * (kD ω - c))
          (g := fun _ => c ^ 2) (hD.int_sq.add (iS.const_mul _)) (integrable_const _),
        integral_add (f := fun ω => (kD ω - c) ^ 2) (g := fun ω => 2 * c * (kD ω - c))
          hD.int_sq (iS.const_mul _), integral_const_mul]
      simp
    have h4 := hD.le
    have h5 := mul_le_mul_of_nonneg_left h3.2 (by positivity : (0 : ℝ) ≤ 2 * c)
    rw [e2]
    nlinarith
  -- the lintegral of `LDV²`
  have hL : ∫⁻ θ, LDV n θ ^ 2 ∂hidGauss (2 * n) (mW n) ≤ ENNReal.ofReal ((c + s) ^ 2) := by
    have hpt : ∀ θ : HidParam (2 * n) (mW n), LDV n θ ^ 2 ≤
        ∫⁻ ω : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)),
          KW2 (mA := mA n) (mF := mF n) (((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n), ω.2)
          ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n))) := by
      intro θ
      rw [LDV_eq_KW hn1 θ]
      refine (sq_lintegral_le _ ((measurable_KW (mA := mA n) (mF := mF n)).comp
        ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
          measurable_snd)).aemeasurable).trans ?_
      exact lintegral_mono fun ω => KW_sq_le _
    refine (lintegral_mono hpt).trans ?_
    rw [lint_KW2 hn1, ← lint_kD2_eq hN]
    have e4 : ∀ ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) ×
        Rest (2 * n) (mW n) n (mA n) (mF n),
        ENNReal.ofReal (kD ω) ^ 2 = ENNReal.ofReal (kD ω ^ 2) := fun ω =>
      (ENNReal.ofReal_pow (hK0 ω) 2).symm
    simp_rw [e4]
    rw [← ofReal_integral_eq_lintegral_ofReal iK2
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hK2le
  have hfin : ∀ θ : HidParam (2 * n) (mW n), LDV n θ ≠ ⊤ := fun θ => by
    rw [LDV_eq_ofReal hn θ]
    exact ENNReal.ofReal_ne_top
  have eD : ∀ θ : HidParam (2 * n) (mW n),
      ENNReal.ofReal (DKV n θ ^ 2) = ENNReal.ofReal (((n : ℝ) / 4) ^ 2) * LDV n θ ^ 2 := by
    intro θ
    unfold DKV
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hfin θ)]
  have iD := DKV_sq_int hn
  refine ⟨(measurable_DKV hn1).aestronglyMeasurable, iD, ?_⟩
  have h6 : ENNReal.ofReal (∫ θ, DKV n θ ^ 2 ∂hidGauss (2 * n) (mW n)) ≤
      ENNReal.ofReal (((n : ℝ) / 4) ^ 2 * (c + s) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal iD
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)]
    simp_rw [eD]
    rw [lintegral_const_mul _ ((measurable_LDV hn1).pow_const 2),
      ENNReal.ofReal_mul (by positivity)]
    gcongr
  have h7 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h6
  refine h7.trans (le_of_eq ?_)
  rw [hc, hs]
  field_simp

end BstLean.Part145

open BstLean.Part145 in
#print axioms DKV_L2
