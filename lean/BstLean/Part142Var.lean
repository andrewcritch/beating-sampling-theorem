import BstLean.Part141All
import BstLean.Part142Anchor
import BstLean.Part142FD

/-!
# Part 142 (step S1): the mean variance under the stand-in, for fixed `(M₁, M₂)`

Role: `delegations/statements/p142-spec.md`, item 4 (the stand-in term). In Parts 139 to 141 the
mean variance `E_c Var_{ν̂_c} φ` of `φ = F∘A` under the stand-in is bounded by the second moment
`S = 4/n`. Here it is bounded by `S·(D_θ + eAFr + 1.83/n)`, where
`D_θ = E_{M₃,u,u′}[1 − κ^{∘4}(⟨x(u), x(u′)⟩)]` (about `1 − κ^{∘6}(0) ≈ 0.223`).

* `s1_cross`: `E(X − Y)² = E X² − E_c Y_c²` for `X = E_{μ_M} φ`, `Y_c = E_{ν_c} φ` (from the
  conditional mean identity `s1_mean_test` of Part 134).
* `sq_mean_eq`: `(E a)² = E a² − E (a(u) − a(u′))²/2`.
* `lint_phi_diff`: for unit `x, x′`:
  `E_{A,F} (F(A(x)) − F(A(x′)))²/2 ≤ S·(1 − κ^{∘4}(⟨x, x′⟩) + eAFr)`.
* `DTh n θ`, **`errFixedHat142`**: for fixed `θ = (M₁, M₂) ∈ goodHat n`:
  `E_{A,F} E_{M₃}(Bn − gHat)² ≤
    ((1 + η)(1.83/n)(D_θ + eAFr + 1.83/n) + 4(1 + 1/η)·HbarH n ζ θ)·(4/n)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141

/-! ## The cross term of the stand-in -/

section cross

variable {n m : ℕ} {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]

/-- `E_M(E_{μ_M} φ − E_{ν_{Mb}} φ)² = E_M(E_{μ_M} φ)² − E_c(E_{ν_c} φ)²`: the stand-in mean is
the conditional mean given `c = M b`. -/
theorem s1_cross (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ} (hh : Measurable h)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M, ((∫ x, φ x ∂muM μ h M) - ∫ x, φ x ∂standIn μ h v b (M.mulVec b)) ^ 2
        ∂gaussMat n m v =
      ∫ M, (∫ x, φ x ∂muM μ h M) ^ 2 ∂gaussMat n m v -
        ∫ c, (∫ x, φ x ∂standIn μ h v b c) ^ 2 ∂cDist n v b := by
  have bX := bm_muM (n := n) μ hh hφ
  have bYc := bm_standIn (n := n) μ v b hh hφ
  have mb : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => M.mulVec b) :=
    measurable_mulVec_right b
  have bY := bYc.comp mb
  have h1 := s1_mean_test μ v hb hh hφ bYc
  have h2 : ∫ M, (∫ x, φ x ∂standIn μ h v b (M.mulVec b)) ^ 2 ∂gaussMat n m v =
      ∫ c, (∫ x, φ x ∂standIn μ h v b c) ^ 2 ∂cDist n v b := by
    rw [← cDist_eq, integral_map mb.aemeasurable bYc.sq.meas.aestronglyMeasurable]
  have h3 : ∫ c, (∫ x, φ x ∂standIn μ h v b c) * (∫ x, φ x ∂standIn μ h v b c) ∂cDist n v b =
      ∫ c, (∫ x, φ x ∂standIn μ h v b c) ^ 2 ∂cDist n v b :=
    integral_congr_ae (Filter.Eventually.of_forall fun c => by ring)
  rw [h3] at h1
  set X : Matrix (Fin n) (Fin m) ℝ → ℝ := fun M => ∫ x, φ x ∂muM μ h M with hX
  set Y : Matrix (Fin n) (Fin m) ℝ → ℝ :=
    fun M => ∫ x, φ x ∂standIn μ h v b (M.mulVec b) with hY
  have i1 : Integrable (fun M => X M ^ 2) (gaussMat n m v) := bX.sq.integrable _
  have i2 : Integrable (fun M => 2 * (Y M * X M)) (gaussMat n m v) :=
    ((bY.mul bX).integrable (gaussMat n m v)).const_mul 2
  have i3 : Integrable (fun M => Y M ^ 2) (gaussMat n m v) := bY.sq.integrable _
  have e : (fun M => (X M - Y M) ^ 2) = fun M => (X M ^ 2 - 2 * (Y M * X M)) + Y M ^ 2 := by
    funext M; ring
  change ∫ M, (X M - Y M) ^ 2 ∂gaussMat n m v = ∫ M, X M ^ 2 ∂gaussMat n m v - _
  change ∫ M, Y M * X M ∂gaussMat n m v = _ at h1
  change ∫ M, Y M ^ 2 ∂gaussMat n m v = _ at h2
  rw [e, integral_add (f := fun M => X M ^ 2 - 2 * (Y M * X M)) (i1.sub i2) i3,
    integral_sub (f := fun M => X M ^ 2) i1 i2, integral_const_mul, h1, h2]
  ring

/-- `s1_cross` for the World network. -/
theorem s1_cross_mlp {N : ℕ} (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ)
    (M₂ : Matrix (Fin m) (Fin m) ℝ) {b : Fin m → ℝ} (hb : b ≠ 0)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((M₁, M₂, M₃) : MlpParam N m n)) -
        ∫ x, φ x ∂standIn (uniformSphere N) (hid2 M₁ M₂) (2 / (m : ℝ)) b (M₃.mulVec b)) ^ 2
        ∂gaussMat n m (2 / (m : ℝ)) =
      ∫ M₃, (∫ x, φ x ∂muWn ((M₁, M₂, M₃) : MlpParam N m n)) ^ 2 ∂gaussMat n m (2 / (m : ℝ)) -
        ∫ c, (∫ x, φ x ∂standIn (uniformSphere N) (hid2 M₁ M₂) (2 / (m : ℝ)) b c) ^ 2
          ∂cDist n (2 / (m : ℝ)) b := by
  have := uniformSphere_isProbability N hN
  exact s1_cross (uniformSphere N) (2 / (m : ℝ)) hb (continuous_hid2 M₁ M₂).measurable hφ

end cross

/-- `(E a)² = E a² − E(a(u) − a(u′))²/2` for a bounded measurable `a` on a probability space. -/
lemma sq_mean_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : Ω → ℝ} (ha : BM a) :
    (∫ u, a u ∂P) ^ 2 =
      ∫ u, a u ^ 2 ∂P - ∫ p : Ω × Ω, (a p.1 - a p.2) ^ 2 / 2 ∂(P.prod P) := by
  have h1 := ha.integrable P
  have h2 := ha.sq.integrable P
  have hB : BM (fun p : Ω × Ω => (a p.1 - a p.2) ^ 2) :=
    ((ha.comp measurable_fst).sub (ha.comp measurable_snd)).sq
  have inner : ∀ x : Ω, ∫ y, (a x - a y) ^ 2 ∂P =
      a x ^ 2 - 2 * a x * (∫ y, a y ∂P) + ∫ y, a y ^ 2 ∂P := by
    intro x
    have e : (fun y : Ω => (a x - a y) ^ 2) =
        fun y => ((fun _ => a x ^ 2) y - 2 * a x * a y) + a y ^ 2 := by
      funext y; ring
    rw [e, integral_add (f := fun y => (fun _ => a x ^ 2) y - 2 * a x * a y)
        ((integrable_const _).sub (h1.const_mul _)) h2,
      integral_sub (f := fun _ => a x ^ 2) (integrable_const _) (h1.const_mul _),
      integral_const_mul]
    simp
  have e3 : ∫ p : Ω × Ω, (a p.1 - a p.2) ^ 2 ∂(P.prod P) =
      2 * ∫ u, a u ^ 2 ∂P - 2 * (∫ u, a u ∂P) ^ 2 := by
    rw [integral_prod _ (hB.integrable _)]
    simp_rw [inner]
    have i4 : Integrable (fun x : Ω => 2 * a x * (∫ y, a y ∂P)) P :=
      (h1.const_mul 2).mul_const _
    rw [integral_add (f := fun x => a x ^ 2 - 2 * a x * (∫ y, a y ∂P)) (h2.sub i4)
        (integrable_const _),
      integral_sub (f := fun x => a x ^ 2) h2 i4, integral_mul_const, integral_const_mul]
    simp
    ring
  rw [integral_div, e3]
  ring

/-! ## The mean squared difference of `F∘A` at two unit points -/

section diff

variable {n mA mF : ℕ}

/-- The distance kernel `(k(x, x) + k(x′, x′))/2 − k(x, x′)` of Part 132, for one network `A`. -/
noncomputable def dk (F : MlpParam n mF 1) (A : MlpParam n mA n) (x x' : Fin n → ℝ) : ℝ :=
  (kern F A A x x + kern F A A x' x') / 2 - kern F A A x x'

lemma dk_nonneg (F : MlpParam n mF 1) (A : MlpParam n mA n) (x x' : Fin n → ℝ) :
    0 ≤ dk F A x x' := by
  unfold dk
  rw [kernD_eq]
  exact mul_nonneg (by positivity) (eD_nonneg _ _)

lemma measurable_dk (x x' : Fin n → ℝ) :
    Measurable (fun p : MlpParam n mA n × MlpParam n mF 1 => dk p.2 p.1 x x') := by
  unfold dk
  exact (((measurable_kern_comp measurable_snd measurable_fst measurable_fst measurable_const
    measurable_const).add (measurable_kern_comp measurable_snd measurable_fst measurable_fst
    measurable_const measurable_const)).div_const 2).sub
    (measurable_kern_comp measurable_snd measurable_fst measurable_fst measurable_const
      measurable_const)

/-- The mean over the last matrix of `F`: `E_{F₃}(F(A(x)) − F(A(x′)))²/2 = dk`. -/
lemma F3_diff (A : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ)
    (F₂ : Matrix (Fin mF) (Fin mF) ℝ) (F₃' : Matrix (Fin 1) (Fin mF) ℝ) (x x' : Fin n → ℝ) :
    Integrable (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
      (phiN A (F₁, F₂, F₃) x - phiN A (F₁, F₂, F₃) x') ^ 2 / 2) (gaussMat 1 mF (2 / (mF : ℝ))) ∧
    ∫ F₃ : Matrix (Fin 1) (Fin mF) ℝ, (phiN A (F₁, F₂, F₃) x - phiN A (F₁, F₂, F₃) x') ^ 2 / 2
      ∂gaussMat 1 mF (2 / (mF : ℝ)) = dk (F₁, F₂, F₃') A x x' := by
  set w : Fin mF → ℝ := hid2 F₁ F₂ (mlpEval A x) - hid2 F₁ F₂ (mlpEval A x') with hw
  have e : ∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ,
      (phiN A (F₁, F₂, F₃) x - phiN A (F₁, F₂, F₃) x') ^ 2 / 2 = normSq (F₃.mulVec w) / 2 := by
    intro F₃
    have h1 : phiN A (F₁, F₂, F₃) x - phiN A (F₁, F₂, F₃) x' = (F₃.mulVec w) 0 := by
      rw [hw, Matrix.mulVec_sub]
      rfl
    rw [h1]
    unfold normSq
    rw [Fin.sum_univ_one]
  obtain ⟨hi, he⟩ := layer_lin_sq (m := 1) (two_div_nonneg mF) w
  simp_rw [e]
  refine ⟨hi.div_const 2, ?_⟩
  rw [integral_div, he]
  unfold dk
  rw [kernD_eq, eD_eq]
  simp only [Nat.cast_one, one_mul]
  ring

/-- **For unit `x, x′`**: `E_{A,F}(F(A(x)) − F(A(x′)))²/2 ≤ (4/n)(1 − κ^{∘4}(⟨x, x′⟩) + eAFr)`. -/
lemma lint_phi_diff (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    ∫⁻ p : MlpParam n mA n × MlpParam n mF 1,
      ENNReal.ofReal ((phiN p.1 p.2 x - phiN p.1 p.2 x') ^ 2 / 2)
      ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
    ENNReal.ofReal (4 / (n : ℝ) * (1 - kappa^[4] (dotp x x') + eAFr n mA mF)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set G : MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((phiN p.1 p.2 x - phiN p.1 p.2 x') ^ 2 / 2) with hG
  set H : MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (dk p.2 p.1 x x') with hH
  have mphi : ∀ y : Fin n → ℝ, Measurable (fun p : MlpParam n mA n × MlpParam n mF 1 =>
      phiN p.1 p.2 y) := fun y =>
    BstLean.Part131.continuous_phiN_all.measurable.comp (measurable_id.prodMk measurable_const)
  have mG : Measurable G :=
    ENNReal.measurable_ofReal.comp ((((mphi x).sub (mphi x')).pow_const 2).div_const 2)
  have mH : Measurable H := ENNReal.measurable_ofReal.comp (measurable_dk x x')
  -- step 1: integrate the last matrix of `F`
  have step1 : ∫⁻ p, G p ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) =
      ∫⁻ p, H p ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) := by
    rw [lintegral_prod _ mG.aemeasurable, lintegral_prod _ mH.aemeasurable]
    refine lintegral_congr fun A => ?_
    have mGA : Measurable (fun F : MlpParam n mF 1 => G (A, F)) :=
      mG.comp (measurable_const.prodMk measurable_id)
    have mHA : Measurable (fun F : MlpParam n mF 1 => H (A, F)) :=
      mH.comp (measurable_const.prodMk measurable_id)
    change ∫⁻ F, G (A, F) ∂((gaussMat mF n (2 / (n : ℝ))).prod
        ((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ))))) =
      ∫⁻ F, H (A, F) ∂((gaussMat mF n (2 / (n : ℝ))).prod
        ((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))))
    rw [lintegral_prod _ mGA.aemeasurable, lintegral_prod _ mHA.aemeasurable]
    refine lintegral_congr fun F₁ => ?_
    have mGF : Measurable (fun q : Matrix (Fin mF) (Fin mF) ℝ × Matrix (Fin 1) (Fin mF) ℝ =>
        G (A, (F₁, q))) := mGA.comp (measurable_const.prodMk measurable_id)
    have mHF : Measurable (fun q : Matrix (Fin mF) (Fin mF) ℝ × Matrix (Fin 1) (Fin mF) ℝ =>
        H (A, (F₁, q))) := mHA.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ mGF.aemeasurable, lintegral_prod _ mHF.aemeasurable]
    refine lintegral_congr fun F₂ => ?_
    obtain ⟨hi, he⟩ := F3_diff A F₁ F₂ 0 x x'
    have eL : ∫⁻ F₃, G (A, (F₁, (F₂, F₃))) ∂gaussMat 1 mF (2 / (mF : ℝ)) =
        ENNReal.ofReal (dk (F₁, F₂, 0) A x x') := by
      rw [← he]
      exact (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => by positivity)).symm
    have eR : ∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ, H (A, (F₁, (F₂, F₃))) =
        ENNReal.ofReal (dk (F₁, F₂, 0) A x x') := fun F₃ => rfl
    rw [eL]
    simp_rw [eR]
    simp
  -- step 2: to the triple `(A, A′, F)` of Part 132
  set T3 := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)) with hT3
  have mdrop : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      (p.1, p.2.2)) := measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have step2 : ∫⁻ p, H p ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) =
      ∫⁻ p, H (p.1, p.2.2) ∂T3 := by
    rw [← map_dropMid (mlpGauss n mA n) (mlpGauss n mA n) (mlpGauss n mF 1),
      lintegral_map mH mdrop]
  -- step 3: the three kernels
  have hGk : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hG0 : 3 / 10 ≤ (kappa ∘ kappa) 0 := by
    have := kappa2_zero_ge
    simp only [Function.comp_apply]
    linarith
  have hcF := BstLean.Part133.cF2o_pos hmF
  have hcA := cAr_pos hGk hmA hn
  have hS : L2le T3 (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x' - 4 / (n : ℝ) * kappa^[4] (dotp x x'))
      (4 / (n : ℝ) * eAFr n mA mF) :=
    kern_same_L2_of hn hmA hx hx' hcF hcA (fun y y' => KF_L2o hn hmF y y')
      (mlp_psi_L2r hGk hG0 hmA hn hn x x')
  have he0 : 0 ≤ eAFr n mA mF := by unfold eAFr; positivity
  have iK : Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      kern p.2.2 p.1 p.1 x x') T3 := (memLp_of_L2le_sub hS).integrable one_le_two
  obtain ⟨iX, -⟩ := kern_diag_gen (mA := mA) (mF := mF) hn hmA hmF x
  obtain ⟨iX', -⟩ := kern_diag_gen (mA := mA) (mF := mF) hn hmA hmF x'
  have eX := kern_diag_mean (mA := mA) (mF := mF) hn hmA hmF hx
  have eX' := kern_diag_mean (mA := mA) (mF := mF) hn hmA hmF hx'
  have hlow : 4 / (n : ℝ) * kappa^[4] (dotp x x') - 4 / (n : ℝ) * eAFr n mA mF ≤
      ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kern p.2.2 p.1 p.1 x x' ∂T3 := by
    have h1 := sq_integral_le hS.int_sq
    have h2 := h1.trans hS.le
    have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
    have h4 : ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1,
        (kern p.2.2 p.1 p.1 x x' - 4 / (n : ℝ) * kappa^[4] (dotp x x')) ∂T3 =
        (∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1,
          kern p.2.2 p.1 p.1 x x' ∂T3) - 4 / (n : ℝ) * kappa^[4] (dotp x x') := by
      rw [integral_sub iK (integrable_const _)]
      simp
    rw [h4] at h3
    linarith [h3.1]
  have iD : Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      dk p.2.2 p.1 x x') T3 := by
    unfold dk
    exact ((iX.add iX').div_const 2).sub iK
  have eD' : ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, dk p.2.2 p.1 x x' ∂T3 =
      4 / (n : ℝ) - ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1,
        kern p.2.2 p.1 p.1 x x' ∂T3 := by
    unfold dk
    rw [integral_sub (f := fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        (kern p.2.2 p.1 p.1 x x + kern p.2.2 p.1 p.1 x' x') / 2) ((iX.add iX').div_const 2) iK,
      integral_div, integral_add (f := fun p : MlpParam n mA n × MlpParam n mA n ×
        MlpParam n mF 1 => kern p.2.2 p.1 p.1 x x) iX iX', eX, eX']
    ring
  rw [step1, step2]
  have e3 : ∫⁻ p, H (p.1, p.2.2) ∂T3 = ENNReal.ofReal (∫ p : MlpParam n mA n × MlpParam n mA n ×
      MlpParam n mF 1, dk p.2.2 p.1 x x' ∂T3) :=
    (ofReal_integral_eq_lintegral_ofReal iD
      (Filter.Eventually.of_forall fun p => dk_nonneg _ _ _ _)).symm
  rw [e3]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [eD']
  linarith

end diff

/-! ## The second moment of a difference at two random points -/

section outD

variable {n mA mF : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma bm_half {α : Type*} [MeasurableSpace α] {F : α → ℝ} (hF : BM F) :
    BM (fun x => F x / 2) := by
  have := hF.mul (BstLean.Part105.BM.const (α := α) (2 : ℝ)⁻¹)
  simpa [div_eq_mul_inv] using this

/-- Half the mean squared difference of `F∘A` at the two random points `o(ω)/|o(ω)|`,
`o′(ω)/|o′(ω)|`, as a function of `(A, F)`. -/
noncomputable def LoutD (o o' : Ω → Fin n → ℝ) (p : MlpParam n mA n × MlpParam n mF 1) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((phiS p.1 p.2 (o ω) - phiS p.1 p.2 (o' ω)) ^ 2 / 2) ∂P

lemma measurable_LoutD {o o' : Ω → Fin n → ℝ} (ho : Measurable o) (ho' : Measurable o') :
    Measurable (LoutD (mA := mA) (mF := mF) P o o') :=
  Measurable.lintegral_prod_right'
    (f := fun q : (MlpParam n mA n × MlpParam n mF 1) × Ω =>
      ENNReal.ofReal ((phiS q.1.1 q.1.2 (o q.2) - phiS q.1.1 q.1.2 (o' q.2)) ^ 2 / 2))
    (ENNReal.measurable_ofReal.comp ((((measurable_phiS_out ho).sub
      (measurable_phiS_out ho')).pow_const 2).div_const 2))

lemma lintegral_LoutD_le (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {o o' : Ω → Fin n → ℝ}
    (ho : Measurable o) (ho' : Measurable o') :
    ∫⁻ p, LoutD (mA := mA) (mF := mF) P o o' p ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
      ∫⁻ ω, ENNReal.ofReal (4 / (n : ℝ) *
        (1 - kappa^[4] (dotp (sphPt (o ω)) (sphPt (o' ω))) + eAFr n mA mF)) ∂P := by
  unfold LoutD
  rw [lintegral_lintegral_swap
    (f := fun (p : MlpParam n mA n × MlpParam n mF 1) (ω : Ω) =>
      ENNReal.ofReal ((phiS p.1 p.2 (o ω) - phiS p.1 p.2 (o' ω)) ^ 2 / 2))
    (ENNReal.measurable_ofReal.comp ((((measurable_phiS_out ho).sub
      (measurable_phiS_out ho')).pow_const 2).div_const 2)).aemeasurable]
  refine lintegral_mono fun ω => ?_
  exact lint_phi_diff hn hmA hmF (normSq_sphPt hn (o ω)) (normSq_sphPt hn (o' ω))

lemma ofReal_integral_outD (hn : 1 ≤ n) (A : MlpParam n mA n) (F : MlpParam n mF 1)
    {o o' : Ω → Fin n → ℝ} (ho : Measurable o) (ho' : Measurable o') :
    ENNReal.ofReal (∫ ω, (phiS A F (o ω) - phiS A F (o' ω)) ^ 2 / 2 ∂P) =
      LoutD P o o' (A, F) := by
  have hb : BM (fun ω => (phiS A F (o ω) - phiS A F (o' ω)) ^ 2 / 2) :=
    bm_half (((bm_phiS hn A F).comp ho).sub ((bm_phiS hn A F).comp ho')).sq
  exact ofReal_integral_eq_lintegral_ofReal (hb.integrable P)
    (Filter.Eventually.of_forall fun _ => by positivity)

end outD

/-! ## Fixed `(M₁, M₂)` -/

section fixed

variable {n : ℕ}

/-- The point `W(u)` (before the normalization) as a function of `(M₃, u)`. -/
noncomputable def oA (θ : HidParam (2 * n) (mW n))
    (ω : Matrix (Fin n) (Fin (mW n)) ℝ × (Fin (2 * n) → ℝ)) : Fin n → ℝ :=
  mlpEval ((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n) ω.2

/-- The point `W(u)` as a function of `(M₃, (u, u′))`. -/
noncomputable def oD1 (θ : HidParam (2 * n) (mW n))
    (ω : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ))) : Fin n → ℝ :=
  mlpEval ((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n) ω.2.1

/-- The point `W(u′)` as a function of `(M₃, (u, u′))`. -/
noncomputable def oD2 (θ : HidParam (2 * n) (mW n))
    (ω : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ))) : Fin n → ℝ :=
  mlpEval ((θ.1, θ.2, ω.1) : MlpParam (2 * n) (mW n) n) ω.2.2

/-- The point of the exact stand-in as a function of `(ξ, (u, γ))`, `c = √v·|b̂|·ξ`. -/
noncomputable def o1 (θ : HidParam (2 * n) (mW n))
    (ω : (Fin n → ℝ) × ((Fin (2 * n) → ℝ) × (Fin n → ℝ))) : Fin n → ℝ :=
  sphPt (lam (bhat θ) (hid2 θ.1 θ.2 ω.2.1) •
      ((Real.sqrt (2 / (mW n : ℝ)) * Real.sqrt (normSq (bhat θ))) • ω.1) +
    sig (2 / (mW n : ℝ)) (bhat θ) (hid2 θ.1 θ.2 ω.2.1) • ω.2.2)

/-- The point of the cheap stand-in as a function of `(ξ, γ)`. -/
noncomputable def o2 (θ : HidParam (2 * n) (mW n)) (ω : (Fin n → ℝ) × (Fin n → ℝ)) :
    Fin n → ℝ :=
  sphPt ((Real.sqrt (2 / (mW n : ℝ)) * Real.sqrt (normSq (bhat θ))) • ω.1 +
    tauHat (2 * n) (mW n) θ • ω.2)

lemma measurable_oA (θ : HidParam (2 * n) (mW n)) : Measurable (oA θ) :=
  continuous_mlpEval_joint.measurable.comp
    ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)

lemma measurable_oD1 (θ : HidParam (2 * n) (mW n)) : Measurable (oD1 θ) :=
  continuous_mlpEval_joint.measurable.comp
    ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
      (measurable_fst.comp measurable_snd))

lemma measurable_oD2 (θ : HidParam (2 * n) (mW n)) : Measurable (oD2 θ) :=
  continuous_mlpEval_joint.measurable.comp
    ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
      (measurable_snd.comp measurable_snd))

lemma measurable_o1 (θ : HidParam (2 * n) (mW n)) : Measurable (o1 θ) := by
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  exact measurable_sphPt.comp
    ((((measurable_lam (bhat θ)).comp (hh.comp (measurable_fst.comp measurable_snd))).smul
      ((measurable_const_smul (Real.sqrt (2 / (mW n : ℝ)) *
        Real.sqrt (normSq (bhat θ)))).comp measurable_fst)).add
      (((measurable_sig (2 / (mW n : ℝ)) (bhat θ)).comp
        (hh.comp (measurable_fst.comp measurable_snd))).smul
        (measurable_snd.comp measurable_snd)))

lemma measurable_o2 (θ : HidParam (2 * n) (mW n)) : Measurable (o2 θ) :=
  measurable_sphPt.comp
    (((measurable_const_smul (Real.sqrt (2 / (mW n : ℝ)) *
      Real.sqrt (normSq (bhat θ)))).comp measurable_fst).add
      ((measurable_const_smul (tauHat (2 * n) (mW n) θ)).comp measurable_snd))

lemma k4_mem {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : 0 ≤ kappa^[4] t ∧ kappa^[4] t ≤ 1 :=
  ⟨(kGood_iterate 3).nonneg_on ht, (kGood_iterate 3).le_one ht⟩

/-- `D_θ = E_{M₃} E_{u,u′}[1 − κ^{∘4}(⟨x(u), x(u′)⟩)]` for fixed `θ = (M₁, M₂)`. -/
noncomputable def DTh (n : ℕ) (θ : HidParam (2 * n) (mW n)) : ℝ :=
  ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
    (∫ uu, (1 - kappa^[4] (tX (N := 2 * n) (mW := mW n) (n := n)
      (uu, ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)))) ∂lawU2 (2 * n))
    ∂gaussMat n (mW n) (2 / (mW n : ℝ))

/-- The integrand of `DTh`, as a function of `(θ, M₃, (u, u′))`. -/
lemma bm_rD (hn : 1 ≤ n) :
    BM (fun q : (HidParam (2 * n) (mW n) × Matrix (Fin n) (Fin (mW n)) ℝ) ×
        ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) =>
      1 - kappa^[4] (tX (N := 2 * n) (mW := mW n) (n := n)
        (q.2, ((q.1.1.1, q.1.1.2, q.1.2) : MlpParam (2 * n) (mW n) n)))) := by
  refine ⟨measurable_const.sub ((continuous_kappa.iterate 4).measurable.comp
    (measurable_tX.comp (measurable_snd.prodMk
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.comp measurable_fst)))))), 1, fun q => ?_⟩
  have h := k4_mem (tX_mem (N := 2 * n) (mW := mW n) hn
    (q.2, ((q.1.1.1, q.1.1.2, q.1.2) : MlpParam (2 * n) (mW n) n)))
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

lemma DTh_nonneg (hn : 1 ≤ n) (θ : HidParam (2 * n) (mW n)) : 0 ≤ DTh n θ := by
  unfold DTh
  refine integral_nonneg fun M₃ => integral_nonneg fun uu => ?_
  have h := k4_mem (tX_mem (N := 2 * n) (mW := mW n) hn
    (uu, ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)))
  change (0 : ℝ) ≤ 1 - kappa^[4] (tX (N := 2 * n) (mW := mW n) (n := n)
    (uu, ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)))
  linarith [h.2]

/-- The mean over `(A, F)` of the mean squared difference at `(x(u), x(u′))`. -/
lemma lint_LoutD_theta {mA mF : ℕ} (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    (θ : HidParam (2 * n) (mW n)) :
    ∫⁻ p, LoutD (mA := mA) (mF := mF)
        ((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n))) (oD1 θ) (oD2 θ) p
        ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
      ENNReal.ofReal (4 / (n : ℝ) * (DTh n θ + eAFr n mA mF)) := by
  have hN : 1 ≤ 2 * n := by omega
  have := lawU2_prob hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he0 : 0 ≤ eAFr n mA mF := by
    have hcF := BstLean.Part133.cF2o_pos hmF
    have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn
    unfold eAFr; positivity
  set Pd := (gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n)) with hPd
  refine (lintegral_LoutD_le Pd hn hmA hmF (measurable_oD1 θ) (measurable_oD2 θ)).trans ?_
  set r : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) → ℝ :=
    fun ω => 1 - kappa^[4] (dotp (sphPt (oD1 θ ω)) (sphPt (oD2 θ ω))) with hr
  have br : BM r := (bm_rD hn).comp (g := fun ω : Matrix (Fin n) (Fin (mW n)) ℝ ×
      ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) => ((θ, ω.1), ω.2))
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hr0 : ∀ ω, 0 ≤ r ω := by
    intro ω
    have h := k4_mem (dotp_unit_mem (normSq_sphPt hn (oD1 θ ω)) (normSq_sphPt hn (oD2 θ ω)))
    rw [hr]
    linarith [h.2]
  have bq : BM (fun ω => 4 / (n : ℝ) * (r ω + eAFr n mA mF)) :=
    (BstLean.Part105.BM.const _).mul (br.add (BstLean.Part105.BM.const _))
  have e1 : ∫⁻ ω, ENNReal.ofReal (4 / (n : ℝ) *
      (1 - kappa^[4] (dotp (sphPt (oD1 θ ω)) (sphPt (oD2 θ ω))) + eAFr n mA mF)) ∂Pd =
      ENNReal.ofReal (∫ ω, 4 / (n : ℝ) * (r ω + eAFr n mA mF) ∂Pd) :=
    (ofReal_integral_eq_lintegral_ofReal (bq.integrable Pd)
      (Filter.Eventually.of_forall fun ω => by have := hr0 ω; positivity)).symm
  rw [e1]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [integral_const_mul, integral_add (br.integrable Pd) (integrable_const _)]
  have e2 : ∫ ω, r ω ∂Pd = DTh n θ := by
    rw [hPd, integral_prod _ (br.integrable _)]
    rfl
  rw [e2]
  simp

/-- **The mean variance under the stand-in**, for `θ ∈ goodHat n` and a bounded measurable
`φ`: `E_c Var_{ν̂_c} φ ≤ (1 + 1.83/n)·E_c E_{ν̂_c} φ² − E_{M₃}(E_{μ_W} φ)²`. -/
lemma var_bound_fixed (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c]
        ∂cDist n (2 / (mW n : ℝ)) (bhat θ) ≤
      (1 + 183 / 100 / (n : ℝ)) *
        (∫ c, (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) -
      ∫ M₃, (∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) := by
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  have b1 := bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (bhat θ) hh hφ.sq
  have bY := bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (bhat θ) hh hφ
  have hvar : ∀ c : Fin n → ℝ,
      Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c] =
      (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) -
        (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) ^ 2 := by
    intro c
    have := standIn_prob (n := n) (uniformSphere (2 * n)) hh (2 / (mW n : ℝ)) (bhat θ) c
    exact var_bm _ hφ
  have hVeq : ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
        (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ) =
      (∫ c, (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) -
        ∫ c, (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) ^ 2 ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by
    simp_rw [hvar]
    exact integral_sub (b1.integrable _) (bY.sq.integrable _)
  have hcross := s1_cross_mlp (n := n) hN θ.1 θ.2 (bhat_ne hn hθ) hφ
  have hmse := standInHat140 hn hθ hφ
  have hY0 : 0 ≤ ∫ c, (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
      (2 / (mW n : ℝ)) (bhat θ) c) ^ 2 ∂cDist n (2 / (mW n : ℝ)) (bhat θ) :=
    integral_nonneg fun _ => sq_nonneg _
  rw [hcross] at hmse
  rw [hVeq] at hmse ⊢
  have hδ : (0 : ℝ) ≤ 183 / 100 / (n : ℝ) := by positivity
  set J := ∫ c, (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
    (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ)
  set Y2 := ∫ c, (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
    (2 / (mW n : ℝ)) (bhat θ) c) ^ 2 ∂cDist n (2 / (mW n : ℝ)) (bhat θ)
  have h3 : 183 / 100 / (n : ℝ) * (J - Y2) ≤ 183 / 100 / (n : ℝ) * J :=
    mul_le_mul_of_nonneg_left (by linarith) hδ
  linarith

/-- `E_{M₃} Bn² = E φ(x(u))² − E (φ(x(u)) − φ(x(u′)))²/2` for fixed `(A, F)`. -/
lemma EX2_eq {mA mF : ℕ} (hn : 1 ≤ n) (θ : HidParam (2 * n) (mW n)) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) :
    ∫ M₃, (∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) =
      ∫ ω, phiS A F (oA θ ω) ^ 2
          ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (uniformSphere (2 * n))) -
        ∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2
          ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n))) := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have := lawU2_prob hN
  have hφ : BM (phiS A F) := bm_phiS hn A F
  set g : Matrix (Fin n) (Fin (mW n)) ℝ × (Fin (2 * n) → ℝ) → ℝ :=
    fun ω => phiS A F (oA θ ω) with hg
  have bg : BM g := hφ.comp (measurable_oA θ)
  set gd : Matrix (Fin n) (Fin (mW n)) ℝ × ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) → ℝ :=
    fun ω => (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2 with hgd
  have bgd : BM gd :=
    bm_half ((hφ.comp (measurable_oD1 θ)).sub (hφ.comp (measurable_oD2 θ))).sq
  have hX : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      (∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) ^ 2 =
      (∫ u, g (M₃, u) ^ 2 ∂uniformSphere (2 * n)) -
        ∫ p, gd (M₃, p) ∂lawU2 (2 * n) := by
    intro M₃
    have e1 : ∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) =
        ∫ u, g (M₃, u) ∂uniformSphere (2 * n) := by
      unfold muWn
      rw [integral_map (measurable_sphPt_mlpEval _).aemeasurable hφ.meas.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      change phiS A F (sphPt (mlpEval ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) u)) =
        phiS A F (mlpEval ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) u)
      unfold phiS
      rw [sphPt_idem hn]
    rw [e1]
    exact sq_mean_eq (uniformSphere (2 * n)) (a := fun u => g (M₃, u))
      (bg.comp (measurable_const.prodMk measurable_id))
  simp_rw [hX]
  have i1 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      ∫ u, g (M₃, u) ^ 2 ∂uniformSphere (2 * n)) (gaussMat n (mW n) (2 / (mW n : ℝ))) :=
    (bg.sq.integral_right (uniformSphere (2 * n))).integrable _
  have i2 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      ∫ p, gd (M₃, p) ∂lawU2 (2 * n)) (gaussMat n (mW n) (2 / (mW n : ℝ))) :=
    (bgd.integral_right (lawU2 (2 * n))).integrable _
  rw [integral_sub i1 i2, integral_prod (fun ω => g ω ^ 2) (bg.sq.integrable _),
    integral_prod gd (bgd.integrable _)]

/-- **The real inequality for fixed `θ ∈ goodHat n` and fixed `(A, F)`.** -/
lemma fixed_real (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n) {ζ : ℝ}
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) (A : MlpParam n (mA n) n)
    (F : MlpParam n (mF n) 1) :
    (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))) +
      (1 + η) * (183 / 100 / (n : ℝ)) * (∫ ω, phiS A F (oA θ ω) ^ 2
        ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (uniformSphere (2 * n)))) ≤
    (1 + η) * (183 / 100 / (n : ℝ)) * (1 + 183 / 100 / (n : ℝ)) *
        (∫ ω, phiS A F (o1 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod
          ((uniformSphere (2 * n)).prod (stdGauss (Fin n))))) +
      (1 + η) * (183 / 100 / (n : ℝ)) * (∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2
        ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n)))) +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        ((∫ ω, phiS A F (o1 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod
          ((uniformSphere (2 * n)).prod (stdGauss (Fin n))))) +
        ∫ ω, phiS A F (o2 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod (stdGauss (Fin n)))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := uniformSphere_isProbability (2 * n) hN
  have hH := HbarH_nonneg n ζ θ
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  have hφ : BM (phiS A F) := bm_phiS hn1 A F
  have h0 := cheapStandInHat hn hθ hζ0 hζ1 hη hφ 0
  simp only [sub_zero] at h0
  have eL : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, phiS A F x ∂cheapIn (M₃.mulVec (bhat θ)) (tauHat (2 * n) (mW n) θ)) ^ 2 =
      (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
        gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2 := by
    intro M₃
    rw [integral_phiS_muWn hn1, integral_phiS_cheapIn hn1]
    rfl
  simp_rw [eL] at h0
  have b1 := bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (bhat θ) hh hφ.sq
  have b2 : BM (fun c : Fin n → ℝ =>
      ∫ x, phiS A F x ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ)) :=
    bm_cheapIn measurable_id measurable_const hφ.sq
  have hsplit : ∫ c, ((∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
        (2 / (mW n : ℝ)) (bhat θ) c) +
        ∫ x, phiS A F x ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ))
        ∂cDist n (2 / (mW n : ℝ)) (bhat θ) =
      (∫ c, (∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
        (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) +
        ∫ c, (∫ x, phiS A F x ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ))
          ∂cDist n (2 / (mW n : ℝ)) (bhat θ) :=
    integral_add (b1.integrable _) (b2.integrable _)
  have e1 : ∫ c, (∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
        (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ) =
      ∫ ω, phiS A F (o1 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod
        ((uniformSphere (2 * n)).prod (stdGauss (Fin n)))) :=
    J1_eq (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (bhat θ) hh hφ.sq
  have e2 : ∫ c, (∫ x, phiS A F x ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ))
        ∂cDist n (2 / (mW n : ℝ)) (bhat θ) =
      ∫ ω, phiS A F (o2 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) :=
    J2_eq (n := n) (2 / (mW n : ℝ)) (bhat θ) (tauHat (2 * n) (mW n) θ) hφ.sq
  have hV := var_bound_fixed hn hθ hφ
  rw [EX2_eq hn1 θ A F, e1] at hV
  rw [hsplit, e1, e2] at h0
  have hc : (0 : ℝ) ≤ (1 + η) * (183 / 100 / (n : ℝ)) := by positivity
  have h5 := mul_le_mul_of_nonneg_left hV hc
  have e5 : (1 + η) * (183 / 100 / (n : ℝ) *
      ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
        (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) =
      (1 + η) * (183 / 100 / (n : ℝ)) *
      ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
        (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by ring
  rw [e5] at h0
  linarith

/-- **The error for fixed `(M₁, M₂)` on the good event, with the variance of the stand-in.**
For `n ≥ 4096`, `θ = (M₁, M₂) ∈ goodHat n` and `0 ≤ ζ < 1`:
`E_{A,F} E_{M₃}(Bn − gHat)² ≤
  ((1 + η)(1.83/n)(D_θ + eAFr + 1.83/n) + 4(1 + 1/η)·HbarH n ζ θ)·(4/n)`. -/
theorem errFixedHat142 (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ goodHat n) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)))
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal (((1 + η) * (183 / 100 / (n : ℝ)) *
        (DTh n θ + eAFr n (mA n) (mF n) + 183 / 100 / (n : ℝ)) +
      4 * (1 + 1 / η) * HbarH n ζ θ) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have := lawU2_prob hN
  have hH := HbarH_nonneg n ζ θ
  have hD0 := DTh_nonneg hn1 θ
  have he0 : 0 ≤ eAFr n (mA n) (mF n) := by
    have hcF := BstLean.Part133.cF2o_pos hmF
    have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn1
    unfold eAFr; positivity
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set Pa := gM.prod (uniformSphere (2 * n)) with hPa
  set Pd := gM.prod (lawU2 (2 * n)) with hPd
  set P₁ := (stdGauss (Fin n)).prod ((uniformSphere (2 * n)).prod (stdGauss (Fin n))) with hP₁
  set P₂ := (stdGauss (Fin n)).prod (stdGauss (Fin n)) with hP₂
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set c : ℝ := (1 + η) * (183 / 100 / (n : ℝ)) with hc
  set δ : ℝ := 183 / 100 / (n : ℝ) with hδ
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
    have hr := fixed_real hn hθ hζ0 hζ1 hη A F
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
  have hSd := lint_LoutD_theta (mA := mA n) (mF := mF n) hn1 hmA hmF θ
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
      ENNReal.ofReal (c * (1 + δ) * S + c * (S * (DTh n θ + eAFr n (mA n) (mF n))) +
        a₂ * (S + S)) := by
    rw [ENNReal.ofReal_mul (q := S) hc0]
    refine hint.trans ?_
    have hD0' : 0 ≤ S * (DTh n θ + eAFr n (mA n) (mF n)) := by positivity
    have hcd : 0 ≤ c * (1 + δ) := by positivity
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (q := S) hcd,
      ENNReal.ofReal_mul (q := S * (DTh n θ + eAFr n (mA n) (mF n))) hc0,
      ENNReal.ofReal_mul (q := S + S) ha₂0, ENNReal.ofReal_add hS0 hS0]
    exact add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hSd)) le_rfl
  have h2 := ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hfin
  rw [← ENNReal.ofReal_sub _ (mul_nonneg hc0 hS0)] at h2
  refine h2.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [ha₂]
  ring

end fixed

end BstLean.Part142

open BstLean.Part142 in
#print axioms s1_cross
open BstLean.Part142 in
#print axioms lint_phi_diff
open BstLean.Part142 in
#print axioms errFixedHat142
