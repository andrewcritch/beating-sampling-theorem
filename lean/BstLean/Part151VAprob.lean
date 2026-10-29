import BstLean.Part151VAmeas

/-!
# Part 151, Proposition VA (b), stage (c): the probabilities of the bad events

`fixP k n` is the distribution of `((W, A, θF), η)`; all blocks are independent. Each bad event
is paid in its conditional step (the order of the random variables of the document):

* `prob_slice`: a general Fubini step: if every section of a measurable set `B` in the last
  variable has probability at most `q`, then `B` has probability at most `q`.
* `fix_map_theta`, `fix_map_A3`: under `fixP`, the matrices `θF = (F₁, F₂)`, and the last matrix
  `A₃` of `A`, are independent of all other variables.
* `prob_X12`, `prob_X3`, `prob_ON`, `prob_Tm`, `prob_FE`, `prob_JU`, `prob_s`, `prob_U`: the
  probability of each bad event.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (nrm nrm_sq nrm_nonneg)
open BstLean.Part134 (lam res sig)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part149 (thA tauOutOf measurable_thA)
open BstLean.Part150 (CMap)

/-! ## General steps -/

section gen

variable {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]

/-- **A Fubini step.** `μ` is, through the measurable maps `e'` and `e` (`e ∘ e' = id`), the
product `ρ ⊗ ν`. If every section `{y | e (x, y) ∈ B}` of a measurable set `B` has
`ν`-probability at most `q`, then `μ(B) ≤ q`. -/
lemma prob_slice (μ : Measure Z) (ρ : Measure X) (ν : Measure Y) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν] {e' : Z → X × Y} {e : X × Y → Z} (he' : Measurable e')
    (he : Measurable e) (hmap : μ.map e' = ρ.prod ν) (hid : ∀ z, e (e' z) = z) {B : Set Z}
    (hB : MeasurableSet B) {q : ℝ} (hq : 0 ≤ q) (h : ∀ x, ν.real {y | e (x, y) ∈ B} ≤ q) :
    μ.real B ≤ q := by
  have eB : B = e' ⁻¹' (e ⁻¹' B) := by
    ext z
    simp only [mem_preimage, hid]
  have hpt : ∀ x, ν (Prod.mk x ⁻¹' (e ⁻¹' B)) ≤ ENNReal.ofReal q := by
    intro x
    have hx := h x
    rw [measureReal_def] at hx
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hq).mpr hx
  have hle : μ B ≤ ENNReal.ofReal q := by
    rw [eB, ← Measure.map_apply he' (he hB), hmap, Measure.prod_apply (he hB)]
    calc ∫⁻ x, ν (Prod.mk x ⁻¹' (e ⁻¹' B)) ∂ρ ≤ ∫⁻ _x, ENNReal.ofReal q ∂ρ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal q := by simp
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hq hle

lemma prob_marg (μ : Measure Z) (ρ : Measure X) {f : Z → X} (hf : Measurable f)
    (hmap : μ.map f = ρ) {S : Set X} (hS : MeasurableSet S) :
    μ.real {z | f z ∈ S} = ρ.real S := by
  rw [← hmap, map_measureReal_apply hf hS]
  rfl

lemma map_fst_prob (ρ : Measure X) (ν : Measure Y) [IsProbabilityMeasure ν] [SFinite ρ] :
    (ρ.prod ν).map Prod.fst = ρ := by
  rw [Measure.map_fst_prod]; simp

end gen

/-! ## The independent blocks of `fixP` -/

section maps

variable {k n : ℕ}

/-- `θF` last. -/
def eTh' (ω : Fix k n) :
    ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) × (Fin k → Fin n → ℝ)) ×
      HidParam n (mF n) :=
  (((ω.1.1, ω.1.2.1), ω.2), ω.1.2.2)

def eTh (p : ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) × (Fin k → Fin n → ℝ)) ×
    HidParam n (mF n)) : Fix k n :=
  ((p.1.1.1, p.1.1.2, p.2), p.1.2)

lemma measurable_eTh' : Measurable (eTh' (k := k) (n := n)) := by unfold eTh'; fun_prop

lemma measurable_eTh : Measurable (eTh (k := k) (n := n)) := by unfold eTh; fun_prop

lemma eTh_eTh' (ω : Fix k n) : eTh (eTh' ω) = ω := rfl

/-- **`θF = (F₁, F₂)` is independent of `(W, A, η)`.** -/
theorem fix_map_theta :
    (fixP k n).map eTh' =
      (((mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n)).prod (gamK k n)).prod
        (hidGauss n (mF n)) := by
  have s1 := assoc_symm_map (mlpGauss (2 * n) (mW n) n) (mlpGauss n (mA n) n)
    (hidGauss n (mF n))
  have s2 := map_fst_prod (gamK k n) (by fun_prop) s1
  have s3 := swap_last ((mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n))
    (hidGauss n (mF n)) (gamK k n)
  rw [← s2, Measure.map_map (by fun_prop) (by fun_prop)] at s3
  unfold fixP
  rw [← s3]
  rfl

/-- `A₃` last. -/
def eA3' (ω : Fix k n) :
    ((MlpParam (2 * n) (mW n) n × HidParam n (mA n) × HidParam n (mF n)) ×
      (Fin k → Fin n → ℝ)) × Matrix (Fin n) (Fin (mA n)) ℝ :=
  (((ω.1.1, ((ω.1.2.1.1, ω.1.2.1.2.1), ω.1.2.2)), ω.2), ω.1.2.1.2.2)

def eA3 (p : ((MlpParam (2 * n) (mW n) n × HidParam n (mA n) × HidParam n (mF n)) ×
    (Fin k → Fin n → ℝ)) × Matrix (Fin n) (Fin (mA n)) ℝ) : Fix k n :=
  ((p.1.1.1, (p.1.1.2.1.1, p.1.1.2.1.2, p.2), p.1.1.2.2), p.1.2)

lemma measurable_eA3' : Measurable (eA3' (k := k) (n := n)) := by unfold eA3'; fun_prop

lemma measurable_eA3 : Measurable (eA3 (k := k) (n := n)) := by unfold eA3; fun_prop

lemma eA3_eA3' (ω : Fix k n) : eA3 (eA3' ω) = ω := rfl

/-- **The last matrix `A₃` of `A` is independent of `(W, A₁, A₂, θF, η)`.** -/
theorem fix_map_A3 :
    (fixP k n).map eA3' =
      (((mlpGauss (2 * n) (mW n) n).prod ((hidGauss n (mA n)).prod (hidGauss n (mF n)))).prod
        (gamK k n)).prod (gaussMat n (mA n) (2 / (mA n : ℝ))) := by
  -- `A = (A₁, (A₂, A₃))` to `((A₁, A₂), A₃)`
  have sA : (mlpGauss n (mA n) n).map
      (fun A : MlpParam n (mA n) n => (((A.1, A.2.1) : HidParam n (mA n)), A.2.2)) =
      (hidGauss n (mA n)).prod (gaussMat n (mA n) (2 / (mA n : ℝ))) := by
    unfold mlpGauss hidGauss
    exact assoc_symm_map _ _ _
  -- `(A, θF)` to `(((A₁, A₂), θF), A₃)`
  have sAθ : ((mlpGauss n (mA n) n).prod (hidGauss n (mF n))).map
      (fun p : MlpParam n (mA n) n × HidParam n (mF n) =>
        ((((p.1.1, p.1.2.1) : HidParam n (mA n)), p.2), p.1.2.2)) =
      ((hidGauss n (mA n)).prod (hidGauss n (mF n))).prod
        (gaussMat n (mA n) (2 / (mA n : ℝ))) := by
    have h1 := map_fst_prod (hidGauss n (mF n)) (by fun_prop) sA
    have h2 := swap_last (hidGauss n (mA n)) (gaussMat n (mA n) (2 / (mA n : ℝ)))
      (hidGauss n (mF n))
    rw [← h1, Measure.map_map (by fun_prop) (by fun_prop)] at h2
    rw [← h2]
    rfl
  -- with `W`
  have sW : ((mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (hidGauss n (mF n)))).map
      (fun x : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × HidParam n (mF n) =>
        ((x.1, (((x.2.1.1, x.2.1.2.1) : HidParam n (mA n)), x.2.2)), x.2.1.2.2)) =
      ((mlpGauss (2 * n) (mW n) n).prod ((hidGauss n (mA n)).prod (hidGauss n (mF n)))).prod
        (gaussMat n (mA n) (2 / (mA n : ℝ))) := by
    have h1 := map_snd_prod (mlpGauss (2 * n) (mW n) n) (by fun_prop) sAθ
    have h2 := assoc_symm_map (mlpGauss (2 * n) (mW n) n)
      ((hidGauss n (mA n)).prod (hidGauss n (mF n))) (gaussMat n (mA n) (2 / (mA n : ℝ)))
    rw [← h1, Measure.map_map (by fun_prop) (by fun_prop)] at h2
    rw [← h2]
    rfl
  -- with `η`
  have s4 := map_fst_prod (gamK k n) (by fun_prop) sW
  have s5 := swap_last ((mlpGauss (2 * n) (mW n) n).prod
    ((hidGauss n (mA n)).prod (hidGauss n (mF n)))) (gaussMat n (mA n) (2 / (mA n : ℝ)))
    (gamK k n)
  rw [← s4, Measure.map_map (by fun_prop) (by fun_prop)] at s5
  unfold fixP
  rw [← s5]
  rfl

/-- The marginal of `(W, A)`. -/
theorem fix_map_WA :
    (fixP k n).map (fun ω : Fix k n => (ω.1.1, ω.1.2.1)) =
      (mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n) := by
  have h := congrArg (Measure.map (fun p : ((MlpParam (2 * n) (mW n) n ×
    MlpParam n (mA n) n) × (Fin k → Fin n → ℝ)) × HidParam n (mF n) => p.1.1))
    (fix_map_theta (k := k) (n := n))
  rw [Measure.map_map (by fun_prop) measurable_eTh'] at h
  have e : (fun p : ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) ×
      (Fin k → Fin n → ℝ)) × HidParam n (mF n) => p.1.1) = Prod.fst ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map measurable_fst measurable_fst, map_fst_prob, map_fst_prob] at h
  exact h

/-- The marginal of `(W, (A₁, A₂))`. -/
theorem fix_map_W12 :
    (fixP k n).map (fun ω : Fix k n => (ω.1.1, thA ω.1.2.1)) =
      (mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n)) := by
  have h := congrArg (Measure.map (fun p : ((MlpParam (2 * n) (mW n) n ×
    HidParam n (mA n) × HidParam n (mF n)) × (Fin k → Fin n → ℝ)) ×
    Matrix (Fin n) (Fin (mA n)) ℝ => p.1.1)) (fix_map_A3 (k := k) (n := n))
  rw [Measure.map_map (by fun_prop) measurable_eA3'] at h
  have e : (fun p : ((MlpParam (2 * n) (mW n) n × HidParam n (mA n) × HidParam n (mF n)) ×
      (Fin k → Fin n → ℝ)) × Matrix (Fin n) (Fin (mA n)) ℝ => p.1.1) =
      Prod.fst ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map measurable_fst measurable_fst, map_fst_prob, map_fst_prob] at h
  have h2 := map_snd_prod (mlpGauss (2 * n) (mW n) n)
    (f := fun q : HidParam n (mA n) × HidParam n (mF n) => q.1) measurable_fst
    (map_fst_prob (hidGauss n (mA n)) (hidGauss n (mF n)))
  rw [← h, Measure.map_map (by fun_prop) (by fun_prop)] at h2
  rw [← h2]
  rfl

end maps

/-! ## The bad events -/

section events

variable {k n : ℕ}

/-- The charge of one fourth-moment event: `(432/m_F²)(1 + 63/m_F)(2/δ⁴)`. -/
noncomputable def chF (n : ℕ) (δ : ℝ) : ℝ :=
  432 / (mF n : ℝ) ^ 2 * (1 + 63 / (mF n)) * (1 / δ ^ 4 + 1 / δ ^ 4)

/-- The Lipschitz constant of the features on the operator-norm event: `L_F = K1·K2`. -/
noncomputable def LFc (n : ℕ) (uF : ℝ) : ℝ := K1 n (mF n) uF * K2 (mF n) uF

lemma LFc_pos (hn : 1 ≤ n) {uF : ℝ} (huF : 0 ≤ uF) : 0 < LFc n uF := by
  have hmF : 1 ≤ mF n := mF_pos hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < mF n := by exact_mod_cast hmF
  have h1 : 0 < √(mF n : ℝ) := Real.sqrt_pos.mpr hm0
  have h2 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  unfold LFc K1 K2
  have a1 : 0 < √(2 / (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have a2 : 0 < √(2 / (mF n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have b1 : 0 < √(mF n : ℝ) + √(n : ℝ) + uF := by linarith
  have b2 : 0 < √(mF n : ℝ) + √(mF n : ℝ) + uF := by linarith
  positivity

variable (bh : CMap n) (k)

/-- `(W, (A₁, A₂))` is outside `X12`. -/
def B12 (X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))) : Set (Fix k n) :=
  {ω | (ω.1.1, thA ω.1.2.1) ∉ X12}

/-- `(W, A)` is outside `X3`. -/
def B3 (X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)) : Set (Fix k n) :=
  {ω | (ω.1.1, ω.1.2.1) ∉ X3}

/-- The operator-norm event of `F` fails. -/
def BON (uF : ℝ) : Set (Fix k n) := {ω | ω.1.2.2 ∉ EON n (mF n) uF}

/-- The event of equation (Tm) fails (on `X12`). -/
def BTm (X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))) (δ : ℝ) : Set (Fix k n) :=
  {ω | (ω.1.1, thA ω.1.2.1) ∈ X12 ∧
    (1 + δ) * (1 + δ) * (2 / (n : ℝ) * Dc bh ω.1.1 ω.1.2.1) <
      2 / (mF n : ℝ) * normSq (dM bh ω.1.1 ω.1.2.1 ω.1.2.2)}

/-- The feature-energy event at `(c_A, σ_p)` fails. -/
def BFE (δ : ℝ) : Set (Fix k n) :=
  {ω | (1 + δ) * (1 + δ) * (2 / (n : ℝ) *
      (normSq (cAv bh ω.1.1 ω.1.2.1) + n * sigP bh ω.1.1 ω.1.2.1 ^ 2)) <
    2 / (mF n : ℝ) * ∫ γ, normSq (zS ω.1.2.2 (cAv bh ω.1.1 ω.1.2.1) (sigP bh ω.1.1 ω.1.2.1) γ)
      ∂stdGauss (Fin n)}

/-- The event `E_{JU}` at `c = c_A` fails. -/
def BJU (δ : ℝ) : Set (Fix k n) :=
  {ω | 2 * (1 + δ) * (1 + δ) <
    PhiU bh ω.1.1 ω.1.2.1.1 ω.1.2.1.2.1 ω.1.2.2 (cAv bh ω.1.1 ω.1.2.1)}

/-- The event `E_s` of the sampling term fails (on the operator-norm event). -/
def Bs (uF Lc : ℝ) : Set (Fix k n) :=
  {ω | ω.1.2.2 ∈ EON n (mF n) uF ∧
    √(2 / (mF n : ℝ) * ((∫ γ, normSq (zS ω.1.2.2 (cAv bh ω.1.1 ω.1.2.1)
      (sigP bh ω.1.1 ω.1.2.1) γ) ∂stdGauss (Fin n)) / k)) + uS n k (LFc n uF) Lc ≤
      Ts ω.1.2.2 (cAv bh ω.1.1 ω.1.2.1) (sigP bh ω.1.1 ω.1.2.1) k ω.2}

/-- The events `E_U`, `E_×` fail (on `X12` and on the operator-norm event). -/
def BU (X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))) (uF Mr Lc : ℝ) :
    Set (Fix k n) :=
  {ω | (ω.1.1, thA ω.1.2.1) ∈ X12 ∧ ω.1.2.2 ∈ EON n (mF n) uF ∧
    ¬ (TU bh ω.1.1 ω.1.2.1.1 ω.1.2.1.2.1 ω.1.2.2 ω.1.2.1.2.2 <
        √(Mr * PhiU bh ω.1.1 ω.1.2.1.1 ω.1.2.1.2.1 ω.1.2.2 (cAv bh ω.1.1 ω.1.2.1)) +
          uU n (LFc n uF) Mr Lc ∧
      -(√(2 / (mF n : ℝ)) * ∑ i, wX bh ω.1.1 ω.1.2.1 ω.1.2.2 k ω.2 (cAv bh ω.1.1 ω.1.2.1) i *
        dU bh ω.1.1 ω.1.2.1 ω.1.2.2 i) < uU n (LFc n uF) Mr Lc)}

/-! ### Measurability -/

variable {bh} {k}

lemma mW' : Measurable (fun ω : Fix k n => ω.1.1) := by fun_prop
lemma mA' : Measurable (fun ω : Fix k n => ω.1.2.1) := by fun_prop
lemma mθ' : Measurable (fun ω : Fix k n => ω.1.2.2) := by fun_prop
lemma mη' : Measurable (fun ω : Fix k n => ω.2) := by fun_prop

lemma m12' : Measurable (fun ω : Fix k n => (ω.1.1, thA ω.1.2.1)) :=
  mW'.prodMk (measurable_thA.comp mA')

lemma EON_meas (n m : ℕ) (u : ℝ) : MeasurableSet (EON n m u) := by
  unfold EON
  have h1 : Measurable (fun θ : HidParam n m => BstLean.Part152.opN θ.1) :=
    BstLean.Part152.opN_continuous.measurable.comp measurable_fst
  have h2 : Measurable (fun θ : HidParam n m => BstLean.Part152.opN θ.2) :=
    BstLean.Part152.opN_continuous.measurable.comp measurable_snd
  exact (measurableSet_lt h1 measurable_const).inter (measurableSet_lt h2 measurable_const)

lemma B12_meas {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (h : MeasurableSet X12) : MeasurableSet (B12 k X12) := (m12' h).compl

lemma B3_meas {X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)}
    (h : MeasurableSet X3) : MeasurableSet (B3 k X3) :=
  ((mW'.prodMk mA') h).compl

lemma BON_meas (uF : ℝ) : MeasurableSet (BON (n := n) k uF) := (mθ' (EON_meas n (mF n) uF)).compl

lemma BTm_meas (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h : MeasurableSet X12)
    (δ : ℝ) : MeasurableSet (BTm k bh X12 δ) := by
  have h1 : Measurable (fun ω : Fix k n =>
      (1 + δ) * (1 + δ) * (2 / (n : ℝ) * Dc bh ω.1.1 ω.1.2.1)) :=
    measurable_const.mul (measurable_const.mul
      (meas_Dc (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1) hbh mW' mA'))
  have h2 : Measurable (fun ω : Fix k n =>
      2 / (mF n : ℝ) * normSq (dM bh ω.1.1 ω.1.2.1 ω.1.2.2)) := by
    unfold normSq
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (meas_dM (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1)
        (fθ := fun ω => ω.1.2.2) hbh mW' mA' mθ' i).pow_const 2)
  have h3 : MeasurableSet {ω : Fix k n | (1 + δ) * (1 + δ) * (2 / (n : ℝ) *
      Dc bh ω.1.1 ω.1.2.1) < 2 / (mF n : ℝ) * normSq (dM bh ω.1.1 ω.1.2.1 ω.1.2.2)} :=
    measurableSet_lt h1 h2
  exact (m12' h).inter h3

lemma BFE_meas (hbh : Measurable bh) (δ : ℝ) : MeasurableSet (BFE k bh δ) := by
  have hc := meas_cAv (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1) hbh mW' mA'
  have hσ := meas_sigP (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1) hbh mW' mA'
  refine measurableSet_lt ?_ ?_
  · exact measurable_const.mul (measurable_const.mul
      ((measurable_normSq.comp hc).add (measurable_const.mul (hσ.pow_const 2))))
  · exact measurable_const.mul (meas_IzS (gθ := fun ω : Fix k n => ω.1.2.2) mθ' hc hσ)

lemma BJU_meas (hbh : Measurable bh) (δ : ℝ) : MeasurableSet (BJU k bh δ) := by
  have hc := meas_cAv (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1) hbh mW' mA'
  exact measurableSet_lt measurable_const
    (meas_PhiU (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1)
      (fθ := fun ω => ω.1.2.2) hbh mW' mA' mθ' hc)

lemma Bs_meas (hbh : Measurable bh) (uF Lc : ℝ) : MeasurableSet (Bs k bh uF Lc) := by
  have hc := meas_cAv (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1) hbh mW' mA'
  have hσ := meas_sigP (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1) hbh mW' mA'
  have h1 : Measurable (fun ω : Fix k n => √(2 / (mF n : ℝ) *
      ((∫ γ, normSq (zS ω.1.2.2 (cAv bh ω.1.1 ω.1.2.1) (sigP bh ω.1.1 ω.1.2.1) γ)
        ∂stdGauss (Fin n)) / k)) + uS n k (LFc n uF) Lc) :=
    ((measurable_const.mul ((meas_IzS (gθ := fun ω : Fix k n => ω.1.2.2) mθ' hc
      hσ).div_const _)).sqrt).add_const _
  have h2 : Measurable (fun ω : Fix k n =>
      Ts ω.1.2.2 (cAv bh ω.1.1 ω.1.2.1) (sigP bh ω.1.1 ω.1.2.1) k ω.2) :=
    meas_Ts (gθ := fun ω : Fix k n => ω.1.2.2) (fη := fun ω => ω.2) mθ' hc hσ mη'
  exact (mθ' (EON_meas n (mF n) uF)).inter (measurableSet_le h1 h2)

lemma BU_meas (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h : MeasurableSet X12)
    (uF Mr Lc : ℝ) : MeasurableSet (BU k bh X12 uF Mr Lc) := by
  have hc := meas_cAv (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1) hbh mW' mA'
  have hTU := meas_TU (fW := fun ω : Fix k n => ω.1.1) (fA1 := fun ω => ω.1.2.1.1)
    (fA2 := fun ω => ω.1.2.1.2.1) (fA3 := fun ω => ω.1.2.1.2.2) (fθ := fun ω => ω.1.2.2) hbh
    mW' (by fun_prop) (by fun_prop) (by fun_prop) mθ'
  have hPhi := meas_PhiU (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1)
    (fθ := fun ω => ω.1.2.2) hbh mW' mA' mθ' hc
  have hX : Measurable (fun ω : Fix k n => -(√(2 / (mF n : ℝ)) *
      ∑ i, wX bh ω.1.1 ω.1.2.1 ω.1.2.2 k ω.2 (cAv bh ω.1.1 ω.1.2.1) i *
        dU bh ω.1.1 ω.1.2.1 ω.1.2.2 i)) :=
    (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (meas_wX (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1)
        (fθ := fun ω => ω.1.2.2) (fη := fun ω => ω.2) hbh mW' mA' mθ' mη' hc i).mul
      (meas_dU (fW := fun ω : Fix k n => ω.1.1) (fA := fun ω => ω.1.2.1)
        (fθ := fun ω => ω.1.2.2) hbh mW' mA' mθ' i))).neg
  refine (m12' h).inter ((mθ' (EON_meas n (mF n) uF)).inter ?_)
  exact ((measurableSet_lt hTU (((measurable_const.mul hPhi).sqrt).add_const _)).inter
    (measurableSet_lt hX measurable_const)).compl

end events

end BstLean.Part151
