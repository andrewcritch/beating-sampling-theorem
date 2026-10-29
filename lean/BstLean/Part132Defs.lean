import BstLean.Part132Net
import BstLean.Part131All

/-!
# Part 132, item 1 (definitions): the kernel averages `b₂`, `b₁₁`

Role: `delegations/statements/p132-spec.md`. Paper source: `onW2c-cx.md` §8 ((16), (18)),
`onW4-opus-prover.md` §2 (`k(u, u′) = (2/m_F)⟨H_A(u), H_A(u′)⟩`, `b₂ = E k`).

* `kern F A A' x x' = (2/m_F)·⟨H_A(x), H_{A′}(x′)⟩`, `H_A(x) = ReLU(F₂ ReLU(F₁ A(x)))` the last
  hidden vector of `F` at `A(x)`.
* `xW W u = W(u)/|W(u)|` (the fixed point `e0` at `W(u) = 0`).
* `lawR`: the distribution of `(W, (A, (A′, F)))`, four independent networks; `lawU2`: two
  independent uniform inputs `(u, u′)`.
* `b2 = E kern F A A (x(u)) (x(u′))`, `b11 = E kern F A A′ (x(u)) (x(u′))`, means under
  `lawU2 ⊗ lawR`.
* `lawR_map`: the distribution `lawAll` of Part 131 is the image of `lawR`.
* `kgen`: the five integrands of the proof; measurability and integrability.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131

variable {N mW n mA mF : ℕ}

/-- **The kernel** `k = (2/m_F)·⟨H_A(x), H_{A′}(x′)⟩`: the scaled inner product of the last hidden
vectors of `F` at `A(x)` and `A′(x′)`. It does not read the last matrix `F.2.2` of `F`. -/
noncomputable def kern (F : MlpParam n mF 1) (A A' : MlpParam n mA n) (x x' : Fin n → ℝ) : ℝ :=
  2 / (mF : ℝ) * dotp (hidF F.1 F.2.1 A x) (hidF F.1 F.2.1 A' x')

/-- `x = W(u)/|W(u)|`, with the fixed point `e0 n` at `W(u) = 0`. -/
noncomputable def xW (W : MlpParam N mW n) (u : Fin N → ℝ) : Fin n → ℝ := sphPt (mlpEval W u)

/-- The four networks in the order `(W, (A, (A′, F)))`. -/
abbrev Rest (N mW n mA mF : ℕ) : Type :=
  MlpParam N mW n × MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1

/-- The distribution of `(W, (A, (A′, F)))`: four independent random ReLU MLPs. -/
noncomputable def lawR (N mW n mA mF : ℕ) : Measure (Rest N mW n mA mF) :=
  (mlpGauss N mW n).prod ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))

/-- Two independent uniform unit vectors `(u, u′)` of `ℝ^N`. -/
noncomputable def lawU2 (N : ℕ) : Measure ((Fin N → ℝ) × (Fin N → ℝ)) :=
  (uniformSphere N).prod (uniformSphere N)

instance : IsProbabilityMeasure (lawR N mW n mA mF) := by unfold lawR; infer_instance

/-- **`b₂`**: the mean, over the networks and two independent inputs `u, u′`, of
`(2/m_F)·⟨H_A(x(u)), H_A(x(u′))⟩` (the same Agent network at both inputs). -/
noncomputable def b2 (N mW n mA mF : ℕ) : ℝ :=
  ∫ ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF,
    kern ω.2.2.2.2 ω.2.2.1 ω.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2)
    ∂((lawU2 N).prod (lawR N mW n mA mF))

/-- **`b₁₁`**: the same with two independent Agent networks `A`, `A′`:
the mean of `(2/m_F)·⟨H_A(x(u)), H_{A′}(x(u′))⟩`. -/
noncomputable def b11 (N mW n mA mF : ℕ) : ℝ :=
  ∫ ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF,
    kern ω.2.2.2.2 ω.2.2.1 ω.2.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2)
    ∂((lawU2 N).prod (lawR N mW n mA mF))

/-! ## The measure identities -/

section meas

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (μ : Measure α) (ν : Measure β) (τ : Measure γ) [SFinite μ] [SFinite ν] [SFinite τ]

/-- `(a, (a′, f)) ↦ (f, (a, a′))` maps `μ ⊗ (ν ⊗ τ)` to `τ ⊗ (μ ⊗ ν)`. -/
lemma map_rot3 :
    (μ.prod (ν.prod τ)).map (fun p : α × β × γ => (p.2.2, (p.1, p.2.1))) =
      τ.prod (μ.prod ν) := by
  calc (μ.prod (ν.prod τ)).map (fun p : α × β × γ => (p.2.2, (p.1, p.2.1)))
      = (((μ.prod ν).prod τ).map MeasurableEquiv.prodAssoc).map
          (fun p : α × β × γ => (p.2.2, (p.1, p.2.1))) := by rw [Measure.prodAssoc_prod]
    _ = ((μ.prod ν).prod τ).map Prod.swap :=
        Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)
    _ = τ.prod (μ.prod ν) := Measure.prod_swap

/-- `(a, (a′, f)) ↦ (a′, (a, f))` keeps `μ ⊗ (μ ⊗ τ)`. -/
lemma map_swap12 :
    (μ.prod (μ.prod τ)).map (fun p : α × α × γ => (p.2.1, (p.1, p.2.2))) =
      μ.prod (μ.prod τ) := by
  conv_lhs => rw [← Measure.prodAssoc_prod]
  rw [Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  have h := Measure.map_prod_map (μ.prod μ) τ (f := Prod.swap) (g := id) measurable_swap
    measurable_id
  rw [Measure.prod_swap, Measure.map_id] at h
  conv_rhs => rw [← Measure.prodAssoc_prod, h]
  rw [Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  rfl

end meas

/-- The map from `(W, (A, (A′, F)))` to the point `((W, F), (A, A′))` of Part 131. -/
def toAll (r : Rest N mW n mA mF) :
    (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n × MlpParam n mA n :=
  ((r.1, r.2.2.2), (r.2.1, r.2.2.1))

lemma measurable_toAll : Measurable (toAll (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) := by
  unfold toAll; fun_prop

/-- **`lawAll` of Part 131 is the image of `lawR`** under `(W, (A, (A′, F))) ↦ ((W, F), (A, A′))`. -/
theorem lawR_map : (lawR N mW n mA mF).map toAll = lawAll N mW n mA mF := by
  unfold lawR lawAll lawWF
  have h1 := map_rot3 (mlpGauss n mA n) (mlpGauss n mA n) (mlpGauss n mF 1)
  have h2 := Measure.map_prod_map (mlpGauss N mW n)
    ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) (f := id)
    (g := fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 => (p.2.2, (p.1, p.2.1)))
    measurable_id (by fun_prop)
  rw [Measure.map_id, h1] at h2
  have h3 := Measure.prodAssoc_prod (μ := mlpGauss N mW n) (ν := mlpGauss n mF 1)
    (τ := (mlpGauss n mA n).prod (mlpGauss n mA n))
  rw [h2] at h3
  have h4 := congrArg (Measure.map MeasurableEquiv.prodAssoc.symm) h3
  rw [Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    MeasurableEquiv.symm_comp_self, Measure.map_id,
    Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)] at h4
  rw [h4]
  rfl

/-- The exchange of `A` and `A′`. -/
def swapA (r : Rest N mW n mA mF) : Rest N mW n mA mF := (r.1, (r.2.2.1, (r.2.1, r.2.2.2)))

lemma measurable_swapA :
    Measurable (swapA (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) := by
  unfold swapA; fun_prop

theorem lawR_swapA : (lawR N mW n mA mF).map swapA = lawR N mW n mA mF := by
  unfold lawR
  have h1 := map_swap12 (mlpGauss n mA n) (mlpGauss n mF 1)
  have h2 := Measure.map_prod_map (mlpGauss N mW n)
    ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) (f := id)
    (g := fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 => (p.2.1, (p.1, p.2.2)))
    measurable_id (by fun_prop)
  rw [Measure.map_id, h1] at h2
  conv_rhs => rw [h2]
  rfl

/-! ## The five integrands -/

/-- The general integrand: `pa`, `pa'` choose `A` (`false`) or `A′` (`true`) at the first and at
the second input; `dg = true` uses the input `u` twice. -/
noncomputable def kgen (pa pa' dg : Bool)
    (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  kern ω.2.2.2.2 (bif pa then ω.2.2.2.1 else ω.2.2.1) (bif pa' then ω.2.2.2.1 else ω.2.2.1)
    (xW ω.2.1 ω.1.1) (xW ω.2.1 (bif dg then ω.1.1 else ω.1.2))

lemma b2_eq : b2 N mW n mA mF =
    ∫ ω, kgen false false false ω ∂((lawU2 N).prod (lawR N mW n mA mF)) := rfl

lemma b11_eq : b11 N mW n mA mF =
    ∫ ω, kgen false true false ω ∂((lawU2 N).prod (lawR N mW n mA mF)) := rfl

lemma measurable_xW : Measurable (fun p : MlpParam N mW n × (Fin N → ℝ) => xW p.1 p.2) :=
  measurable_sphPt.comp continuous_mlpEval_joint.measurable

lemma normSq_xW (hn : 1 ≤ n) (W : MlpParam N mW n) (u : Fin N → ℝ) : normSq (xW W u) = 1 :=
  normSq_sphPt hn _

lemma continuous_kern : Continuous (fun p : (MlpParam n mF 1 × MlpParam n mA n ×
    MlpParam n mA n) × (Fin n → ℝ) × (Fin n → ℝ) => kern p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  unfold kern dotp
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  have c1 : Continuous (fun p : (MlpParam n mF 1 × MlpParam n mA n ×
      MlpParam n mA n) × (Fin n → ℝ) × (Fin n → ℝ) =>
      ((p.1.2.1, p.1.1.1, p.1.1.2.1), p.2.1)) :=
    ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
      ((continuous_fst.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_fst.comp (continuous_snd.comp (continuous_fst.comp continuous_fst))))).prodMk
      (continuous_fst.comp continuous_snd)
  have c2 : Continuous (fun p : (MlpParam n mF 1 × MlpParam n mA n ×
      MlpParam n mA n) × (Fin n → ℝ) × (Fin n → ℝ) =>
      ((p.1.2.2, p.1.1.1, p.1.1.2.1), p.2.2)) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk
      ((continuous_fst.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_fst.comp (continuous_snd.comp (continuous_fst.comp continuous_fst))))).prodMk
      (continuous_snd.comp continuous_snd)
  exact ((continuous_hidF_all i).comp c1).mul ((continuous_hidF_all i).comp c2)

lemma measurable_kern_comp {Ω : Type*} [MeasurableSpace Ω] {fF : Ω → MlpParam n mF 1}
    {fA fA' : Ω → MlpParam n mA n} {fx fx' : Ω → (Fin n → ℝ)} (hF : Measurable fF)
    (hA : Measurable fA) (hA' : Measurable fA') (hx : Measurable fx) (hx' : Measurable fx') :
    Measurable (fun ω => kern (fF ω) (fA ω) (fA' ω) (fx ω) (fx' ω)) :=
  Measurable.comp (g := fun p : (MlpParam n mF 1 × MlpParam n mA n ×
      MlpParam n mA n) × (Fin n → ℝ) × (Fin n → ℝ) => kern p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2)
    (f := fun ω => ((fF ω, fA ω, fA' ω), (fx ω, fx' ω)))
    continuous_kern.measurable ((hF.prodMk (hA.prodMk hA')).prodMk (hx.prodMk hx'))

lemma measurable_xW_comp {Ω : Type*} [MeasurableSpace Ω] {fW : Ω → MlpParam N mW n}
    {fu : Ω → (Fin N → ℝ)} (hW : Measurable fW) (hu : Measurable fu) :
    Measurable (fun ω => xW (fW ω) (fu ω)) :=
  Measurable.comp (g := fun p : MlpParam N mW n × (Fin N → ℝ) => xW p.1 p.2)
    (f := fun ω => (fW ω, fu ω)) measurable_xW (hW.prodMk hu)

section proj

variable {U W' A' F' : Type*} [MeasurableSpace U] [MeasurableSpace W'] [MeasurableSpace A']
  [MeasurableSpace F']

lemma meas_pW : Measurable (fun ω : (U × U) × W' × A' × A' × F' => ω.2.1) :=
  measurable_fst.comp measurable_snd
lemma meas_pu1 : Measurable (fun ω : (U × U) × W' × A' × A' × F' => ω.1.1) :=
  measurable_fst.comp measurable_fst
lemma meas_pu2 : Measurable (fun ω : (U × U) × W' × A' × A' × F' => ω.1.2) :=
  measurable_snd.comp measurable_fst
lemma meas_pA1 : Measurable (fun ω : (U × U) × W' × A' × A' × F' => ω.2.2.1) :=
  measurable_fst.comp (measurable_snd.comp measurable_snd)
lemma meas_pA2 : Measurable (fun ω : (U × U) × W' × A' × A' × F' => ω.2.2.2.1) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
lemma meas_pF : Measurable (fun ω : (U × U) × W' × A' × A' × F' => ω.2.2.2.2) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
lemma meas_pA (b : Bool) : Measurable (fun ω : (U × U) × W' × A' × A' × F' =>
    (bif b then ω.2.2.2.1 else ω.2.2.1)) := by
  cases b
  · exact meas_pA1
  · exact meas_pA2
lemma meas_pu (b : Bool) : Measurable (fun ω : (U × U) × W' × A' × A' × F' =>
    (bif b then ω.1.1 else ω.1.2)) := by
  cases b
  · exact meas_pu2
  · exact meas_pu1

end proj

lemma measurable_kgen (pa pa' dg : Bool) :
    Measurable (kgen (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) pa pa' dg) :=
  measurable_kern_comp meas_pF (meas_pA pa) (meas_pA pa')
    (measurable_xW_comp meas_pW meas_pu1) (measurable_xW_comp meas_pW (meas_pu dg))

/-! ## Integrability -/

lemma frob_integrable (a b : ℕ) (v : ℝ) :
    Integrable (frob : Matrix (Fin a) (Fin b) ℝ → ℝ) (gaussMat a b v) :=
  integrable_of_sq continuous_frob.measurable frob_nonneg (frob_sq_integrable a b v)

/-- `Φ(F) = ‖F₂‖²‖F₁‖²` and `Ψ(A) = ‖A₃‖²‖A₂‖²‖A₁‖²` (squared Frobenius norms). -/
def frF (F : MlpParam n mF 1) : ℝ := frob F.1 * frob F.2.1
def frA' (A : MlpParam n mA n) : ℝ := frob A.1 * (frob A.2.1 * frob A.2.2)

lemma frF_nonneg (F : MlpParam n mF 1) : 0 ≤ frF F :=
  mul_nonneg (frob_nonneg _) (frob_nonneg _)

lemma frA'_nonneg (A : MlpParam n mA n) : 0 ≤ frA' A :=
  mul_nonneg (frob_nonneg _) (mul_nonneg (frob_nonneg _) (frob_nonneg _))

lemma frF_integrable : Integrable (frF (n := n) (mF := mF)) (mlpGauss n mF 1) := by
  unfold mlpGauss
  exact (frob_integrable _ _ _).mul_prod ((frob_integrable _ _ _).comp_fst _)

lemma frA'_integrable : Integrable (frA' (n := n) (mA := mA)) (mlpGauss n mA n) := by
  unfold mlpGauss
  exact (frob_integrable _ _ _).mul_prod ((frob_integrable _ _ _).mul_prod (frob_integrable _ _ _))

lemma normSq_hidF_le (F : MlpParam n mF 1) (A : MlpParam n mA n) {x : Fin n → ℝ}
    (hx : normSq x = 1) : normSq (hidF F.1 F.2.1 A x) ≤ frF F * frA' A := by
  have h2 := normSq_hid2_le F.1 F.2.1 (mlpEval A x)
  have h3 := normSq_mlpEval_le A x
  rw [hx, mul_one] at h3
  have := frob_nonneg F.1; have := frob_nonneg F.2.1
  have := frob_nonneg A.1; have := frob_nonneg A.2.1; have := frob_nonneg A.2.2
  unfold hidF frF frA'
  calc _ ≤ frob F.2.1 * (frob F.1 * normSq (mlpEval A x)) := h2
    _ ≤ frob F.2.1 * (frob F.1 * (frob A.2.2 * (frob A.2.1 * (frob A.1 * 1)))) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity))
          (by positivity)
    _ = _ := by ring

/-- For unit vectors: `|kern F A A′ x x′| ≤ (2/m_F)·Φ(F)·(Ψ(A) + Ψ(A′))`. -/
lemma abs_kern_le (F : MlpParam n mF 1) (A A' : MlpParam n mA n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    |kern F A A' x x'| ≤ 2 / (mF : ℝ) * (frF F * (frA' A + frA' A')) := by
  unfold kern
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (mF : ℝ))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc _ ≤ normSq (hidF F.1 F.2.1 A x) + normSq (hidF F.1 F.2.1 A' x') := abs_dotp_le _ _
    _ ≤ frF F * frA' A + frF F * frA' A' :=
        add_le_add (normSq_hidF_le F A hx) (normSq_hidF_le F A' hx')
    _ = _ := by ring

/-- The bound, as a function of `(A, (A′, F))`. -/
noncomputable def bndAAF (mF : ℕ) (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) : ℝ :=
  2 / (mF : ℝ) * (frF p.2.2 * (frA' p.1 + frA' p.2.1))

lemma bndAAF_integrable : Integrable (bndAAF (n := n) (mA := mA) mF)
    ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) := by
  have h1 : Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      frA' p.1 * frF p.2.2) ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) :=
    frA'_integrable.mul_prod (frF_integrable.comp_snd _)
  have h2 : Integrable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
      frA' p.2.1 * frF p.2.2) ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) :=
    (frA'_integrable.mul_prod frF_integrable).comp_snd _
  have e : (bndAAF (n := n) (mA := mA) mF) = fun p => 2 / (mF : ℝ) *
      (frA' p.1 * frF p.2.2 + frA' p.2.1 * frF p.2.2) := by
    funext p; unfold bndAAF; ring
  rw [e]
  exact (h1.add h2).const_mul _

lemma abs_kgen_le (hn : 1 ≤ n) (pa pa' dg : Bool)
    (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) :
    |kgen pa pa' dg ω| ≤ 2 * bndAAF mF ω.2.2 := by
  unfold kgen
  refine (abs_kern_le _ _ _ (normSq_xW hn _ _) (normSq_xW hn _ _)).trans ?_
  unfold bndAAF
  have h1 := frA'_nonneg ω.2.2.1
  have h2 := frA'_nonneg ω.2.2.2.1
  have h3 := frF_nonneg ω.2.2.2.2
  have h4 : (0 : ℝ) ≤ 2 / (mF : ℝ) := by positivity
  have key : frF ω.2.2.2.2 * ((bif pa then frA' ω.2.2.2.1 else frA' ω.2.2.1) +
      (bif pa' then frA' ω.2.2.2.1 else frA' ω.2.2.1)) ≤
      2 * (frF ω.2.2.2.2 * (frA' ω.2.2.1 + frA' ω.2.2.2.1)) := by
    cases pa <;> cases pa' <;> simp only [Bool.cond_true, Bool.cond_false] <;> nlinarith
  have e : ∀ b : Bool, frA' (bif b then ω.2.2.2.1 else ω.2.2.1) =
      (bif b then frA' ω.2.2.2.1 else frA' ω.2.2.1) := by
    intro b; cases b <;> rfl
  rw [e, e]
  calc _ ≤ 2 / (mF : ℝ) * (2 * (frF ω.2.2.2.2 * (frA' ω.2.2.1 + frA' ω.2.2.2.1))) :=
        mul_le_mul_of_nonneg_left key h4
    _ = _ := by ring

/-- Every one of the five integrands is integrable under `lawU2 ⊗ lawR`. -/
theorem kgen_integrable (hn : 1 ≤ n) (hN : 1 ≤ N) (pa pa' dg : Bool) :
    Integrable (kgen (mW := mW) (mA := mA) (mF := mF) pa pa' dg)
      ((lawU2 N).prod (lawR N mW n mA mF)) := by
  have := uniformSphere_isProbability N hN
  have hb : Integrable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      2 * bndAAF mF ω.2.2) ((lawU2 N).prod (lawR N mW n mA mF)) := by
    unfold lawR lawU2
    exact (((bndAAF_integrable.comp_snd _).const_mul 2).comp_snd _)
  exact Integrable.mono' hb (measurable_kgen pa pa' dg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => abs_kgen_le hn pa pa' dg ω)

end BstLean.Part132

open BstLean.Part132 in
#print axioms lawR_map
open BstLean.Part132 in
#print axioms kgen_integrable
