import BstLean.Part153EN
import BstLean.Part153Norms2
import BstLean.Part153PP
import BstLean.Part153SJ
import BstLean.Part153Lp
import BstLean.Part150Bin

/-!
# Part 153: the `A`-stage events assembled in one event of `(A₁, A₂)`

Paper source: `proofs/option-n/theorem5-13-events-final.tex` (the event table and the union
bound) and `theorem5-01-statement-notation.tex` ("The order of the random variables").

* `prod_real_le_of_fibre`, `prod_real_fst`: the two-stage union bound for a product measure.
* `measurable_lpNorm_param`, `measurable_N2_joint`, `measurable_N1`, `measurable_int_N2`,
  `measurable_Pb_joint`, `measurable_int_Pb`, `measurable_gO_A1`, `measurable_opN_A1`,
  `measurable_sqrt_GamS`, `measurable_Xi4`: measurability in the weights.
* `BadE`, `Bad1`, `BadBe`, `BadN22`, `BadN24`, `Bad2`, `GoodA`: the bad sets and the `A`-stage
  event, at the level `L_c = 12`.
* **`measurableSet_GoodA`**, **`GoodA_prob`**: the event is measurable and
  `Pr(GoodAᶜ) ≤ exp(−n/2) + 7·exp(−12) + p_sc + p_Ξ`.
* `GoodA_op`, `GoodA_energy`, `GoodA_norms`, `GoodA_be`, `GoodA_EN_iii`, `GoodA_Xi`: the
  deterministic bounds on the event.
* `GoodAw`, `GoodAw_prob`, `GoodAw_Xi`: the event with the weak Jacobian bound of Lemma PP
  (`P = 8`, `M = 10`, `p_Ξ = 1/1000`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open scoped ENNReal NNReal

/-! ## 1. The two-stage union bound -/

section twoStage

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ₁ : Measure X} {μ₂ : Measure Y}
  [IsProbabilityMeasure μ₂]

/-- **The two-stage bound**: if every fibre `{y | (x, y) ∈ S}` of a measurable set `S` has
`μ₂`-probability at most `q`, then `S` has `μ₁ ⊗ μ₂`-probability at most `q`. -/
theorem prod_real_le_of_fibre [IsProbabilityMeasure μ₁] {S : Set (X × Y)}
    (hS : MeasurableSet S) {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ x, μ₂.real {y | (x, y) ∈ S} ≤ q) : (μ₁.prod μ₂).real S ≤ q := by
  rw [measureReal_def, Measure.prod_apply hS]
  refine ENNReal.toReal_le_of_le_ofReal hq ?_
  calc ∫⁻ x, μ₂ (Prod.mk x ⁻¹' S) ∂μ₁ ≤ ∫⁻ _, ENNReal.ofReal q ∂μ₁ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ₂ (Prod.mk x ⁻¹' S))]
        exact ENNReal.ofReal_le_ofReal (h x)
    _ = ENNReal.ofReal q := by simp

/-- An event of the first variable has the same probability under the product measure. -/
theorem prod_real_fst (S₁ : Set X) : (μ₁.prod μ₂).real {p | p.1 ∈ S₁} = μ₁.real S₁ := by
  have e : {p : X × Y | p.1 ∈ S₁} = S₁ ×ˢ (univ : Set Y) := by
    ext p
    simp
  rw [e, measureReal_def, Measure.prod_prod, measure_univ, mul_one, measureReal_def]

end twoStage

/-! ## 2. Measurability in the weights -/

/-- `θ ↦ ‖G θ‖_{L^k(μ)}` is measurable for a jointly measurable `G` with `G θ ∈ L^k(μ)`. -/
lemma measurable_lpNorm_param {Θ Ξ : Type*} [MeasurableSpace Θ] [MeasurableSpace Ξ]
    {μ : Measure Ξ} [SFinite μ] {k : ℕ} (hk : k ≠ 0) {G : Θ → Ξ → ℝ}
    (hG : Measurable (Function.uncurry G)) (hmem : ∀ θ, MemLp (G θ) (k : ℝ≥0∞) μ) :
    Measurable (fun θ => lpNorm (G θ) (k : ℝ≥0∞) μ) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hGm : Measurable fun p : Θ × Ξ => ENNReal.ofReal (|G p.1 p.2| ^ k) :=
    ((continuous_abs.measurable.comp hG).pow_const k).ennreal_ofReal
  have hpow : ∀ θ, ENNReal.ofReal (lpNorm (G θ) (k : ℝ≥0∞) μ) ^ k =
      ∫⁻ ξ, ENNReal.ofReal (|G θ ξ| ^ k) ∂μ := fun θ => by
    rw [ofReal_lpNorm (hmem θ), eLpNorm_nat_pow hk (hmem θ).aestronglyMeasurable]
  have e : (fun θ => lpNorm (G θ) (k : ℝ≥0∞) μ) =
      fun θ => ((∫⁻ ξ, ENNReal.ofReal (|G θ ξ| ^ k) ∂μ) ^ (1 / (k : ℝ))).toReal := by
    funext θ
    rw [← hpow θ, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hk',
      ENNReal.rpow_one, ENNReal.toReal_ofReal lpNorm_nonneg]
  rw [e]
  exact ((hGm.lintegral_prod_right').pow_const _).ennreal_toReal

section meas

variable {n : ℕ}

/-- `√ω₂` is jointly measurable in `((A₁, A₂), ξ)`. -/
lemma measurable_sq2_joint3 (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) ×
      (Fin n → ℝ) => sq2 q.1.1 q.1.2 c τ q.2) := by
  have hc1 : Continuous (fun q : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin n → ℝ) => q.1 *ᵥ q.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  have hc2 : Continuous (fun q : Matrix (Fin (mA n)) (Fin (mA n)) ℝ × (Fin (mA n) → ℝ) =>
      q.1 *ᵥ q.2) := Continuous.matrix_mulVec continuous_fst continuous_snd
  have hx : Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) => sphPt (c + τ • q.2)) :=
    (measurable_x c τ).comp measurable_snd
  have h1 : Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      reluV (q.1.1 *ᵥ sphPt (c + τ • q.2))) :=
    measurable_reluV.comp (hc1.measurable.comp ((measurable_fst.comp measurable_fst).prodMk hx))
  have h2 : Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      q.1.2 *ᵥ reluV (q.1.1 *ᵥ sphPt (c + τ • q.2))) :=
    hc2.measurable.comp ((measurable_snd.comp measurable_fst).prodMk h1)
  exact ((continuous_normSq.measurable.comp (measurable_reluV.comp h2)).sqrt).div_const _

/-- `(A₁, A₂) ↦ N_{2k}` is measurable. -/
lemma measurable_N2_joint (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      N2 k θ.1 θ.2 c τ) :=
  measurable_lpNorm_param (μ := stdGauss (Fin n)) (by omega)
    (G := fun (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
      (ξ : Fin n → ℝ) => sq2 θ.1 θ.2 c τ ξ - 1)
    ((measurable_sq2_joint3 c τ).sub_const 1) (fun θ => memLp_sq2_sub hn θ.1 θ.2 c τ _)

/-- `A₁ ↦ N_{1k}` is measurable. -/
lemma measurable_N1 (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => N1 k A₁ c τ) :=
  measurable_lpNorm_param (μ := stdGauss (Fin n)) (by omega)
    (G := fun (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (ξ : Fin n → ℝ) => sq1 A₁ c τ ξ - 1)
    ((measurable_sq1_joint c τ).sub_const 1) (fun A₁ => memLp_sq1_sub hn A₁ c τ _)

/-- `A₁ ↦ E[N_{2k} | A₁]` is measurable. -/
lemma measurable_int_N2 (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      ∫ A₂, N2 k A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) :=
  ((measurable_N2_joint hn hk c τ).stronglyMeasurable.integral_prod_right'
    (ν := gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)))).measurable

/-- `(A₁, A₂) ↦ 𝖯_b` is measurable. -/
lemma measurable_Pb_joint {m : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      Pb θ.1 c τ θ.2) := by
  have hf : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      (((c, τ), θ) : ((Fin n → ℝ) × ℝ) × BstLean.Part136.HidParam n m)) :=
    measurable_const.prodMk measurable_id
  have hb : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      bO θ.1 θ.2 c τ) := by
    have h := (measurable_bO (n := n) (m := m)).comp hf
    exact h
  have h1 : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      √(normSq (bO θ.1 θ.2 c τ))) := (continuous_normSq.measurable.comp hb).sqrt
  exact h1.const_mul _

/-- `A₁ ↦ E[𝖯_b | A₁]` is measurable. -/
lemma measurable_int_Pb {m : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat m m (2 / (m : ℝ))) :=
  ((measurable_Pb_joint (m := m) c τ).stronglyMeasurable.integral_prod_right'
    (ν := gaussMat m m (2 / (m : ℝ)))).measurable

/-- `A₁ ↦ gO A₁ c τ` (the energy in the row form) is measurable. -/
lemma measurable_gO_A1 {m : ℕ} (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => gO A₁ c τ) := by
  have e : (fun A₁ : Matrix (Fin m) (Fin n) ℝ => gO A₁ c τ) = fun A₁ => GamS A₁ c τ :=
    funext fun A => (GamS_eq_gO hm A c τ).symm
  rw [e]
  exact measurable_GamS c τ

/-- `A₁ ↦ ‖A₁‖_op` is measurable. -/
lemma measurable_opN_A1 {p q : ℕ} : Measurable (opN : Matrix (Fin p) (Fin q) ℝ → ℝ) :=
  opN_continuous.measurable

/-- `A₁ ↦ √Γ` is measurable. -/
lemma measurable_sqrt_GamS {m : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => √(GamS A₁ c τ)) :=
  (measurable_GamS c τ).sqrt

/-- `(A₁, A₂) ↦ Ξ₄` is measurable. -/
lemma measurable_Xi4 {m : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      Xi4 θ.1 θ.2 c τ) := by
  have hF : Measurable (fun q : (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ) ×
      (Fin n → ℝ) => opN (jacT q.1.1 q.1.2 (sphPt (c + τ • q.2))) ^ 4 *
        (normSq (c + τ • q.2))⁻¹ ^ 2) :=
    ((measurable_opN_jacT_sph c τ).pow_const 4).mul
      (((BstLean.Part130.measurable_normSq.comp
        (measurable_const.add (measurable_snd.const_smul τ))).inv).pow_const 2)
  unfold Xi4
  exact ((hF.stronglyMeasurable.integral_prod_right'
    (ν := stdGauss (Fin n))).measurable.sqrt).const_mul _

end meas

/-! ## 3. The `A`-stage event -/

section event

variable {n : ℕ}

/-- The complement of `E_e` at `L_c = 12` (the set of `Ee_prob` with `v = 2/n`, `m = n²`). -/
def BadE (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | √(2 * 12 * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2)) <
    |√(GamS A c τ) - ∫ A, √(GamS A c τ) ∂gaussMat (mA n) n (2 / (n : ℝ))|}

/-- The bad set of `A₁`: the complements of `E_op`, `E_e`, `E_{N12}`, `E_{N14}`, and a set `Bsc`
(the complement of `E_sc`). -/
def Bad1 (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) (Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  (Eop n)ᶜ ∪ BadE n c τ ∪ {A₁ | N12bar n 12 < N1 2 A₁ c τ} ∪ {A₁ | N14bar n 12 < N1 4 A₁ c τ} ∪
    Bsc

/-- The complement of `E_be` at `L_c = 12`, for a fixed `A₁` (the set of `Ebe_prob`). -/
def BadBe (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) :
    Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {A₂ | ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
    √(2 * 12 * (2 / ((mA n : ℕ) : ℝ)) * gO A₁ c τ) < Pb A₁ c τ A₂}

/-- The complement of `E_{N22}` at `L_c = 12`, for a fixed `A₁` (the set of `N22_event`). -/
def BadN22 (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) :
    Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {A₂ | ∫ A₂, N2 2 A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
    2 * √12 * (1 + N1 2 A₁ c τ) / n < N2 2 A₁ A₂ c τ}

/-- The complement of `E_{N24}` at `L_c = 12`, for a fixed `A₁` (the set of `N24_event`). -/
def BadN24 (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) :
    Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {A₂ | ∫ A₂, N2 4 A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
    √(2 * 12) * (√(2 / ((mA n : ℕ) : ℝ)) * opN A₁ / √(n : ℝ)) < N2 4 A₁ A₂ c τ}

/-- The bad set of `A₂`, for a fixed `A₁`. -/
def Bad2 (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) :
    Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  BadBe n c τ A₁ ∪ BadN22 n c τ A₁ ∪ BadN24 n c τ A₁

/-- **The `A`-stage event**, a set of `θ = (A₁, A₂)`. `BXi` is a bad set of `θ` (the complement
of `E_{Pp}`). -/
def GoodA (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) (Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ))
    (BXi : Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {θ | θ.1 ∉ Bad1 n c τ Bsc ∧ θ.2 ∉ Bad2 n c τ θ.1 ∧ θ ∉ BXi}

lemma measurableSet_Eop (n : ℕ) : MeasurableSet (Eop n) :=
  measurableSet_le measurable_opN_A1 measurable_const

lemma measurableSet_BadE (c : Fin n → ℝ) (τ : ℝ) : MeasurableSet (BadE n c τ) :=
  measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((measurable_sqrt_GamS c τ).sub_const _))

lemma measurableSet_Bad1 (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    {Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)} (hBsc : MeasurableSet Bsc) :
    MeasurableSet (Bad1 n c τ Bsc) :=
  (((((measurableSet_Eop n).compl).union (measurableSet_BadE c τ)).union
    (measurableSet_lt measurable_const (measurable_N1 hn (by norm_num) c τ))).union
    (measurableSet_lt measurable_const (measurable_N1 hn (by norm_num) c τ))).union hBsc

/-- The set `{(A₁, A₂) | A₂ ∈ Bad2 A₁}` is measurable. -/
lemma measurableSet_Bad2 (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    MeasurableSet {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      θ.2 ∈ Bad2 n c τ θ.1} := by
  have h1 : MeasurableSet {θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ | θ.2 ∈ BadBe n c τ θ.1} :=
    measurableSet_lt (((measurable_int_Pb c τ).comp measurable_fst).add
      ((((measurable_gO_A1 (one_le_mA hn) c τ).comp measurable_fst).const_mul _).sqrt))
      (measurable_Pb_joint c τ)
  have h2 : MeasurableSet {θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ | θ.2 ∈ BadN22 n c τ θ.1} :=
    measurableSet_lt (((measurable_int_N2 hn (by norm_num) c τ).comp measurable_fst).add
      (((((measurable_N1 hn (by norm_num) c τ).comp measurable_fst).const_add 1).const_mul
        _).div_const _))
      (measurable_N2_joint hn (by norm_num) c τ)
  have h3 : MeasurableSet {θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ | θ.2 ∈ BadN24 n c τ θ.1} :=
    measurableSet_lt (((measurable_int_N2 hn (by norm_num) c τ).comp measurable_fst).add
      ((((measurable_opN_A1.comp measurable_fst).const_mul _).div_const _).const_mul _))
      (measurable_N2_joint hn (by norm_num) c τ)
  exact (h1.union h2).union h3

/-- **The `A`-stage event is measurable.** -/
theorem measurableSet_GoodA (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    {Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)} (hBsc : MeasurableSet Bsc)
    {BXi : Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)}
    (hBXi : MeasurableSet BXi) : MeasurableSet (GoodA n c τ Bsc BXi) :=
  ((measurable_fst (measurableSet_Bad1 hn c τ hBsc)).compl).inter
    (((measurableSet_Bad2 hn c τ).compl).inter hBXi.compl)

/-- The charge of the bad set of `A₁`. -/
theorem Bad1_prob (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    {Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)} {psc : ℝ}
    (hpsc : (gaussMat (mA n) n (2 / (n : ℝ))).real Bsc ≤ psc) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (Bad1 n c τ Bsc) ≤
      Real.exp (-(n : ℝ) / 2) + 4 * Real.exp (-12) + psc := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h12 : (0 : ℝ) ≤ 12 := by norm_num
  have hE : (gaussMat (mA n) n (2 / (n : ℝ))).real (BadE n c τ) ≤ 2 * Real.exp (-12) :=
    Ee_prob (m := mA n) c τ (div_pos two_pos hn0) h12
  have h1 := measureReal_union_le (μ := gaussMat (mA n) n (2 / (n : ℝ)))
    ((Eop n)ᶜ ∪ BadE n c τ ∪ {A₁ | N12bar n 12 < N1 2 A₁ c τ} ∪
      {A₁ | N14bar n 12 < N1 4 A₁ c τ}) Bsc
  have h2 := measureReal_union_le (μ := gaussMat (mA n) n (2 / (n : ℝ)))
    ((Eop n)ᶜ ∪ BadE n c τ ∪ {A₁ | N12bar n 12 < N1 2 A₁ c τ})
    {A₁ | N14bar n 12 < N1 4 A₁ c τ}
  have h3 := measureReal_union_le (μ := gaussMat (mA n) n (2 / (n : ℝ)))
    ((Eop n)ᶜ ∪ BadE n c τ) {A₁ | N12bar n 12 < N1 2 A₁ c τ}
  have h4 := measureReal_union_le (μ := gaussMat (mA n) n (2 / (n : ℝ))) (Eop n)ᶜ (BadE n c τ)
  have h5 := Eop_prob hn
  have h6 := N12_event hn c τ h12
  have h7 := N14_event hn c τ h12
  unfold Bad1
  linarith

/-- The charge of the bad set of `A₂`, for each fixed `A₁`. -/
theorem Bad2_prob (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) :
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))).real (Bad2 n c τ A₁) ≤
      3 * Real.exp (-12) := by
  have h12 : (0 : ℝ) ≤ 12 := by norm_num
  have hb : (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))).real (BadBe n c τ A₁) ≤
      Real.exp (-12) := Ebe_prob (one_le_mA hn) A₁ c τ h12
  have h22 : (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))).real (BadN22 n c τ A₁) ≤
      Real.exp (-12) := N22_event hn A₁ c τ h12
  have h24 : (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))).real (BadN24 n c τ A₁) ≤
      Real.exp (-12) := N24_event hn A₁ c τ h12
  have h1 := measureReal_union_le (μ := gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)))
    (BadBe n c τ A₁ ∪ BadN22 n c τ A₁) (BadN24 n c τ A₁)
  have h2 := measureReal_union_le (μ := gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)))
    (BadBe n c τ A₁) (BadN22 n c τ A₁)
  unfold Bad2
  linarith

/-- **The union bound for the `A`-stage event**:
`Pr(GoodAᶜ) ≤ exp(−n/2) + 7·exp(−12) + p_sc + p_Ξ`. Charges: `E_op`: `exp(−n/2)`; `E_e`:
`2e^{−12}`; `E_{N12}`, `E_{N14}`: `2e^{−12}`; `E_be`, `E_{N22}`, `E_{N24}`: `3e^{−12}` (each one
for a fixed `A₁`). -/
theorem GoodA_prob (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    {Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)} {psc : ℝ}
    (hpsc : (gaussMat (mA n) n (2 / (n : ℝ))).real Bsc ≤ psc)
    {BXi : Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)} {pXi : ℝ}
    (hpXi : (nuA n).real BXi ≤ pXi) :
    (nuA n).real (GoodA n c τ Bsc BXi)ᶜ ≤
      Real.exp (-(n : ℝ) / 2) + 7 * Real.exp (-12) + psc + pXi := by
  have hsub : (GoodA n c τ Bsc BXi)ᶜ ⊆
      ({θ | θ.1 ∈ Bad1 n c τ Bsc} ∪ {θ | θ.2 ∈ Bad2 n c τ θ.1}) ∪ BXi := by
    intro θ hθ
    by_contra h
    apply hθ
    refine ⟨fun h1 => h (Or.inl (Or.inl h1)), fun h2 => h (Or.inl (Or.inr h2)),
      fun h3 => h (Or.inr h3)⟩
  have h1 := measureReal_mono (μ := nuA n) hsub
  have h2 := measureReal_union_le (μ := nuA n)
    ({θ | θ.1 ∈ Bad1 n c τ Bsc} ∪ {θ | θ.2 ∈ Bad2 n c τ θ.1}) BXi
  have h3 := measureReal_union_le (μ := nuA n)
    {θ | θ.1 ∈ Bad1 n c τ Bsc} {θ | θ.2 ∈ Bad2 n c τ θ.1}
  have h4 : (nuA n).real {θ | θ.1 ∈ Bad1 n c τ Bsc} =
      (gaussMat (mA n) n (2 / (n : ℝ))).real (Bad1 n c τ Bsc) := prod_real_fst _
  have h5 : (nuA n).real {θ | θ.2 ∈ Bad2 n c τ θ.1} ≤ 3 * Real.exp (-12) :=
    prod_real_le_of_fibre (measurableSet_Bad2 hn c τ) (by positivity)
      (fun A₁ => Bad2_prob hn c τ A₁)
  have h6 := Bad1_prob hn c τ hpsc
  linarith

/-! ## 4. The deterministic bounds on the event -/

variable {c : Fin n → ℝ} {τ : ℝ} {Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)}
  {BXi : Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)}
  {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}

/-- The membership in `GoodA`, as a list of conditions. -/
lemma GoodA_unpack (h : (A₁, A₂) ∈ GoodA n c τ Bsc BXi) :
    A₁ ∈ Eop n ∧
    |√(GamS A₁ c τ) - ∫ A, √(GamS A c τ) ∂gaussMat (mA n) n (2 / (n : ℝ))| ≤
      √(2 * 12 * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2)) ∧
    N1 2 A₁ c τ ≤ N12bar n 12 ∧ N1 4 A₁ c τ ≤ N14bar n 12 ∧ A₁ ∉ Bsc ∧
    A₂ ∉ BadBe n c τ A₁ ∧ A₂ ∉ BadN22 n c τ A₁ ∧ A₂ ∉ BadN24 n c τ A₁ ∧ (A₁, A₂) ∉ BXi := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨not_not.mp fun h => h1 (Or.inl (Or.inl (Or.inl (Or.inl h)))),
    not_lt.mp fun h => h1 (Or.inl (Or.inl (Or.inl (Or.inr h)))),
    not_lt.mp fun h => h1 (Or.inl (Or.inl (Or.inr h))),
    not_lt.mp fun h => h1 (Or.inl (Or.inr h)),
    fun h => h1 (Or.inr h),
    fun h => h2 (Or.inl (Or.inl h)), fun h => h2 (Or.inl (Or.inr h)), fun h => h2 (Or.inr h), h3⟩

/-- **(a)** On `GoodA`: `A₁ ∈ E_op`, `t_A‖A₁‖_op² ≤ 4w_n/n`, `Γ ≤ (4w_n/n)·ρ²`. -/
theorem GoodA_op (hn : 1 ≤ n) (h : (A₁, A₂) ∈ GoodA n c τ Bsc BXi) :
    A₁ ∈ Eop n ∧ 2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2 ≤ 4 * wn n / n ∧
    GamS A₁ c τ ≤ 4 * wn n / n * (normSq c + (n : ℝ) * τ ^ 2) :=
  ⟨(GoodA_unpack h).1, Eop_sq hn (GoodA_unpack h).1, GamS_le_Eop hn (GoodA_unpack h).1 c τ⟩

/-- **(b)** On `GoodA`, `n ≥ 8192`: `|Γ − γ_Aρ²| ≤ (11/1000)·γ_Aρ²`. -/
theorem GoodA_energy (hn : 8192 ≤ n) (h : (A₁, A₂) ∈ GoodA n c τ Bsc BXi) :
    |GamS A₁ c τ - 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)| ≤
      11 / 1000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) :=
  Ee_delta_12 hn c τ (GoodA_unpack h).2.1

/-- **(c)** On `GoodA`: the bounds on `N₁₂`, `N₁₄`, `N₂₂`, `N₂₄`, and
`E_x|ω₂ − 1| ≤ N̄₂₂(2 + N̄₂₂)`. -/
theorem GoodA_norms (hn : 1 ≤ n) (h : (A₁, A₂) ∈ GoodA n c τ Bsc BXi) :
    N1 2 A₁ c τ ≤ N12bar n 12 ∧ N1 4 A₁ c τ ≤ N14bar n 12 ∧
    N2 2 A₁ A₂ c τ ≤ N22bar n 12 ∧ N2 4 A₁ A₂ c τ ≤ N24bar n 12 ∧
    ∫ ξ, |sq2 A₁ A₂ c τ ξ ^ 2 - 1| ∂stdGauss (Fin n) ≤ N22bar n 12 * (2 + N22bar n 12) := by
  obtain ⟨hop, -, h12, h14, -, -, h22, h24, -⟩ := GoodA_unpack h
  have b22 : N2 2 A₁ A₂ c τ ≤ N22bar n 12 := N22_le_bar hn h12 h22
  have b24 : N2 4 A₁ A₂ c τ ≤ N24bar n 12 := N24_le_bar hn (by norm_num) hop h14 h24
  refine ⟨h12, h14, b22, b24, (int_abs_sq2_sq_sub_one_le hn A₁ A₂ c τ).trans ?_⟩
  have h0 := N2_nonneg 2 A₁ A₂ c τ
  nlinarith

/-- **(d)** On `GoodA`: `𝖯_b ≤ E[𝖯_b | A₁] + √(2·12·t_A·Γ)`. -/
theorem GoodA_be (h : (A₁, A₂) ∈ GoodA n c τ Bsc BXi) :
    Pb A₁ c τ A₂ ≤ ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
      √(2 * 12 * (2 / ((mA n : ℕ) : ℝ)) * gO A₁ c τ) :=
  not_lt.mp (GoodA_unpack h).2.2.2.2.2.1

/-- **(d)** On `GoodA`, `n ≥ 8192`, `τ > 0`: if `Bsc` contains the set `{s_h² < c_s τ²}` and
`θ_lo ≤ nτ²/ρ²`, then `e_b° ≤ 1 + 2δ_e − (1 − 1/π)(c_s/2)θ_lo` (the conclusion of `EN_iii`). -/
theorem GoodA_EN_iii (hn : 8192 ≤ n) (hτ : 0 < τ) {cs θlo : ℝ} (hcs : 0 ≤ cs)
    (hBsc : {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < cs * τ ^ 2} ⊆ Bsc)
    (hθ : θlo ≤ (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))
    (h : (A₁, A₂) ∈ GoodA n c τ Bsc BXi) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤
      1 + 2 * (11 / 1000) - (1 - 1 / π) * (cs / 2) * θlo := by
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hρ : 0 < normSq c + (n : ℝ) * τ ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg c) (by positivity)
  have hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ :=
    not_lt.mp fun hlt => (GoodA_unpack h).2.2.2.2.1 (hBsc hlt)
  exact EN_iii hn A₁ A₂ c τ hρ (GoodA_unpack h).2.1 hcs hsc hθ (GoodA_be h)

/-- **(e)** On `GoodA`, `n ≥ 6`, `τ > 0`: if `BXi` contains the set `{Ξ₄ > M·γ_A/n}`, then
`Ξ ≤ M·γ_A/n`; `t_A·Var_ξ⟨w, h₂(x)⟩ ≤ (M·γ_A/n)·|w|²` for every `w`; and
`Var_ξ φ(√t_A·h₂(x)) ≤ L_φ²·M·γ_A/n` for every Lipschitz `φ`. -/
theorem GoodA_Xi (hn : 6 ≤ n) (hτ : 0 < τ) {M : ℝ}
    (hBXi : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      M * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ⊆ BXi)
    (h : (A₁, A₂) ∈ GoodA n c τ Bsc BXi) :
    XiS A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n ∧
    (∀ w : Fin (mA n) → ℝ,
      2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
        ∫ ξ', w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
        M * (2 / (n : ℝ)) / n * normSq w) ∧
    (∀ (φ : (Fin (mA n) → ℝ) → ℝ) (Lφ : ℝ), 0 ≤ Lφ → EuLip φ Lφ →
      ∫ ξ, (φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
        ∫ ξ', φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ')))
          ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤ Lφ ^ 2 * (M * (2 / (n : ℝ)) / n)) := by
  have h4 : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n :=
    not_lt.mp fun hlt => (GoodA_unpack h).2.2.2.2.2.2.2.2 (hBXi hlt)
  have hX : XiS A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n := (XiS_le_Xi4 hn A₁ A₂ c hτ).trans h4
  refine ⟨hX, fun w => ?_, fun φ Lφ hL hφ => ?_⟩
  · exact (cov_hid2_le hn A₁ A₂ c hτ w).trans (mul_le_mul_of_nonneg_right hX (normSq_nonneg w))
  · exact (lemmaS_jac hn A₁ A₂ c hτ hL hφ).2.trans (mul_le_mul_of_nonneg_left hX (sq_nonneg _))

end event

/-! ## 5. The event with the weak Jacobian bound of Lemma PP (`P = 8`, `M = 10`) -/

section weak

variable {n : ℕ}

/-- `𝔪_8 = (2⁸·8!)^{1/16} ≤ 3`. -/
lemma gaussMomConst_eight_le : gaussMomConst 8 ≤ 3 := by
  have h := gaussMomConst_pow (P := 8) (by norm_num)
  have h0 := gaussMomConst_nonneg 8
  by_contra hlt
  have h3 : (3 : ℝ) < gaussMomConst 8 := not_le.mp hlt
  have h4 : (3 : ℝ) ^ (2 * 8) < gaussMomConst 8 ^ (2 * 8) :=
    pow_lt_pow_left₀ h3 (by norm_num) (by norm_num)
  rw [h] at h4
  norm_num [Nat.factorial] at h4

/-- The weak constant at `P = 8`: `j_W(n, 8) ≤ 2047/1000` for `n ≥ 8192`. -/
lemma jW_eight_le (hn : 8192 ≤ n) : jW n 8 ≤ 2047 / 1000 := by
  have hn0 : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hs : (90 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h1 : 1 / √(n : ℝ) ≤ 1 / 90 := one_div_le_one_div_of_le (by norm_num) hs
  have h2 : gaussMomConst 8 / n ≤ 3 / 8192 :=
    div_le_div₀ (by norm_num) gaussMomConst_eight_le (by norm_num) hn0
  have h3 : 0 ≤ 1 / √(n : ℝ) := by positivity
  have h4 : 0 ≤ gaussMomConst 8 / n := div_nonneg (gaussMomConst_nonneg 8) hnpos.le
  unfold jW
  nlinarith

/-- The charge of `Ξ₄ > 10·γ_A/n` with the weak constant of Lemma PP at `P = 8`: at most
`1/1000` for `n ≥ 8192`. -/
theorem Xi4_weak_prob (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {θ | 10 * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤ 1 / 1000 := by
  have hn0 : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have h := lemmaPP_Xi4_weak (P := 8) (by norm_num) (by omega) c hτ (M := 10) (by norm_num)
  refine h.trans ?_
  have hj := jW_eight_le hn
  have hj0 := jW_nonneg n 8
  have hd : (0 : ℝ) < ((n : ℝ) - 1 - 2 * ((8 : ℕ) : ℝ)) * 10 := by push_cast; linarith
  have hr0 : 0 ≤ jW n 8 ^ 2 * n / (((n : ℝ) - 1 - 2 * ((8 : ℕ) : ℝ)) * 10) :=
    div_nonneg (by positivity) hd.le
  have hr : jW n 8 ^ 2 * n / (((n : ℝ) - 1 - 2 * ((8 : ℕ) : ℝ)) * 10) ≤ 42 / 100 := by
    rw [div_le_iff₀ hd]
    push_cast
    have hj2 : jW n 8 ^ 2 ≤ (2047 / 1000) ^ 2 := pow_le_pow_left₀ hj0 hj 2
    nlinarith
  calc (jW n 8 ^ 2 * n / (((n : ℝ) - 1 - 2 * ((8 : ℕ) : ℝ)) * 10)) ^ 8
      ≤ (42 / 100 : ℝ) ^ 8 := pow_le_pow_left₀ hr0 hr 8
    _ ≤ 1 / 1000 := by norm_num

/-- **The `A`-stage event with the weak Jacobian bound**: `GoodA` with
`BXi = {Ξ₄ > 10·γ_A/n}`. -/
def GoodAw (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) (Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  GoodA n c τ Bsc {θ | 10 * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ}

theorem measurableSet_GoodAw (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    {Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)} (hBsc : MeasurableSet Bsc) :
    MeasurableSet (GoodAw n c τ Bsc) :=
  measurableSet_GoodA hn c τ hBsc (measurableSet_lt measurable_const (measurable_Xi4 c τ))

/-- **The union bound with the weak Jacobian bound**, `n ≥ 8192`, `τ > 0`:
`Pr(GoodAwᶜ) ≤ exp(−n/2) + 7·exp(−12) + p_sc + 1/1000`. -/
theorem GoodAw_prob (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)} {psc : ℝ}
    (hpsc : (gaussMat (mA n) n (2 / (n : ℝ))).real Bsc ≤ psc) :
    (nuA n).real (GoodAw n c τ Bsc)ᶜ ≤
      Real.exp (-(n : ℝ) / 2) + 7 * Real.exp (-12) + psc + 1 / 1000 :=
  GoodA_prob (by omega) c τ hpsc (Xi4_weak_prob hn c hτ)

/-- On `GoodAw`, `n ≥ 8192`, `τ > 0`: the bounds (e) with `M = 10`. -/
theorem GoodAw_Xi (hn : 8192 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {Bsc : Set (Matrix (Fin (mA n)) (Fin n) ℝ)}
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodAw n c τ Bsc) :
    XiS A₁ A₂ c τ ≤ 10 * (2 / (n : ℝ)) / n ∧
    (∀ w : Fin (mA n) → ℝ,
      2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
        ∫ ξ', w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
        10 * (2 / (n : ℝ)) / n * normSq w) ∧
    (∀ (φ : (Fin (mA n) → ℝ) → ℝ) (Lφ : ℝ), 0 ≤ Lφ → EuLip φ Lφ →
      ∫ ξ, (φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
        ∫ ξ', φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ')))
          ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤ Lφ ^ 2 * (10 * (2 / (n : ℝ)) / n)) :=
  GoodA_Xi (by omega) hτ (M := 10) (fun _ hθ => hθ) h

end weak

end BstLean.Part153

#print axioms BstLean.Part153.prod_real_le_of_fibre
#print axioms BstLean.Part153.prod_real_fst
#print axioms BstLean.Part153.measurable_N2_joint
#print axioms BstLean.Part153.measurable_N1
#print axioms BstLean.Part153.measurable_int_N2
#print axioms BstLean.Part153.measurable_Pb_joint
#print axioms BstLean.Part153.measurable_int_Pb
#print axioms BstLean.Part153.measurable_gO_A1
#print axioms BstLean.Part153.measurable_opN_A1
#print axioms BstLean.Part153.measurable_sqrt_GamS
#print axioms BstLean.Part153.measurable_Xi4
#print axioms BstLean.Part153.measurableSet_GoodA
#print axioms BstLean.Part153.GoodA_prob
#print axioms BstLean.Part153.GoodA_op
#print axioms BstLean.Part153.GoodA_energy
#print axioms BstLean.Part153.GoodA_norms
#print axioms BstLean.Part153.GoodA_be
#print axioms BstLean.Part153.GoodA_EN_iii
#print axioms BstLean.Part153.GoodA_Xi
#print axioms BstLean.Part153.Xi4_weak_prob
#print axioms BstLean.Part153.measurableSet_GoodAw
#print axioms BstLean.Part153.GoodAw_prob
#print axioms BstLean.Part153.GoodAw_Xi
