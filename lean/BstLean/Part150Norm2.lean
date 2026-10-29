import BstLean.Part150Norm
import BstLean.Part135Dir
import BstLean.Part131Block

/-!
# Part 150, item 5, a part: the paper's oracle first layer against the one of Part 149

For a FIXED first matrix `A₁`, a centre `c` and a scalar `τ > 0`: `y = c + τγ`, `γ` a standard
Gaussian vector of `ℝⁿ`, `ρ = rhoC c τ`. The paper's oracle first layer is `hO/ρ`, `gO/ρ²`,
`sO2/ρ²` (Gaussian means of the unnormalized input, `Part150CDefs`). The oracle first layer of
Part 149 is `b1`, `N2` (means over the normalized input `sphPt y`; `a1`, `errD1`, `Qk`).

* `stdGauss_lin_map`, `hO_eq_gauss`, `relu_sq_eq_gauss`, `gO_eq_gauss`: the projection identities.
* `kern_weighted`: the weighted kernel inequality.
* `e1N c τ A₁ = b1 − (1/ρ)·hO`; `e1N_eq : e1N_i = E[wN·a1_i]`.
* `N2_sub_gO`: `|N2 − (m/2)·gO/ρ²| ≤ √errD1·√VN`.
* `e1N_normSq_le`: `|e1N|² ≤ VN·√(Qk k) + k·(E[wN·|a1|])²`;
  `wnrm_sq_le`: `(E[wN·|a1|])² ≤ 2·VN·errD1/d + d·VN²/2`, `d = m/n`.
* `dotp_b1_e1N_le`: `|⟨b1, e1N⟩| ≤ √VN·√(Qk k) + k·|E[wN·|a1|]|·√N2`.
* `sMF_sq_sub_sO2`: `|(2/m)(N2 − |b1|²) − sO2/ρ²| ≤ (2/m)(√errD1·√VN + 2|⟨b1, e1N⟩| + |e1N|²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part134 BstLean.Part137 BstLean.Part141 BstLean.Part149
open BstLean.Part132 (nrm nrm_nonneg nrm_sq)
open BstLean.Part136 (hbar bm_fst bm_snd)

lemma bm_mul_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : BM f) (hg : Integrable g μ) : Integrable (fun x => g x * f x) μ := by
  obtain ⟨B, hB⟩ := hf.bdd
  refine (hg.norm.mul_const B).mono' (hg.aestronglyMeasurable.mul hf.meas.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs (f x)]
  exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)

/-! ## The projection identities -/

variable {n m : ℕ}

/-- A linear form `⟨γ, r⟩` of a standard Gaussian vector has the distribution of `|r|·Z`. -/
theorem stdGauss_lin_map (r : Fin n → ℝ) :
    (stdGauss (Fin n)).map (fun γ => γ ⬝ᵥ r) =
      (gaussianReal 0 1).map (fun z => √(∑ j, r j ^ 2) * z) := by
  have hD : 0 ≤ r ⬝ᵥ r := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have e : ∑ j, r j ^ 2 = r ⬝ᵥ r := by
    simp only [dotProduct]; exact Finset.sum_congr rfl fun j _ => sq (r j)
  rw [BstLean.Part131.stdGauss_dot, gaussianReal_map_const_mul, e]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt hD, Real.coe_toNNReal _ hD]

lemma gauss_lin_integral (r : Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ γ, f (γ ⬝ᵥ r) ∂stdGauss (Fin n) = ∫ z, f (√(∑ j, r j ^ 2) * z) ∂gaussianReal 0 1 := by
  have m1 : Measurable (fun γ : Fin n → ℝ => γ ⬝ᵥ r) := by
    unfold dotProduct; fun_prop
  have m2 : Measurable (fun z : ℝ => √(∑ j, r j ^ 2) * z) := by fun_prop
  rw [← integral_map m1.aemeasurable hf.aestronglyMeasurable, stdGauss_lin_map,
    integral_map m2.aemeasurable hf.aestronglyMeasurable]

lemma gauss_lin_integrable (r : Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hi : Integrable (fun z => f (√(∑ j, r j ^ 2) * z)) (gaussianReal 0 1)) :
    Integrable (fun γ : Fin n → ℝ => f (γ ⬝ᵥ r)) (stdGauss (Fin n)) := by
  have m1 : Measurable (fun γ : Fin n → ℝ => γ ⬝ᵥ r) := by
    unfold dotProduct; fun_prop
  have m2 : Measurable (fun z : ℝ => √(∑ j, r j ^ 2) * z) := by fun_prop
  have h1 := (integrable_map_measure (μ := gaussianReal 0 1) hf.aestronglyMeasurable
    m2.aemeasurable).mpr hi
  rw [← stdGauss_lin_map] at h1
  exact (integrable_map_measure hf.aestronglyMeasurable m1.aemeasurable).mp h1

lemma mulVec_shift (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (γ : Fin n → ℝ)
    (i : Fin m) :
    (A₁.mulVec (c + τ • γ)) i = mRow A₁ c i + τ * (γ ⬝ᵥ fun j => A₁ i j) := by
  unfold mRow
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The paper's oracle first-layer mean as a mean over `γ`. -/
theorem hO_eq_gauss (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (i : Fin m) :
    Integrable (fun γ : Fin n → ℝ => relu ((A₁.mulVec (c + τ • γ)) i)) (stdGauss (Fin n)) ∧
    hO A₁ c τ i = ∫ γ, relu ((A₁.mulVec (c + τ • γ)) i) ∂stdGauss (Fin n) := by
  have mf : Measurable (fun x : ℝ => relu (mRow A₁ c i + τ * x)) :=
    measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id))
  have e : (fun z : ℝ => relu (mRow A₁ c i + τ * (√(∑ j, A₁ i j ^ 2) * z))) =
      fun z => relu (mRow A₁ c i + sRow A₁ τ i * z) := by
    funext z; unfold sRow; congr 1; ring
  simp_rw [mulVec_shift]
  constructor
  · refine gauss_lin_integrable (fun j => A₁ i j) mf ?_
    rw [e]; exact integrable_relu_shift _ _
  · rw [gauss_lin_integral (fun j => A₁ i j) mf, e]
    rfl

/-- The paper's oracle second moment of one row as a mean over `γ`. -/
theorem relu_sq_eq_gauss (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (i : Fin m) :
    Integrable (fun γ : Fin n → ℝ => relu ((A₁.mulVec (c + τ • γ)) i) ^ 2) (stdGauss (Fin n)) ∧
    ∫ z, relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2 ∂gaussianReal 0 1 =
      ∫ γ, relu ((A₁.mulVec (c + τ • γ)) i) ^ 2 ∂stdGauss (Fin n) := by
  have mf : Measurable (fun x : ℝ => relu (mRow A₁ c i + τ * x) ^ 2) :=
    (measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id))).pow_const 2
  have e : (fun z : ℝ => relu (mRow A₁ c i + τ * (√(∑ j, A₁ i j ^ 2) * z)) ^ 2) =
      fun z => relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2 := by
    funext z; unfold sRow; congr 2; ring
  simp_rw [mulVec_shift]
  constructor
  · refine gauss_lin_integrable (fun j => A₁ i j) mf ?_
    rw [e]; exact integrable_relu_shift_sq _ _
  · rw [gauss_lin_integral (fun j => A₁ i j) mf, e]

/-- `(m/2)·γ_Γ = E|relu(A₁ y)|²`. -/
theorem gO_eq_gauss (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun γ : Fin n → ℝ => normSq (reluV (A₁.mulVec (c + τ • γ)))) (stdGauss (Fin n)) ∧
    (m : ℝ) / 2 * gO A₁ c τ =
      ∫ γ, normSq (reluV (A₁.mulVec (c + τ • γ))) ∂stdGauss (Fin n) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hi := fun i : Fin m => (relu_sq_eq_gauss A₁ c τ i).1
  constructor
  · unfold normSq reluV
    exact integrable_finsetSum _ fun i _ => hi i
  · unfold gO normSq reluV
    rw [integral_finsetSum _ fun i _ => hi i]
    simp_rw [(relu_sq_eq_gauss A₁ c τ _).2]
    field_simp

/-! ## The weighted kernel inequality -/

section generic

variable {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]

/-- `|Σ_i (E u a_i)(E v a_i) − k(E u|a|)(E v|a|)| ≤ √(E u²)·√(E v²)·√(QkG a k)`. -/
theorem kern_weighted {a : U → Fin m → ℝ} (ha : ∀ j, BM (fun x => a x j)) (k : ℝ) {u v : U → ℝ}
    (hu : Measurable u) (hv : Measurable v) (hu2 : Integrable (fun x => u x ^ 2) μ)
    (hv2 : Integrable (fun x => v x ^ 2) μ) :
    |∑ i, (∫ x, u x * a x i ∂μ) * (∫ x, v x * a x i ∂μ) -
        k * ((∫ x, u x * nrm (a x) ∂μ) * ∫ x, v x * nrm (a x) ∂μ)| ≤
      √(∫ x, u x ^ 2 ∂μ) * √(∫ x, v x ^ 2 ∂μ) * √(QkG μ a k) := by
  have hu1 : Integrable u μ :=
    ((memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mpr hu2).integrable one_le_two
  have hv1 : Integrable v μ :=
    ((memLp_two_iff_integrable_sq hv.aestronglyMeasurable).mpr hv2).integrable one_le_two
  have iu : ∀ i, Integrable (fun x => u x * a x i) μ := fun i => bm_mul_integrable (ha i) hu1
  have iv : ∀ i, Integrable (fun x => v x * a x i) μ := fun i => bm_mul_integrable (ha i) hv1
  have iun : Integrable (fun x => u x * nrm (a x)) μ := bm_mul_integrable (bm_nrm_of ha) hu1
  have ivn : Integrable (fun x => v x * nrm (a x)) μ := bm_mul_integrable (bm_nrm_of ha) hv1
  set F : U × U → ℝ := fun p => u p.1 * v p.2 with hF
  set D : U × U → ℝ := fun p => dotp (a p.1) (a p.2) - k * (nrm (a p.1) * nrm (a p.2)) with hD
  have bD : BM D := (bm_dotp_of ha).sub ((BM.const k).mul (bm_pn_of ha))
  have i1 : ∀ i, Integrable (fun p : U × U => (u p.1 * a p.1 i) * (v p.2 * a p.2 i))
      (μ.prod μ) := fun i => (iu i).mul_prod (iv i)
  have i2 : Integrable (fun p : U × U => (u p.1 * nrm (a p.1)) * (v p.2 * nrm (a p.2)))
      (μ.prod μ) := iun.mul_prod ivn
  have eFD : (fun p => F p * D p) = fun p : U × U =>
      (∑ i, (u p.1 * a p.1 i) * (v p.2 * a p.2 i)) -
        k * ((u p.1 * nrm (a p.1)) * (v p.2 * nrm (a p.2))) := by
    funext p
    simp only [hF, hD, dotp]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  have iS : Integrable (fun p : U × U => ∑ i, (u p.1 * a p.1 i) * (v p.2 * a p.2 i)) (μ.prod μ) :=
    integrable_finsetSum _ fun i _ => i1 i
  have iFD : Integrable (fun p => F p * D p) (μ.prod μ) := by
    rw [eFD]; exact iS.sub (i2.const_mul k)
  have vFD : ∫ p, F p * D p ∂(μ.prod μ) =
      ∑ i, (∫ x, u x * a x i ∂μ) * (∫ x, v x * a x i ∂μ) -
        k * ((∫ x, u x * nrm (a x) ∂μ) * ∫ x, v x * nrm (a x) ∂μ) := by
    rw [eFD, integral_sub iS (i2.const_mul k), integral_finsetSum _ fun i _ => i1 i,
      integral_const_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact integral_prod_mul (fun x => u x * a x i) (fun x => v x * a x i)
    · congr 1
      exact integral_prod_mul (fun x => u x * nrm (a x)) (fun x => v x * nrm (a x))
  have eF2 : (fun p => F p ^ 2) = fun p : U × U => u p.1 ^ 2 * v p.2 ^ 2 := by
    funext p; simp only [hF]; ring
  have iF2 : Integrable (fun p => F p ^ 2) (μ.prod μ) := by
    rw [eF2]; exact hu2.mul_prod hv2
  have vF2 : ∫ p, F p ^ 2 ∂(μ.prod μ) = (∫ x, u x ^ 2 ∂μ) * ∫ x, v x ^ 2 ∂μ := by
    rw [eF2]; exact integral_prod_mul (fun x => u x ^ 2) (fun x => v x ^ 2)
  have h := abs_int_mul_le iF2 (bD.sq.integrable _) iFD
  rw [vFD, vF2, Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)] at h
  exact h

end generic

/-! ## The comparison -/

/-- The first-layer difference `b1 − hO/ρ`. -/
noncomputable def e1N (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) : Fin m → ℝ :=
  b1 c τ A₁ - (1 / rhoC c τ) • hO A₁ c τ

lemma ae_ne_zero (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᵐ γ ∂stdGauss (Fin n), normSq (c + τ • γ) ≠ 0 := by
  have := BstLean.Part140.stdGauss_nullSingleton hn
  have hsub : {γ : Fin n → ℝ | ¬ normSq (c + τ • γ) ≠ 0} ⊆ {(-(1 / τ)) • c} := by
    intro γ hγ
    simp only [ne_eq, not_not, mem_setOf_eq] at hγ
    have h0 : ∀ i, (c + τ • γ) i ^ 2 = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hγ i (Finset.mem_univ i)
    rw [mem_singleton_iff]
    funext i
    have := pow_eq_zero_iff (two_ne_zero) |>.mp (h0 i)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp
    linarith
  exact measure_mono_null hsub (measure_singleton _)

/-- At a nonzero input: `|y|·a1 = relu(A₁ y)`. -/
lemma a1_scale (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) {γ : Fin n → ℝ}
    (h : normSq (c + τ • γ) ≠ 0) (i : Fin m) :
    nrm (c + τ • γ) * a1 c τ A₁ γ i = relu ((A₁.mulVec (c + τ • γ)) i) := by
  have hpos : 0 < nrm (c + τ • γ) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h))
  unfold a1 reluV
  rw [BstLean.Part135.sphPt_eq h, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [relu_mul_of_nonneg (by positivity)]
  unfold nrm at hpos ⊢
  field_simp

/-- `e1N_i = E[wN·a1_i]`. -/
theorem e1N_eq (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    e1N c τ A₁ i = ∫ γ, wN c τ γ * a1 c τ A₁ γ i ∂stdGauss (Fin n) := by
  have hρ := rhoC_pos hn c hτ
  obtain ⟨hi, he⟩ := hO_eq_gauss A₁ c τ i
  have ia : Integrable (fun γ => a1 c τ A₁ γ i) (stdGauss (Fin n)) :=
    (bm_a1 hn c τ A₁ i).integrable _
  have hae : (fun γ => wN c τ γ * a1 c τ A₁ γ i) =ᵐ[stdGauss (Fin n)]
      fun γ => a1 c τ A₁ γ i - 1 / rhoC c τ * relu ((A₁.mulVec (c + τ • γ)) i) := by
    filter_upwards [ae_ne_zero hn c hτ] with γ hγ
    rw [← a1_scale A₁ c τ hγ i]
    unfold wN
    field_simp
  rw [integral_congr_ae hae, integral_sub ia (hi.const_mul _), integral_const_mul, ← he]
  rfl

/-- `|a1|²·|y|² = |relu(A₁ y)|²` at a nonzero input. -/
lemma a1_scale_sq (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) {γ : Fin n → ℝ}
    (h : normSq (c + τ • γ) ≠ 0) :
    normSq (c + τ • γ) * normSq (a1 c τ A₁ γ) = normSq (reluV (A₁.mulVec (c + τ • γ))) := by
  unfold normSq reluV
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← a1_scale A₁ c τ h i, mul_pow, nrm_sq]
  rfl

/-- **The second moments**: `|N2 − (m/2)·gO/ρ²| ≤ √errD1·√VN`. -/
theorem N2_sub_gO (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    |N2 c τ A₁ - (m : ℝ) / 2 * gO A₁ c τ / rhoC c τ ^ 2| ≤
      √(errD1 c τ A₁) * √(VN c τ) := by
  have hρ := rhoC_pos hn c hτ
  obtain ⟨u1, u0, u2, uV⟩ := uN_moments hn c hτ
  obtain ⟨gi, ge⟩ := gO_eq_gauss hm A₁ c τ
  have bN := bm_normSq_a1 hn c τ A₁
  set d : ℝ := (m : ℝ) / n with hd
  have bf : BM (fun γ => normSq (a1 c τ A₁ γ) - d) := bN.sub (BM.const d)
  have iN : Integrable (fun γ => normSq (a1 c τ A₁ γ)) (stdGauss (Fin n)) := bN.integrable _
  have ifu : Integrable (fun γ => (normSq (a1 c τ A₁ γ) - d) * uN c τ γ) (stdGauss (Fin n)) := by
    have := bm_mul_integrable bf u1
    simpa [mul_comm] using this
  have hae : (fun γ => (normSq (a1 c τ A₁ γ) - d) * uN c τ γ + d * uN c τ γ) =ᵐ[stdGauss (Fin n)]
      fun γ => normSq (a1 c τ A₁ γ) -
        1 / rhoC c τ ^ 2 * normSq (reluV (A₁.mulVec (c + τ • γ))) := by
    filter_upwards [ae_ne_zero hn c hτ] with γ hγ
    rw [← a1_scale_sq A₁ c τ hγ]
    unfold uN
    field_simp
    ring
  have key : N2 c τ A₁ - (m : ℝ) / 2 * gO A₁ c τ / rhoC c τ ^ 2 =
      ∫ γ, (normSq (a1 c τ A₁ γ) - d) * uN c τ γ ∂stdGauss (Fin n) := by
    have h1 : ∫ γ, ((normSq (a1 c τ A₁ γ) - d) * uN c τ γ + d * uN c τ γ) ∂stdGauss (Fin n) =
        N2 c τ A₁ - (m : ℝ) / 2 * gO A₁ c τ / rhoC c τ ^ 2 := by
      rw [integral_congr_ae hae, integral_sub iN (gi.const_mul _), integral_const_mul, ← ge]
      unfold N2
      ring
    rw [← h1, integral_add ifu (u1.const_mul d), integral_const_mul, u0]
    ring
  rw [key]
  have h := abs_int_mul_le (bf.sq.integrable _) u2 ifu
  rw [uV] at h
  exact h

lemma Qk_eq_QkG (k : ℝ) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    Qk k c τ A₁ = QkG (stdGauss (Fin n)) (a1 c τ A₁) k := rfl

/-- **The first-layer difference**: `|e1N|² ≤ VN·√(Qk k) + k·(E[wN·|a1|])²`. -/
theorem e1N_normSq_le (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (k : ℝ) :
    normSq (e1N c τ A₁) ≤ VN c τ * √(Qk k c τ A₁) +
      k * (∫ γ, wN c τ γ * nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n)) ^ 2 := by
  obtain ⟨w1, w2, wV, _, _⟩ := wN_moments hn c hτ
  have h := kern_weighted (stdGauss (Fin n)) (bm_a1 hn c τ A₁) k (measurable_wN c τ)
    (measurable_wN c τ) w2 w2
  rw [← Qk_eq_QkG, Real.mul_self_sqrt (integral_nonneg fun γ => sq_nonneg _)] at h
  have e : normSq (e1N c τ A₁) = ∑ i, (∫ γ, wN c τ γ * a1 c τ A₁ γ i ∂stdGauss (Fin n)) *
      (∫ γ, wN c τ γ * a1 c τ A₁ γ i ∂stdGauss (Fin n)) := by
    unfold normSq
    exact Finset.sum_congr rfl fun i _ => by rw [e1N_eq hn c hτ A₁ i, sq]
  rw [← e] at h
  have h2 := (abs_le.mp h).2
  have h3 : (∫ γ, wN c τ γ ^ 2 ∂stdGauss (Fin n)) * √(Qk k c τ A₁) ≤
      VN c τ * √(Qk k c τ A₁) := mul_le_mul_of_nonneg_right wV (Real.sqrt_nonneg _)
  nlinarith

/-- `(E[wN·|a1|])² ≤ 2·VN·errD1/d + d·VN²/2`, `d = m/n`. -/
theorem wnrm_sq_le (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    (∫ γ, wN c τ γ * nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n)) ^ 2 ≤
      2 * VN c τ * errD1 c τ A₁ / ((m : ℝ) / n) + (m : ℝ) / n * VN c τ ^ 2 / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨w1, w2, wV, w0, wh⟩ := wN_moments hn c hτ
  have hV0 := VN_nonneg c τ
  set d : ℝ := (m : ℝ) / n with hd
  have hd0 : 0 < d := by positivity
  set s : ℝ := √d with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hd0
  have hs2 : s ^ 2 = d := Real.sq_sqrt hd0.le
  have bR := bm_nrm_a1 hn c τ A₁
  have bN := bm_normSq_a1 hn c τ A₁
  have bg : BM (fun γ => nrm (a1 c τ A₁ γ) - s) := bR.sub (BM.const s)
  have ig : Integrable (fun γ => wN c τ γ * (nrm (a1 c τ A₁ γ) - s)) (stdGauss (Fin n)) :=
    bm_mul_integrable bg w1
  have hE0 : 0 ≤ errD1 c τ A₁ := integral_nonneg fun _ => sq_nonneg _
  have hg2 : ∫ γ, (nrm (a1 c τ A₁ γ) - s) ^ 2 ∂stdGauss (Fin n) ≤ errD1 c τ A₁ / d := by
    have hle : ∀ γ, (nrm (a1 c τ A₁ γ) - s) ^ 2 ≤ (normSq (a1 c τ A₁ γ) - d) ^ 2 / d := by
      intro γ
      have hx := nrm_nonneg (a1 c τ A₁ γ)
      rw [le_div_iff₀ hd0, ← nrm_sq, ← hs2]
      have : (nrm (a1 c τ A₁ γ) ^ 2 - s ^ 2) ^ 2 =
          (nrm (a1 c τ A₁ γ) - s) ^ 2 * (nrm (a1 c τ A₁ γ) + s) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0.le (by linarith) 2) (sq_nonneg _)
    have := integral_mono (bg.sq.integrable (stdGauss (Fin n)))
      (((bN.sub (BM.const d)).sq.integrable (stdGauss (Fin n))).div_const d) hle
    rw [integral_div] at this
    exact this
  have h1 := cs_int w2 (bg.sq.integrable (stdGauss (Fin n))) ig
  have hP : (∫ γ, wN c τ γ * (nrm (a1 c τ A₁ γ) - s) ∂stdGauss (Fin n)) ^ 2 ≤
      VN c τ * (errD1 c τ A₁ / d) :=
    h1.trans (mul_le_mul wV hg2 (integral_nonneg fun _ => sq_nonneg _) hV0)
  have esplit : ∫ γ, wN c τ γ * nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n) =
      (∫ γ, wN c τ γ * (nrm (a1 c τ A₁ γ) - s) ∂stdGauss (Fin n)) +
        s * ∫ γ, wN c τ γ ∂stdGauss (Fin n) := by
    rw [← integral_const_mul, ← integral_add ig (w1.const_mul s)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun γ => by ring)
  rw [esplit]
  set P := ∫ γ, wN c τ γ * (nrm (a1 c τ A₁ γ) - s) ∂stdGauss (Fin n)
  set Q := ∫ γ, wN c τ γ ∂stdGauss (Fin n)
  have hQ2 : (s * Q) ^ 2 ≤ d * (VN c τ / 2) ^ 2 := by
    rw [mul_pow, hs2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ w0 wh 2) hd0.le
  have e2 : 2 * VN c τ * errD1 c τ A₁ / d + d * VN c τ ^ 2 / 2 =
      2 * (VN c τ * (errD1 c τ A₁ / d)) + 2 * (d * (VN c τ / 2) ^ 2) := by ring
  rw [e2]
  nlinarith [sq_nonneg (P - s * Q)]

/-- **The cross term**: `|⟨b1, e1N⟩| ≤ √VN·√(Qk k) + k·|E[wN·|a1|]|·√N2`, `k ≥ 0`. -/
theorem dotp_b1_e1N_le (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) {k : ℝ} (hk : 0 ≤ k) :
    |dotp (b1 c τ A₁) (e1N c τ A₁)| ≤ √(VN c τ) * √(Qk k c τ A₁) +
      k * |∫ γ, wN c τ γ * nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n)| * √(N2 c τ A₁) := by
  obtain ⟨w1, w2, wV, _, _⟩ := wN_moments hn c hτ
  have h := kern_weighted (stdGauss (Fin n)) (bm_a1 hn c τ A₁) k (u := fun _ => 1)
    measurable_const (measurable_wN c τ) (integrable_const _) w2
  simp only [one_mul, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one,
    Real.sqrt_one] at h
  rw [← Qk_eq_QkG] at h
  have e : dotp (b1 c τ A₁) (e1N c τ A₁) = ∑ i, (∫ γ, a1 c τ A₁ γ i ∂stdGauss (Fin n)) *
      (∫ γ, wN c τ γ * a1 c τ A₁ γ i ∂stdGauss (Fin n)) := by
    unfold dotp
    exact Finset.sum_congr rfl fun i _ => by rw [e1N_eq hn c hτ A₁ i]; rfl
  rw [← e] at h
  have bR := bm_nrm_a1 hn c τ A₁
  have hR0 : 0 ≤ ∫ γ, nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n) :=
    integral_nonneg fun _ => nrm_nonneg _
  have hR : ∫ γ, nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n) ≤ √(N2 c τ A₁) := by
    apply Real.le_sqrt_of_sq_le
    have := bm_sq_int_le (stdGauss (Fin n)) bR
    simp_rw [nrm_sq] at this
    exact this
  set X := ∫ γ, wN c τ γ * nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n)
  set R := ∫ γ, nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n)
  have h1 : √(∫ γ, wN c τ γ ^ 2 ∂stdGauss (Fin n)) * √(Qk k c τ A₁) ≤
      √(VN c τ) * √(Qk k c τ A₁) :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt wV) (Real.sqrt_nonneg _)
  have h2 : |k * (R * X)| ≤ k * |X| * √(N2 c τ A₁) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hk, abs_of_nonneg hR0]
    calc k * (R * |X|) ≤ k * (√(N2 c τ A₁) * |X|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR (abs_nonneg _)) hk
      _ = k * |X| * √(N2 c τ A₁) := by ring
  have h3 : |dotp (b1 c τ A₁) (e1N c τ A₁)| ≤
      |dotp (b1 c τ A₁) (e1N c τ A₁) - k * (R * X)| + |k * (R * X)| := by
    have := abs_add_le (dotp (b1 c τ A₁) (e1N c τ A₁) - k * (R * X)) (k * (R * X))
    simpa using this
  linarith

/-- **The squared scales**:
`|(2/m)(N2 − |b1|²) − sO2/ρ²| ≤ (2/m)(√errD1·√VN + 2|⟨b1, e1N⟩| + |e1N|²)`. The first term is
`sMF²` of Part 149. -/
theorem sMF_sq_sub_sO2 (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    |2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)) - sO2 A₁ c τ / rhoC c τ ^ 2| ≤
      2 / (m : ℝ) * (√(errD1 c τ A₁) * √(VN c τ) + 2 * |dotp (b1 c τ A₁) (e1N c τ A₁)| +
        normSq (e1N c τ A₁)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hρ := rhoC_pos hn c hτ
  have hN := N2_sub_gO hn hm c hτ A₁
  have ehO : ∀ i, hO A₁ c τ i = rhoC c τ * (b1 c τ A₁ i - e1N c τ A₁ i) := by
    intro i
    unfold e1N
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have esum : (∑ i, hO A₁ c τ i ^ 2) / rhoC c τ ^ 2 =
      normSq (b1 c τ A₁) - 2 * dotp (b1 c τ A₁) (e1N c τ A₁) + normSq (e1N c τ A₁) := by
    simp_rw [ehO, mul_pow]
    rw [← Finset.mul_sum, mul_div_assoc, mul_comm, div_mul_cancel₀ _ (pow_pos hρ 2).ne']
    unfold normSq dotp
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : 2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)) - sO2 A₁ c τ / rhoC c τ ^ 2 =
      2 / (m : ℝ) * ((N2 c τ A₁ - (m : ℝ) / 2 * gO A₁ c τ / rhoC c τ ^ 2) -
        2 * dotp (b1 c τ A₁) (e1N c τ A₁) + normSq (e1N c τ A₁)) := by
    unfold sO2
    rw [sub_div, mul_div_assoc, esum]
    field_simp
    ring
  rw [key, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / (m : ℝ))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hd := abs_nonneg (dotp (b1 c τ A₁) (e1N c τ A₁))
  have he0 := normSq_nonneg (e1N c τ A₁)
  rw [abs_le] at hN ⊢
  constructor
  · linarith [neg_abs_le (dotp (b1 c τ A₁) (e1N c τ A₁)), le_abs_self (dotp (b1 c τ A₁) (e1N c τ A₁))]
  · linarith [neg_abs_le (dotp (b1 c τ A₁) (e1N c τ A₁)), le_abs_self (dotp (b1 c τ A₁) (e1N c τ A₁))]

end BstLean.Part150

open BstLean.Part150 in
#print axioms uN_moments
open BstLean.Part150 in
#print axioms VN_le
open BstLean.Part150 in
#print axioms wN_moments
open BstLean.Part150 in
#print axioms hO_eq_gauss
open BstLean.Part150 in
#print axioms gO_eq_gauss
open BstLean.Part150 in
#print axioms kern_weighted
open BstLean.Part150 in
#print axioms e1N_eq
open BstLean.Part150 in
#print axioms N2_sub_gO
open BstLean.Part150 in
#print axioms e1N_normSq_le
open BstLean.Part150 in
#print axioms wnrm_sq_le
open BstLean.Part150 in
#print axioms dotp_b1_e1N_le
open BstLean.Part150 in
#print axioms sMF_sq_sub_sO2
