import BstLean.Part133All

/-!
# Part 135: the direction of the output of a random network

* `gauss_dir_mean`, `gauss_dir_sq`: the direction `sphPt ξ` of a standard Gaussian vector `ξ` of
  `ℝⁿ` is isotropic: `E⟨y, sphPt ξ⟩ = 0`, `E⟨y, sphPt ξ⟩² ≤ |y|²/n`.
* `lin_dir_mean`, `lin_dir_sq`: the same for the direction of `M h`, `M` a Gaussian matrix, `h ≠ 0`.
* `world_dir_mean`, `world_dir_sq`: for a random network `W`, a unit input `u` and a unit vector
  `y`: `|E⟨y, x(u)⟩| ≤ epsW m`, `E⟨y, x(u)⟩² ≤ 1/n + epsW m`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part135

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

variable {n : ℕ}

/-! ## The zero event of a standard Gaussian vector -/

lemma stdGauss_zero_null (hn : 1 ≤ n) : stdGauss (Fin n) {ξ | normSq ξ = 0} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hsub : {ξ : Fin n → ℝ | normSq ξ = 0} ⊆ Function.eval (⟨0, hn⟩ : Fin n) ⁻¹' {(0 : ℝ)} := by
    intro ξ hξ
    have h0 : ξ = 0 := normSq_eq_zero hξ
    show ξ ⟨0, hn⟩ = 0
    rw [h0]; rfl
  refine measure_mono_null hsub ?_
  have hmp := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) (⟨0, hn⟩ : Fin n)
  have e : stdGauss (Fin n) = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := rfl
  rw [e, hmp.measure_preimage (measurableSet_singleton (0 : ℝ)).nullMeasurableSet]
  exact measure_singleton 0

lemma stdGauss_ne_zero_ae (hn : 1 ≤ n) : ∀ᵐ ξ ∂stdGauss (Fin n), normSq ξ ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  exact stdGauss_zero_null hn

/-! ## Pointwise identities -/

lemma dotp_smul_right (c : ℝ) (y ξ : Fin n → ℝ) : dotp y (c • ξ) = c * dotp y ξ := by
  unfold dotp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul]; ring

lemma dotp_neg_right (y s : Fin n → ℝ) : dotp y (-s) = -dotp y s := by
  unfold dotp
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply]; ring

lemma normSq_neg (ξ : Fin n → ℝ) : normSq (-ξ) = normSq ξ := by
  unfold normSq
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply]; ring

lemma sphPt_eq {ξ : Fin n → ℝ} (h : normSq ξ ≠ 0) : sphPt ξ = (1 / √(normSq ξ)) • ξ := by
  rw [sphPt_of_ne ξ h]; rfl

lemma sphPt_neg {ξ : Fin n → ℝ} (h : normSq ξ ≠ 0) : sphPt (-ξ) = -sphPt ξ := by
  rw [sphPt_eq (by rwa [normSq_neg]), sphPt_eq h, normSq_neg, smul_neg]

lemma dotp_sphPt_sq {ξ : Fin n → ℝ} (h : normSq ξ ≠ 0) (y : Fin n → ℝ) :
    dotp y (sphPt ξ) ^ 2 = dotp y ξ ^ 2 / normSq ξ := by
  have h0 : 0 ≤ normSq ξ := normSq_nonneg ξ
  rw [sphPt_eq h, dotp_smul_right, mul_pow, div_pow, one_pow, Real.sq_sqrt h0]
  ring

lemma abs_dotp_unit {y s : Fin n → ℝ} (hy : normSq y = 1) (hs : normSq s = 1) :
    |dotp y s| ≤ 1 := by
  have h := abs_dotp_le_nrm y s
  rwa [nrm_of_normSq_one hy, nrm_of_normSq_one hs, mul_one] at h

lemma sq_dotp_unit {y s : Fin n → ℝ} (hy : normSq y = 1) (hs : normSq s = 1) :
    |dotp y s ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr (abs_dotp_unit hy hs)

lemma abs_integral_le_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : ∀ ω, |f ω| ≤ 1) : |∫ ω, f ω ∂μ| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := 1)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hf ω)
  simpa using h

/-! ## The mean -/

lemma stdGauss_neg : (stdGauss (Fin n)).map (fun z : Fin n → ℝ => -z) = stdGauss (Fin n) := by
  unfold stdGauss
  change (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (fun z i => -z i) = _
  rw [Measure.pi_map_pi (fun _ => measurable_neg.aemeasurable)]
  simp only [gaussianReal_map_neg, neg_zero]

lemma measurable_dir (y : Fin n → ℝ) : Measurable (fun ξ : Fin n → ℝ => dotp y (sphPt ξ)) :=
  measurable_dotp_comp (f := fun _ => y) (g := sphPt) measurable_const measurable_sphPt

/-- the direction of a standard Gaussian vector: mean zero -/
theorem gauss_dir_mean {n : ℕ} (hn : 1 ≤ n) (y : Fin n → ℝ) :
    ∫ ξ, dotp y (sphPt ξ) ∂stdGauss (Fin n) = 0 := by
  have h1 : ∫ ξ, dotp y (sphPt ξ) ∂((stdGauss (Fin n)).map (fun z : Fin n → ℝ => -z)) =
      ∫ ξ, dotp y (sphPt (-ξ)) ∂stdGauss (Fin n) :=
    integral_map measurable_neg.aemeasurable (measurable_dir y).aestronglyMeasurable
  rw [stdGauss_neg] at h1
  have h2 : ∫ ξ, dotp y (sphPt (-ξ)) ∂stdGauss (Fin n) =
      ∫ ξ, -dotp y (sphPt ξ) ∂stdGauss (Fin n) := by
    refine integral_congr_ae ?_
    filter_upwards [stdGauss_ne_zero_ae hn] with ξ hξ
    rw [sphPt_neg hξ, dotp_neg_right]
  rw [h2, integral_neg] at h1
  linarith

/-! ## The second moment -/

/-- `F_{ij}(ξ) = ξ_i ξ_j / |ξ|²` (`0` at `ξ = 0`). -/
noncomputable def Fq (i j : Fin n) (ξ : Fin n → ℝ) : ℝ := ξ i * ξ j / normSq ξ

lemma measurable_Fq (i j : Fin n) : Measurable (Fq i j) := by
  show Measurable (fun ξ : Fin n → ℝ => ξ i * ξ j / normSq ξ)
  exact ((measurable_pi_apply i).mul (measurable_pi_apply j)).div continuous_normSq.measurable

lemma sq_le_normSq (ξ : Fin n → ℝ) (i : Fin n) : ξ i ^ 2 ≤ normSq ξ :=
  Finset.single_le_sum (f := fun k => ξ k ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

lemma abs_Fq_le (i j : Fin n) (ξ : Fin n → ℝ) : |Fq i j ξ| ≤ 1 := by
  unfold Fq
  rw [abs_div, abs_of_nonneg (normSq_nonneg ξ)]
  refine div_le_one_of_le₀ ?_ (normSq_nonneg ξ)
  have h1 := sq_le_normSq ξ i
  have h2 := sq_le_normSq ξ j
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (ξ i - ξ j), sq_nonneg (ξ i + ξ j)]

lemma integrable_Fq (i j : Fin n) : Integrable (Fq i j) (stdGauss (Fin n)) :=
  Integrable.mono' (integrable_const (1 : ℝ)) (measurable_Fq i j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact abs_Fq_le i j ξ)

/-- The change of the sign of the coordinate `i`. -/
def flipC (i : Fin n) (ξ : Fin n → ℝ) : Fin n → ℝ := fun k => if k = i then -ξ k else ξ k

lemma measurable_flipC (i : Fin n) : Measurable (flipC i) := by
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hk : k = i
  · simp only [flipC, hk, ↓reduceIte]; exact (measurable_pi_apply i).neg
  · simp only [flipC, hk, ↓reduceIte]; exact measurable_pi_apply k

lemma stdGauss_flip (i : Fin n) : (stdGauss (Fin n)).map (flipC i) = stdGauss (Fin n) := by
  have hf : ∀ k : Fin n, Measurable (fun t : ℝ => if k = i then -t else t) := by
    intro k
    by_cases hk : k = i
    · simp only [hk, ↓reduceIte]; exact measurable_neg
    · simp only [hk, ↓reduceIte]; exact measurable_id
  have h : (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
      (fun x k => (fun (k : Fin n) (t : ℝ) => if k = i then -t else t) k (x k)) =
      Measure.pi (fun k : Fin n => (gaussianReal 0 1).map (fun t : ℝ => if k = i then -t else t)) :=
    Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
      (f := fun (k : Fin n) (t : ℝ) => if k = i then -t else t) (fun k => (hf k).aemeasurable)
  have e : (fun k : Fin n => (gaussianReal 0 1).map (fun t : ℝ => if k = i then -t else t)) =
      fun _ => gaussianReal 0 1 := by
    funext k
    by_cases hk : k = i
    · simp only [hk, ↓reduceIte]; rw [gaussianReal_map_neg, neg_zero]
    · simp only [hk, ↓reduceIte]; exact Measure.map_id
  rw [e] at h
  exact h

lemma normSq_flipC (i : Fin n) (ξ : Fin n → ℝ) : normSq (flipC i ξ) = normSq ξ := by
  unfold normSq flipC
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma Fq_flip {i j : Fin n} (hij : i ≠ j) (ξ : Fin n → ℝ) :
    Fq i j (flipC i ξ) = -Fq i j ξ := by
  unfold Fq
  rw [normSq_flipC]
  simp only [flipC, ↓reduceIte, Ne.symm hij]
  ring

lemma integral_Fq_offdiag {i j : Fin n} (hij : i ≠ j) :
    ∫ ξ, Fq i j ξ ∂stdGauss (Fin n) = 0 := by
  have h1 : ∫ ξ, Fq i j ξ ∂((stdGauss (Fin n)).map (flipC i)) =
      ∫ ξ, Fq i j (flipC i ξ) ∂stdGauss (Fin n) :=
    integral_map (measurable_flipC i).aemeasurable (measurable_Fq i j).aestronglyMeasurable
  rw [stdGauss_flip] at h1
  simp only [Fq_flip hij] at h1
  rw [integral_neg] at h1
  linarith

/-- The exchange of the coordinates `i` and `j`. -/
def swapC (i j : Fin n) (ξ : Fin n → ℝ) : Fin n → ℝ := fun k => ξ (Equiv.swap i j k)

lemma measurable_swapC (i j : Fin n) : Measurable (swapC i j) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

lemma stdGauss_swap (i j : Fin n) : (stdGauss (Fin n)).map (swapC i j) = stdGauss (Fin n) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => gaussianReal 0 1)
    (Equiv.swap i j)).map_eq
  have hf : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Equiv.swap i j) :
      (Fin n → ℝ) → (Fin n → ℝ)) = swapC i j := by
    funext Z k
    obtain ⟨α, rfl⟩ := (Equiv.swap i j).surjective k
    have := Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => ℝ) (Equiv.swap i j) Z α
    simp only [swapC, Equiv.swap_apply_self]
    exact this
  rw [hf] at h
  exact h

lemma normSq_swapC (i j : Fin n) (ξ : Fin n → ℝ) : normSq (swapC i j ξ) = normSq ξ := by
  unfold normSq swapC
  exact Equiv.sum_comp (Equiv.swap i j) (fun k => ξ k ^ 2)

lemma Fq_swap (i j : Fin n) (ξ : Fin n → ℝ) : Fq i i (swapC i j ξ) = Fq j j ξ := by
  unfold Fq
  rw [normSq_swapC]
  simp only [swapC, Equiv.swap_apply_left]

lemma integral_Fq_diag (i j : Fin n) :
    ∫ ξ, Fq i i ξ ∂stdGauss (Fin n) = ∫ ξ, Fq j j ξ ∂stdGauss (Fin n) := by
  have h1 : ∫ ξ, Fq i i ξ ∂((stdGauss (Fin n)).map (swapC i j)) =
      ∫ ξ, Fq i i (swapC i j ξ) ∂stdGauss (Fin n) :=
    integral_map (measurable_swapC i j).aemeasurable (measurable_Fq i i).aestronglyMeasurable
  rw [stdGauss_swap] at h1
  simp only [Fq_swap] at h1
  exact h1

lemma sum_Fq_diag_le (ξ : Fin n → ℝ) : ∑ i, Fq i i ξ ≤ 1 := by
  unfold Fq
  rw [← Finset.sum_div]
  have e : ∑ i, ξ i * ξ i = normSq ξ := by
    unfold normSq
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact div_self_le_one _

lemma integral_Fq_diag_le (hn : 1 ≤ n) (i : Fin n) :
    ∫ ξ, Fq i i ξ ∂stdGauss (Fin n) ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ∑ j : Fin n, ∫ ξ, Fq j j ξ ∂stdGauss (Fin n) ≤ 1 := by
    calc ∑ j : Fin n, ∫ ξ, Fq j j ξ ∂stdGauss (Fin n)
        = ∫ ξ, ∑ j : Fin n, Fq j j ξ ∂stdGauss (Fin n) :=
          (integral_finsetSum _ (fun j _ => integrable_Fq j j)).symm
      _ ≤ ∫ _ξ, (1 : ℝ) ∂stdGauss (Fin n) :=
          integral_mono (integrable_finsetSum _ (fun j _ => integrable_Fq j j))
            (integrable_const _) sum_Fq_diag_le
      _ = 1 := by simp
  have h2 : ∑ j : Fin n, ∫ ξ, Fq j j ξ ∂stdGauss (Fin n) =
      n * ∫ ξ, Fq i i ξ ∂stdGauss (Fin n) := by
    rw [Finset.sum_congr rfl (fun j _ => integral_Fq_diag j i)]
    simp
  rw [h2] at h1
  rw [le_div_iff₀ hn']
  linarith

/-- the direction of a standard Gaussian vector: second moment at most |y|²/n (it is an equality;
`≤` is enough) -/
theorem gauss_dir_sq {n : ℕ} (hn : 1 ≤ n) (y : Fin n → ℝ) :
    ∫ ξ, dotp y (sphPt ξ) ^ 2 ∂stdGauss (Fin n) ≤ normSq y / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : ∫ ξ, dotp y (sphPt ξ) ^ 2 ∂stdGauss (Fin n) =
      ∫ ξ, ∑ i, ∑ j, y i * y j * Fq i j ξ ∂stdGauss (Fin n) := by
    refine integral_congr_ae ?_
    filter_upwards [stdGauss_ne_zero_ae hn] with ξ hξ
    rw [dotp_sphPt_sq hξ]
    unfold dotp Fq
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∫ ξ, ∑ i, ∑ j, y i * y j * Fq i j ξ ∂stdGauss (Fin n) =
      ∑ i, ∑ j, y i * y j * ∫ ξ, Fq i j ξ ∂stdGauss (Fin n) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (integrable_Fq i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (integrable_Fq i j).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have e3 : ∀ i, ∑ j, y i * y j * ∫ ξ, Fq i j ξ ∂stdGauss (Fin n) =
      y i ^ 2 * ∫ ξ, Fq i i ξ ∂stdGauss (Fin n) := by
    intro i
    rw [Finset.sum_eq_single i]
    · ring
    · intro j _ hj
      rw [integral_Fq_offdiag (Ne.symm hj)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [e1, e2, Finset.sum_congr rfl (fun i _ => e3 i)]
  calc ∑ i, y i ^ 2 * ∫ ξ, Fq i i ξ ∂stdGauss (Fin n)
      ≤ ∑ i, y i ^ 2 * (1 / (n : ℝ)) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (integral_Fq_diag_le hn i) (sq_nonneg _)
    _ = normSq y / n := by
        unfold normSq
        rw [← Finset.sum_mul]; ring

/-! ## The direction of `M h` -/

lemma lin_dir_transfer {k : ℕ} {v : ℝ} (hv : 0 < v) (h : Fin k → ℝ) (hh : normSq h ≠ 0)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) :
    ∫ M : Matrix (Fin n) (Fin k) ℝ, f (sphPt (M.mulVec h)) ∂gaussMat n k v =
      ∫ ξ, f (sphPt ξ) ∂stdGauss (Fin n) := by
  have hc : 0 < √v * √(normSq h) :=
    mul_pos (Real.sqrt_pos.mpr hv)
      (Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg h) (Ne.symm hh)))
  have hg : Measurable (fun x : Fin n → ℝ => f (sphPt x)) := hf.comp measurable_sphPt
  have h1 : ∫ x, f (sphPt x)
      ∂((gaussMat n k v).map (fun M : Matrix (Fin n) (Fin k) ℝ => M.mulVec h)) =
      ∫ M : Matrix (Fin n) (Fin k) ℝ, f (sphPt (M.mulVec h)) ∂gaussMat n k v :=
    integral_map (measurable_mulVec_right h).aemeasurable hg.aestronglyMeasurable
  have h2 : ∫ x, f (sphPt x)
      ∂((stdGauss (Fin n)).map (fun ξ : Fin n → ℝ => (√v * √(normSq h)) • ξ)) =
      ∫ ξ : Fin n → ℝ, f (sphPt ((√v * √(normSq h)) • ξ)) ∂stdGauss (Fin n) :=
    integral_map (measurable_const_smul _).aemeasurable hg.aestronglyMeasurable
  rw [gaussMat_mulVec] at h1
  rw [← h1, h2]
  simp only [sphPt_smul hc]

lemma measurable_dotp_right (y : Fin n → ℝ) : Measurable (fun s : Fin n → ℝ => dotp y s) :=
  measurable_dotp_comp (f := fun _ => y) (g := fun s => s) measurable_const measurable_id

/-- the same for the direction of `M h`, `M` a Gaussian matrix, `h ≠ 0` -/
theorem lin_dir_mean {n k : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : 0 < v) (h : Fin k → ℝ)
    (hh : normSq h ≠ 0) (y : Fin n → ℝ) :
    ∫ M : Matrix (Fin n) (Fin k) ℝ, dotp y (sphPt (M.mulVec h)) ∂gaussMat n k v = 0 :=
  (lin_dir_transfer hv h hh (f := fun s => dotp y s) (measurable_dotp_right y)).trans
    (gauss_dir_mean hn y)

theorem lin_dir_sq {n k : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : 0 < v) (h : Fin k → ℝ)
    (hh : normSq h ≠ 0) (y : Fin n → ℝ) :
    ∫ M : Matrix (Fin n) (Fin k) ℝ, dotp y (sphPt (M.mulVec h)) ^ 2 ∂gaussMat n k v ≤
      normSq y / n :=
  (lin_dir_transfer hv h hh (f := fun s => dotp y s ^ 2)
    ((measurable_dotp_right y).pow_const 2)).trans_le (gauss_dir_sq hn y)

/-! ## The whole network -/

lemma integral_assoc_eq {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] {f : α × β × γ → ℝ}
    (hf : Integrable f (μ.prod (ν.prod τ))) :
    Integrable (fun z : α × β => ∫ c, f (z.1, (z.2, c)) ∂τ) (μ.prod ν) ∧
    ∫ ω, f ω ∂(μ.prod (ν.prod τ)) = ∫ z : α × β, ∫ c, f (z.1, (z.2, c)) ∂τ ∂(μ.prod ν) := by
  have e : ∫ ω, f ω ∂(μ.prod (ν.prod τ)) =
      ∫ z, f (MeasurableEquiv.prodAssoc z) ∂((μ.prod ν).prod τ) := by
    rw [← Measure.prodAssoc_prod, integral_map_equiv]
  have hf' : Integrable (fun z => f (MeasurableEquiv.prodAssoc z)) ((μ.prod ν).prod τ) := by
    have h1 : Integrable f (Measure.map MeasurableEquiv.prodAssoc ((μ.prod ν).prod τ)) := by
      rw [Measure.prodAssoc_prod]; exact hf
    exact (integrable_map_equiv _ f).mp h1
  refine ⟨hf'.integral_prod_left, ?_⟩
  rw [e]
  exact integral_prod _ hf'

variable {N m : ℕ}

lemma measurable_world (u : Fin N → ℝ) (y : Fin n → ℝ) :
    Measurable (fun W : MlpParam N m n => dotp y (xW W u)) :=
  measurable_dotp_comp (f := fun _ => y) (g := fun W : MlpParam N m n => xW W u) measurable_const
    (measurable_xW_comp measurable_id measurable_const)

/-- the direction of the output of a random network at a unit input `u`, against a unit vector
`y` -/
theorem world_dir_mean {N m n : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {u : Fin N → ℝ}
    (hu : normSq u = 1) {y : Fin n → ℝ} (hy : normSq y = 1) :
    |∫ W : MlpParam N m n, dotp y (xW W u) ∂mlpGauss N m n| ≤ epsW m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hint : Integrable (fun W : MlpParam N m n => dotp y (xW W u))
      ((gaussMat m N (2 / (N : ℝ))).prod
        ((gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ))))) :=
    Integrable.mono' (integrable_const (1 : ℝ)) (measurable_world u y).aestronglyMeasurable
      (Filter.Eventually.of_forall fun W => by
        rw [Real.norm_eq_abs]; exact abs_dotp_unit hy (normSq_xW hn W u))
  obtain ⟨ig, eg⟩ := integral_assoc_eq (gaussMat m N (2 / (N : ℝ))) (gaussMat m m (2 / (m : ℝ)))
    (gaussMat n m (2 / (m : ℝ))) hint
  have eg' : ∫ W : MlpParam N m n, dotp y (xW W u) ∂mlpGauss N m n =
      ∫ z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
        ∫ c : Matrix (Fin n) (Fin m) ℝ, dotp y (xW ((z.1, (z.2, c)) : MlpParam N m n) u)
          ∂gaussMat n m (2 / (m : ℝ))
        ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) := eg
  have hpt : ∀ z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      |∫ c : Matrix (Fin n) (Fin m) ℝ, dotp y (xW ((z.1, (z.2, c)) : MlpParam N m n) u)
          ∂gaussMat n m (2 / (m : ℝ))| ≤
        (if normSq (hid2 z.1 z.2 u) = 0 then (1 : ℝ) else 0) := by
    intro z
    split_ifs with h0
    · exact abs_integral_le_one fun c => abs_dotp_unit hy (normSq_xW hn _ u)
    · simp only [xW_eq]
      rw [lin_dir_mean hn (by positivity) _ h0 y, abs_zero]
  rw [eg']
  exact abs_integral_le_integral_abs.trans
    ((integral_mono ig.abs (integrable_zero_ind u) hpt).trans (hid2_zero hN hm hu))

theorem world_dir_sq {N m n : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) (hn : 1 ≤ n) {u : Fin N → ℝ}
    (hu : normSq u = 1) {y : Fin n → ℝ} (hy : normSq y = 1) :
    ∫ W : MlpParam N m n, dotp y (xW W u) ^ 2 ∂mlpGauss N m n ≤ 1 / (n : ℝ) + epsW m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hint : Integrable (fun W : MlpParam N m n => dotp y (xW W u) ^ 2)
      ((gaussMat m N (2 / (N : ℝ))).prod
        ((gaussMat m m (2 / (m : ℝ))).prod (gaussMat n m (2 / (m : ℝ))))) :=
    Integrable.mono' (integrable_const (1 : ℝ))
      ((measurable_world u y).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun W => by
        rw [Real.norm_eq_abs]; exact sq_dotp_unit hy (normSq_xW hn W u))
  obtain ⟨ig, eg⟩ := integral_assoc_eq (gaussMat m N (2 / (N : ℝ))) (gaussMat m m (2 / (m : ℝ)))
    (gaussMat n m (2 / (m : ℝ))) hint
  have eg' : ∫ W : MlpParam N m n, dotp y (xW W u) ^ 2 ∂mlpGauss N m n =
      ∫ z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
        ∫ c : Matrix (Fin n) (Fin m) ℝ, dotp y (xW ((z.1, (z.2, c)) : MlpParam N m n) u) ^ 2
          ∂gaussMat n m (2 / (m : ℝ))
        ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) := eg
  have hpt : ∀ z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      ∫ c : Matrix (Fin n) (Fin m) ℝ, dotp y (xW ((z.1, (z.2, c)) : MlpParam N m n) u) ^ 2
          ∂gaussMat n m (2 / (m : ℝ)) ≤
        1 / (n : ℝ) + (if normSq (hid2 z.1 z.2 u) = 0 then (1 : ℝ) else 0) := by
    intro z
    have h1n : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    split_ifs with h0
    · have hb := abs_integral_le_one (μ := gaussMat n m (2 / (m : ℝ)))
        (f := fun c : Matrix (Fin n) (Fin m) ℝ =>
          dotp y (xW ((z.1, (z.2, c)) : MlpParam N m n) u) ^ 2)
        (fun c => sq_dotp_unit hy (normSq_xW hn _ u))
      have := (le_abs_self _).trans hb
      linarith
    · simp only [xW_eq]
      have := lin_dir_sq hn (v := 2 / (m : ℝ)) (by positivity) _ h0 y
      rw [hy] at this
      linarith
  have hb : Integrable (fun z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      1 / (n : ℝ) + (if normSq (hid2 z.1 z.2 u) = 0 then (1 : ℝ) else 0))
      ((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) :=
    (integrable_const _).add (integrable_zero_ind u)
  have h1 := integral_mono ig hb hpt
  have h2 : ∫ z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
      (1 / (n : ℝ) + (if normSq (hid2 z.1 z.2 u) = 0 then (1 : ℝ) else 0))
      ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) =
      1 / (n : ℝ) + ∫ z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ,
        (if normSq (hid2 z.1 z.2 u) = 0 then (1 : ℝ) else 0)
        ∂((gaussMat m N (2 / (N : ℝ))).prod (gaussMat m m (2 / (m : ℝ)))) := by
    rw [integral_add (integrable_const _) (integrable_zero_ind u)]
    congr 1
    simp
  have h3 := hid2_zero hN hm hu
  rw [eg']
  linarith

end BstLean.Part135

open BstLean.Part135 in
#print axioms gauss_dir_mean
open BstLean.Part135 in
#print axioms gauss_dir_sq
open BstLean.Part135 in
#print axioms lin_dir_mean
open BstLean.Part135 in
#print axioms lin_dir_sq
open BstLean.Part135 in
#print axioms world_dir_mean
open BstLean.Part135 in
#print axioms world_dir_sq
