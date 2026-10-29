import BstLean.Part107WickA

/-!
# Part 107, the two-point and four-point moments of `ℓ·A₁(x)`: `wick107`, `qDom107`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part105

variable {n dA : ℕ}

/-- The coefficient vector of the linear form `ξ ↦ ℓ·A(x)`. -/
noncomputable def vv (ℓ x : Fin n → ℝ) : CoefIdx n n dA → ℝ :=
  fun i => ℓ i.1 * monoVal x i.2 / Real.sqrt (bwWeight i.2)

lemma qLin_coord (ξ : CoefIdx n n dA → ℝ) (ℓ x : Fin n → ℝ) :
    qLin (bwOfCoord ((1 : ℝ) • ξ)) ℓ x = lin (vv ℓ x) ξ := by
  simp only [qLin, dot, bwEval, bwOfCoord, lin, vv, Fintype.sum_prod_type, Finset.mul_sum,
    Pi.smul_apply, smul_eq_mul, one_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => ?_
  ring

lemma monoSum (x y : Fin n → ℝ) :
    ∑ m : MonoIdx n dA, monoVal x m * monoVal y m / bwWeight m = kap dA (dot x y) := by
  unfold kap
  have h : ∀ f : MonoIdx n dA → ℝ,
      ∑ m, f m = ∑ j ∈ Finset.range (dA + 1), ∑ m : MonoIdx n dA, if m.deg = j then f m else 0 := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_ite_eq]
    simp [MonoIdx.deg, m.1.2]
  rw [h]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact multinomial105 n dA x y j (Nat.lt_succ_iff.mp (Finset.mem_range.1 hj))

lemma ip_vv (ℓ x y : Fin n → ℝ) :
    ip (vv (dA := dA) ℓ x) (vv ℓ y) = (∑ a, ℓ a ^ 2) * kap dA (dot x y) := by
  rw [← monoSum, Finset.sum_mul_sum]
  simp only [ip, vv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => ?_
  have hw := Real.mul_self_sqrt (bwWeight_nonneg m)
  have hp := bwWeight_pos m
  have hs : Real.sqrt (bwWeight m) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  rw [div_mul_div_comm, hw]
  field_simp

lemma measurable_qLin (x : Fin n → ℝ) :
    Measurable (fun ω : (CoefIdx n n dA → ℝ) × (Fin n → ℝ) => qLin ω.1 ω.2 x) := by
  unfold qLin dot
  exact Finset.measurable_sum _ fun a _ =>
    ((measurable_pi_apply a).comp measurable_snd).mul ((measurable_bwEval x a).comp measurable_fst)

lemma measurable_qLin_left (ℓ x : Fin n → ℝ) :
    Measurable (fun A : CoefIdx n n dA → ℝ => qLin A ℓ x) :=
  (measurable_qLin x).comp measurable_prodMk_right

/-! ## The dominating function -/

/-- `Q(A, ℓ) = (Σ_a |ℓ_a|)(Σ_i |A_i|)`. -/
noncomputable def Qf (ω : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ a, |ω.2 a|) * ∑ i, |ω.1 i|

lemma Qf_nonneg (ω : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)) : 0 ≤ Qf ω := by
  unfold Qf
  positivity

lemma measurable_Qf : Measurable (Qf (n := n) (dA := dA)) := by
  unfold Qf
  fun_prop

lemma abs_qLin_le (A : CoefIdx n n dA → ℝ) (ℓ x : Fin n → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ m : MonoIdx n dA, |monoVal x m| ≤ C) : |qLin A ℓ x| ≤ C * Qf (A, ℓ) := by
  have hS : ∀ a : Fin n, ∑ m : MonoIdx n dA, |A (a, m)| ≤ ∑ i, |A i| := by
    intro a
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun a => ∑ m : MonoIdx n dA, |A (a, m)|)
      (fun b _ => Finset.sum_nonneg fun m _ => abs_nonneg _) (Finset.mem_univ a)
  have hE : ∀ a : Fin n, |bwEval A x a| ≤ C * ∑ i, |A i| := by
    intro a
    unfold bwEval
    calc |∑ m : MonoIdx n dA, A (a, m) * monoVal x m|
        ≤ ∑ m : MonoIdx n dA, |A (a, m) * monoVal x m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m : MonoIdx n dA, |A (a, m)| * C := Finset.sum_le_sum fun m _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hC m) (abs_nonneg _)
      _ = (∑ m : MonoIdx n dA, |A (a, m)|) * C := by rw [Finset.sum_mul]
      _ ≤ (∑ i, |A i|) * C := mul_le_mul_of_nonneg_right (hS a) hC0
      _ = _ := mul_comm _ _
  unfold qLin dot Qf
  calc |∑ a, ℓ a * bwEval A x a| ≤ ∑ a, |ℓ a * bwEval A x a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |ℓ a| * (C * ∑ i, |A i|) := Finset.sum_le_sum fun a _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hE a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- `Σ_m |x^m|`. -/
noncomputable def Mx (dA : ℕ) (x : Fin n → ℝ) : ℝ := ∑ m : MonoIdx n dA, |monoVal x m|

lemma Mx_nonneg (x : Fin n → ℝ) : 0 ≤ Mx dA x := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma abs_qLin_le_Mx (A : CoefIdx n n dA → ℝ) (ℓ x : Fin n → ℝ) :
    |qLin A ℓ x| ≤ Mx dA x * Qf (A, ℓ) :=
  abs_qLin_le A ℓ x _ (Mx_nonneg x) fun m =>
    Finset.single_le_sum (f := fun m : MonoIdx n dA => |monoVal x m|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ m)

lemma Qf4_integrable : Integrable (fun ω => Qf ω ^ 4) (AL n dA) := by
  have hg : Integrable (fun ℓ : Fin n → ℝ => (∑ a, |ℓ a|) ^ 4) (stdGauss (Fin n)) := by
    simpa using absPow4_int (ι := Fin n) (fun _ => 1)
  have hf : Integrable (fun A : CoefIdx n n dA → ℝ => (∑ i, |A i|) ^ 4) (bwGauss n n dA 1) := by
    unfold bwGauss
    have hm : Measurable (fun A : CoefIdx n n dA → ℝ => (∑ i, |A i|) ^ 4) := by fun_prop
    rw [integrable_map_measure hm.aestronglyMeasurable (measurable_bwGaussMap 1).aemeasurable]
    refine (absPow4_int (ι := CoefIdx n n dA) (fun i => 1 / Real.sqrt (bwWeight i.2))).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Function.comp_apply, bwOfCoord, Pi.smul_apply, smul_eq_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  refine (hf.mul_prod hg).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Qf]
  ring

theorem qDom107 : QDom107 := by
  intro n dA
  refine ⟨Qf, measurable_Qf, Qf_nonneg, Qf4_integrable, fun ω x hx => ?_⟩
  have h := abs_qLin_le ω.1 ω.2 x 1 zero_le_one (fun m => by
    rw [monoVal_eq_prod]
    refine Finset.prod_induction _ (fun r : ℝ => |r| ≤ 1) (fun a b ha hb => ?_) (by simp)
      (fun l _ => ?_)
    · rw [abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg b]
    · rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hx l))
  simpa using h

/-! ## The moments -/

lemma q4_integrable (x₁ x₂ x₃ x₄ : Fin n → ℝ) :
    Integrable (fun ω : (CoefIdx n n dA → ℝ) × (Fin n → ℝ) =>
      qLin ω.1 ω.2 x₁ * qLin ω.1 ω.2 x₂ * qLin ω.1 ω.2 x₃ * qLin ω.1 ω.2 x₄) (AL n dA) := by
  refine Integrable.mono' (Qf4_integrable.const_mul (Mx dA x₁ * Mx dA x₂ * Mx dA x₃ * Mx dA x₄))
    ((((measurable_qLin x₁).mul (measurable_qLin x₂)).mul (measurable_qLin x₃)).mul
      (measurable_qLin x₄)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := abs_qLin_le_Mx ω.1 ω.2 x₁
  have h2 := abs_qLin_le_Mx ω.1 ω.2 x₂
  have h3 := abs_qLin_le_Mx ω.1 ω.2 x₃
  have h4 := abs_qLin_le_Mx ω.1 ω.2 x₄
  have p : ∀ x : Fin n → ℝ, 0 ≤ Mx dA x * Qf ω := fun x => mul_nonneg (Mx_nonneg x) (Qf_nonneg ω)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  calc |qLin ω.1 ω.2 x₁| * |qLin ω.1 ω.2 x₂| * |qLin ω.1 ω.2 x₃| * |qLin ω.1 ω.2 x₄|
      ≤ (Mx dA x₁ * Qf ω) * (Mx dA x₂ * Qf ω) * (Mx dA x₃ * Qf ω) * (Mx dA x₄ * Qf ω) :=
        mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (p x₁)) h3 (abs_nonneg _)
          (mul_nonneg (p x₁) (p x₂))) h4 (abs_nonneg _)
          (mul_nonneg (mul_nonneg (p x₁) (p x₂)) (p x₃))
    _ = _ := by ring

lemma q2_integrable (x₁ x₂ : Fin n → ℝ) :
    Integrable (fun ω : (CoefIdx n n dA → ℝ) × (Fin n → ℝ) =>
      qLin ω.1 ω.2 x₁ * qLin ω.1 ω.2 x₂) (AL n dA) := by
  refine Integrable.mono'
    (((integrable_const (1 : ℝ)).add Qf4_integrable).const_mul (Mx dA x₁ * Mx dA x₂))
    ((measurable_qLin x₁).mul (measurable_qLin x₂)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := abs_qLin_le_Mx ω.1 ω.2 x₁
  have h2 := abs_qLin_le_Mx ω.1 ω.2 x₂
  have hQ := Qf_nonneg ω
  have hM : 0 ≤ Mx dA x₁ * Mx dA x₂ := mul_nonneg (Mx_nonneg _) (Mx_nonneg _)
  rw [Real.norm_eq_abs, abs_mul]
  calc |qLin ω.1 ω.2 x₁| * |qLin ω.1 ω.2 x₂|
      ≤ (Mx dA x₁ * Qf ω) * (Mx dA x₂ * Qf ω) :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (Mx_nonneg x₁) hQ)
    _ = Mx dA x₁ * Mx dA x₂ * Qf ω ^ 2 := by ring
    _ ≤ Mx dA x₁ * Mx dA x₂ * (1 + Qf ω ^ 4) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (Qf ω ^ 2 - 1), sq_nonneg (Qf ω)]) hM

theorem wick107 : Wick107 := by
  intro n dA x₁ x₂ x₃ x₄
  constructor
  · have inner : ∀ ℓ : Fin n → ℝ, ∫ A, qLin A ℓ x₁ * qLin A ℓ x₂ ∂bwGauss n n dA 1 =
        (∑ a, ℓ a ^ 2) * kap dA (dot x₁ x₂) := by
      intro ℓ
      have hm : Measurable (fun A : CoefIdx n n dA → ℝ => qLin A ℓ x₁ * qLin A ℓ x₂) :=
        (measurable_qLin_left ℓ x₁).mul (measurable_qLin_left ℓ x₂)
      rw [bwGauss_integral 1 _ hm]
      simp_rw [qLin_coord]
      rw [wick2, ip_vv]
    rw [integral_prod_symm _ (q2_integrable x₁ x₂)]
    simp_rw [inner]
    rw [integral_mul_const, normSq_mom1, Fintype.card_fin]
  · have inner : ∀ ℓ : Fin n → ℝ,
        ∫ A, qLin A ℓ x₁ * qLin A ℓ x₂ * qLin A ℓ x₃ * qLin A ℓ x₄ ∂bwGauss n n dA 1 =
        (∑ a, ℓ a ^ 2) ^ 2 *
          (kap dA (dot x₁ x₂) * kap dA (dot x₃ x₄) + kap dA (dot x₁ x₃) * kap dA (dot x₂ x₄) +
            kap dA (dot x₁ x₄) * kap dA (dot x₂ x₃)) := by
      intro ℓ
      have hm : Measurable (fun A : CoefIdx n n dA → ℝ =>
          qLin A ℓ x₁ * qLin A ℓ x₂ * qLin A ℓ x₃ * qLin A ℓ x₄) :=
        (((measurable_qLin_left ℓ x₁).mul (measurable_qLin_left ℓ x₂)).mul
          (measurable_qLin_left ℓ x₃)).mul (measurable_qLin_left ℓ x₄)
      rw [bwGauss_integral 1 _ hm]
      simp_rw [qLin_coord]
      rw [wick4]
      simp_rw [ip_vv]
      ring
    rw [integral_prod_symm _ (q4_integrable x₁ x₂ x₃ x₄)]
    simp_rw [inner]
    rw [integral_mul_const, normSq_mom2, Fintype.card_fin]

#print axioms wick107
#print axioms qDom107

end BstLean.Part107
