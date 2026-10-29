import BstLean.Part218Ordered

/-! A concrete second moment bounds both ordered-row covariance classes. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory

section
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {φ : X × X → ℝ} (hφ : Measurable φ) (iφ : MemLp φ 2 (μ.prod μ))
include hφ iφ

theorem iid_ordered_pair_mean {m : ℕ} :
    (∫ x : Fin m → X, ∑ p : Fin m × Fin m, orderedRow φ p x ∂Measure.pi fun _ : Fin m => μ) =
      (m : ℝ) * ((m : ℝ) - 1) * ∫ p, φ p ∂μ.prod μ := by
  classical
  rw [integral_finsetSum _ (fun p _ => (orderedRow_memLp μ iφ p).integrable one_le_two)]
  have he : ∀ p : Fin m × Fin m,
      (∫ x, orderedRow φ p x ∂Measure.pi fun _ : Fin m => μ) =
      (∫ z, φ z ∂μ.prod μ) - if p.1 = p.2 then (∫ z, φ z ∂μ.prod μ) else 0 := by
    intro p
    by_cases hp : p.1 = p.2
    · simp [orderedRow, hp]
    · simp only [orderedRow, hp, ite_false, sub_zero]
      exact pair_mean μ hφ hp
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_sub_distrib]
  ring

theorem shared_pair_le_second :
    (∫ p : X × (X × X), φ (p.1, p.2.1) * φ (p.1, p.2.2) ∂μ.prod (μ.prod μ)) ≤
      ∫ p, φ p ^ 2 ∂μ.prod μ := by
  let P := Measure.pi fun _ : Fin 3 => μ
  let f : (Fin 3 → X) → ℝ := fun x => φ (x 0, x 1)
  let g : (Fin 3 → X) → ℝ := fun x => φ (x 0, x 2)
  have iF : MemLp f 2 P := pair_memLp μ iφ (by decide)
  have iG : MemLp g 2 P := pair_memLp μ iφ (by decide)
  have hb := integral_mono (iF.integrable_mul iG) ((iF.integrable_sq.add iG.integrable_sq).div_const 2)
    (fun x => show f x * g x ≤ (f x ^ 2 + g x ^ 2) / 2 by nlinarith [sq_nonneg (f x - g x)])
  change (∫ x, f x * g x ∂P) ≤ (∫ x, (f x ^ 2 + g x ^ 2) / 2 ∂P) at hb
  rw [integral_div, integral_add iF.integrable_sq iG.integrable_sq] at hb
  have ef : (∫ x, f x ^ 2 ∂P) = ∫ p, φ p ^ 2 ∂μ.prod μ :=
    pair_mean μ (hφ.pow_const 2) (by decide : (0 : Fin 3) ≠ 1)
  have eg : (∫ x, g x ^ 2 ∂P) = ∫ p, φ p ^ 2 ∂μ.prod μ :=
    pair_mean μ (hφ.pow_const 2) (by decide : (0 : Fin 3) ≠ 2)
  rw [ef, eg] at hb
  have hm : Measurable (fun p : X × (X × X) => φ (p.1, p.2.1) * φ (p.1, p.2.2)) :=
    (hφ.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hφ.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have mp := iid_triple μ (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (0 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 2)
  have he := integral_map (μ := P) mp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [mp.map_eq] at he
  change (∫ p : X × (X × X), φ (p.1, p.2.1) * φ (p.1, p.2.2) ∂μ.prod (μ.prod μ)) =
    ∫ x, f x * g x ∂P at he
  rw [he]
  linarith

theorem iid_ordered_pair_variance_bound {m : ℕ} (hm : 2 ≤ m)
    (hsym : ∀ x y, φ (x, y) = φ (y, x)) :
    Var[fun x : Fin m → X => ∑ p : Fin m × Fin m, orderedRow φ p x;
      Measure.pi fun _ : Fin m => μ] ≤
      (4 * (m : ℝ) ^ 3 + 2 * (m : ℝ) ^ 2) * ∫ p, φ p ^ 2 ∂μ.prod μ := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 0 ≤ (m : ℝ) - 1 := by linarith
  have hm2 : 0 ≤ (m : ℝ) - 2 := by linarith
  let E := ∫ p, φ p ^ 2 ∂μ.prod μ
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hv := iid_ordered_pair_variance (m := m) μ hφ iφ hsym rfl rfl
  rw [hv]
  have h1 := shared_pair_le_second μ hφ iφ
  have hmean := sq_nonneg (∫ p, φ p ∂μ.prod μ)
  have hz1 : (∫ p : X × (X × X), φ (p.1, p.2.1) * φ (p.1, p.2.2)
      ∂μ.prod (μ.prod μ)) - (∫ p, φ p ∂μ.prod μ) ^ 2 ≤ E := by dsimp [E]; linarith
  have hz2 : E - (∫ p, φ p ∂μ.prod μ) ^ 2 ≤ E := sub_le_self _ hmean
  have hc1 : 0 ≤ 4 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by positivity
  have hc2 : 0 ≤ 2 * (m : ℝ) * ((m : ℝ) - 1) := by positivity
  have h := add_le_add (mul_le_mul_of_nonneg_left hz1 hc1) (mul_le_mul_of_nonneg_left hz2 hc2)
  apply h.trans
  have ha : (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) ≤ (m : ℝ) ^ 3 := by nlinarith
  have hb : (m : ℝ) * ((m : ℝ) - 1) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hc := mul_le_mul_of_nonneg_right (show
    4 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) + 2 * (m : ℝ) * ((m : ℝ) - 1) ≤
      4 * (m : ℝ) ^ 3 + 2 * (m : ℝ) ^ 2 by nlinarith) hE
  nlinarith [hc]

end
end BstLean.Part218
#print axioms BstLean.Part218.iid_ordered_pair_variance_bound
