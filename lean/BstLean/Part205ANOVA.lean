import BstLean.Part142Spread

/-! Exact pair ANOVA for one bounded measurable field under independent inputs. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part139

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : ℕ} (z : Ω → Fin m → ℝ) (hz : ∀ i, BM (fun x => z x i))

noncomputable def meanDirection (x : Ω) : ℝ :=
  ∑ i, (z x i - meanV μ z i) * meanV μ z i

include hz

lemma meanDirection_bm : BM (meanDirection μ z) :=
  BM.sum _ fun i _ => ((hz i).sub (BM.const _)).mul (BM.const _)

lemma centred_coordinate_mean (i : Fin m) :
    ∫ x, (z x i - meanV μ z i) ∂μ = 0 := by
  rw [integral_sub ((hz i).integrable μ) (integrable_const _)]
  simp [meanV]

lemma meanDirection_zero : ∫ x, meanDirection μ z x ∂μ = 0 := by
  unfold meanDirection
  rw [integral_finsetSum _ (fun i _ => (((hz i).sub (BM.const _)).mul (BM.const _)).integrable μ)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_mul_const, centred_coordinate_mean μ z hz i, zero_mul]

/-- The scalar directional moment is exactly the covariance quadratic form. -/
lemma meanDirection_second :
    (∫ x, meanDirection μ z x ^ 2 ∂μ) =
      ∑ i, ∑ j, meanV μ z i * covV μ z i j * meanV μ z j := by
  let ξ := fun x i => z x i - meanV μ z i
  have hξ : ∀ i, BM (fun x => ξ x i) := fun i => (hz i).sub (BM.const _)
  have he : (fun x => meanDirection μ z x ^ 2) = fun x =>
      ∑ i, ∑ j, (meanV μ z i * meanV μ z j) * (ξ x i * ξ x j) := by
    funext x
    unfold meanDirection
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [ξ]
    ring
  have hi : ∀ i j, Integrable
      (fun x => (meanV μ z i * meanV μ z j) * (ξ x i * ξ x j)) μ :=
    fun i j => (((hξ i).mul (hξ j)).integrable μ).const_mul _
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  change (meanV μ z i * meanV μ z j) * covV μ z i j = _
  ring

/-- The three centred pair terms are orthogonal under the product input distribution. -/
theorem pair_anova :
    (∫ p : Ω × Ω, (dotp (z p.1) (z p.2) - normSq (meanV μ z)) ^ 2 ∂μ.prod μ) =
      (∑ i, ∑ j, covV μ z i j ^ 2) + 2 * (∫ x, meanDirection μ z x ^ 2 ∂μ) := by
  let a := meanV μ z
  let ξ := fun x i => z x i - a i
  have hξ : ∀ i, BM (fun x => ξ x i) := fun i => (hz i).sub (BM.const _)
  have hξ0 : ∀ i, ∫ x, ξ x i ∂μ = 0 := fun i => centred_coordinate_mean μ z hz i
  let P : Ω × Ω → ℝ := fun p => ∑ i, ξ p.1 i * ξ p.2 i
  let R : Ω × Ω → ℝ := fun p => meanDirection μ z p.1 + meanDirection μ z p.2
  have hP : BM P := BM.sum _ fun i _ => (hξ i).fst.mul (hξ i).snd
  have hr := meanDirection_bm μ z hz
  have hR : BM R := hr.fst.add hr.snd
  have hexp : ∀ p : Ω × Ω, dotp (z p.1) (z p.2) - normSq a = P p + R p := by
    intro p
    unfold dotp normSq P R meanDirection
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ξ, a]
    ring
  have hPP : (∫ p, P p ^ 2 ∂μ.prod μ) = ∑ i, ∑ j, covV μ z i j ^ 2 := by
    have he : (fun p => P p ^ 2) = fun p : Ω × Ω =>
        ∑ i, ∑ j, (ξ p.1 i * ξ p.1 j) * (ξ p.2 i * ξ p.2 j) := by
      funext p
      dsimp [P]
      rw [pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hi : ∀ i j, Integrable
        (fun p : Ω × Ω => (ξ p.1 i * ξ p.1 j) * (ξ p.2 i * ξ p.2 j)) (μ.prod μ) :=
      fun i j => ((hξ i).mul (hξ j)).integrable μ |>.mul_prod (((hξ i).mul (hξ j)).integrable μ)
    rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_prod_mul (fun x => ξ x i * ξ x j) (fun x => ξ x i * ξ x j), pow_two]
    rfl
  have hPR : (∫ p, P p * R p ∂μ.prod μ) = 0 := by
    have he : (fun p => P p * R p) = fun p : Ω × Ω =>
        ∑ i, ((ξ p.1 i * meanDirection μ z p.1) * ξ p.2 i +
          ξ p.1 i * (ξ p.2 i * meanDirection μ z p.2)) := by
      funext p
      dsimp [P, R]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hi1 : ∀ i, Integrable
        (fun p : Ω × Ω => (ξ p.1 i * meanDirection μ z p.1) * ξ p.2 i) (μ.prod μ) :=
      fun i => (((hξ i).mul hr).integrable μ).mul_prod ((hξ i).integrable μ)
    have hi2 : ∀ i, Integrable
        (fun p : Ω × Ω => ξ p.1 i * (ξ p.2 i * meanDirection μ z p.2)) (μ.prod μ) :=
      fun i => ((hξ i).integrable μ).mul_prod (((hξ i).mul hr).integrable μ)
    have hi12 : ∀ i, Integrable (fun p : Ω × Ω =>
        (ξ p.1 i * meanDirection μ z p.1) * ξ p.2 i +
          ξ p.1 i * (ξ p.2 i * meanDirection μ z p.2)) (μ.prod μ) :=
      fun i => (hi1 i).add (hi2 i)
    rw [he, integral_finsetSum _ (fun i _ => hi12 i)]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_add (hi1 i) (hi2 i),
      integral_prod_mul (fun x => ξ x i * meanDirection μ z x) (fun x => ξ x i),
      integral_prod_mul (fun x => ξ x i) (fun x => ξ x i * meanDirection μ z x), hξ0 i]
    simp
  have hRR : (∫ p, R p ^ 2 ∂μ.prod μ) = 2 * (∫ x, meanDirection μ z x ^ 2 ∂μ) := by
    have he : (fun p => R p ^ 2) = fun p : Ω × Ω =>
        meanDirection μ z p.1 ^ 2 + 2 * (meanDirection μ z p.1 * meanDirection μ z p.2) +
          meanDirection μ z p.2 ^ 2 := by funext p; dsimp [R]; ring
    have i1 : Integrable (fun p : Ω × Ω => meanDirection μ z p.1 ^ 2) (μ.prod μ) :=
      hr.sq.fst.integrable _
    have i12 : Integrable (fun p : Ω × Ω => 2 * (meanDirection μ z p.1 * meanDirection μ z p.2))
        (μ.prod μ) := (hr.fst.mul hr.snd).integrable _ |>.const_mul 2
    have i2 : Integrable (fun p : Ω × Ω => meanDirection μ z p.2 ^ 2) (μ.prod μ) :=
      hr.sq.snd.integrable _
    have iA : Integrable (fun p : Ω × Ω => meanDirection μ z p.1 ^ 2 +
        2 * (meanDirection μ z p.1 * meanDirection μ z p.2)) (μ.prod μ) := i1.add i12
    rw [he, integral_add iA i2, integral_add i1 i12, integral_const_mul,
      integral_prod_mul, meanDirection_zero μ z hz,
      integral_prod (fun p : Ω × Ω => meanDirection μ z p.1 ^ 2) i1,
      integral_prod_symm (fun p : Ω × Ω => meanDirection μ z p.2 ^ 2) i2]
    simp
    <;> ring
  have he2 : (fun p : Ω × Ω => (dotp (z p.1) (z p.2) - normSq a) ^ 2) =
      fun p => P p ^ 2 + 2 * (P p * R p) + R p ^ 2 := by
    funext p
    rw [hexp]
    ring
  have iA : Integrable (fun p => P p ^ 2 + 2 * (P p * R p)) (μ.prod μ) :=
    (hP.sq.integrable _).add ((hP.mul hR).integrable _ |>.const_mul 2)
  rw [he2, integral_add iA (hR.sq.integrable _),
    integral_add (hP.sq.integrable _) ((hP.mul hR).integrable _ |>.const_mul 2),
    integral_const_mul, hPP, hPR, hRR]
  ring

end
end BstLean.Part205

#print axioms BstLean.Part205.meanDirection_second
#print axioms BstLean.Part205.pair_anova
