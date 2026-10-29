import BstLean.Part57Defs
import BstLean.Part56Key_Energy

/-! Algebra and bounded measurability for normalized Gaussian projections onto frame complements. -/

namespace BstLean.Part57.KeyProof
open MeasureTheory BstLean.Part29 BstLean.Part56
open BstLean.Part41 (Mono)
variable {n r : ℕ}

def pvec (V : Fin r → Fin n → ℝ) (g : Fin n → ℝ) : Fin n → ℝ :=
  fun i => g i - ∑ a, coordY V g a * V a i

lemma span_sq (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (y : Fin r → ℝ) :
    ∑ i, spanV V y i ^ 2 = ∑ a, y a ^ 2 := by
  simp only [spanV, sq, Finset.sum_mul_sum]
  have he : (∑ i, ∑ a, ∑ b, y a * V a i * (y b * V b i)) =
      ∑ a, ∑ b, y a * y b * ∑ i, V a i * V b i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  simp only [show ∀ a b : Fin r, ∑ i, V a i * V b i = if a = b then 1 else 0 from hV]
  simp

lemma rho_eq (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (x : Fin n → ℝ) :
    rhoSq V x = ∑ i, x i ^ 2 - ∑ a, coordY V x a ^ 2 := by
  have hsq := span_sq V hV (coordY V x)
  have hcross : ∑ l, x l * ∑ a, coordY V x a * V a l = ∑ a, coordY V x a ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : ∑ l, x l * (coordY V x a * V a l) = coordY V x a * ∑ l, V a l * x l := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; ring
    rw [this, sq]
    rfl
  unfold rhoSq
  have hexp : ∑ l, (x l - ∑ a, coordY V x a * V a l) ^ 2 =
      ∑ l, x l ^ 2 - 2 * ∑ l, x l * ∑ a, coordY V x a * V a l +
        ∑ l, (∑ a, coordY V x a * V a l) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hexp, hcross]
  change _ - _ + (∑ i, spanV V (coordY V x) i ^ 2) = _
  rw [hsq]
  ring

lemma pvec_contract (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (g : Fin n → ℝ) :
    ∑ i, pvec V g i ^ 2 ≤ ∑ i, g i ^ 2 := by
  change rhoSq V g ≤ _
  rw [rho_eq V hV]
  exact sub_le_self _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma pvec_orth (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (g : Fin n → ℝ) (a : Fin r) :
    ∑ i, V a i * pvec V g i = 0 := by
  simp only [pvec, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  have he : (∑ b, ∑ i, V a i * (coordY V g b * V b i)) = coordY V g a := by
    have hi (b : Fin r) : (∑ i, V a i * (coordY V g b * V b i)) =
        coordY V g b * ∑ i, V a i * V b i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simp_rw [hi, show ∀ a b : Fin r, ∑ i, V a i * V b i = if a = b then 1 else 0 from hV]
    simp
  rw [he]
  exact sub_self _

lemma dir_sq (V : Fin r → Fin n → ℝ) (g : Fin n → ℝ) :
    ∑ i, perpDirR V g i ^ 2 ≤ 1 := by
  let q : ℝ := ∑ i, pvec V g i ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  change (∑ i, ((1 / Real.sqrt q) * pvec V g i) ^ 2) ≤ 1
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, div_pow, one_pow, Real.sq_sqrt hq]
  by_cases hz : q = 0
  · simp [hz]
  · rw [one_div_mul_cancel hz]

lemma dir_abs (V : Fin r → Fin n → ℝ) (g : Fin n → ℝ) (i : Fin n) :
    |perpDirR V g i| ≤ 1 := by
  have hs := (Finset.single_le_sum (fun l _ => sq_nonneg (perpDirR V g l))
    (Finset.mem_univ i)).trans (dir_sq V g)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (perpDirR V g i + 1), sq_nonneg (perpDirR V g i - 1)]

lemma dir_orth (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (y : Fin r → ℝ)
    (g : Fin n → ℝ) : dot56 (spanV V y) (perpDirR V g) = 0 := by
  change (∑ i, (∑ a, y a * V a i) * ((1 / Real.sqrt (rhoSq V g)) * pvec V g i)) = 0
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (a : Fin r) : (∑ i, y a * V a i * ((1 / Real.sqrt (rhoSq V g)) * pvec V g i)) =
      (y a * (1 / Real.sqrt (rhoSq V g))) * ∑ i, V a i * pvec V g i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [he, pvec_orth V hV, mul_zero]
  simp

lemma measurable_dir (V : Fin r → Fin n → ℝ) : Measurable (perpDirR V) := by
  have hm (i : Fin n) : Measurable (fun g => pvec V g i) := by
    unfold pvec coordY
    fun_prop
  have hq : Measurable (fun g => rhoSq V g) := by
    change Measurable (fun g => ∑ i, pvec V g i ^ 2)
    exact Finset.measurable_sum _ fun i _ => (hm i).pow_const 2
  apply Measurable.of_eval
  intro i
  exact (measurable_const.div hq.sqrt).mul (hm i)

lemma integrable_cont_dir (V : Fin r → Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) : Integrable (fun g => f (perpDirR V g)) (stdGauss (Fin n)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound (hf.measurable.comp (measurable_dir V)).aestronglyMeasurable C
  filter_upwards [] with g
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · exact (abs_le.mp (dir_abs V g i)).1
  · exact (abs_le.mp (dir_abs V g i)).2

lemma dot_pvec (V : Fin r → Fin n → ℝ) (a g : Fin n → ℝ) :
    dot56 a (pvec V g) = dot56 (pvec V a) g := by
  have he (a g : Fin n → ℝ) : dot56 a (pvec V g) = dot56 a g - ∑ b, coordY V a b * coordY V g b := by
    simp only [dot56, pvec, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    unfold coordY
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hd (a g : Fin n → ℝ) : dot56 a g = dot56 g a := by
    unfold dot56
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hd (pvec V a), he, he, hd g a]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  ring

end BstLean.Part57.KeyProof
