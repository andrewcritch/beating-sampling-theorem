import BstLean.Part57PropD_Average
import BstLean.Part56Key_Energy

/-! Dimension-independent bounds for the perpendicular feature in Prop D. -/
namespace BstLean.Part57.PropD57
open BstLean.Part41 (Mono)
open BstLean.Part56 (PhiJI dot56 tensorCoeff56 enum56)
variable {n r : ℕ}

private theorem sum_injective_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (F : κ → ℝ) (hF : ∀ q, 0 ≤ F q) :
    (∑ p, F (f p)) ≤ ∑ q, F q := by
  classical
  calc
    _ = ∑ q ∈ Finset.univ.image f, F q := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑ q, F q := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun q _ _ => hF q)

/-- Orthogonality gives a coefficient bound without vector-valued interpolation. -/
theorem PhiJI_norm_sq_le (d j i : ℕ) (hj : j ≤ d) (a w : Fin n → ℝ)
    (ha : ∑ l, a l ^ 2 ≤ 1) (hw : ∑ l, w l ^ 2 ≤ 1)
    (haw : dot56 a w = 0) :
    ∑ p : Mono n d, PhiJI d j i a w p ^ 2 ≤ (2 : ℝ) ^ j := by
  classical
  have he := BstLean.Part56.PhiJI_inner_block56 d j i i hj a a w w
  simp only [← pow_two] at he
  rw [he]
  apply (sum_injective_le (enum56 : Sym (Fin n) j → Fin j → Fin n)
    BstLean.Part56.enum_injective56 (fun τ => tensorCoeff56 j i a w τ ^ 2)
    (fun _ => sq_nonneg _)).trans
  have he' := BstLean.Part56.tensorCoeff_inner56 j i a w w haw haw
  simp only [← pow_two] at he'
  rw [he']
  have ha0 : 0 ≤ dot56 a a := by unfold dot56; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hw0 : 0 ≤ dot56 w w := by unfold dot56; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have ha1 : dot56 a a ≤ 1 := by simpa only [dot56, ← pow_two] using ha
  have hw1 : dot56 w w ≤ 1 := by simpa only [dot56, ← pow_two] using hw
  calc
    _ ≤ (j.choose i : ℝ) * 1 * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (pow_le_one₀ ha0 ha1) (Nat.cast_nonneg _)
      · exact pow_le_one₀ hw0 hw1
      · exact pow_nonneg hw0 _
      · positivity
    _ = (j.choose i : ℝ) := by ring
    _ ≤ (2 : ℝ) ^ j := by exact_mod_cast Nat.choose_le_two_pow j i

/-- Each frame column is orthogonal to the normalized perpendicular projection. -/
theorem perpDirR_orthogonal (V : Fin r → Fin n → ℝ) (hV : OrthoF V)
    (g : Fin n → ℝ) (a : Fin r) :
    ∑ i, V a i * perpDirR V g i = 0 := by
  classical
  let c : ℝ := 1 / Real.sqrt (∑ i, (g i - ∑ b, coordY V g b * V b i) ^ 2)
  have he (i : Fin n) : V a i * perpDirR V g i =
      c * (V a i * g i - ∑ b, coordY V g b * (V a i * V b i)) := by
    have hs : (∑ b, coordY V g b * (V a i * V b i)) =
        V a i * ∑ b, coordY V g b * V b i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    simp only [perpDirR, Pi.smul_apply, smul_eq_mul, hs, c]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_comm]
  simp_rw [← Finset.mul_sum,
    show ∀ a b : Fin r, ∑ i, V a i * V b i = if a = b then 1 else 0 from hV]
  simp [coordY]

theorem spanV_perpDirR_orthogonal (V : Fin r → Fin n → ℝ) (hV : OrthoF V)
    (y : Fin r → ℝ) (g : Fin n → ℝ) :
    dot56 (spanV V y) (perpDirR V g) = 0 := by
  unfold dot56 spanV
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, perpDirR_orthogonal V hV g, mul_zero]
  simp

/-- A uniform bound on the squared norm of the divided perpendicular feature. -/
theorem psiHatR_norm_sq_le (d j : ℕ) (hj : j ≤ d) (u : ℝ) (a w : Fin n → ℝ)
    (ha : ∑ l, a l ^ 2 ≤ 1) (hw : ∑ l, w l ^ 2 ≤ 1)
    (haw : dot56 a w = 0) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∑ p : Mono n d, psiHatR d j u a w p ^ 2 ≤ (j : ℝ) ^ 2 * 2 ^ j := by
  classical
  have hU : (∑ i ∈ Finset.range j, (u ^ i) ^ 2) ≤ (j : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range j, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        pow_le_one₀ (pow_nonneg hu0 i) (pow_le_one₀ hu0 hu1)
      _ = _ := by simp
  have hp (p : Mono n d) : psiHatR d j u a w p ^ 2 ≤
      (j : ℝ) * ∑ i ∈ Finset.range j, PhiJI d j (i + 1) a w p ^ 2 := by
    simp only [psiHatR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range j) (fun i => u ^ i)
      (fun i => PhiJI d j (i + 1) a w p)).trans
        (mul_le_mul_of_nonneg_right hU (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ p : Mono n d, (j : ℝ) * ∑ i ∈ Finset.range j, PhiJI d j (i + 1) a w p ^ 2 :=
      Finset.sum_le_sum fun p _ => hp p
    _ = (j : ℝ) * ∑ i ∈ Finset.range j, ∑ p : Mono n d, PhiJI d j (i + 1) a w p ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (j : ℝ) * ∑ _i ∈ Finset.range j, (2 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        PhiJI_norm_sq_le d j (i + 1) hj a w ha hw haw) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two, mul_assoc]

/-- The squared norm bound for the actual frame and Gaussian perpendicular direction. -/
theorem psiHatR_frame_norm_sq_le (d j : ℕ) (hj : j ≤ d)
    (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (y : Fin r → ℝ) (g : Fin n → ℝ)
    (u : ℝ) (hy : ∑ a, y a ^ 2 ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∑ p : Mono n d, psiHatR d j u (spanV V y) (perpDirR V g) p ^ 2 ≤
      (j : ℝ) ^ 2 * 2 ^ j :=
  psiHatR_norm_sq_le d j hj u _ _ ((spanV_sumsq V hV y).trans_le hy)
    (perpDirR_sumsq_le_one V g) (spanV_perpDirR_orthogonal V hV y g) hu0 hu1


end BstLean.Part57.PropD57
