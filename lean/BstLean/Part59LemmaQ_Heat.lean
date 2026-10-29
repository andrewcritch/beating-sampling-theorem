import BstLean.Part59LemmaQ_Shift
import BstLean.Part53Error_Heat

namespace BstLean.Part59
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open BstLean.Part41
open BstLean.Part53 (fvA heatA)
open BstLean.Part29 (stdGauss)
noncomputable section

private lemma reindex59x {R : Type*} [AddCommMonoid R] (k : ℕ) (g : ℕ → ℕ → R) :
    (∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j / 2 + 1), g j i) =
      ∑ c ∈ Finset.range (k + 1),
        ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k), g (c + 2 * i) i := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun p => ⟨p.1 - 2 * p.2, p.2⟩)
    (fun q => ⟨q.1 + 2 * q.2, q.2⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hp ⊢
    omega
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hq ⊢
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    apply Sigma.ext
    · dsimp; omega
    · rfl
  · intro q hq
    ext <;> simp
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    simp only
    congr 1
    omega

lemma heat_weight59x (v : ℝ) (c i : ℕ) :
    (v / 2) ^ i / (i.factorial : ℝ) *
      (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ)) =
        (cQ (c + 2 * i) i : ℝ) * v ^ i := by
  simp only [cQ, Nat.add_sub_cancel_right, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, div_pow]
  field_simp

lemma heat_integral_unit59x {n : ℕ} (k : ℕ) (A : Tens n)
    (hA : ∀ j, IsSymmT (A j)) (y : Fin n → ℝ) :
    gaussianExpectation59x (shift59x y
      (∑ j ∈ Finset.range (k + 1), plainL j (Tl A j))) =
      fvA k (heatA k 1 A) y := by
  classical
  simp_rw [plain_expand _ _ (Tl_perm A _ (hA _)), map_sum,
    map_mul]
  have hc (r : ℝ) : shift59x y (MvPolynomial.C r) = MvPolynomial.C r := by
    simp [shift59x]
  simp_rw [hc, gaussianExpectation_C_mul59x, shifted_wick_expectation59x]
  rw [reindex59x]
  unfold fvA
  apply Finset.sum_congr rfl
  intro c hc
  unfold contr heatA
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [heat_weight59x]
  simp only [one_pow, mul_one, Finset.mul_sum]
  let e : (Fin (c + 2 * i - 2 * i) → Fin n) ≃ (Fin c → Fin n) :=
    Equiv.arrowCongr (finCongr (Nat.add_sub_cancel_right c (2 * i))) (Equiv.refl _)
  apply Finset.sum_equiv e (by simp)
  intro w hw
  dsimp [e, Equiv.arrowCongr]
  have ht : traceL i (Tl A (c + 2 * i)) (List.ofFn w) =
      trL i (A (c + 2 * i)) (fun t => w ⟨t.1, by have := t.2; omega⟩) := by
    unfold traceL trL
    apply Finset.sum_congr rfl
    intro u hu
    unfold Tl
    have hl : (dblL u ++ List.ofFn w).length = c + 2 * i := by
      simp only [List.length_append, dblL_length, List.length_ofFn]
      omega
    rw [dif_pos hl]
    congr 1
    funext t
    unfold glue
    simp only [List.get_eq_getElem, Fin.val_cast]
    split_ifs with h
    · rw [List.getElem_append_left (by rw [dblL_length]; exact h), dblL_getElem]
    · rw [List.getElem_append_right (by rw [dblL_length]; omega)]
      simp [dblL_length]
  rw [ht]
  have hp : (∏ t, y (w t)) = ∏ x : Fin c, y (w ((finCongr
      (Nat.add_sub_cancel_right c (2 * i))).symm x)) :=
    ((finCongr (Nat.add_sub_cancel_right c (2 * i))).symm.prod_comp (fun t => y (w t))).symm
  rw [hp]
  rw [← mul_assoc]
  congr 1

lemma eval_shift59x {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y Z : ι → ℝ) (p : MvPolynomial ι ℝ) :
    MvPolynomial.eval Z (shift59x y p) = MvPolynomial.eval (fun i => Z i + y i) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [shift59x]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    simp [shift59x]

lemma heat_integral_unit_eval59x {n : ℕ} (k : ℕ) (A : Tens n)
    (hA : ∀ j, IsSymmT (A j)) (y : Fin n → ℝ) :
    (∫ Z, fvA k A (fun i => y i + Z i) ∂stdGauss (Fin n)) =
      fvA k (heatA k 1 A) y := by
  have h := heat_integral_unit59x k A hA y
  change (∫ Z, MvPolynomial.eval Z (shift59x y
      (∑ j ∈ Finset.range (k + 1), plainL j (Tl A j))) ∂stdGauss (Fin n)) = _ at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with Z
  rw [eval_shift59x, map_sum]
  unfold fvA
  apply Finset.sum_congr rfl
  intro j hj
  rw [eval_plainL]
  simp only [contr, Tl_ofFn]
  simp_rw [add_comm (Z _) (y _)]

def degreeScale59x {n : ℕ} (s : ℝ) (A : Tens n) : Tens n := fun j w => s ^ j * A j w

lemma heat_scale59x {n : ℕ} (k : ℕ) (s : ℝ) (hs : s ≠ 0) (A : Tens n)
    (y : Fin n → ℝ) :
    fvA k (heatA k 1 (degreeScale59x s A)) (fun i => y i / s) =
      fvA k (heatA k (s ^ 2) A) y := by
  classical
  unfold fvA
  apply Finset.sum_congr rfl
  intro c hc
  unfold contr
  apply Finset.sum_congr rfl
  intro w hw
  unfold heatA
  simp_rw [Finset.sum_mul, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro i hi
  rw [heat_weight59x, heat_weight59x]
  simp only [one_pow, mul_one, trL, degreeScale59x, ← Finset.mul_sum]
  rw [pow_add, pow_mul]
  field_simp

lemma fvA_scale59x {n : ℕ} (k : ℕ) (s : ℝ) (hs : s ≠ 0) (A : Tens n)
    (y Z : Fin n → ℝ) :
    fvA k (degreeScale59x s A) (fun i => y i / s + Z i) =
      fvA k A (fun i => y i + s * Z i) := by
  classical
  unfold fvA
  apply Finset.sum_congr rfl
  intro j hj
  unfold contr degreeScale59x
  apply Finset.sum_congr rfl
  intro w hw
  have hp : s ^ j * ∏ t : Fin j, (y (w t) / s + Z (w t)) =
      ∏ t : Fin j, (y (w t) + s * Z (w t)) := by
    rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t ht
    field_simp
  change s ^ j * A j w * (∏ t, (y (w t) / s + Z (w t))) =
    A j w * ∏ t, (y (w t) + s * Z (w t))
  calc
    _ = A j w * (s ^ j * ∏ t, (y (w t) / s + Z (w t))) := by ring
    _ = _ := by rw [hp]

lemma heat_integral_square59x {n : ℕ} (k : ℕ) (s : ℝ) (hs : s ≠ 0)
    (A : Tens n) (hA : ∀ j, IsSymmT (A j)) (y : Fin n → ℝ) :
    (∫ Z, fvA k A (fun i => y i + s * Z i) ∂stdGauss (Fin n)) =
      fvA k (heatA k (s ^ 2) A) y := by
  have hsym : ∀ j, IsSymmT (degreeScale59x s A j) := by
    intro j σ w
    simp only [degreeScale59x, hA j σ w]
  have h := heat_integral_unit_eval59x k (degreeScale59x s A) hsym (fun i => y i / s)
  simp_rw [fvA_scale59x k s hs A y] at h
  exact h.trans (heat_scale59x k s hs A y)

end
end BstLean.Part59
