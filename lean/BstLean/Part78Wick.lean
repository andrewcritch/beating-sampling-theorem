import BstLean.Part78Defs
import BstLean.Part35Wick

/-!
# Part 78, wave 1: Gaussian moment identities (`GaussLin`, `WickTwoPoint`, `AffFourth 3`)
-/

namespace BstLean.Part78

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part35 (stdGauss_wick_step stdGauss_prod_integrable)

section Lin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Coordinate moments -/

lemma w_one (a : ι) : (∫ z, z a ∂stdGauss ι) = 0 := by
  have hw := stdGauss_wick_step a 0 (Fin.elim0 : Fin 0 → ι)
  simpa using hw

lemma w_two (a b : ι) : (∫ z, z a * z b ∂stdGauss ι) = if a = b then 1 else 0 := by
  have hw := stdGauss_wick_step a 1 ![b]
  simpa [Fin.sum_univ_succ, Fin.prod_univ_succ, eq_comm] using hw

lemma w_three (a b c : ι) : (∫ z, z a * z b * z c ∂stdGauss ι) = 0 := by
  have hw := stdGauss_wick_step a 2 ![b, c]
  rw [show (Finset.univ : Finset (Fin 2)) = {0,1} by decide] at hw
  norm_num [Finset.erase_insert_of_ne, Finset.erase_insert, Fin.prod_univ_succ, w_one] at hw
  simpa [mul_assoc] using hw

private lemma delta_mul (p : Prop) [Decidable p] (x : ℝ) :
    (if p then x else 0) = (if p then (1 : ℝ) else 0) * x := by
  split_ifs <;> simp

lemma w_four (a b c d : ι) :
    (∫ z, z a * z b * z c * z d ∂stdGauss ι) =
      (if a = b then (1 : ℝ) else 0) * (if c = d then (1 : ℝ) else 0) +
      (if a = c then (1 : ℝ) else 0) * (if b = d then (1 : ℝ) else 0) +
      (if a = d then (1 : ℝ) else 0) * (if b = c then (1 : ℝ) else 0) := by
  have hw := stdGauss_wick_step a 3 ![b,c,d]
  rw [show (Finset.univ : Finset (Fin 3)) = {0,1,2} by decide] at hw
  norm_num [Finset.erase_insert_of_ne, Finset.erase_insert, Fin.prod_univ_succ] at hw
  try dsimp at hw
  simp_rw [← mul_assoc, w_two] at hw
  rw [delta_mul (b = a), delta_mul (c = a), delta_mul (d = a)] at hw
  simp only [show b = a ↔ a = b from eq_comm,
    show c = a ↔ a = c from eq_comm, show d = a ↔ a = d from eq_comm] at hw
  convert hw using 1 <;> ring

lemma i_one (a : ι) : Integrable (fun z : ι → ℝ => z a) (stdGauss ι) := by
  simpa [Fin.prod_univ_succ] using stdGauss_prod_integrable 1 ![a]

lemma i_two (a b : ι) : Integrable (fun z : ι → ℝ => z a * z b) (stdGauss ι) := by
  simpa [Fin.prod_univ_succ, mul_assoc] using stdGauss_prod_integrable 2 ![a, b]

lemma i_three (a b c : ι) : Integrable (fun z : ι → ℝ => z a * z b * z c) (stdGauss ι) := by
  simpa [Fin.prod_univ_succ, mul_assoc] using stdGauss_prod_integrable 3 ![a, b, c]

lemma i_four (a b c d : ι) :
    Integrable (fun z : ι → ℝ => z a * z b * z c * z d) (stdGauss ι) := by
  simpa [Fin.prod_univ_succ, mul_assoc] using stdGauss_prod_integrable 4 ![a, b, c, d]

/-! ### Linear forms -/

/-- The linear form `b·u`. -/
def lin (b : ι → ℝ) (u : ι → ℝ) : ℝ := ∑ j, b j * u j

/-- The dot product. -/
def dot (b c : ι → ℝ) : ℝ := ∑ j, b j * c j

lemma lin1_int (a : ι → ℝ) : Integrable (fun u => lin a u) (stdGauss ι) := by
  unfold lin
  exact integrable_finsetSum _ (fun j _ => (i_one j).const_mul _)

lemma lin1 (a : ι → ℝ) : ∫ u, lin a u ∂stdGauss ι = 0 := by
  unfold lin
  rw [integral_finsetSum _ (fun j _ => (i_one j).const_mul _)]
  simp [integral_const_mul, w_one]

lemma lin2_ex (a b : ι → ℝ) (u : ι → ℝ) :
    lin a u * lin b u = ∑ j, ∑ k, (a j * b k) * (u j * u k) := by
  unfold lin
  rw [Finset.sum_mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

lemma lin2_int (a b : ι → ℝ) : Integrable (fun u => lin a u * lin b u) (stdGauss ι) := by
  simp_rw [lin2_ex]
  exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    (i_two j k).const_mul _))

lemma lin2 (a b : ι → ℝ) : ∫ u, lin a u * lin b u ∂stdGauss ι = dot a b := by
  simp_rw [lin2_ex]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    (i_two j k).const_mul _))]
  simp_rw [integral_finsetSum _ (fun k _ => (i_two _ k).const_mul _), integral_const_mul, w_two]
  simp [dot]

lemma lin3_ex (a b c : ι → ℝ) (u : ι → ℝ) :
    lin a u * lin b u * lin c u = ∑ j, ∑ k, ∑ l, (a j * b k * c l) * (u j * u k * u l) := by
  rw [lin2_ex]
  simp_rw [Finset.sum_mul]
  unfold lin
  simp_rw [Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

lemma lin3_int (a b c : ι → ℝ) :
    Integrable (fun u => lin a u * lin b u * lin c u) (stdGauss ι) := by
  simp_rw [lin3_ex]
  exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun l _ => (i_three j k l).const_mul _)))

lemma lin3 (a b c : ι → ℝ) : ∫ u, lin a u * lin b u * lin c u ∂stdGauss ι = 0 := by
  simp_rw [lin3_ex]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun l _ => (i_three j k l).const_mul _)))]
  simp_rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
    (i_three _ k l).const_mul _)),
    integral_finsetSum _ (fun l _ => (i_three _ _ l).const_mul _), integral_const_mul, w_three]
  simp

lemma lin4_ex (a b c d : ι → ℝ) (u : ι → ℝ) :
    lin a u * lin b u * lin c u * lin d u =
      ∑ j, ∑ k, ∑ l, ∑ m, (a j * b k * c l * d m) * (u j * u k * u l * u m) := by
  rw [lin3_ex]
  simp_rw [Finset.sum_mul]
  unfold lin
  simp_rw [Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

lemma lin4_int (a b c d : ι → ℝ) :
    Integrable (fun u => lin a u * lin b u * lin c u * lin d u) (stdGauss ι) := by
  simp_rw [lin4_ex]
  exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun m _ =>
      (i_four j k l m).const_mul _))))

lemma lin4 (a b c d : ι → ℝ) :
    ∫ u, lin a u * lin b u * lin c u * lin d u ∂stdGauss ι =
      dot a b * dot c d + dot a c * dot b d + dot a d * dot b c := by
  simp_rw [lin4_ex]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun m _ =>
      (i_four j k l m).const_mul _))))]
  simp_rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
    integrable_finsetSum _ (fun m _ => (i_four _ k l m).const_mul _))),
    integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun m _ =>
      (i_four _ _ l m).const_mul _)),
    integral_finsetSum _ (fun m _ => (i_four _ _ _ m).const_mul _), integral_const_mul, w_four]
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∑ j, ∑ k, ∑ l, ∑ m, a j * b k * c l * d m *
      ((if j = k then (1 : ℝ) else 0) * (if l = m then (1 : ℝ) else 0)) = dot a b * dot c d := by
    simp only [dot, Finset.sum_mul_sum]
    simp
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h2 : ∑ j, ∑ k, ∑ l, ∑ m, a j * b k * c l * d m *
      ((if j = l then (1 : ℝ) else 0) * (if k = m then (1 : ℝ) else 0)) = dot a c * dot b d := by
    simp only [dot, Finset.sum_mul_sum]
    simp
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have h3 : ∑ j, ∑ k, ∑ l, ∑ m, a j * b k * c l * d m *
      ((if j = m then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0)) = dot a d * dot b c := by
    simp only [dot, Finset.sum_mul_sum]
    simp
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  rw [h1, h2, h3]

end Lin

/-- **Second moment of a linear form.** -/
theorem gaussLin : GaussLin := by
  intro ι _ b c
  classical
  exact ⟨lin2_int b c, lin2 b c⟩

/-- **Fourth moment of an affine function of a Gaussian vector**, constant `3`. -/
theorem affFourth3 : AffFourth 3 := by
  intro ι _ c0 b
  classical
  change ∫ u, (c0 + lin b u) ^ 4 ∂stdGauss ι ≤ 3 * (∫ u, (c0 + lin b u) ^ 2 ∂stdGauss ι) ^ 2
  have h1 := lin1_int b
  have h2 := lin2_int b b
  have h3 := lin3_int b b b
  have h4 := lin4_int b b b b
  have e2 : ∫ u, (c0 + lin b u) ^ 2 ∂stdGauss ι = c0 ^ 2 + dot b b := by
    have hex (u : ι → ℝ) : (c0 + lin b u) ^ 2 = c0 ^ 2 + 2 * c0 * lin b u + lin b u * lin b u := by
      ring
    simp_rw [hex]
    have j1 : Integrable (fun u => c0 ^ 2 + 2 * c0 * lin b u) (stdGauss ι) :=
      (integrable_const _).add (h1.const_mul _)
    rw [integral_add j1 h2,
      integral_add (integrable_const _) (h1.const_mul _), integral_const_mul, lin1, lin2]
    simp
  have e4 : ∫ u, (c0 + lin b u) ^ 4 ∂stdGauss ι =
      c0 ^ 4 + 6 * c0 ^ 2 * dot b b + 3 * dot b b ^ 2 := by
    have hex (u : ι → ℝ) : (c0 + lin b u) ^ 4 = c0 ^ 4 + 4 * c0 ^ 3 * lin b u +
        6 * c0 ^ 2 * (lin b u * lin b u) + 4 * c0 * (lin b u * lin b u * lin b u) +
        lin b u * lin b u * lin b u * lin b u := by
      ring
    simp_rw [hex]
    have j1 : Integrable (fun u => c0 ^ 4 + 4 * c0 ^ 3 * lin b u) (stdGauss ι) :=
      (integrable_const _).add (h1.const_mul _)
    have j2 : Integrable (fun u => c0 ^ 4 + 4 * c0 ^ 3 * lin b u +
        6 * c0 ^ 2 * (lin b u * lin b u)) (stdGauss ι) := j1.add (h2.const_mul _)
    have j3 : Integrable (fun u => c0 ^ 4 + 4 * c0 ^ 3 * lin b u +
        6 * c0 ^ 2 * (lin b u * lin b u) + 4 * c0 * (lin b u * lin b u * lin b u))
        (stdGauss ι) := j2.add (h3.const_mul _)
    rw [integral_add j3 h4, integral_add j2 (h3.const_mul _), integral_add j1 (h2.const_mul _),
      integral_add (integrable_const _) (h1.const_mul _)]
    simp only [integral_const_mul, lin1, lin2, lin3, lin4]
    simp
    ring
  rw [e2, e4]
  have hd : 0 ≤ dot b b := Finset.sum_nonneg (fun j _ => mul_self_nonneg (b j))
  nlinarith [sq_nonneg (c0 ^ 2)]

/-! ### The two-point identity -/

section TwoPoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- `a·L + Lᵀ H L` for a vector of values `L`. -/
def phiL (a : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (L : Fin n → ℝ) : ℝ :=
  ∑ i, a i * L i + ∑ i, ∑ j, H i j * L i * L j

lemma phiL_mul (a : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (L L' : Fin n → ℝ) :
    phiL a H L * phiL a H L' =
      ∑ i, ∑ k, (a i * a k) * (L i * L' k) +
      ∑ i, ∑ k, ∑ l, (a i * H k l) * (L i * L' k * L' l) +
      ∑ i, ∑ j, ∑ k, (H i j * a k) * (L i * L j * L' k) +
      ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) * (L i * L j * L' k * L' l) := by
  have t1 : (∑ i, a i * L i) * (∑ k, a k * L' k) = ∑ i, ∑ k, (a i * a k) * (L i * L' k) := by
    simp_rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have t2 : (∑ i, a i * L i) * (∑ k, ∑ l, H k l * L' k * L' l) =
      ∑ i, ∑ k, ∑ l, (a i * H k l) * (L i * L' k * L' l) := by
    simp_rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have t3 : (∑ i, ∑ j, H i j * L i * L j) * (∑ k, a k * L' k) =
      ∑ i, ∑ j, ∑ k, (H i j * a k) * (L i * L j * L' k) := by
    simp_rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have t4 : (∑ i, ∑ j, H i j * L i * L j) * (∑ k, ∑ l, H k l * L' k * L' l) =
      ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) * (L i * L j * L' k * L' l) := by
    simp_rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  unfold phiL
  rw [← t1, ← t2, ← t3, ← t4]
  ring

lemma phiL_mean (a : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (B : Fin n → ι → ℝ) :
    ∫ u, phiL a H (fun i => lin (B i) u) ∂stdGauss ι = ∑ i, ∑ j, H i j * dot (B i) (B j) := by
  unfold phiL
  have hA : Integrable (fun u => ∑ i, a i * lin (B i) u) (stdGauss ι) :=
    integrable_finsetSum _ (fun i _ => (lin1_int (B i)).const_mul _)
  have hex (u : ι → ℝ) : (∑ i, ∑ j, H i j * lin (B i) u * lin (B j) u) =
      ∑ i, ∑ j, H i j * (lin (B i) u * lin (B j) u) := by
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  simp_rw [hex]
  have hB : Integrable (fun u => ∑ i, ∑ j, H i j * (lin (B i) u * lin (B j) u)) (stdGauss ι) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      (lin2_int (B i) (B j)).const_mul _))
  rw [integral_add hA hB, integral_finsetSum _ (fun i _ => (lin1_int (B i)).const_mul _),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      (lin2_int (B i) (B j)).const_mul _))]
  simp_rw [integral_finsetSum _ (fun j _ => (lin2_int (B _) (B j)).const_mul _),
    integral_const_mul, lin1, lin2]
  simp

lemma phiL_two (a : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (B B' : Fin n → ι → ℝ) :
    ∫ u, phiL a H (fun i => lin (B i) u) * phiL a H (fun i => lin (B' i) u) ∂stdGauss ι =
      ∑ i, ∑ k, (a i * a k) * dot (B i) (B' k) +
      ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) *
        (dot (B i) (B j) * dot (B' k) (B' l) + dot (B i) (B' k) * dot (B j) (B' l) +
          dot (B i) (B' l) * dot (B j) (B' k)) := by
  simp_rw [phiL_mul]
  have i1 : Integrable (fun u => ∑ i, ∑ k, (a i * a k) * (lin (B i) u * lin (B' k) u))
      (stdGauss ι) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ =>
      (lin2_int (B i) (B' k)).const_mul _))
  have i2 : Integrable (fun u => ∑ i, ∑ k, ∑ l, (a i * H k l) *
      (lin (B i) u * lin (B' k) u * lin (B' l) u)) (stdGauss ι) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun l _ => (lin3_int (B i) (B' k) (B' l)).const_mul _)))
  have i3 : Integrable (fun u => ∑ i, ∑ j, ∑ k, (H i j * a k) *
      (lin (B i) u * lin (B j) u * lin (B' k) u)) (stdGauss ι) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun k _ => (lin3_int (B i) (B j) (B' k)).const_mul _)))
  have i4 : Integrable (fun u => ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) *
      (lin (B i) u * lin (B j) u * lin (B' k) u * lin (B' l) u)) (stdGauss ι) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
        (lin4_int (B i) (B j) (B' k) (B' l)).const_mul _))))
  have i12 : Integrable (fun u => ∑ i, ∑ k, (a i * a k) * (lin (B i) u * lin (B' k) u) +
      ∑ i, ∑ k, ∑ l, (a i * H k l) * (lin (B i) u * lin (B' k) u * lin (B' l) u))
      (stdGauss ι) := i1.add i2
  have i123 : Integrable (fun u => ∑ i, ∑ k, (a i * a k) * (lin (B i) u * lin (B' k) u) +
      ∑ i, ∑ k, ∑ l, (a i * H k l) * (lin (B i) u * lin (B' k) u * lin (B' l) u) +
      ∑ i, ∑ j, ∑ k, (H i j * a k) * (lin (B i) u * lin (B j) u * lin (B' k) u))
      (stdGauss ι) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2]
  have e1 : ∫ u, ∑ i, ∑ k, (a i * a k) * (lin (B i) u * lin (B' k) u) ∂stdGauss ι =
      ∑ i, ∑ k, (a i * a k) * dot (B i) (B' k) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ =>
      (lin2_int (B i) (B' k)).const_mul _))]
    simp_rw [integral_finsetSum _ (fun k _ => (lin2_int (B _) (B' k)).const_mul _),
      integral_const_mul, lin2]
  have e2 : ∫ u, ∑ i, ∑ k, ∑ l, (a i * H k l) *
      (lin (B i) u * lin (B' k) u * lin (B' l) u) ∂stdGauss ι = 0 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun l _ => (lin3_int (B i) (B' k) (B' l)).const_mul _)))]
    simp_rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
        (lin3_int (B _) (B' k) (B' l)).const_mul _)),
      integral_finsetSum _ (fun l _ => (lin3_int (B _) (B' _) (B' l)).const_mul _),
      integral_const_mul, lin3]
    simp
  have e3 : ∫ u, ∑ i, ∑ j, ∑ k, (H i j * a k) *
      (lin (B i) u * lin (B j) u * lin (B' k) u) ∂stdGauss ι = 0 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun k _ => (lin3_int (B i) (B j) (B' k)).const_mul _)))]
    simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
        (lin3_int (B _) (B j) (B' k)).const_mul _)),
      integral_finsetSum _ (fun k _ => (lin3_int (B _) (B _) (B' k)).const_mul _),
      integral_const_mul, lin3]
    simp
  have e4 : ∫ u, ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) *
      (lin (B i) u * lin (B j) u * lin (B' k) u * lin (B' l) u) ∂stdGauss ι =
      ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) *
        (dot (B i) (B j) * dot (B' k) (B' l) + dot (B i) (B' k) * dot (B j) (B' l) +
          dot (B i) (B' l) * dot (B j) (B' k)) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
        (lin4_int (B i) (B j) (B' k) (B' l)).const_mul _))))]
    simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
        integrable_finsetSum _ (fun l _ => (lin4_int (B _) (B j) (B' k) (B' l)).const_mul _))),
      integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
        (lin4_int (B _) (B _) (B' k) (B' l)).const_mul _)),
      integral_finsetSum _ (fun l _ => (lin4_int (B _) (B _) (B' _) (B' l)).const_mul _),
      integral_const_mul, lin4]
  rw [e1, e2, e3, e4]
  ring

end TwoPoint

/-- The coefficient vector of `W ↦ zv W p i`. -/
def bv {J : Type*} {n : ℕ} (p : J → ℝ) (i : Fin n) : J × Fin n → ℝ :=
  fun β => if β.2 = i then p β.1 else 0

lemma zv_lin {J : Type*} [Fintype J] {n : ℕ} (W : J × Fin n → ℝ) (p : J → ℝ) (i : Fin n) :
    zv W p i = lin (bv p i) W := by
  unfold zv lin bv
  rw [Fintype.sum_prod_type]
  simp [mul_comm]

lemma bv_dot {J : Type*} [Fintype J] {n : ℕ} (p p' : J → ℝ) (i j : Fin n) :
    dot (bv p i) (bv p' j) = if i = j then ∑ q, p q * p' q else 0 := by
  unfold dot bv
  rw [Fintype.sum_prod_type]
  by_cases h : i = j
  · subst h; simp
  · simp [h]
    intro q
    exact absurd q.symm h

lemma Phi_phiL {J : Type*} [Fintype J] {n : ℕ} (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (W : J × Fin n → ℝ) (p : J → ℝ) :
    Phi a H W p = phiL a (fun i j => H i j) (fun i => lin (bv p i) W) := by
  unfold Phi phiL
  simp_rw [zv_lin]

/-- **Two-point (Wick) identity** for `Φ`. -/
theorem wickTwoPoint : WickTwoPoint := by
  intro J _ n a H hH p p'
  classical
  simp_rw [Phi_phiL]
  rw [phiL_mean, phiL_two]
  simp_rw [bv_dot]
  have hsq (r : J → ℝ) : ∑ q, r q ^ 2 = ∑ q, r q * r q := by
    apply Finset.sum_congr rfl; intro q _; ring
  rw [hsq p, hsq p']
  generalize (∑ q, p q * p q) = P
  generalize (∑ q, p' q * p' q) = P'
  generalize (∑ q, p q * p' q) = X
  refine ⟨?_, ?_⟩
  · simp [trH, Finset.sum_mul]
  · have h0 : ∑ i, ∑ k, (a i * a k) * (if i = k then X else 0) = nsq a * X := by
      simp [nsq, Finset.sum_mul, pow_two]
    have h1 : ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) *
        ((if i = j then P else 0) * (if k = l then P' else 0)) = trH H ^ 2 * (P * P') := by
      simp
      simp only [trH, pow_two, Finset.sum_mul, Finset.mul_sum]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ring
    have h2 : ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) *
        ((if i = k then X else 0) * (if j = l then X else 0)) = frobH H * X ^ 2 := by
      simp only [frobH, Finset.sum_mul]
      simp
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ring
    have h3 : ∑ i, ∑ j, ∑ k, ∑ l, (H i j * H k l) *
        ((if i = l then X else 0) * (if j = k then X else 0)) = frobH H * X ^ 2 := by
      simp only [frobH, Finset.sum_mul]
      simp
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [hH.apply i j]
      ring
    simp only [mul_add, Finset.sum_add_distrib]
    rw [h0, h1, h2, h3]
    ring

#print axioms gaussLin
#print axioms wickTwoPoint
#print axioms affFourth3

end BstLean.Part78
