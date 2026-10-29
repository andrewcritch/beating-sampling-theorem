import BstLean.Part82WickStep

/-!
# Part 82: the two-point (Wick) identity for the cubic `Φ` (`Wick3`)
-/

namespace BstLean.Part82.WickAux

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part78 (lin dot Good good_coord lin1 lin2 lin3 lin4 phiL bv zv_lin bv_dot Phi_phiL
  nsq trH frobH zv)

/-! ### Integrals of nested finite sums -/

section isum
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {K1 K2 K3 K4 K5 K6 : Type*} [Fintype K1] [Fintype K2] [Fintype K3] [Fintype K4]
  [Fintype K5] [Fintype K6]

lemma isum1 (f : K1 → Ω → ℝ) (h : ∀ a, Good μ (f a)) :
    ∫ w, ∑ a, f a w ∂μ = ∑ a, ∫ w, f a w ∂μ :=
  integral_finsetSum _ (fun a _ => (h a).integrable)

lemma isum2 (f : K1 → K2 → Ω → ℝ) (h : ∀ a b, Good μ (f a b)) :
    ∫ w, ∑ a, ∑ b, f a b w ∂μ = ∑ a, ∑ b, ∫ w, f a b w ∂μ := by
  rw [isum1 (fun a w => ∑ b, f a b w) (fun a => Good.sum _ (fun b _ => h a b))]
  exact Finset.sum_congr rfl (fun a _ => isum1 _ (h a))

lemma isum3 (f : K1 → K2 → K3 → Ω → ℝ) (h : ∀ a b c, Good μ (f a b c)) :
    ∫ w, ∑ a, ∑ b, ∑ c, f a b c w ∂μ = ∑ a, ∑ b, ∑ c, ∫ w, f a b c w ∂μ := by
  rw [isum1 (fun a w => ∑ b, ∑ c, f a b c w)
    (fun a => Good.sum _ (fun b _ => Good.sum _ (fun c _ => h a b c)))]
  exact Finset.sum_congr rfl (fun a _ => isum2 _ (h a))

lemma isum4 (f : K1 → K2 → K3 → K4 → Ω → ℝ) (h : ∀ a b c d, Good μ (f a b c d)) :
    ∫ w, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d w ∂μ = ∑ a, ∑ b, ∑ c, ∑ d, ∫ w, f a b c d w ∂μ := by
  rw [isum1 (fun a w => ∑ b, ∑ c, ∑ d, f a b c d w)
    (fun a => Good.sum _ (fun b _ => Good.sum _ (fun c _ => Good.sum _ (fun d _ => h a b c d))))]
  exact Finset.sum_congr rfl (fun a _ => isum3 _ (h a))

lemma isum5 (f : K1 → K2 → K3 → K4 → K5 → Ω → ℝ) (h : ∀ a b c d e, Good μ (f a b c d e)) :
    ∫ w, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e w ∂μ =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∫ w, f a b c d e w ∂μ := by
  rw [isum1 (fun a w => ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e w)
    (fun a => Good.sum _ (fun b _ => Good.sum _ (fun c _ => Good.sum _ (fun d _ =>
      Good.sum _ (fun e _ => h a b c d e)))))]
  exact Finset.sum_congr rfl (fun a _ => isum4 _ (h a))

lemma isum6 (f : K1 → K2 → K3 → K4 → K5 → K6 → Ω → ℝ)
    (h : ∀ a b c d e g, Good μ (f a b c d e g)) :
    ∫ w, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g w ∂μ =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, ∫ w, f a b c d e g w ∂μ := by
  rw [isum1 (fun a w => ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g w)
    (fun a => Good.sum _ (fun b _ => Good.sum _ (fun c _ => Good.sum _ (fun d _ =>
      Good.sum _ (fun e _ => Good.sum _ (fun g _ => h a b c d e g))))))]
  exact Finset.sum_congr rfl (fun a _ => isum5 _ (h a))

end isum

section Cubic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- `T[L,L,L]` for a vector of values `L`. -/
def cubL (T : T3 n) (L : Fin n → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, T i j k * L i * L j * L k

/-- Closes a goal `Good (stdGauss ι) f` for `f` a polynomial expression in linear forms. -/
macro "good" : tactic =>
  `(tactic| repeat (first
    | exact good_lin _
    | (apply Good.sum; intro _ _)
    | apply Good.add
    | apply Good.mul
    | exact Good.const _))

lemma good_cubL (T : T3 n) (B : Fin n → ι → ℝ) :
    Good (stdGauss ι) (fun u => cubL T (fun i => lin (B i) u)) := by
  unfold cubL; good

lemma good_phiL (a : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (B : Fin n → ι → ℝ) :
    Good (stdGauss ι) (fun u => phiL a H (fun i => lin (B i) u)) := by
  unfold phiL; good

lemma cub_mean (T : T3 n) (B : Fin n → ι → ℝ) :
    ∫ u, cubL T (fun i => lin (B i) u) ∂stdGauss ι = 0 := by
  unfold cubL
  have hex (u : ι → ℝ) : (∑ i, ∑ j, ∑ k, T i j k * lin (B i) u * lin (B j) u * lin (B k) u) =
      ∑ i, ∑ j, ∑ k, T i j k * (lin (B i) u * lin (B j) u * lin (B k) u) := by
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  simp_rw [hex]
  rw [isum3 _ (by intros; good)]
  simp_rw [integral_const_mul, lin3]
  simp

lemma phi_cub_mul (a : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (T : T3 n) (L L' : Fin n → ℝ) :
    phiL a H L * cubL T L' =
      ∑ i, ∑ k, ∑ l, ∑ m, (a i * T k l m) * (L i * L' k * L' l * L' m) +
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, (H i j * T k l m) * (L i * (L j * L' k * L' l * L' m)) := by
  have t1 : (∑ i, a i * L i) * (∑ k, ∑ l, ∑ m, T k l m * L' k * L' l * L' m) =
      ∑ i, ∑ k, ∑ l, ∑ m, (a i * T k l m) * (L i * L' k * L' l * L' m) := by
    simp_rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have t2 : (∑ i, ∑ j, H i j * L i * L j) * (∑ k, ∑ l, ∑ m, T k l m * L' k * L' l * L' m) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, (H i j * T k l m) * (L i * (L j * L' k * L' l * L' m)) := by
    simp_rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  unfold phiL cubL
  rw [← t1, ← t2]
  ring

lemma cub_cub_mul (T : T3 n) (L L' : Fin n → ℝ) :
    cubL T L * cubL T L' =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, (T i j k * T l m r) *
        (L i * (L j * L k * L' l * L' m * L' r)) := by
  unfold cubL
  simp_rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

lemma phi_cub (a : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (T : T3 n) (B B' : Fin n → ι → ℝ) :
    ∫ u, phiL a H (fun i => lin (B i) u) * cubL T (fun i => lin (B' i) u) ∂stdGauss ι =
      ∑ i, ∑ k, ∑ l, ∑ m, (a i * T k l m) *
        (dot (B i) (B' k) * dot (B' l) (B' m) + dot (B i) (B' l) * dot (B' k) (B' m) +
          dot (B i) (B' m) * dot (B' k) (B' l)) := by
  simp_rw [phi_cub_mul]
  rw [integral_add (Good.integrable (by good)) (Good.integrable (by good)),
    isum4 _ (by intros; good), isum5 _ (by intros; good)]
  simp_rw [integral_const_mul, lin4, lin5]
  simp

lemma cub_cub (T : T3 n) (B B' : Fin n → ι → ℝ) :
    ∫ u, cubL T (fun i => lin (B i) u) * cubL T (fun i => lin (B' i) u) ∂stdGauss ι =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, (T i j k * T l m r) *
        (dot (B i) (B j) * (dot (B k) (B' l) * dot (B' m) (B' r) +
            dot (B k) (B' m) * dot (B' l) (B' r) + dot (B k) (B' r) * dot (B' l) (B' m)) +
          dot (B i) (B k) * (dot (B j) (B' l) * dot (B' m) (B' r) +
            dot (B j) (B' m) * dot (B' l) (B' r) + dot (B j) (B' r) * dot (B' l) (B' m)) +
          dot (B i) (B' l) * (dot (B j) (B k) * dot (B' m) (B' r) +
            dot (B j) (B' m) * dot (B k) (B' r) + dot (B j) (B' r) * dot (B k) (B' m)) +
          dot (B i) (B' m) * (dot (B j) (B k) * dot (B' l) (B' r) +
            dot (B j) (B' l) * dot (B k) (B' r) + dot (B j) (B' r) * dot (B k) (B' l)) +
          dot (B i) (B' r) * (dot (B j) (B k) * dot (B' l) (B' m) +
            dot (B j) (B' l) * dot (B k) (B' m) + dot (B j) (B' m) * dot (B k) (B' l))) := by
  simp_rw [cub_cub_mul]
  rw [isum6 _ (by intros; good)]
  simp_rw [integral_const_mul, lin6]

end Cubic

/-! ### Contractions with Kronecker deltas -/

section Delta

variable {n : ℕ}

/-- `T c p p`, as a separate symbol (so that `simp` does not see a permutation lemma). -/
def tr3 (T : T3 n) (c p : Fin n) : ℝ := T c p p

lemma hs0 (T : T3 n) (p c : Fin n) : T c p p = tr3 T c p := rfl
lemma hs1 (T : T3 n) (hT : SymT T) (p c : Fin n) : T p c p = tr3 T c p := (hT p c p).1
lemma hs2 (T : T3 n) (hT : SymT T) (p c : Fin n) : T p p c = tr3 T c p := by
  rw [(hT p p c).2, (hT p c p).1]; rfl

lemma pp0 (T : T3 n) (x y z : Fin n) : T x y z * T x y z = T x y z ^ 2 := by ring
lemma pp1 (T : T3 n) (hT : SymT T) (x y z : Fin n) : T x y z * T y x z = T x y z ^ 2 := by
  rw [(hT y x z).1]; ring
lemma pp2 (T : T3 n) (hT : SymT T) (x y z : Fin n) : T x y z * T x z y = T x y z ^ 2 := by
  rw [(hT x z y).2]; ring
lemma pp3 (T : T3 n) (hT : SymT T) (x y z : Fin n) : T x y z * T z y x = T x y z ^ 2 := by
  rw [(hT z y x).1, (hT y z x).2, (hT y x z).1]; ring
lemma pp4 (T : T3 n) (hT : SymT T) (x y z : Fin n) : T x y z * T y z x = T x y z ^ 2 := by
  rw [(hT y z x).2, (hT y x z).1]; ring
lemma pp5 (T : T3 n) (hT : SymT T) (x y z : Fin n) : T x y z * T z x y = T x y z ^ 2 := by
  rw [(hT z x y).1, (hT x z y).2]; ring

lemma tA1 (T : T3 n) (w : ℝ) :
    ∑ c, ∑ p, ∑ q, tr3 T c p * tr3 T c q * w = w * ∑ c, trT T c * trT T c := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  unfold trT tr3
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _
  ring

lemma tA2 (T : T3 n) (w : ℝ) :
    ∑ p, ∑ c, ∑ q, tr3 T c p * tr3 T c q * w = w * ∑ c, trT T c * trT T c := by
  rw [Finset.sum_comm]; exact tA1 T w

lemma tB1 (T : T3 n) (w : ℝ) :
    ∑ x, ∑ y, ∑ z, T x y z ^ 2 * w = w * frobT T := by
  unfold frobT
  simp only [Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

lemma tQ1 (a : Fin n → ℝ) (T : T3 n) (w : ℝ) :
    ∑ i, ∑ x, a i * tr3 T i x * w = w * ∑ i, a i * trT T i := by
  unfold trT tr3
  simp only [Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

lemma cc1 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = j then c1 else 0) * ((if k = l then c2 else 0) *
        (if m = r then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc2 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = j then c1 else 0) * ((if k = m then c2 else 0) *
        (if l = r then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc3 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = j then c1 else 0) * ((if k = r then c2 else 0) *
        (if l = m then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc4 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = k then c1 else 0) * ((if j = l then c2 else 0) *
        (if m = r then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc5 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = k then c1 else 0) * ((if j = m then c2 else 0) *
        (if l = r then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc6 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = k then c1 else 0) * ((if j = r then c2 else 0) *
        (if l = m then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc7 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = l then c1 else 0) * ((if j = k then c2 else 0) *
        (if m = r then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc8 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = l then c1 else 0) * ((if j = m then c2 else 0) *
        (if k = r then c3 else 0))) = c1 * (c2 * c3) * (frobT T) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc9 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = l then c1 else 0) * ((if j = r then c2 else 0) *
        (if k = m then c3 else 0))) = c1 * (c2 * c3) * (frobT T) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc10 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = m then c1 else 0) * ((if j = k then c2 else 0) *
        (if l = r then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc11 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = m then c1 else 0) * ((if j = l then c2 else 0) *
        (if k = r then c3 else 0))) = c1 * (c2 * c3) * (frobT T) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc12 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = m then c1 else 0) * ((if j = r then c2 else 0) *
        (if k = l then c3 else 0))) = c1 * (c2 * c3) * (frobT T) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc13 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = r then c1 else 0) * ((if j = k then c2 else 0) *
        (if l = m then c3 else 0))) = c1 * (c2 * c3) * (∑ c, trT T c * trT T c) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc14 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = r then c1 else 0) * ((if j = l then c2 else 0) *
        (if k = m then c3 else 0))) = c1 * (c2 * c3) * (frobT T) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma cc15 (T : T3 n) (hT : SymT T) (c1 c2 c3 : ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ r, T i j k * T l m r *
      ((if i = r then c1 else 0) * ((if j = m then c2 else 0) *
        (if k = l then c3 else 0))) = c1 * (c2 * c3) * (frobT T) := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [hs0 T, hs1 T hT, hs2 T hT, pp0 T, pp1 T hT, pp2 T hT, pp3 T hT, pp4 T hT, pp5 T hT]
  first | exact tA1 T _ | exact tA2 T _ | exact tB1 T _

lemma qc1 (a : Fin n → ℝ) (T : T3 n) (hT : SymT T) (c1 c2 : ℝ) :
    ∑ i, ∑ k, ∑ l, ∑ m, a i * T k l m *
      ((if i = k then c1 else 0) * (if l = m then c2 else 0)) =
      c1 * c2 * ∑ i, a i * trT T i := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [hs0 T, hs1 T hT, hs2 T hT]
  exact tQ1 a T _

lemma qc2 (a : Fin n → ℝ) (T : T3 n) (hT : SymT T) (c1 c2 : ℝ) :
    ∑ i, ∑ k, ∑ l, ∑ m, a i * T k l m *
      ((if i = l then c1 else 0) * (if k = m then c2 else 0)) =
      c1 * c2 * ∑ i, a i * trT T i := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [hs0 T, hs1 T hT, hs2 T hT]
  exact tQ1 a T _

lemma qc3 (a : Fin n → ℝ) (T : T3 n) (hT : SymT T) (c1 c2 : ℝ) :
    ∑ i, ∑ k, ∑ l, ∑ m, a i * T k l m *
      ((if i = m then c1 else 0) * (if k = l then c2 else 0)) =
      c1 * c2 * ∑ i, a i * trT T i := by
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [hs0 T, hs1 T hT, hs2 T hT]
  exact tQ1 a T _

lemma AA_sum (a : Fin n → ℝ) (T : T3 n) (s s' : ℝ) :
    ∑ i, AA a T s i * AA a T s' i =
      nsq a + 3 * (s + s') * (∑ i, a i * trT T i) + 9 * (s * s') * ∑ c, trT T c * trT T c := by
  unfold AA nsq
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  ring

end Delta

end BstLean.Part82.WickAux

namespace BstLean.Part82

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part78 (lin dot Good phiL bv zv_lin bv_dot Phi_phiL nsq trH frobH zv)
open WickAux

/-- **Two-point (Wick) identity** for the cubic `Φ`. -/
theorem wick3 : Wick3 := by
  intro J _ n a H hH T hT p p'
  classical
  have h78 := BstLean.Part78.wickTwoPoint J n a H hH p p'
  have e3 (r : J → ℝ) (W : J × Fin n → ℝ) : Phi3 a H T W r =
      phiL a (fun i j => H i j) (fun i => lin (bv r i) W) +
        cubL T (fun i => lin (bv r i) W) := by
    unfold Phi3 phiL cubL
    simp_rw [zv_lin]
  simp_rw [Phi_phiL] at h78
  have gP (r : J → ℝ) := good_phiL (ι := J × Fin n) a (fun i j => H i j) (bv r)
  have gC (r : J → ℝ) := good_cubL (ι := J × Fin n) T (bv r)
  simp_rw [e3]
  refine ⟨?_, ?_⟩
  · rw [integral_add (gP p).integrable (gC p).integrable, h78.1, cub_mean, add_zero]
  · have hex (W : J × Fin n → ℝ) :
        (phiL a (fun i j => H i j) (fun i => lin (bv p i) W) + cubL T (fun i => lin (bv p i) W)) *
        (phiL a (fun i j => H i j) (fun i => lin (bv p' i) W) +
          cubL T (fun i => lin (bv p' i) W)) =
        phiL a (fun i j => H i j) (fun i => lin (bv p i) W) *
            phiL a (fun i j => H i j) (fun i => lin (bv p' i) W) +
          phiL a (fun i j => H i j) (fun i => lin (bv p i) W) * cubL T (fun i => lin (bv p' i) W) +
          phiL a (fun i j => H i j) (fun i => lin (bv p' i) W) * cubL T (fun i => lin (bv p i) W) +
          cubL T (fun i => lin (bv p i) W) * cubL T (fun i => lin (bv p' i) W) := by ring
    simp_rw [hex]
    have g1 := (gP p).mul (gP p')
    have g2 := (gP p).mul (gC p')
    have g3 := (gP p').mul (gC p)
    have g4 := (gC p).mul (gC p')
    have g12 := g1.add g2
    have g123 := g12.add g3
    rw [integral_add g123.integrable g4.integrable, integral_add g12.integrable g3.integrable,
      integral_add g1.integrable g2.integrable,
      h78.2, phi_cub, phi_cub, cub_cub]
    simp_rw [bv_dot]
    have hsq (r : J → ℝ) : ∑ q, r q ^ 2 = ∑ q, r q * r q := by
      apply Finset.sum_congr rfl; intro q _; ring
    have hc : ∑ q, p' q * p q = ∑ q, p q * p' q := by
      apply Finset.sum_congr rfl; intro q _; ring
    rw [hsq p, hsq p', hc]
    generalize (∑ q, p q * p q) = P
    generalize (∑ q, p' q * p' q) = P'
    generalize (∑ q, p q * p' q) = X
    simp only [mul_add]
    simp (config := {maxSteps := 4000000}) only [Finset.sum_add_distrib, qc1 a T hT, qc2 a T hT, qc3 a T hT, cc1 T hT, cc2 T hT, cc3 T hT, cc4 T hT, cc5 T hT, cc6 T hT, cc7 T hT, cc8 T hT, cc9 T hT, cc10 T hT, cc11 T hT, cc12 T hT, cc13 T hT, cc14 T hT, cc15 T hT]
    unfold C2
    rw [AA_sum]
    ring

#print axioms wick3

end BstLean.Part82
