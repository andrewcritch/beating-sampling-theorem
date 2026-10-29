import BstLean.Part107Defs

/-!
# Part 107, the Wick formula for four linear forms of a standard Gaussian vector
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Kronecker delta. -/
def dl (i j : ι) : ℝ := if i = j then 1 else 0

lemma sum_mul_dl (g : ι → ℝ) (j : ι) : ∑ l, g l * dl j l = g j := by
  simp [dl]

lemma mom2 (i j : ι) : ∫ z, z i * z j ∂stdGauss ι = dl i j := by
  have hw := BstLean.Part35.stdGauss_wick_step i 1 (fun _ : Fin 1 => j)
  simpa [eq_comm, dl] using hw

lemma int4 (i j k l : ι) : Integrable (fun z : ι → ℝ => z i * z j * z k * z l) (stdGauss ι) := by
  have h := BstLean.Part35.stdGauss_prod_integrable (ι := ι) 4 ![i, j, k, l]
  simpa [Fin.prod_univ_four] using h

lemma int2 (i j : ι) : Integrable (fun z : ι → ℝ => z i * z j) (stdGauss ι) := by
  have h := BstLean.Part35.stdGauss_prod_integrable (ι := ι) 2 ![i, j]
  simpa [Fin.prod_univ_two] using h

lemma mom4 (i j k l : ι) :
    ∫ z, z i * z j * z k * z l ∂stdGauss ι =
      dl i j * dl k l + dl i k * dl j l + dl i l * dl j k := by
  have hw := BstLean.Part35.stdGauss_wick_step i 3 ![j, k, l]
  have e0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have e1 : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have e2 : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  have p0 : ∀ z : ι → ℝ, ∏ x ∈ ({1, 2} : Finset (Fin 3)), z (![j, k, l] x) = z k * z l :=
    fun z => by rw [Finset.prod_pair (by decide)]; rfl
  have p1 : ∀ z : ι → ℝ, ∏ x ∈ ({0, 2} : Finset (Fin 3)), z (![j, k, l] x) = z j * z l :=
    fun z => by rw [Finset.prod_pair (by decide)]; rfl
  have p2 : ∀ z : ι → ℝ, ∏ x ∈ ({0, 1} : Finset (Fin 3)), z (![j, k, l] x) = z j * z k :=
    fun z => by rw [Finset.prod_pair (by decide)]; rfl
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, e0, e1, e2, p0, p1, p2, mom2] at hw
  have hw' : ∫ z : ι → ℝ, z i * (z j * z k * z l) ∂stdGauss ι =
      dl j i * dl k l + dl k i * dl j l + dl l i * dl j k := by
    refine hw.trans ?_
    change ((if j = i then dl k l else 0) + if k = i then dl j l else 0) +
      (if l = i then dl j k else 0) = _
    simp only [dl]
    split_ifs <;> simp_all
  have e : ∀ z : ι → ℝ, z i * z j * z k * z l = z i * (z j * z k * z l) := fun z => by ring
  simp_rw [e, hw']
  have hs : ∀ a b : ι, dl a b = dl b a := fun a b => by simp [dl, eq_comm]
  rw [hs i j, hs i k, hs i l]

/-- A linear form. -/
def lin (a : ι → ℝ) (z : ι → ℝ) : ℝ := ∑ i, z i * a i

lemma collapse1 (F : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, F i j k l * (dl i j * dl k l) = ∑ i, ∑ k, F i i k k := by
  have e : ∀ i j k l, F i j k l * (dl i j * dl k l) = (F i j k l * dl i j) * dl k l := by
    intros; ring
  simp_rw [e, sum_mul_dl, ← Finset.sum_mul, sum_mul_dl]

lemma collapse2 (F : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, F i j k l * (dl i k * dl j l) = ∑ i, ∑ j, F i j i j := by
  have e : ∀ i j k l, F i j k l * (dl i k * dl j l) = (F i j k l * dl i k) * dl j l := by
    intros; ring
  simp_rw [e, sum_mul_dl]

lemma collapse3 (F : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, F i j k l * (dl i l * dl j k) = ∑ i, ∑ j, F i j j i := by
  have e : ∀ i j k l, F i j k l * (dl i l * dl j k) = (F i j k l * dl j k) * dl i l := by
    intros; ring
  simp_rw [e, sum_mul_dl]

omit [DecidableEq ι] in
lemma lin4_expand (a b c d z : ι → ℝ) :
    lin a z * lin b z * lin c z * lin d z =
      ∑ i, ∑ j, ∑ k, ∑ l, (a i * b j * c k * d l) * (z i * z j * z k * z l) := by
  rw [show lin a z * lin b z * lin c z * lin d z = lin d z * lin c z * lin b z * lin a z by ring]
  simp only [lin, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [DecidableEq ι] in
lemma lin2_expand (a b z : ι → ℝ) :
    lin a z * lin b z = ∑ i, ∑ j, (a i * b j) * (z i * z j) := by
  rw [mul_comm]
  simp only [lin, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The inner product of coefficient vectors. -/
def ip (a b : ι → ℝ) : ℝ := ∑ i, a i * b i

theorem wick2 (a b : ι → ℝ) : ∫ z, lin a z * lin b z ∂stdGauss ι = ip a b := by
  simp_rw [lin2_expand]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (int2 i j).const_mul _]
  simp_rw [integral_finsetSum _ fun j _ => (int2 _ j).const_mul _, integral_const_mul, mom2,
    sum_mul_dl]
  rfl

theorem wick4 (a b c d : ι → ℝ) :
    ∫ z, lin a z * lin b z * lin c z * lin d z ∂stdGauss ι =
      ip a b * ip c d + ip a c * ip b d + ip a d * ip b c := by
  simp_rw [lin4_expand]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (int4 i j k l).const_mul _]
  simp_rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => (int4 _ j k l).const_mul _,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (int4 _ _ k l).const_mul _,
    integral_finsetSum _ fun l _ => (int4 _ _ _ l).const_mul _, integral_const_mul, mom4,
    mul_add, Finset.sum_add_distrib, collapse1, collapse2, collapse3]
  simp only [ip, Finset.sum_mul_sum]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `(Σ_i |c_i z_i|)⁴` is integrable. -/
theorem absPow4_int (c : ι → ℝ) :
    Integrable (fun z : ι → ℝ => (∑ i, |c i * z i|) ^ 4) (stdGauss ι) := by
  have h : ∀ z : ι → ℝ, (∑ i, |c i * z i|) ^ 4 =
      ∑ τ : Fin 4 → ι, |(∏ s, c (τ s)) * ∏ s, z (τ s)| := by
    intro z
    have h1 : (∑ i, |c i * z i|) ^ 4 = ∏ _s : Fin 4, ∑ i, |c i * z i| := by simp
    rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib, Finset.abs_prod]
  simp_rw [h]
  exact integrable_finsetSum _ fun τ _ =>
    ((BstLean.Part35.stdGauss_prod_integrable 4 τ).const_mul _).abs

theorem normSq_mom1 : ∫ z : ι → ℝ, ∑ i, z i ^ 2 ∂stdGauss ι = (Fintype.card ι : ℝ) := by
  have e : ∀ (z : ι → ℝ) i, z i ^ 2 = z i * z i := fun z i => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => int2 i i]
  simp [mom2, dl]

theorem normSq_mom2 :
    ∫ z : ι → ℝ, (∑ i, z i ^ 2) ^ 2 ∂stdGauss ι =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 2) := by
  have e : ∀ (z : ι → ℝ), (∑ i, z i ^ 2) ^ 2 = ∑ i, ∑ j, z i * z i * z j * z j := by
    intro z
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => int4 i i j j]
  simp_rw [integral_finsetSum _ fun j _ => int4 _ _ j j, mom4]
  have e2 : ∀ i j : ι, dl i i * dl j j + dl i j * dl i j + dl i j * dl i j =
      1 + 2 * dl i j := by
    intro i j
    simp only [dl]
    split_ifs <;> norm_num
  simp_rw [e2, Finset.sum_add_distrib, ← Finset.mul_sum]
  have e3 : ∀ i : ι, ∑ j, dl i j = 1 := fun i => by simp [dl]
  simp_rw [e3]
  simp
  ring

end Generic

end BstLean.Part107
