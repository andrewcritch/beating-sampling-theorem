import BstLean.Part78Defs
import BstLean.Part71Feature

/-!
# Part 78: explicit sphere constants for the degree-`≤ 2` raw monomial features
-/

namespace BstLean.Part78

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM)

variable {n : ℕ}

/-! ## Sums over `JJ n` -/

lemma sumJJ (g : Mono n 2 → ℝ) : ∑ q : JJ n, g q.1 = ∑ p, g p - g default := by
  classical
  have h : ∑ q : JJ n, g q.1 = ∑ p ∈ Finset.univ.filter (fun p : Mono n 2 => p ≠ default), g p := by
    rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  rw [h, Finset.filter_ne' Finset.univ (default : Mono n 2),
    Finset.sum_erase_eq_sub (Finset.mem_univ _)]

lemma sumJJ0 (g : Mono n 2 → ℝ) (h0 : g default = 0) : ∑ q : JJ n, g q.1 = ∑ p, g p := by
  rw [sumJJ, h0, sub_zero]

/-! ## Sums over `Sym2` and `Sym _ 2` -/

lemma sum_sym2_two (f : Sym2 (Fin n) → ℝ) :
    2 * ∑ s, f s = ∑ i, ∑ j, f s(i, j) + ∑ i, f s(i, i) := by
  classical
  have hd : ∑ s with s.IsDiag, f s = ∑ i, f s(i, i) := by
    rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    exact Fintype.sum_equiv Sym2.diagElemEquiv (fun x : {s : Sym2 (Fin n) // s.IsDiag} => f x.1)
      (fun i => f s(i, i)) (fun x => by
      conv_lhs => rw [← Sym2.diag_diagElem x.2]
      rfl)
  have hnd : ∑ s with ¬ s.IsDiag, f s
      = ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag with p.1 < p.2, f s(p.1, p.2) := by
    have := Finset.sum_sym2_filter_not_isDiag (Finset.univ : Finset (Fin n)) f
    rwa [Finset.sym2_univ] at this
  have hsplit : ∑ s, f s = ∑ i, f s(i, i)
      + ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag with p.1 < p.2, f s(p.1, p.2) := by
    rw [← hd, ← hnd, Finset.sum_filter_add_sum_filter_not]
  have hgt : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag with p.2 < p.1, f s(p.1, p.2)
      = ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag with p.1 < p.2, f s(p.1, p.2) := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨fun h => hp.1 h.symm, hp.2⟩
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨fun h => hp.1 h.symm, hp.2⟩
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; simp [Sym2.eq_swap]
  have hall : ∑ i, ∑ j, f s(i, j) = ∑ i, f s(i, i)
      + ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f s(p.1, p.2) := by
    rw [← Fintype.sum_prod_type', ← Finset.sum_diag (Finset.univ : Finset (Fin n))
        (fun p : Fin n × Fin n => f s(p.1, p.2)),
      ← Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.diag_union_offDiag,
      Finset.univ_product_univ]
  have hoff : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f s(p.1, p.2)
      = ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag with p.1 < p.2, f s(p.1, p.2)
      + ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag with p.2 < p.1, f s(p.1, p.2) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : Fin n × Fin n => p.1 < p.2)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, not_lt]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_ne h2 (Ne.symm h1)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.le⟩
  rw [hall, hoff, hgt, hsplit]; ring

lemma sum_sym_two (x y : Fin n → ℝ) :
    ∑ β : Sym (Fin n) 2, monoVal x β.1 * monoVal y β.1
      = ((∑ i, x i * y i) ^ 2 + ∑ i, x i ^ 2 * y i ^ 2) / 2 := by
  classical
  have h1 : ∑ β : Sym (Fin n) 2, monoVal x β.1 * monoVal y β.1
      = ∑ s : Sym2 (Fin n), monoVal x (Sym2.equivSym (Fin n) s).1
          * monoVal y (Sym2.equivSym (Fin n) s).1 :=
    (Fintype.sum_equiv (Sym2.equivSym (Fin n)) _ _ (fun _ => rfl)).symm
  have hv : ∀ (z : Fin n → ℝ) (i j : Fin n),
      monoVal z (Sym2.equivSym (Fin n) s(i, j)).1 = z i * z j := by
    intro z i j
    have : (Sym2.equivSym (Fin n) s(i, j)).1 = {i, j} := rfl
    rw [this]; simp [monoVal]
  have h2 := sum_sym2_two (fun s : Sym2 (Fin n) => monoVal x (Sym2.equivSym (Fin n) s).1
          * monoVal y (Sym2.equivSym (Fin n) s).1)
  simp only [hv] at h2
  rw [h1]
  have h3 : (∑ i, x i * y i) ^ 2 = ∑ i, ∑ j, x i * x j * (y i * y j) := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have h4 : ∑ i, x i ^ 2 * y i ^ 2 = ∑ i, x i * x i * (y i * y i) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [h3, h4]; linarith

lemma sum_sym_one (x y : Fin n → ℝ) :
    ∑ β : Sym (Fin n) 1, monoVal x β.1 * monoVal y β.1 = ∑ i, x i * y i := by
  classical
  have := Fintype.sum_equiv (Sym.oneEquiv (α := Fin n))
    (fun i => x i * y i) (fun β : Sym (Fin n) 1 => monoVal x β.1 * monoVal y β.1)
    (fun i => by
      show x i * y i = (Multiset.map x {i}).prod * (Multiset.map y {i}).prod
      simp)
  exact this.symm

lemma sum_sym_zero (x y : Fin n → ℝ) :
    ∑ β : Sym (Fin n) 0, monoVal x β.1 * monoVal y β.1 = 1 := by
  classical
  rw [Fintype.sum_unique]
  simp [monoVal, Sym.eq_nil_of_card_zero]

theorem kap_formula (n : ℕ) (x y : Fin n → ℝ) :
    kap x y = ∑ i, x i * y i + ((∑ i, x i * y i) ^ 2 + ∑ i, x i ^ 2 * y i ^ 2) / 2 := by
  classical
  unfold kap pf
  rw [sumJJ (fun p => phiM x p * phiM y p), Fintype.sum_sigma, Fin.sum_univ_three]
  have e0 := sum_sym_zero x y
  have e1 := sum_sym_one x y
  have e2 := sum_sym_two x y
  simp only [phiM] at *
  have hd : monoVal x (default : Mono n 2).2.1 * monoVal y (default : Mono n 2).2.1 = 1 := by
    simp [monoVal, default]
  erw [e0, e1, e2, hd]
  ring

/-! ## The feature operator bound -/

theorem featOp3 (n : ℕ) (hn : 1 ≤ n) : FeatOp n 3 := by
  classical
  intro c
  let a : Mono n 2 → ℝ := fun p => if h : p ≠ default then c ⟨p, h⟩ else 0
  have ha0 : a default = 0 := by simp [a]
  have haq : ∀ q : JJ n, a q.1 = c q := fun q => by simp [a, q.2]
  have h := BstLean.Part71.Feat71.featureBound 2 n hn a ha0
  have e1 : ∀ x : Fin n → ℝ, ∑ q : JJ n, c q * pf x q = ∑ p, a p * phiM x p := by
    intro x
    rw [← sumJJ0 (fun p => a p * phiM x p) (by simp [ha0])]
    exact Finset.sum_congr rfl (fun q _ => by rw [haq]; rfl)
  have e2 : ∑ q : JJ n, c q ^ 2 = BstLean.Part53.nsq a := by
    unfold BstLean.Part53.nsq
    rw [← sumJJ0 (fun p => a p ^ 2) (by simp [ha0])]
    exact Finset.sum_congr rfl (fun q _ => by rw [haq])
  simp_rw [e1]
  rw [e2]
  convert h using 2
  norm_num

/-! ## Sphere constants -/

lemma sphere_cont_integrable78 (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

/-- `q(x) = Σ_i x_i⁴`. -/
def q4 (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 4

lemma kap_diag_sphere (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    kap x x = 3 / 2 + q4 x / 2 := by
  rw [kap_formula]
  have h1 : ∑ i, x i * x i = 1 := by rw [← hx]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : ∑ i, x i ^ 2 * x i ^ 2 = q4 x := Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, h2]; ring

lemma q4_nonneg (x : Fin n → ℝ) : 0 ≤ q4 x :=
  Finset.sum_nonneg (fun i _ => by positivity)

lemma q4_le_one (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : q4 x ≤ 1 := by
  rw [← hx]
  apply Finset.sum_le_sum
  intro i _
  have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  rw [hx] at hi
  nlinarith [sq_nonneg (x i)]

lemma kap_diag_le_two (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : kap x x ≤ 2 := by
  rw [kap_diag_sphere x hx]; linarith [q4_le_one x hx]

lemma kap_diag_cont : Continuous (fun x : Fin n → ℝ => kap x x) := by
  have : (fun x : Fin n → ℝ => kap x x) = fun x =>
      ∑ i, x i * x i + ((∑ i, x i * x i) ^ 2 + ∑ i, x i ^ 2 * x i ^ 2) / 2 :=
    funext (fun x => kap_formula n x x)
  rw [this]; fun_prop

lemma q4_cont : Continuous (q4 (n := n)) := by unfold q4; fun_prop

lemma integral_q4 (hn : 1 ≤ n) : ∫ x, q4 x ∂uniformSphere n = 3 / ((n : ℝ) + 2) := by
  have hM := BstLean.Part29.uniformSphere_moments n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have e : ∀ x : Fin n → ℝ, q4 x = ∑ i, x i * x i * x i * x i :=
    fun x => Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ => hM.int4 i i i i)]
  simp_rw [hM.m4]
  simp only [and_self, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

lemma tG_eq (hn : 1 ≤ n) : tG n = 3 / 2 + 3 / (2 * ((n : ℝ) + 2)) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold tG
  have h : (fun x : Fin n → ℝ => kap x x) =ᵐ[uniformSphere n] fun x => 3 / 2 + q4 x / 2 := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact kap_diag_sphere x hx
  have hA : ∫ x, (3 / 2 + q4 x / 2) ∂uniformSphere n
      = ∫ _x : Fin n → ℝ, (3 / 2 : ℝ) ∂uniformSphere n + ∫ x, q4 x / 2 ∂uniformSphere n :=
    integral_add (integrable_const _) ((sphere_cont_integrable78 hn q4_cont).div_const 2)
  have hB : ∫ x, q4 x / 2 ∂uniformSphere n = (∫ x, q4 x ∂uniformSphere n) / 2 := integral_div _ _
  rw [integral_congr_ae h, hA, hB, integral_q4 hn]
  have hp : (n : ℝ) + 2 ≠ 0 := by positivity
  simp
  field_simp

lemma inner_kap (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∫ y, kap x y ∂uniformSphere n = (∑ i, x i ^ 2) / n := by
  have hM := BstLean.Part29.uniformSphere_moments n hn
  have e : ∀ y : Fin n → ℝ, kap x y = ∑ i, x i * y i
      + ((∑ i, ∑ j, x i * x j * (y i * y j)) + ∑ i, x i ^ 2 * (y i * y i)) / 2 := by
    intro y
    have a1 : (∑ i, x i * y i) ^ 2 = ∑ i, ∑ j, x i * x j * (y i * y j) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    have a2 : ∑ i, x i ^ 2 * y i ^ 2 = ∑ i, x i ^ 2 * (y i * y i) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [kap_formula, a1, a2]
  simp_rw [e]
  have i1 : Integrable (fun y : Fin n → ℝ => ∑ i, x i * y i) (uniformSphere n) :=
    integrable_finsetSum _ (fun i _ => (hM.int1 i).const_mul _)
  have i2 : Integrable (fun y : Fin n → ℝ => ∑ i, ∑ j, x i * x j * (y i * y j)) (uniformSphere n) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hM.int2 i j).const_mul _))
  have i3 : Integrable (fun y : Fin n → ℝ => ∑ i, x i ^ 2 * (y i * y i)) (uniformSphere n) :=
    integrable_finsetSum _ (fun i _ => (hM.int2 i i).const_mul _)
  have hA : ∫ y, (∑ i, x i * y i
      + ((∑ i, ∑ j, x i * x j * (y i * y j)) + ∑ i, x i ^ 2 * (y i * y i)) / 2) ∂uniformSphere n
      = ∫ y, ∑ i, x i * y i ∂uniformSphere n
        + ∫ y, ((∑ i, ∑ j, x i * x j * (y i * y j)) + ∑ i, x i ^ 2 * (y i * y i)) / 2
            ∂uniformSphere n :=
    integral_add i1 ((i2.add i3).div_const 2)
  have hB : ∫ y, ((∑ i, ∑ j, x i * x j * (y i * y j)) + ∑ i, x i ^ 2 * (y i * y i)) / 2
            ∂uniformSphere n
      = (∫ y, ((∑ i, ∑ j, x i * x j * (y i * y j)) + ∑ i, x i ^ 2 * (y i * y i))
            ∂uniformSphere n) / 2 := integral_div _ _
  have hC : ∫ y, ((∑ i, ∑ j, x i * x j * (y i * y j)) + ∑ i, x i ^ 2 * (y i * y i))
            ∂uniformSphere n
      = ∫ y, (∑ i, ∑ j, x i * x j * (y i * y j)) ∂uniformSphere n
        + ∫ y, ∑ i, x i ^ 2 * (y i * y i) ∂uniformSphere n := integral_add i2 i3
  rw [hA, hB, hC,
    integral_finsetSum _ (fun i _ => (hM.int1 i).const_mul _),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hM.int2 i j).const_mul _)),
    integral_finsetSum _ (fun i _ => (hM.int2 i i).const_mul _)]
  have s1 : ∑ i, ∫ y, x i * y i ∂uniformSphere n = 0 := by
    apply Finset.sum_eq_zero; intro i _
    rw [integral_const_mul, hM.m1, mul_zero]
  have s3 : ∑ i, ∫ y, x i ^ 2 * (y i * y i) ∂uniformSphere n = (∑ i, x i ^ 2) / n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [integral_const_mul, hM.m2]; simp; ring
  have s2 : ∑ i, ∫ y, ∑ j, x i * x j * (y i * y j) ∂uniformSphere n = (∑ i, x i ^ 2) / n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [integral_finsetSum _ (fun j _ => (hM.int2 i j).const_mul _)]
    simp_rw [integral_const_mul, hM.m2]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  rw [s1, s2, s3]; ring

lemma mm1_eq (hn : 1 ≤ n) : mm1 n = 1 / (n : ℝ) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold mm1
  simp_rw [inner_kap hn]
  have h : (fun x : Fin n → ℝ => (∑ i, x i ^ 2) / (n : ℝ)) =ᵐ[uniformSphere n]
      fun _ => 1 / (n : ℝ) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    rw [hx]
  rw [integral_congr_ae h]; simp

lemma kk2_bounds (hn : 1 ≤ n) :
    tG n ^ 2 ≤ kk2 n ∧ kk2 n ≤ tG n ^ 2 + 3 / (4 * ((n : ℝ) + 2)) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have iK : Integrable (fun x : Fin n → ℝ => kap x x) (uniformSphere n) :=
    sphere_cont_integrable78 hn kap_diag_cont
  have iK2 : Integrable (fun x : Fin n → ℝ => kap x x ^ 2) (uniformSphere n) :=
    sphere_cont_integrable78 hn (kap_diag_cont.pow 2)
  have ex : ∀ c : ℝ, ∫ x, (kap x x - c) ^ 2 ∂uniformSphere n = kk2 n - 2 * c * tG n + c ^ 2 := by
    intro c
    have e : ∀ x : Fin n → ℝ, (kap x x - c) ^ 2 = kap x x ^ 2 - 2 * c * kap x x + c ^ 2 :=
      fun x => by ring
    simp_rw [e]
    have hA : ∫ x, (kap x x ^ 2 - 2 * c * kap x x + c ^ 2) ∂uniformSphere n
        = ∫ x, (kap x x ^ 2 - 2 * c * kap x x) ∂uniformSphere n
          + ∫ _x : Fin n → ℝ, c ^ 2 ∂uniformSphere n :=
      integral_add (iK2.sub (iK.const_mul _)) (integrable_const _)
    have hB : ∫ x, (kap x x ^ 2 - 2 * c * kap x x) ∂uniformSphere n
        = ∫ x, kap x x ^ 2 ∂uniformSphere n - ∫ x, 2 * c * kap x x ∂uniformSphere n :=
      integral_sub iK2 (iK.const_mul _)
    rw [hA, hB, integral_const_mul]
    simp [kk2, tG]
  constructor
  · have h := ex (tG n)
    have h0 : 0 ≤ ∫ x, (kap x x - tG n) ^ 2 ∂uniformSphere n :=
      integral_nonneg (fun x => sq_nonneg _)
    nlinarith
  · have h := ex (3 / 2)
    have hle : ∫ x, (kap x x - 3 / 2) ^ 2 ∂uniformSphere n ≤ ∫ x, q4 x / 4 ∂uniformSphere n := by
      apply integral_mono_ae
        (sphere_cont_integrable78 hn ((kap_diag_cont.sub continuous_const).pow 2))
        ((sphere_cont_integrable78 hn q4_cont).div_const 4)
      filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
      show (kap x x - 3 / 2) ^ 2 ≤ q4 x / 4
      rw [kap_diag_sphere x hx]
      nlinarith [q4_nonneg x, q4_le_one x hx]
    rw [integral_div, integral_q4 hn] at hle
    have e3 : 3 / ((n : ℝ) + 2) / 4 = 3 / (4 * ((n : ℝ) + 2)) := by
      rw [div_div, mul_comm]
    rw [e3] at hle
    nlinarith [sq_nonneg (tG n - 3 / 2)]

lemma ss2_nonneg (n : ℕ) : 0 ≤ ss2 n :=
  integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))

lemma ss2_le (hn : 1 ≤ n) : ss2 n ≤ 3 * tG n / (n : ℝ) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have iK : Integrable (fun x : Fin n → ℝ => kap x x) (uniformSphere n) :=
    sphere_cont_integrable78 hn kap_diag_cont
  have hin : ∀ x : Fin n → ℝ,
      ∫ y, kap x y ^ 2 ∂uniformSphere n ≤ 3 / (n : ℝ) * kap x x := by
    intro x
    have h := featOp3 n hn (fun q => pf x q)
    have e : (∑ q : JJ n, pf x q ^ 2) = kap x x := by
      unfold kap; exact Finset.sum_congr rfl (fun q _ => by ring)
    rw [e] at h
    exact h
  have h1 : ss2 n ≤ ∫ x, 3 / (n : ℝ) * kap x x ∂uniformSphere n := by
    unfold ss2
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
      (iK.const_mul _) (Filter.Eventually.of_forall hin)
  rw [integral_const_mul] at h1
  have e : 3 * tG n / (n : ℝ) = 3 / (n : ℝ) * tG n := by ring
  rw [e]; exact h1

theorem sphereConsts (n : ℕ) (hn : 1 ≤ n) : SphereConsts n (3 * tG n) :=
  ⟨tG_eq hn, mm1_eq hn, (kk2_bounds hn).1, (kk2_bounds hn).2, ss2_nonneg n, ss2_le hn,
    fun x hx => kap_diag_le_two x hx⟩

end BstLean.Part78

#print axioms BstLean.Part78.featOp3
#print axioms BstLean.Part78.kap_formula
#print axioms BstLean.Part78.sphereConsts
