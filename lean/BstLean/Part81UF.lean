import BstLean.Part81F3Gen
import BstLean.Part81KDElem
import BstLean.Part78Mean

/-!
# Part 81 (UF): the feature operator bound from a row integral

`featOp_of_row`: if `∫ x_i² Σ_{k ≤ d/2} h_k(x²) dσ ≤ Cr/n` for every coordinate `i`, then
`FeatOp n d Cr`. The Schur test of `Part71Feature`, with the class sum bounded by the complete
homogeneous sums of degree `≤ d/2` (the halves `gam q` have `2·card ≤ card q ≤ d`).
Do not use `sorry`, `native_decide` or `axiom`.
-/
namespace BstLean.Part81.UF
open MeasureTheory BstLean.Part53
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM)
open BstLean.Part81.KD (prodMapUniv mom mom_nonneg mom_odd)
variable {n d : ℕ}

noncomputable def oddP (u : Multiset (Fin n)) (x : Fin n → ℝ) : ℝ := ∏ i, |x i| ^ (u.count i % 2)

noncomputable def gam (u : Multiset (Fin n)) : Multiset (Fin n) :=
  (Finset.univ : Finset (Fin n)).val.bind (fun i => Multiset.replicate (u.count i / 2) i)

lemma count_gam (u : Multiset (Fin n)) (j : Fin n) : (gam u).count j = u.count j / 2 := by
  classical
  unfold gam
  rw [Multiset.count_bind]
  rw [show ((Finset.univ : Finset (Fin n)).val.map fun i => Multiset.count j (Multiset.replicate (u.count i / 2) i)).sum
      = ∑ i, Multiset.count j (Multiset.replicate (u.count i / 2) i) from rfl]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Multiset.count_replicate, hij]
  · simp

lemma card_gam_le (u : Multiset (Fin n)) : Multiset.card (gam u) ≤ Multiset.card u := by
  classical
  have h1 : Multiset.card (gam u) = ∑ i, (gam u).count i := (Multiset.sum_count_eq_card (by simp)).symm
  have h2 : Multiset.card u = ∑ i, u.count i := (Multiset.sum_count_eq_card (by simp)).symm
  rw [h1, h2]
  apply Finset.sum_le_sum; intro i _
  rw [count_gam]; exact Nat.div_le_self _ _

lemma abs_mono_split (u : Multiset (Fin n)) (x : Fin n → ℝ) :
    |monoVal x u| = oddP u x * monoVal (fun i => x i ^ 2) (gam u) := by
  classical
  unfold monoVal oddP
  rw [prodMapUniv, prodMapUniv, Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  rw [count_gam, abs_pow]
  conv_lhs => rw [← Nat.mod_add_div (u.count i) 2]
  rw [pow_add, pow_mul, sq_abs]

lemma mono_ext (p q : Mono n d) (h : (p.2 : Multiset (Fin n)) = (q.2 : Multiset (Fin n))) : p = q := by
  obtain ⟨i, s⟩ := p
  obtain ⟨j, t⟩ := q
  have hij : i = j := by
    apply Fin.ext
    have hs := s.2
    have ht := t.2
    simp only at h
    calc (i : ℕ) = Multiset.card (s : Multiset (Fin n)) := hs.symm
      _ = Multiset.card (t : Multiset (Fin n)) := congrArg _ h
      _ = j := ht
  subst hij
  have : s = t := Subtype.ext h
  subst this
  rfl

lemma two_card_gam_le (u : Multiset (Fin n)) : 2 * Multiset.card (gam u) ≤ Multiset.card u := by
  classical
  have h1 : Multiset.card (gam u) = ∑ i, (gam u).count i := (Multiset.sum_count_eq_card (by simp)).symm
  have h2 : Multiset.card u = ∑ i, u.count i := (Multiset.sum_count_eq_card (by simp)).symm
  rw [h1, h2, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [count_gam]; omega

lemma class_bound (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (x : Fin n → ℝ)
    (hxz : ∀ i, z i = x i ^ 2) (p : Mono n d) :
    ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2),
      |monoVal x q.2.1| ≤ oddP p.2.1 x * ∑ k ∈ Finset.range (d / 2 + 1), hS53 z k := by
  classical
  have hzx : (fun i => x i ^ 2) = z := funext fun i => (hxz i).symm
  let emb : Mono n d → Mono n (d / 2) := fun q =>
    ⟨⟨Multiset.card (gam q.2.1), by
        have h1 := two_card_gam_le q.2.1
        have h2 := q.2.2
        have h3 := q.1.2
        omega⟩,
      ⟨gam q.2.1, rfl⟩⟩
  have hinj : Set.InjOn emb ((Finset.univ : Finset (Mono n d)).filter
      (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)) := by
    intro q hq q' hq' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq hq'
    have hg : gam q.2.1 = gam q'.2.1 := congrArg (fun g : Mono n (d / 2) => (g.2 : Multiset (Fin n))) he
    apply mono_ext
    ext i
    show q.2.1.count i = q'.2.1.count i
    have h2 := congrArg (fun m => m.count i) hg
    simp only [count_gam] at h2
    have := Nat.mod_add_div (q.2.1.count i) 2
    have := Nat.mod_add_div (q'.2.1.count i) 2
    have := hq i
    have := hq' i
    omega
  have hsum : ∑ g : Mono n (d / 2), monoVal z g.2.1 = ∑ k ∈ Finset.range (d / 2 + 1), hS53 z k := by
    rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun k => hS53 z k)]
    rfl
  have hoddp : 0 ≤ oddP p.2.1 x := by unfold oddP; positivity
  calc ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2),
        |monoVal x q.2.1|
      ≤ ∑ g : Mono n (d / 2), oddP p.2.1 x * monoVal z g.2.1 := by
        apply Finset.sum_le_sum_of_injOn emb hinj (Finset.subset_univ _)
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rw [abs_mono_split, hzx]
          have : oddP q.2.1 x = oddP p.2.1 x := by
            unfold oddP; apply Finset.prod_congr rfl; intro i _; rw [hq i]
          rw [this]
        · intro g _ _
          exact mul_nonneg hoddp (Multiset.prod_nonneg fun a ha => by
            obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp ha; exact hz b)
    _ = oddP p.2.1 x * ∑ k ∈ Finset.range (d / 2 + 1), hS53 z k := by rw [← hsum, Finset.mul_sum]

lemma prod_le_one_factor (f : Fin n → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) (i : Fin n) :
    ∏ j, f j ≤ f i := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i, f j ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (hf j).1) (fun j _ => (hf j).2)
  have h0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j := Finset.prod_nonneg fun j _ => (hf j).1
  nlinarith [(hf i).1]

lemma abs_le_one_of_sphere {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (j : Fin n) : |x j| ≤ 1 := by
  have := Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  rw [hx] at this
  exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

lemma L4 (p : Mono n d) (hp : p ≠ default) :
    ∃ i : Fin n, ∀ x : Fin n → ℝ, ∑ j, x j ^ 2 = 1 → |monoVal x p.2.1| * oddP p.2.1 x ≤ x i ^ 2 := by
  classical
  have habs : ∀ x : Fin n → ℝ, |monoVal x p.2.1| = ∏ j, |x j| ^ p.2.1.count j := by
    intro x; unfold monoVal; rw [prodMapUniv, Finset.abs_prod]; simp [abs_pow]
  by_cases hodd : ∃ i, p.2.1.count i % 2 = 1
  · obtain ⟨i, hi⟩ := hodd
    refine ⟨i, fun x hx => ?_⟩
    have hb : ∀ j, 0 ≤ |x j| ∧ |x j| ≤ 1 := fun j => ⟨abs_nonneg _, abs_le_one_of_sphere hx j⟩
    have h1 : |monoVal x p.2.1| ≤ |x i| := by
      rw [habs]
      calc ∏ j, |x j| ^ p.2.1.count j ≤ |x i| ^ p.2.1.count i :=
            prod_le_one_factor _ (fun j => ⟨pow_nonneg (hb j).1 _, pow_le_one₀ (hb j).1 (hb j).2⟩) i
        _ ≤ |x i| := pow_le_of_le_one (hb i).1 (hb i).2 (by omega)
    have h2 : oddP p.2.1 x ≤ |x i| := by
      unfold oddP
      calc ∏ j, |x j| ^ (p.2.1.count j % 2) ≤ |x i| ^ (p.2.1.count i % 2) :=
            prod_le_one_factor _ (fun j => ⟨pow_nonneg (hb j).1 _, pow_le_one₀ (hb j).1 (hb j).2⟩) i
        _ = |x i| := by rw [hi, pow_one]
    have h3 : 0 ≤ oddP p.2.1 x := by unfold oddP; positivity
    calc |monoVal x p.2.1| * oddP p.2.1 x ≤ |x i| * |x i| :=
          mul_le_mul h1 h2 h3 (abs_nonneg _)
      _ = x i ^ 2 := by rw [← sq, sq_abs]
  · push Not at hodd
    have hcard : 1 ≤ Multiset.card p.2.1 := by
      by_contra h0
      push Not at h0
      apply hp
      apply mono_ext
      have : Multiset.card p.2.1 = 0 := by omega
      show p.2.1 = (default : Mono n d).2.1
      rw [Multiset.card_eq_zero.mp this]
      rfl
    obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card p.2.1)
    have hci : 2 ≤ p.2.1.count i := by
      have h1 := Multiset.count_pos.mpr hi
      have h2 := hodd i
      omega
    refine ⟨i, fun x hx => ?_⟩
    have hb : ∀ j, 0 ≤ |x j| ∧ |x j| ≤ 1 := fun j => ⟨abs_nonneg _, abs_le_one_of_sphere hx j⟩
    have hoddP : oddP p.2.1 x = 1 := by
      unfold oddP
      apply Finset.prod_eq_one; intro j _
      have := hodd j
      have : p.2.1.count j % 2 = 0 := by omega
      rw [this, pow_zero]
    rw [hoddP, mul_one, habs]
    calc ∏ j, |x j| ^ p.2.1.count j ≤ |x i| ^ p.2.1.count i :=
          prod_le_one_factor _ (fun j => ⟨pow_nonneg (hb j).1 _, pow_le_one₀ (hb j).1 (hb j).2⟩) i
      _ ≤ |x i| ^ 2 := pow_le_pow_of_le_one (hb i).1 (hb i).2 hci
      _ = x i ^ 2 := sq_abs _

lemma monoVal_add (x : Fin n → ℝ) (u v : Multiset (Fin n)) :
    monoVal x (u + v) = monoVal x u * monoVal x v := by
  unfold monoVal; rw [Multiset.map_add, Multiset.prod_add]

noncomputable def Mpq (p q : Mono n d) : ℝ := ∫ x, monoVal x (p.2.1 + q.2.1) ∂uniformSphere n

lemma cont_hS (k : ℕ) : Continuous (fun x : Fin n → ℝ => hS53 (fun l => x l ^ 2) k) := by
  unfold hS53
  simp_rw [prodMapUniv]
  fun_prop

lemma hS_nonneg (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (k : ℕ) : 0 ≤ hS53 z k :=
  Finset.sum_nonneg fun s _ => KD.prodNonneg53 z hz _

lemma Rp_bound (hn : 1 ≤ n) (Cr : ℝ)
    (hrow : ∀ i : Fin n, ∫ x, x i ^ 2 *
        (∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) ∂uniformSphere n ≤ Cr / (n : ℝ))
    (p : Mono n d) (hp : p ≠ default) :
    ∑ q : Mono n d, Mpq p q ≤ Cr / n := by
  classical
  set cls := (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q : Mono n d => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)]
  have hzero : ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter
      (fun q => ¬ ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2), Mpq p q = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    push Not at hq
    obtain ⟨i, hi⟩ := hq
    apply mom_odd hn
    refine ⟨i, ?_⟩
    rw [Multiset.count_add, Nat.even_add]
    intro h
    apply hi
    rcases Nat.even_or_odd (p.2.1.count i) with he | ho
    · have := h.mp he
      rw [Nat.even_iff.mp he, Nat.even_iff.mp this]
    · have h' : ¬ Even (q.2.1.count i) := fun hq => (Nat.not_even_iff_odd.mpr ho) (h.mpr hq)
      rw [Nat.odd_iff.mp ho, Nat.odd_iff.mp (Nat.not_even_iff_odd.mp h')]
  rw [hzero, add_zero]
  obtain ⟨i, hi⟩ := L4 p hp
  have hint : ∀ q : Mono n d, Integrable (fun x => monoVal x p.2.1 * monoVal x q.2.1) (uniformSphere n) := by
    intro q
    simp_rw [← monoVal_add]
    exact (mom hn _).1
  have hcont : Continuous (fun x : Fin n → ℝ => x i ^ 2 *
      (∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k)) :=
    ((continuous_apply i).pow 2).mul (continuous_finsetSum _ fun k _ => cont_hS k)
  refine le_trans ?_ (hrow i)
  calc ∑ q ∈ cls, Mpq p q = ∫ x, ∑ q ∈ cls, monoVal x p.2.1 * monoVal x q.2.1 ∂uniformSphere n := by
        rw [integral_finsetSum _ fun q _ => hint q]
        apply Finset.sum_congr rfl; intro q _
        unfold Mpq; simp_rw [monoVal_add]
    _ ≤ _ := by
        apply integral_mono_ae (integrable_finsetSum _ fun q _ => hint q)
          (BstLean.Part78.sph_int hn hcont)
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
        have hcb := class_bound (d := d) (fun j => x j ^ 2) (fun j => sq_nonneg _) x (fun _ => rfl) p
        have hS0 : 0 ≤ ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k :=
          Finset.sum_nonneg fun k _ => hS_nonneg _ (fun j => sq_nonneg _) k
        calc ∑ q ∈ cls, monoVal x p.2.1 * monoVal x q.2.1
            ≤ ∑ q ∈ cls, |monoVal x p.2.1| * |monoVal x q.2.1| :=
              Finset.sum_le_sum fun q _ => by rw [← abs_mul]; exact le_abs_self _
          _ = |monoVal x p.2.1| * ∑ q ∈ cls, |monoVal x q.2.1| := by rw [Finset.mul_sum]
          _ ≤ |monoVal x p.2.1| * (oddP p.2.1 x *
                ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) :=
              mul_le_mul_of_nonneg_left hcb (abs_nonneg _)
          _ = (|monoVal x p.2.1| * oddP p.2.1 x) *
                ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k := by ring
          _ ≤ x i ^ 2 * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k :=
              mul_le_mul_of_nonneg_right (hi x hx) hS0

lemma Mpq_symm (p q : Mono n d) : Mpq p q = Mpq q p := by
  unfold Mpq; rw [add_comm]

/-- The Schur test with the row integral as a hypothesis. -/
theorem featureBound_of_row (hn : 1 ≤ n) (Cr : ℝ)
    (hrow : ∀ i : Fin n, ∫ x, x i ^ 2 *
        (∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) ∂uniformSphere n ≤ Cr / (n : ℝ))
    (a : Mono n d → ℝ) (ha0 : a default = 0) :
    ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂uniformSphere n ≤ Cr / (n : ℝ) * ∑ p, a p ^ 2 := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hint : ∀ p q : Mono n d, Integrable (fun x => a p * a q * monoVal x (p.2.1 + q.2.1)) (uniformSphere n) :=
    fun p q => (mom hn _).1.const_mul _
  have hexp : ∀ x : Fin n → ℝ, (∑ p, a p * phiM x p) ^ 2 =
      ∑ p, ∑ q, a p * a q * monoVal x (p.2.1 + q.2.1) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [monoVal_add]; unfold phiM; ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
  simp_rw [integral_finsetSum _ fun q _ => hint _ q, integral_const_mul]
  have hM0 : ∀ p q : Mono n d, 0 ≤ Mpq p q := fun p q => mom_nonneg hn _
  calc ∑ p, ∑ q, a p * a q * ∫ x, monoVal x (p.2.1 + q.2.1) ∂uniformSphere n
      ≤ ∑ p : Mono n d, ∑ q : Mono n d, ((a p ^ 2 + a q ^ 2) / 2) * Mpq p q := by
        apply Finset.sum_le_sum; intro p _
        apply Finset.sum_le_sum; intro q _
        apply mul_le_mul_of_nonneg_right _ (hM0 p q)
        nlinarith [sq_nonneg (a p - a q)]
    _ = ∑ p : Mono n d, a p ^ 2 * ∑ q : Mono n d, Mpq p q := by
        have e1 : ∑ p : Mono n d, ∑ q : Mono n d, ((a p ^ 2 + a q ^ 2) / 2) * Mpq p q =
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a p ^ 2 * Mpq p q) +
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a q ^ 2 * Mpq p q) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q _
          ring
        have e2 : ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a q ^ 2 * Mpq p q) =
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a p ^ 2 * Mpq p q) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro q _
          rw [Mpq_symm]
        rw [e1, e2]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p _
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q _
        ring
    _ ≤ ∑ p : Mono n d, a p ^ 2 * (Cr / n) := by
        apply Finset.sum_le_sum; intro p _
        by_cases hp : p = default
        · rw [hp, ha0]; simp
        · exact mul_le_mul_of_nonneg_left (Rp_bound hn Cr hrow p hp) (sq_nonneg _)
    _ = Cr / (n : ℝ) * ∑ p, a p ^ 2 := by rw [← Finset.sum_mul]; ring

end BstLean.Part81.UF

namespace BstLean.Part81
open MeasureTheory
open BstLean.Part29 (uniformSphere)

/-- **Feature operator bound from the row integral** `∫ x_i² Σ_{k ≤ d/2} h_k(x²) dσ ≤ Cr/n`. -/
theorem featOp_of_row (n d : ℕ) (hn : 1 ≤ n) (Cr : ℝ)
    (hrow : ∀ i : Fin n, ∫ x, x i ^ 2 *
        (∑ k ∈ Finset.range (d / 2 + 1), BstLean.Part53.hS53 (fun l => x l ^ 2) k)
          ∂uniformSphere n ≤ Cr / (n : ℝ)) :
    FeatOp n d Cr :=
  F3.featOp_of_mono _ fun a ha0 => UF.featureBound_of_row hn Cr hrow a ha0

end BstLean.Part81

#print axioms BstLean.Part81.featOp_of_row
