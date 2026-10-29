import BstLean.Part81F3Gen
import BstLean.Part78Sphere

/-!
# Part 81 (F3, rows): Schur test by degree block for the sphere Gram matrix of monomials

`Mpq p q = E x^{p+q}` under the uniform distribution on the sphere. This file proves

* `row_bound`: the row sum of `Mpq` over the monomials of the same degree as `p` is at most
  `E g` whenever `|x^p| · oddP_p(x) ≤ g(x)` on the sphere;
* `schur_deg`: the Schur test for a coefficient vector supported on one degree;
* `cross_zero`: blocks of opposite parity are orthogonal.

The first lemmas are copies of private lemmas of `Part71Feature.lean`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part81.F3

open MeasureTheory BstLean.Part53
open BstLean.Part29 (uniformSphere gaussMom)
open BstLean.Part36 (monoVal gpm rhoD)
open BstLean.Part41 (Mono phiM)

variable {n d : ℕ}

lemma multinomId (z : Fin n → ℝ) (j : ℕ) :
    (∑ i, z i) ^ j = ∑ s : Sym (Fin n) j, (s.1.countPerms : ℝ) * (s.1.map z).prod := by
  classical
  rw [Finset.sum_pow, Finset.sym_univ]

lemma prodNonneg (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (m : Multiset (Fin n)) :
    0 ≤ (m.map z).prod :=
  Multiset.prod_nonneg (fun a ha => by
    obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp ha
    exact hz b)

lemma hSLeOne (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (j : ℕ) :
    ∑ s : Sym (Fin n) j, (s.1.map z).prod ≤ 1 := by
  classical
  have h := multinomId z j
  rw [h1, one_pow] at h
  rw [h]
  apply Finset.sum_le_sum
  intro s _
  have hcp : (1 : ℝ) ≤ s.1.countPerms := by
    have := Nat.multinomial_pos (s := s.1.toFinsupp.support) (f := s.1.toFinsupp)
    unfold Multiset.countPerms
    rw [Finsupp.multinomial_eq]
    exact_mod_cast this
  exact le_mul_of_one_le_left (prodNonneg z hz _) hcp

lemma prodMapUniv (f : Fin n → ℝ) (u : Multiset (Fin n)) :
    (u.map f).prod = ∏ i, f i ^ u.count i := by
  classical
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Multiset.count_eq_zero.mpr (by simpa using hi), pow_zero]

lemma gpm_nonneg (u : Multiset (Fin n)) : 0 ≤ gpm u := by
  unfold gpm
  apply Finset.prod_nonneg; intro i _
  unfold gaussMom; split_ifs <;> positivity

lemma rhoD_pos (hn : 1 ≤ n) (r : ℕ) : 0 < rhoD n r := by
  unfold rhoD
  apply Finset.prod_pos; intro j _
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

lemma mom (hn : 1 ≤ n) (u : Multiset (Fin n)) :
    Integrable (fun x => monoVal x u) (uniformSphere n) ∧
      ∫ x, monoVal x u ∂uniformSphere n = gpm u / rhoD n (Multiset.card u / 2) :=
  BstLean.Part36.sphere_multiset (uniformSphere n) (BstLean.Part33.uniformSphere_prod n _ hn) u
    le_rfl

lemma mom_nonneg (hn : 1 ≤ n) (u : Multiset (Fin n)) :
    0 ≤ ∫ x, monoVal x u ∂uniformSphere n := by
  rw [(mom hn u).2]; exact div_nonneg (gpm_nonneg u) (rhoD_pos hn _).le

lemma mom_odd (hn : 1 ≤ n) (u : Multiset (Fin n)) (h : ∃ i, ¬ Even (u.count i)) :
    ∫ x, monoVal x u ∂uniformSphere n = 0 := by
  rw [(mom hn u).2]
  obtain ⟨i, hi⟩ := h
  have : gpm u = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [gaussMom, hi])
  rw [this, zero_div]

/-- The product of the odd parts `∏ |x_i|^{c_i mod 2}`. -/
noncomputable def oddP (u : Multiset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ∏ i, |x i| ^ (u.count i % 2)

/-- The halved multiset: counts `c_i / 2`. -/
noncomputable def gam (u : Multiset (Fin n)) : Multiset (Fin n) :=
  (Finset.univ : Finset (Fin n)).val.bind (fun i => Multiset.replicate (u.count i / 2) i)

lemma count_gam (u : Multiset (Fin n)) (j : Fin n) : (gam u).count j = u.count j / 2 := by
  classical
  unfold gam
  rw [Multiset.count_bind]
  rw [show ((Finset.univ : Finset (Fin n)).val.map
      fun i => Multiset.count j (Multiset.replicate (u.count i / 2) i)).sum
      = ∑ i, Multiset.count j (Multiset.replicate (u.count i / 2) i) from rfl]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Multiset.count_replicate, hij]
  · simp

lemma card_gam (u : Multiset (Fin n)) :
    2 * Multiset.card (gam u) + ∑ i, u.count i % 2 = Multiset.card u := by
  classical
  have h1 : Multiset.card (gam u) = ∑ i, (gam u).count i :=
    (Multiset.sum_count_eq_card (by simp)).symm
  have h2 : Multiset.card u = ∑ i, u.count i := (Multiset.sum_count_eq_card (by simp)).symm
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [count_gam]; omega

lemma card_gam_le (u : Multiset (Fin n)) : Multiset.card (gam u) ≤ Multiset.card u := by
  have := card_gam u; omega

lemma abs_mono_split (u : Multiset (Fin n)) (x : Fin n → ℝ) :
    |monoVal x u| = oddP u x * monoVal (fun i => x i ^ 2) (gam u) := by
  classical
  unfold monoVal oddP
  rw [prodMapUniv, prodMapUniv, Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro i _
  rw [count_gam, abs_pow]
  conv_lhs => rw [← Nat.mod_add_div (u.count i) 2]
  rw [pow_add, pow_mul, sq_abs]

lemma mono_ext (p q : Mono n d) (h : (p.2 : Multiset (Fin n)) = (q.2 : Multiset (Fin n))) :
    p = q := by
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

/-- The sum of `|x^q|` over the monomials `q` of the degree and the parity class of `p`. -/
lemma class_bound (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (x : Fin n → ℝ)
    (hxz : ∀ i, z i = x i ^ 2) (p : Mono n d) :
    ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter
        (fun q => q.1 = p.1 ∧ ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2),
      |monoVal x q.2.1| ≤ oddP p.2.1 x := by
  classical
  have hzx : (fun i => x i ^ 2) = z := funext fun i => (hxz i).symm
  let emb : Mono n d → Mono n d := fun q =>
    ⟨⟨Multiset.card (gam q.2.1), lt_of_le_of_lt (card_gam_le q.2.1) (by rw [q.2.2]; exact q.1.2)⟩,
      ⟨gam q.2.1, rfl⟩⟩
  set cls := (Finset.univ : Finset (Mono n d)).filter
      (fun q => q.1 = p.1 ∧ ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2) with hcls
  let k0 : Fin (d + 1) := (emb p).1
  let T := (Finset.univ : Finset (Mono n d)).filter (fun g => g.1 = k0)
  have hinj : Set.InjOn emb cls := by
    intro q hq q' hq' he
    simp only [hcls, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq hq'
    have hg : gam q.2.1 = gam q'.2.1 := congrArg (fun g : Mono n d => (g.2 : Multiset (Fin n))) he
    apply mono_ext
    ext i
    show q.2.1.count i = q'.2.1.count i
    have h2 := congrArg (fun m => m.count i) hg
    simp only [count_gam] at h2
    have := Nat.mod_add_div (q.2.1.count i) 2
    have := Nat.mod_add_div (q'.2.1.count i) 2
    have := hq.2 i
    have := hq'.2 i
    omega
  have hmaps : ∀ q ∈ cls, emb q ∈ T := by
    intro q hq
    simp only [hcls, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    show Multiset.card (gam q.2.1) = Multiset.card (gam p.2.1)
    have e1 := card_gam q.2.1
    have e2 := card_gam p.2.1
    have e3 : ∑ i, q.2.1.count i % 2 = ∑ i, p.2.1.count i % 2 :=
      Finset.sum_congr rfl fun i _ => hq.2 i
    have e4 : Multiset.card q.2.1 = Multiset.card p.2.1 := by
      rw [q.2.2, p.2.2, hq.1]
    omega
  have hsum : ∑ g ∈ T, monoVal z g.2.1 ≤ 1 := by
    simp only [T]
    rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single k0]
    · simp only [ite_true]
      exact hSLeOne z hz h1 k0
    · intro m _ hm
      simp [hm]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hoddp : 0 ≤ oddP p.2.1 x := by unfold oddP; positivity
  calc ∑ q ∈ cls, |monoVal x q.2.1|
      ≤ ∑ g ∈ T, oddP p.2.1 x * monoVal z g.2.1 := by
        apply Finset.sum_le_sum_of_injOn emb hinj
        · exact Finset.image_subset_iff.mpr hmaps
        · intro q hq
          simp only [hcls, Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rw [abs_mono_split, hzx]
          have : oddP q.2.1 x = oddP p.2.1 x := by
            unfold oddP; apply Finset.prod_congr rfl; intro i _; rw [hq.2 i]
          rw [this]
        · intro g _ _
          exact mul_nonneg hoddp (prodNonneg z hz _)
    _ = oddP p.2.1 x * ∑ g ∈ T, monoVal z g.2.1 := by rw [Finset.mul_sum]
    _ ≤ oddP p.2.1 x * 1 := mul_le_mul_of_nonneg_left hsum hoddp
    _ = oddP p.2.1 x := mul_one _

lemma monoVal_add (x : Fin n → ℝ) (u v : Multiset (Fin n)) :
    monoVal x (u + v) = monoVal x u * monoVal x v := by
  unfold monoVal; rw [Multiset.map_add, Multiset.prod_add]

/-- The Gram matrix of the monomials: `E x^{p+q}`. -/
noncomputable def Mpq (p q : Mono n d) : ℝ := ∫ x, monoVal x (p.2.1 + q.2.1) ∂uniformSphere n

lemma Mpq_symm (p q : Mono n d) : Mpq p q = Mpq q p := by
  unfold Mpq; rw [add_comm]

lemma Mpq_nonneg (hn : 1 ≤ n) (p q : Mono n d) : 0 ≤ Mpq p q := mom_nonneg hn _

lemma odd_card_count (u : Multiset (Fin n)) (h : Odd (Multiset.card u)) :
    ∃ i, ¬ Even (u.count i) := by
  classical
  by_contra hc
  push Not at hc
  have h2 : Multiset.card u = ∑ i, u.count i := (Multiset.sum_count_eq_card (by simp)).symm
  rw [h2] at h
  exact (Nat.not_even_iff_odd.mpr h) (Finset.even_sum _ fun i _ => hc i)

lemma Mpq_odd (hn : 1 ≤ n) (p q : Mono n d) (h : Odd ((p.1 : ℕ) + q.1)) : Mpq p q = 0 := by
  apply mom_odd hn
  apply odd_card_count
  rw [Multiset.card_add]
  have e1 : Multiset.card p.2.1 = p.1 := p.2.2
  have e2 : Multiset.card q.2.1 = q.1 := q.2.2
  rw [e1, e2]; exact h

/-- **Row sum bound** over the monomials of the degree of `p`. -/
lemma row_bound (hn : 1 ≤ n) (p : Mono n d) (g : (Fin n → ℝ) → ℝ)
    (hg : Integrable g (uniformSphere n))
    (hpt : ∀ x : Fin n → ℝ, ∑ j, x j ^ 2 = 1 → |monoVal x p.2.1| * oddP p.2.1 x ≤ g x) :
    ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => q.1 = p.1), Mpq p q ≤
      ∫ x, g x ∂uniformSphere n := by
  classical
  set cls := (Finset.univ : Finset (Mono n d)).filter
      (fun q => q.1 = p.1 ∧ ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2) with hcls
  rw [← Finset.sum_filter_add_sum_filter_not _
    (fun q : Mono n d => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)]
  have hzero : ∑ q ∈ ((Finset.univ : Finset (Mono n d)).filter (fun q => q.1 = p.1)).filter
      (fun q => ¬ ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2), Mpq p q = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨-, hq⟩ := hq
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
  rw [hzero, add_zero, Finset.filter_filter, ← hcls]
  have hint : ∀ q : Mono n d,
      Integrable (fun x => monoVal x p.2.1 * monoVal x q.2.1) (uniformSphere n) := by
    intro q
    simp_rw [← monoVal_add]
    exact (mom hn _).1
  calc ∑ q ∈ cls, Mpq p q
      = ∫ x, ∑ q ∈ cls, monoVal x p.2.1 * monoVal x q.2.1 ∂uniformSphere n := by
        rw [integral_finsetSum _ fun q _ => hint q]
        apply Finset.sum_congr rfl; intro q _
        unfold Mpq; simp_rw [monoVal_add]
    _ ≤ ∫ x, g x ∂uniformSphere n := by
        apply integral_mono_ae (integrable_finsetSum _ fun q _ => hint q) hg
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
        have hcb := class_bound (d := d) (fun j => x j ^ 2) (fun j => sq_nonneg _) hx x
          (fun _ => rfl) p
        calc ∑ q ∈ cls, monoVal x p.2.1 * monoVal x q.2.1
            ≤ ∑ q ∈ cls, |monoVal x p.2.1| * |monoVal x q.2.1| :=
              Finset.sum_le_sum fun q _ => by rw [← abs_mul]; exact le_abs_self _
          _ = |monoVal x p.2.1| * ∑ q ∈ cls, |monoVal x q.2.1| := by rw [Finset.mul_sum]
          _ ≤ |monoVal x p.2.1| * oddP p.2.1 x :=
              mul_le_mul_of_nonneg_left hcb (abs_nonneg _)
          _ ≤ g x := hpt x hx

/-- The integral of a product of two combinations of monomials. -/
lemma int_pair (hn : 1 ≤ n) (a b : Mono n d → ℝ) :
    Integrable (fun x => (∑ p, a p * phiM x p) * (∑ q, b q * phiM x q)) (uniformSphere n) ∧
      ∫ x, (∑ p, a p * phiM x p) * (∑ q, b q * phiM x q) ∂uniformSphere n =
        ∑ p, ∑ q, a p * b q * Mpq p q := by
  classical
  have hint : ∀ p q : Mono n d,
      Integrable (fun x => a p * b q * monoVal x (p.2.1 + q.2.1)) (uniformSphere n) :=
    fun p q => (mom hn _).1.const_mul _
  have hexp : ∀ x : Fin n → ℝ, (∑ p, a p * phiM x p) * (∑ q, b q * phiM x q) =
      ∑ p, ∑ q, a p * b q * monoVal x (p.2.1 + q.2.1) := by
    intro x
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [monoVal_add]; unfold phiM; ring
  simp_rw [hexp]
  refine ⟨integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q, ?_⟩
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
  simp_rw [integral_finsetSum _ fun q _ => hint _ q, integral_const_mul]
  rfl

/-- **Schur test on one degree block.** -/
lemma schur_deg (hn : 1 ≤ n) (j : Fin (d + 1)) (K : ℝ)
    (hK : ∀ p : Mono n d, p.1 = j →
      ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => q.1 = p.1), Mpq p q ≤ K)
    (a : Mono n d → ℝ) (ha : ∀ p : Mono n d, p.1 ≠ j → a p = 0) :
    ∫ x, (∑ p, a p * phiM x p) * (∑ q, a q * phiM x q) ∂uniformSphere n ≤ K * ∑ p, a p ^ 2 := by
  classical
  rw [(int_pair hn a a).2]
  let M' : Mono n d → Mono n d → ℝ := fun p q => if p.1 = j ∧ q.1 = j then Mpq p q else 0
  have hM's : ∀ p q, M' p q = M' q p := by
    intro p q; simp only [M', Mpq_symm p q, and_comm]
  calc ∑ p, ∑ q, a p * a q * Mpq p q
      ≤ ∑ p : Mono n d, ∑ q : Mono n d, ((a p ^ 2 + a q ^ 2) / 2) * M' p q := by
        apply Finset.sum_le_sum; intro p _
        apply Finset.sum_le_sum; intro q _
        by_cases hp : p.1 = j
        · by_cases hq : q.1 = j
          · simp only [M', hp, hq, and_self, ite_true]
            apply mul_le_mul_of_nonneg_right _ (Mpq_nonneg hn p q)
            nlinarith [sq_nonneg (a p - a q)]
          · simp [M', hq, ha q hq]
        · simp [M', hp, ha p hp]
    _ = ∑ p : Mono n d, a p ^ 2 * ∑ q : Mono n d, M' p q := by
        have e1 : ∑ p : Mono n d, ∑ q : Mono n d, ((a p ^ 2 + a q ^ 2) / 2) * M' p q =
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a p ^ 2 * M' p q) +
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a q ^ 2 * M' p q) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q _
          ring
        have e2 : ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a q ^ 2 * M' p q) =
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a p ^ 2 * M' p q) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro q _
          rw [hM's]
        rw [e1, e2]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p _
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q _
        ring
    _ ≤ ∑ p : Mono n d, a p ^ 2 * K := by
        apply Finset.sum_le_sum; intro p _
        by_cases hp : p.1 = j
        · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          have h := hK p hp
          rw [Finset.sum_filter] at h
          simp only [M', hp, true_and]
          rw [hp] at h
          exact h
        · rw [ha p hp]; simp
    _ = K * ∑ p, a p ^ 2 := by rw [← Finset.sum_mul]; ring

/-- The restriction of a coefficient vector to one degree. -/
noncomputable def part (j : Fin (d + 1)) (a : Mono n d → ℝ) (p : Mono n d) : ℝ :=
  if p.1 = j then a p else 0

/-- **Parity**: blocks of degrees of opposite parity are orthogonal. -/
lemma cross_zero (hn : 1 ≤ n) (i j : Fin (d + 1)) (hij : Odd ((i : ℕ) + j)) (a b : Mono n d → ℝ) :
    ∫ x, (∑ p, part i a p * phiM x p) * (∑ q, part j b q * phiM x q) ∂uniformSphere n = 0 := by
  classical
  rw [(int_pair hn _ _).2]
  apply Finset.sum_eq_zero; intro p _
  apply Finset.sum_eq_zero; intro q _
  by_cases hp : p.1 = i
  · by_cases hq : q.1 = j
    · rw [Mpq_odd hn p q (by rw [hp, hq]; exact hij), mul_zero]
    · simp [part, hq]
  · simp [part, hp]

end BstLean.Part81.F3
