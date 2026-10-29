import BstLean.Part81Defs
import BstLean.Part53Elem
import BstLean.Part71Feature

/-!
# Part 81 (KD), elementary lemmas: copies of the private lemmas of `Part53Elem` and
`Part71Feature` on the complete homogeneous symmetric polynomials `hS53` and on sphere moments.
-/

namespace BstLean.Part81.KD

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere gaussMom)
open BstLean.Part36 (monoVal gpm rhoD)
open BstLean.Part41 (Mono phiM phiSq)
open BstLean.Part53 (hS53 c0)
open Finset

variable {n d : ℕ}

lemma multinomId53 (z : Fin n → ℝ) (j : ℕ) :
    (∑ i, z i) ^ j = ∑ s : Sym (Fin n) j, (s.1.countPerms : ℝ) * (s.1.map z).prod := by
  classical
  rw [Finset.sum_pow, Finset.sym_univ]

lemma cpSpec53 (j : ℕ) (s : Sym (Fin n) j) :
    s.1.countPerms * ∏ i ∈ s.1.toFinset, (s.1.count i).factorial = j.factorial := by
  classical
  unfold Multiset.countPerms
  rw [Finsupp.multinomial_eq, mul_comm]
  have := Nat.multinomial_spec (s := s.1.toFinsupp.support) (f := s.1.toFinsupp)
  rw [Multiset.toFinsupp_support] at this ⊢
  simp only [Multiset.toFinsupp_apply] at this ⊢
  rw [this, Multiset.toFinset_sum_count_eq, s.2]

lemma prodNonneg53 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (m : Multiset (Fin n)) : 0 ≤ (m.map z).prod :=
  Multiset.prod_nonneg (fun a ha => by
    obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp ha
    exact hz b)

lemma hSLeOne53 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (j : ℕ) : hS53 z j ≤ 1 := by
  classical
  have h := multinomId53 z j
  rw [h1, one_pow] at h
  rw [h]
  unfold hS53
  apply Finset.sum_le_sum
  intro s _
  have hcp : (1 : ℝ) ≤ s.1.countPerms := by
    have := Nat.multinomial_pos (s := s.1.toFinsupp.support) (f := s.1.toFinsupp)
    unfold Multiset.countPerms
    rw [Finsupp.multinomial_eq]
    exact_mod_cast this
  exact le_mul_of_one_le_left (prodNonneg53 z hz _) hcp


lemma filterSum53 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (i : Fin n) (j : ℕ) :
    ∑ s ∈ (Finset.univ : Finset (Sym (Fin n) j)).filter (fun s => 2 ≤ s.1.count i), (s.1.map z).prod ≤
      z i ^ 2 * hS53 z (j - 2) := by
  classical
  rcases lt_or_ge j 2 with hj | hj
  · have : (Finset.univ : Finset (Sym (Fin n) j)).filter (fun s => 2 ≤ s.1.count i) = ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_le]
      have := Multiset.count_le_card i s.1
      rw [s.2] at this
      omega
    rw [this, Finset.sum_empty]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun s _ => prodNonneg53 z hz _)
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    set g : Sym (Fin n) m → Sym (Fin n) (m + 2) := fun s' => i ::ₛ i ::ₛ s' with hg
    have hginj : Function.Injective g := by
      intro a b h
      exact (Sym.cons_inj_right _ _ _).mp ((Sym.cons_inj_right _ _ _).mp h)
    have himg : (Finset.univ : Finset (Sym (Fin n) (m + 2))).filter (fun s => 2 ≤ s.1.count i) =
        Finset.univ.image g := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hc
        have h1 : i ∈ s := Multiset.count_pos.mp (by omega)
        have h2 : i ∈ s.erase i h1 := by
          show i ∈ ((s.erase i h1 : Sym (Fin n) (m + 1)) : Multiset (Fin n))
          rw [Sym.coe_erase, ← Multiset.count_pos, Multiset.count_erase_self]
          exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hc)
        exact ⟨(s.erase i h1).erase i h2, by rw [hg]; simp only; rw [Sym.cons_erase, Sym.cons_erase]⟩
      · rintro ⟨s', rfl⟩
        show 2 ≤ Multiset.count i (((i ::ₛ i ::ₛ s') : Sym (Fin n) (m + 2)) : Multiset (Fin n))
        rw [Sym.coe_cons, Sym.coe_cons, Multiset.count_cons_self, Multiset.count_cons_self]
        omega
    rw [himg, Finset.sum_image (fun a _ b _ h => hginj h), Nat.add_sub_cancel]
    unfold hS53
    rw [Finset.mul_sum]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro s' _
    show ((((i ::ₛ i ::ₛ s') : Sym (Fin n) (m + 2)) : Multiset (Fin n)).map z).prod = _
    rw [Sym.coe_cons, Sym.coe_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, pow_two, mul_assoc]
    rfl


lemma hSBounds53 (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (h1 : ∑ i, z i = 1) (j : ℕ) :
    1 / (j.factorial : ℝ) ≤ hS53 z j ∧ hS53 z j ≤ 1 / (j.factorial : ℝ) + ∑ i, z i ^ 2 := by
  classical
  have hid := multinomId53 z j
  rw [h1, one_pow] at hid
  have hjf : (0 : ℝ) < j.factorial := by positivity
  have hP1 : ∀ s : Sym (Fin n) j, 1 ≤ ∏ i ∈ s.1.toFinset, (s.1.count i).factorial :=
    fun s => Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)
  have hcp_le : ∀ s : Sym (Fin n) j, (s.1.countPerms : ℝ) ≤ j.factorial := by
    intro s
    have h := cpSpec53 j s
    have : s.1.countPerms ≤ j.factorial := by
      rw [← h]; exact Nat.le_mul_of_pos_right _ (hP1 s)
    exact_mod_cast this
  have hpn : ∀ s : Sym (Fin n) j, 0 ≤ (s.1.map z).prod := fun s => prodNonneg53 z hz _
  constructor
  · rw [div_le_iff₀ hjf, hid]
    unfold hS53
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _
    nlinarith [hcp_le s, hpn s]
  · -- `j!·h − 1 = Σ (j! − cp) z^s`
    have key : ∀ s : Sym (Fin n) j, ((j.factorial : ℝ) - s.1.countPerms) * (s.1.map z).prod ≤
        (j.factorial : ℝ) * ∑ i, if 2 ≤ s.1.count i then (s.1.map z).prod else 0 := by
      intro s
      by_cases hA : ∀ i, s.1.count i ≤ 1
      · have hP : ∏ i ∈ s.1.toFinset, (s.1.count i).factorial = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          have h1' : 1 ≤ s.1.count i := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hi)
          have : s.1.count i = 1 := le_antisymm (hA i) h1'
          rw [this, Nat.factorial_one]
        have h := cpSpec53 j s
        rw [hP, mul_one] at h
        rw [h, sub_self, zero_mul]
        exact mul_nonneg hjf.le (Finset.sum_nonneg fun i _ => by split_ifs; exact hpn s; exact le_rfl)
      · push Not at hA
        obtain ⟨i0, hi0⟩ := hA
        have hsum : (s.1.map z).prod ≤ ∑ i, if 2 ≤ s.1.count i then (s.1.map z).prod else 0 := by
          have := Finset.single_le_sum (f := fun i => if 2 ≤ s.1.count i then (s.1.map z).prod else 0)
            (fun i _ => by split_ifs; exact hpn s; exact le_rfl) (Finset.mem_univ i0)
          have h2 : 2 ≤ s.1.count i0 := hi0
          simp only [h2, ↓reduceIte] at this
          exact this
        have hcp0 : (0 : ℝ) ≤ s.1.countPerms := by positivity
        calc ((j.factorial : ℝ) - s.1.countPerms) * (s.1.map z).prod ≤ (j.factorial : ℝ) * (s.1.map z).prod :=
              mul_le_mul_of_nonneg_right (by linarith) (hpn s)
          _ ≤ _ := mul_le_mul_of_nonneg_left hsum hjf.le
    have hsumkey := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Sym (Fin n) j))) => key s)
    have hlhs : ∑ s : Sym (Fin n) j, ((j.factorial : ℝ) - s.1.countPerms) * (s.1.map z).prod =
        (j.factorial : ℝ) * hS53 z j - 1 := by
      rw [hid]; unfold hS53
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro s _; ring
    have hrhs : ∑ s : Sym (Fin n) j, (j.factorial : ℝ) * ∑ i, (if 2 ≤ s.1.count i then (s.1.map z).prod else 0) ≤
        (j.factorial : ℝ) * ∑ i, z i ^ 2 := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hjf.le
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter]
      calc _ ≤ z i ^ 2 * hS53 z (j - 2) := filterSum53 z hz i j
        _ ≤ z i ^ 2 * 1 := mul_le_mul_of_nonneg_left (hSLeOne53 z hz h1 _) (sq_nonneg _)
        _ = z i ^ 2 := mul_one _
    rw [hlhs] at hsumkey
    have : (j.factorial : ℝ) * hS53 z j ≤ 1 + (j.factorial : ℝ) * ∑ i, z i ^ 2 := by linarith
    rw [div_add' _ _ _ hjf.ne', le_div_iff₀ hjf]
    linarith

lemma hSZero53 (z : Fin n → ℝ) : hS53 z 0 = 1 := by
  unfold hS53
  rw [Fintype.sum_unique]
  simp [Sym.eq_nil_of_card_zero]

lemma phiSq_hS (d : ℕ) (x : Fin n → ℝ) :
    phiSq d x = ∑ i : Fin (d + 1), hS53 (fun i => x i ^ 2) i := by
  classical
  unfold phiSq phiM hS53
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro s _
  unfold BstLean.Part36.monoVal
  rw [Multiset.prod_map_pow]

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
  BstLean.Part36.sphere_multiset (uniformSphere n) (BstLean.Part33.uniformSphere_prod n _ hn) u le_rfl

lemma mom_nonneg (hn : 1 ≤ n) (u : Multiset (Fin n)) : 0 ≤ ∫ x, monoVal x u ∂uniformSphere n := by
  rw [(mom hn u).2]; exact div_nonneg (gpm_nonneg u) (rhoD_pos hn _).le

lemma mom_odd (hn : 1 ≤ n) (u : Multiset (Fin n)) (h : ∃ i, ¬ Even (u.count i)) :
    ∫ x, monoVal x u ∂uniformSphere n = 0 := by
  rw [(mom hn u).2]
  obtain ⟨i, hi⟩ := h
  have : gpm u = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [gaussMom, hi])
  rw [this, zero_div]

end BstLean.Part81.KD
