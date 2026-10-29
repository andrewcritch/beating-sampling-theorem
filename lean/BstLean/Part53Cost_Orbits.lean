import BstLean.Part53Cost_Constants

namespace BstLean.Part53.CostAux

set_option backward.isDefEq.respectTransparency false

open BstLean.Part41 (Mono mset wordOf IsSymmT contr)
open BstLean.Part36 (monoVal)

noncomputable section

def compOf {n k : ℕ} (p : Mono n k) : CompKey k :=
  ⟨p.1, ⟨p.2.val.toFinset.toList.map p.2.val.count,
    by
      intro i hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp (Finset.mem_toList.mp ha)),
    by
      rw [Finset.sum_map_toList]
      exact (Multiset.toFinset_sum_count_eq _).trans p.2.property⟩⟩

private theorem prodX_mset {α : Type} [DecidableEq α] {c : ℕ} (w : Fin c → α) :
    (∏ t, MvPolynomial.X (w t) : MvPolynomial α ℝ) =
      MvPolynomial.monomial (mset w).toFinsupp 1 := by
  induction c with
  | zero => simp [mset, Multiset.toFinsupp_zero]
  | succ c ih =>
    have hm : mset w = mset (fun t : Fin c => w t.castSucc) + {w (Fin.last c)} := by
      simp only [mset, Fin.univ_val_map, List.ofFn_succ', List.concat_eq_append,
        ← Multiset.coe_add, Multiset.coe_singleton]
    rw [Fin.prod_univ_castSucc, ih, hm, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]

theorem orbitCount_multinomial {α : Type} [Fintype α] [DecidableEq α]
    {c : ℕ} (q : Sym α c) :
    (orbitCount q : ℝ) = (q.val.toFinsupp.multinomial : ℝ) := by
  have hpoly : ((∑ a : α, MvPolynomial.X a : MvPolynomial α ℝ) ^ c) =
      ∑ w : Fin c → α, MvPolynomial.monomial (mset w).toFinsupp 1 := by
    rw [← Fin.prod_const, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact prodX_mset w
  have hh := congrArg (fun p : MvPolynomial α ℝ => p.coeff q.val.toFinsupp) hpoly
  have he : ∀ w : Fin c → α, (mset w).toFinsupp = q.val.toFinsupp ↔ mset w = q.val := by
    intro w
    exact Multiset.toFinsupp.injective.eq_iff
  have hs : q.val.toFinsupp.sum (fun _ m => m) = c :=
    (Multiset.toFinsupp_sum_eq _).trans q.property
  simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_sum_X_pow_of_fintype, Multiset.toFinsupp_sum_eq, q.property,
    hs, ite_true, he, Finset.sum_boole, orbitCount] using hh.symm

theorem compWeight_compOf {n k : ℕ} (p : Mono n k) :
    compWeight (compOf p) = (orbitCount p.2 : ℝ) := by
  classical
  have hspec := Nat.multinomial_spec p.2.val.toFinset p.2.val.count
  rw [Multiset.toFinset_sum_count_eq, p.2.property] at hspec
  have hn : p.2.val.toFinsupp.multinomial = Nat.multinomial p.2.val.toFinset p.2.val.count := by
    simp only [Finsupp.multinomial_eq, Multiset.toFinsupp_support,
      Multiset.toFinsupp_apply]
    congr 1
  have hs : (∏ a ∈ p.2.val.toFinset, (p.2.val.count a).factorial : ℝ) *
      (orbitCount p.2 : ℝ) = (p.1.val.factorial : ℝ) := by
    rw [orbitCount_multinomial, hn]
    exact_mod_cast hspec
  have hd : (∏ a ∈ p.2.val.toFinset, ((p.2.val.count a).factorial : ℝ)) ≠ 0 := by
    positivity
  unfold compWeight compOf
  simp only [List.map_map, Function.comp_def, Finset.prod_map_toList]
  apply (div_eq_iff hd).mpr
  simpa only [mul_comm] using hs.symm

theorem group_orbits {n k : ℕ} (H : Mono n k → ℝ) :
    ∑ p, (orbitCount p.2 : ℝ) * H p =
      ∑ s : CompKey k, compWeight s *
        ∑ p ∈ Finset.univ.filter (fun p : Mono n k => compOf p = s), H p := by
  classical
  conv_lhs => arg 2; ext p; rw [← compWeight_compOf]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := compOf) (f := fun p => compWeight (compOf p) * H p) (by simp)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem monoVal_wordOf {n c : ℕ} [Inhabited (Fin n)] (q : Sym (Fin n) c)
    (y : Fin n → ℝ) : monoVal y q.val = ∏ t, y (wordOf c q.val t) := by
  conv_lhs => rw [← mset_wordOf c q.val q.property]
  simp only [monoVal, mset, Multiset.map_map, Function.comp_def]
  rfl

theorem fvA_orbit_mono {n k : ℕ} [Inhabited (Fin n)] (A : BstLean.Part41.Tens n)
    (hA : ∀ j, IsSymmT (A j)) (y : Fin n → ℝ) :
    fvA k A y = ∑ p : Mono n k, (orbitCount p.2 : ℝ) *
      (A p.1.val (wordOf _ p.2.val) * monoVal y p.2.val) := by
  classical
  unfold fvA
  rw [← Fin.sum_univ_eq_sum_range, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  dsimp only
  rw [contr_orbit _ (hA _) y]
  apply Finset.sum_congr rfl
  intro q hq
  rw [monoVal_wordOf]

end
end BstLean.Part53.CostAux
