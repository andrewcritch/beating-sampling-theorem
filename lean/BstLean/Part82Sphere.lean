import BstLean.Part82Defs
import BstLean.Part78Sphere
import BstLean.Part71Feature

/-!
# Part 82: the sphere constants of the cubic feature kernel

`sphC3 : SphC3 n` for `n ≥ 1000`. On the sphere `κ(x,x) = 5/3 + Σx_i⁴ + (Σx_i⁶)/3`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part82

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal gpm rhoD)
open BstLean.Part41 (Mono phiM)

namespace SphAux

/-! ## Complete homogeneous sums of degree `≤ 3` -/

lemma sum_univ_inst {γ : Type} (i1 i2 : Fintype γ) (f : γ → ℝ) :
    @Finset.sum γ ℝ _ (@Finset.univ γ i1) f = @Finset.sum γ ℝ _ (@Finset.univ γ i2) f := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

open Classical in
/-- `h_k(z) = Σ_{s : Sym α k} Π_{i ∈ s} z_i`. -/
noncomputable def hh (α : Type) [Fintype α] (k : ℕ) (z : α → ℝ) : ℝ :=
  ∑ s : Sym α k, (s.1.map z).prod

lemma hh_zero (α : Type) [Fintype α] (z : α → ℝ) : hh α 0 z = 1 := by
  classical
  unfold hh
  rw [Fintype.sum_unique]
  simp [Sym.eq_nil_of_card_zero]

open Classical in
lemma hh_option (α : Type) [Fintype α] (k : ℕ) (z : Option α → ℝ) :
    hh (Option α) (k + 1) z = z none * hh (Option α) k z + hh α (k + 1) (fun a => z (some a)) := by
  have h := Fintype.sum_equiv (symOptionSuccEquiv (α := α) (n := k)).symm
    (fun t => (((symOptionSuccEquiv (α := α) (n := k)).symm t : Multiset (Option α)).map z).prod)
    (fun s : Sym (Option α) (k + 1) => ((s : Multiset (Option α)).map z).prod) (fun _ => rfl)
  rw [Fintype.sum_sum_type] at h
  have e1 : ∀ s : Sym (Option α) k,
      (((symOptionSuccEquiv (α := α) (n := k)).symm (Sum.inl s) : Multiset (Option α)).map z).prod
        = z none * ((s : Multiset (Option α)).map z).prod := by
    intro s
    show (((none ::ₛ s : Sym (Option α) (k + 1)) : Multiset (Option α)).map z).prod = _
    rw [Sym.coe_cons, Multiset.map_cons, Multiset.prod_cons]
  have e2 : ∀ s : Sym α (k + 1),
      (((symOptionSuccEquiv (α := α) (n := k)).symm (Sum.inr s) : Multiset (Option α)).map z).prod
        = ((s : Multiset α).map (fun a => z (some a))).prod := by
    intro s
    show (((s.map Function.Embedding.some : Sym (Option α) (k + 1)) : Multiset (Option α)).map z).prod = _
    simp
  simp only [e1, e2, ← Finset.mul_sum] at h
  unfold hh
  convert h.symm using 2
  · ext; simp
  all_goals first | exact sum_univ_inst _ _ _ | (congr 1; exact sum_univ_inst _ _ _) | rfl

open Classical in
lemma hh_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (k : ℕ) (z : β → ℝ) :
    hh β k z = hh α k (fun a => z (e a)) := by
  unfold hh
  have h := Fintype.sum_equiv (Sym.equivCongr (n := k) e)
    (fun s : Sym α k => ((s : Multiset α).map (fun a => z (e a))).prod)
    (fun s : Sym β k => ((s : Multiset β).map z).prod) (fun s => by
      simp [Sym.equivCongr])
  exact h.symm

/-- The formulas for `h₁`, `h₂`, `h₃` by power sums. -/
def HForm (α : Type) : Prop :=
  ∀ (_ : Fintype α) (z : α → ℝ),
    hh α 1 z = ∑ i, z i ∧
    hh α 2 z = ((∑ i, z i) ^ 2 + ∑ i, z i ^ 2) / 2 ∧
    hh α 3 z = ((∑ i, z i) ^ 3 + 3 * (∑ i, z i) * (∑ i, z i ^ 2) + 2 * ∑ i, z i ^ 3) / 6

lemma hForm (α : Type) [Finite α] : HForm α := by
  classical
  refine Finite.induction_empty_option (P := HForm) ?_ ?_ ?_ α
  · intro α β e h inst z
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨h1, h2, h3⟩ := h _ (fun a => z (e a))
    rw [hh_equiv e, hh_equiv e, hh_equiv e, h1, h2, h3]
    have e1 : ∑ a, z (e a) = ∑ i, z i := Fintype.sum_equiv e _ _ fun _ => rfl
    have e2 : ∑ a, z (e a) ^ 2 = ∑ i, z i ^ 2 := Fintype.sum_equiv e _ _ fun _ => rfl
    have e3 : ∑ a, z (e a) ^ 3 = ∑ i, z i ^ 3 := Fintype.sum_equiv e _ _ fun _ => rfl
    rw [e1, e2, e3]
    exact ⟨rfl, rfl, rfl⟩
  · intro inst z
    have : ∀ k, hh PEmpty (k + 1) z = 0 := fun k => by
      unfold hh
      apply Finset.sum_eq_zero
      intro s _
      obtain ⟨a, _⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [s.2]; omega : 0 < Multiset.card s.1)
      exact a.elim
    simp [this]
  · intro α _ h inst z
    obtain rfl : inst = instFintypeOption := Subsingleton.elim _ _
    obtain ⟨h1, h2, h3⟩ := h _ (fun a => z (some a))
    have g1 : hh (Option α) 1 z = ∑ i, z i := by
      rw [hh_option, hh_zero, h1, Fintype.sum_option]; ring
    have g2 : hh (Option α) 2 z = ((∑ i, z i) ^ 2 + ∑ i, z i ^ 2) / 2 := by
      rw [hh_option, g1, h2, Fintype.sum_option, Fintype.sum_option]; ring
    refine ⟨g1, g2, ?_⟩
    rw [hh_option, g2, h3, Fintype.sum_option, Fintype.sum_option, Fintype.sum_option]; ring


/-! ## The kernel on the diagonal -/

variable {n : ℕ}

lemma sumJJ' (g : Mono n 3 → ℝ) : ∑ q : JJ3 n, g q.1 = ∑ p, g p - g default := by
  classical
  have h : ∑ q : JJ3 n, g q.1 = ∑ p ∈ Finset.univ.filter (fun p : Mono n 3 => p ≠ default), g p := by
    rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  rw [h, Finset.filter_ne' Finset.univ (default : Mono n 3),
    Finset.sum_erase_eq_sub (Finset.mem_univ _)]

lemma blk (x : Fin n → ℝ) (j : ℕ) :
    ∑ β : Sym (Fin n) j, monoVal x β.1 * monoVal x β.1 = hh (Fin n) j (fun i => x i ^ 2) := by
  unfold hh
  have e : ∀ β : Sym (Fin n) j, monoVal x β.1 * monoVal x β.1
      = ((β : Multiset (Fin n)).map (fun i => x i ^ 2)).prod := by
    intro β
    have : (fun i => x i ^ 2) = fun i => x i * x i := funext fun i => sq (x i)
    rw [this, Multiset.prod_map_mul]
    rfl
  rw [Finset.sum_congr rfl (fun β _ => e β)]
  exact sum_univ_inst _ _ _

/-- `r(x) = Σ_i x_i⁶`. -/
def r6 (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 6

/-- `t(x) = Σ_i x_i¹⁰`. -/
def t10 (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 10

open BstLean.Part78 (q4 q4_nonneg q4_le_one q4_cont integral_q4 sphere_cont_integrable78)

theorem kap3_formula (x : Fin n → ℝ) :
    kap3 x x = hh (Fin n) 1 (fun i => x i ^ 2) + hh (Fin n) 2 (fun i => x i ^ 2)
      + hh (Fin n) 3 (fun i => x i ^ 2) := by
  classical
  unfold kap3 pf3
  rw [sumJJ' (fun p => phiM x p * phiM x p), Fintype.sum_sigma, Fin.sum_univ_four]
  have e0 := blk x 0
  have e1 := blk x 1
  have e2 := blk x 2
  have e3 := blk x 3
  rw [hh_zero] at e0
  simp only [phiM] at *
  have hd : monoVal x (default : Mono n 3).2.1 * monoVal x (default : Mono n 3).2.1 = 1 := by
    simp [monoVal, default]
  erw [e0, e1, e2, e3, hd]
  ring

lemma kap3_sphere (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    kap3 x x = 5 / 3 + q4 x + r6 x / 3 := by
  obtain ⟨h1, h2, h3⟩ := hForm (Fin n) inferInstance (fun i => x i ^ 2)
  rw [kap3_formula, h1, h2, h3, hx]
  have a2 : ∑ i, (x i ^ 2) ^ 2 = q4 x := Finset.sum_congr rfl fun i _ => by ring
  have a3 : ∑ i, (x i ^ 2) ^ 3 = r6 x := Finset.sum_congr rfl fun i _ => by ring
  rw [a2, a3]; ring

lemma coord_sq_le (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) (i : Fin n) : x i ^ 2 ≤ 1 := by
  have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  rwa [hx] at hi

lemma r6_nonneg (x : Fin n → ℝ) : 0 ≤ r6 x := Finset.sum_nonneg fun i _ => by positivity

lemma r6_le_q4 (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : r6 x ≤ q4 x := by
  apply Finset.sum_le_sum
  intro i _
  have h := coord_sq_le x hx i
  have h4 : 0 ≤ x i ^ 4 := by positivity
  nlinarith

lemma q4_sq_le (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : q4 x ^ 2 ≤ r6 x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) x (fun i => x i ^ 3)
  rw [hx, one_mul] at h
  have e1 : ∑ i, x i * x i ^ 3 = q4 x := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (x i ^ 3) ^ 2 = r6 x := Finset.sum_congr rfl fun i _ => by ring
  rwa [e1, e2] at h

lemma r6_sq_le (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : r6 x ^ 2 ≤ t10 x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) x (fun i => x i ^ 5)
  rw [hx, one_mul] at h
  have e1 : ∑ i, x i * x i ^ 5 = r6 x := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (x i ^ 5) ^ 2 = t10 x := Finset.sum_congr rfl fun i _ => by ring
  rwa [e1, e2] at h

lemma kap3_cont : Continuous (fun x : Fin n → ℝ => kap3 x x) :=
  continuous_finsetSum _ fun q _ =>
    (continuous_multiset_prod q.1.2.1 (fun i _ => continuous_apply i)).mul
      (continuous_multiset_prod q.1.2.1 (fun i _ => continuous_apply i))

lemma r6_cont : Continuous (r6 (n := n)) := by unfold r6; fun_prop

lemma t10_cont : Continuous (t10 (n := n)) := by unfold t10; fun_prop

/-! ## Moments of one coordinate -/

lemma momPow (hn : 1 ≤ n) (i : Fin n) (m : ℕ) :
    ∫ x, x i ^ m ∂uniformSphere n = BstLean.Part29.gaussMom m / rhoD n (m / 2) := by
  classical
  have h := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n _ hn) (Multiset.replicate m i) le_rfl).2
  have e : ∀ x : Fin n → ℝ, monoVal x (Multiset.replicate m i) = x i ^ m := by
    intro x; simp [monoVal]
  simp_rw [e] at h
  rw [h, Multiset.card_replicate]
  congr 1
  unfold gpm
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [Ne.symm hj, BstLean.Part29.gaussMom]
  · simp

lemma integral_r6 (hn : 1 ≤ n) :
    ∫ x, r6 x ∂uniformSphere n = 15 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold r6
  rw [integral_finsetSum _ (fun i _ =>
    sphere_cont_integrable78 hn
      (show Continuous fun x : Fin n → ℝ => x i ^ 6 from by fun_prop))]
  simp_rw [momPow hn]
  have g : BstLean.Part29.gaussMom 6 = 15 := by
    norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, show Even 6 from by decide]
  have r : rhoD (n : ℝ) (6 / 2) = (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 4) := by
    norm_num [rhoD, Finset.prod_range_succ]
  rw [g, r]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma integral_t10 (hn : 1 ≤ n) :
    ∫ x, t10 x ∂uniformSphere n =
      945 / (((n : ℝ) + 2) * ((n : ℝ) + 4) * ((n : ℝ) + 6) * ((n : ℝ) + 8)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold t10
  rw [integral_finsetSum _ (fun i _ =>
    sphere_cont_integrable78 hn
      (show Continuous fun x : Fin n → ℝ => x i ^ 10 from by fun_prop))]
  simp_rw [momPow hn]
  have g : BstLean.Part29.gaussMom 10 = 945 := by
    norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, show Even 10 from by decide]
  have r : rhoD (n : ℝ) (10 / 2) =
      (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 4) * ((n : ℝ) + 6) * ((n : ℝ) + 8) := by
    norm_num [rhoD, Finset.prod_range_succ]
  rw [g, r]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ## The three integral bounds -/

lemma int1 (hn : 1 ≤ n) :
    ∫ x, (kap3 x x - 5 / 3) ∂uniformSphere n ≤ 301 / (100 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have iq := sphere_cont_integrable78 hn (q4_cont (n := n))
  have ir := sphere_cont_integrable78 hn (r6_cont (n := n))
  have hle : ∫ x, (kap3 x x - 5 / 3) ∂uniformSphere n ≤ ∫ x, (q4 x + r6 x / 3) ∂uniformSphere n := by
    apply integral_mono_ae (sphere_cont_integrable78 hn (kap3_cont.sub continuous_const))
      (iq.add (ir.div_const 3))
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    show kap3 x x - 5 / 3 ≤ q4 x + r6 x / 3
    rw [kap3_sphere x hx]; linarith
  rw [integral_add iq (ir.div_const 3), integral_div, integral_q4 hn, integral_r6 hn] at hle
  refine hle.trans ?_
  have e : 3 / ((n : ℝ) + 2) + 15 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) / 3 =
      (3 * (n : ℝ) + 17) / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma int2 (hn : 1 ≤ n) :
    ∫ x, (kap3 x x - 5 / 3) ^ 2 ∂uniformSphere n ≤ 27 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ir := sphere_cont_integrable78 hn (r6_cont (n := n))
  have hle : ∫ x, (kap3 x x - 5 / 3) ^ 2 ∂uniformSphere n ≤ ∫ x, 16 / 9 * r6 x ∂uniformSphere n := by
    apply integral_mono_ae
      (sphere_cont_integrable78 hn ((kap3_cont.sub continuous_const).pow 2)) (ir.const_mul _)
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    show (kap3 x x - 5 / 3) ^ 2 ≤ 16 / 9 * r6 x
    rw [kap3_sphere x hx]
    nlinarith [q4_nonneg x, r6_nonneg x, r6_le_q4 x hx, q4_sq_le x hx,
      mul_nonneg (q4_nonneg x) (sub_nonneg.mpr (r6_le_q4 x hx)),
      mul_nonneg (r6_nonneg x) (sub_nonneg.mpr (r6_le_q4 x hx))]
  rw [integral_const_mul, integral_r6 hn] at hle
  refine hle.trans ?_
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma int4 (hn : 1 ≤ n) :
    ∫ x, (kap3 x x - 5 / 3) ^ 4 ∂uniformSphere n ≤ 2990 / (n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have it := sphere_cont_integrable78 hn (t10_cont (n := n))
  have hle : ∫ x, (kap3 x x - 5 / 3) ^ 4 ∂uniformSphere n ≤
      ∫ x, 256 / 81 * t10 x ∂uniformSphere n := by
    apply integral_mono_ae
      (sphere_cont_integrable78 hn ((kap3_cont.sub continuous_const).pow 4)) (it.const_mul _)
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    show (kap3 x x - 5 / 3) ^ 4 ≤ 256 / 81 * t10 x
    rw [kap3_sphere x hx]
    have h2 : (5 / 3 + q4 x + r6 x / 3 - 5 / 3) ^ 2 ≤ 16 / 9 * r6 x := by
      nlinarith [q4_nonneg x, r6_nonneg x, r6_le_q4 x hx, q4_sq_le x hx,
        mul_nonneg (q4_nonneg x) (sub_nonneg.mpr (r6_le_q4 x hx)),
        mul_nonneg (r6_nonneg x) (sub_nonneg.mpr (r6_le_q4 x hx))]
    have h0 : 0 ≤ (5 / 3 + q4 x + r6 x / 3 - 5 / 3) ^ 2 := sq_nonneg _
    have h4 : (5 / 3 + q4 x + r6 x / 3 - 5 / 3) ^ 4 ≤ (16 / 9 * r6 x) ^ 2 := by
      have := pow_le_pow_left₀ h0 h2 2
      calc (5 / 3 + q4 x + r6 x / 3 - 5 / 3) ^ 4
          = ((5 / 3 + q4 x + r6 x / 3 - 5 / 3) ^ 2) ^ 2 := by ring
        _ ≤ _ := this
    nlinarith [r6_sq_le x hx]
  rw [integral_const_mul, integral_t10 hn] at hle
  refine hle.trans ?_
  have hP : ((n : ℝ) + 2) * ((n : ℝ) + 4) * ((n : ℝ) + 6) * ((n : ℝ) + 8) =
      (n : ℝ) ^ 4 + (20 * (n : ℝ) ^ 3 + 140 * (n : ℝ) ^ 2 + 400 * (n : ℝ) + 384) := by ring
  have hPn : (n : ℝ) ^ 4 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 4) * ((n : ℝ) + 6) * ((n : ℝ) + 8) := by
    rw [hP]; nlinarith [pow_pos hn0 3, pow_pos hn0 2]
  rw [← mul_div_assoc]
  calc 256 / 81 * 945 / (((n : ℝ) + 2) * ((n : ℝ) + 4) * ((n : ℝ) + 6) * ((n : ℝ) + 8))
      ≤ 2990 / (((n : ℝ) + 2) * ((n : ℝ) + 4) * ((n : ℝ) + 6) * ((n : ℝ) + 8)) := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ 2990 / (n : ℝ) ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hPn

end SphAux

open SphAux in
/-- **Sphere constants** of the cubic feature kernel. -/
theorem sphC3 (n : ℕ) (hn : 1000 ≤ n) : SphC3 n := by
  have h1 : 1 ≤ n := by omega
  refine ⟨fun x hx => ?_, kap3_cont, int1 h1, int2 h1, int4 h1⟩
  rw [kap3_sphere x hx]
  have := BstLean.Part78.q4_nonneg x
  have := BstLean.Part78.q4_le_one x hx
  have := r6_nonneg x
  have := r6_le_q4 x hx
  constructor <;> linarith

end BstLean.Part82

#print axioms BstLean.Part82.sphC3
