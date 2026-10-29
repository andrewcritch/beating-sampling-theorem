import BstLean.Part81UF

/-!
# Part 81 (UW): the feature operator bound from two weighted row integrals

A weighted Schur test. A monomial `q` is LIGHT when `card (gam q) = k0 q`, where `k0 q = 0` if `q`
has a coordinate with odd exponent and `k0 q = 1` otherwise (so the light monomials are the
squarefree non-constant ones and the squares `x_k²`; the constant monomial is heavy). The weight is
`1` on the light monomials and `τ` on the heavy ones.
Do not use `sorry`, `native_decide` or `axiom`.
-/
namespace BstLean.Part81.UW
open MeasureTheory BstLean.Part53
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM)
open BstLean.Part81.KD (prodMapUniv mom mom_nonneg mom_odd)
open BstLean.Part81.UF
variable {n d : ℕ}

open Classical in
/-- The number of squared factors of a light monomial in the parity class of `u`. -/
noncomputable def k0 (u : Multiset (Fin n)) : ℕ := if ∃ i, u.count i % 2 = 1 then 0 else 1

/-- The Schur weight: `1` on the light monomials, `τ` on the heavy ones. -/
noncomputable def wt (τ : ℝ) (u : Multiset (Fin n)) : ℝ :=
  if Multiset.card (gam u) = k0 u then 1 else τ

lemma wt_pos (τ : ℝ) (hτ : 0 < τ) (u : Multiset (Fin n)) : 0 < wt τ u := by
  unfold wt; split_ifs <;> linarith

/-- The class bound with a weight that depends on the number of squared factors. -/
lemma class_boundW (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    (x : Fin n → ℝ) (hxz : ∀ i, z i = x i ^ 2) (p : Mono n d) :
    ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2),
      c (Multiset.card (gam q.2.1)) * |monoVal x q.2.1|
      ≤ oddP p.2.1 x * ∑ k ∈ Finset.range (d / 2 + 1), c k * hS53 z k := by
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
  have hsum : ∑ g : Mono n (d / 2), c (g.1 : ℕ) * monoVal z g.2.1
      = ∑ k ∈ Finset.range (d / 2 + 1), c k * hS53 z k := by
    rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun k => c k * hS53 z k)]
    apply Finset.sum_congr rfl; intro k _
    unfold hS53
    rw [Finset.mul_sum]
    rfl
  have hoddp : 0 ≤ oddP p.2.1 x := by unfold oddP; positivity
  calc ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2),
        c (Multiset.card (gam q.2.1)) * |monoVal x q.2.1|
      ≤ ∑ g : Mono n (d / 2), oddP p.2.1 x * (c (g.1 : ℕ) * monoVal z g.2.1) := by
        apply Finset.sum_le_sum_of_injOn emb hinj (Finset.subset_univ _)
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rw [abs_mono_split, hzx]
          have : oddP q.2.1 x = oddP p.2.1 x := by
            unfold oddP; apply Finset.prod_congr rfl; intro i _; rw [hq i]
          rw [this]
          apply le_of_eq
          show c (Multiset.card (gam q.2.1)) * (oddP p.2.1 x * monoVal z (gam q.2.1))
            = oddP p.2.1 x * (c (Multiset.card (gam q.2.1)) * monoVal z (gam q.2.1))
          ring
        · intro g _ _
          exact mul_nonneg hoddp (mul_nonneg (hc _) (Multiset.prod_nonneg fun a ha => by
            obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp ha; exact hz b))
    _ = oddP p.2.1 x * ∑ k ∈ Finset.range (d / 2 + 1), c k * hS53 z k := by
        rw [← hsum, Finset.mul_sum]

lemma prod_le_two_factors (g : Fin n → ℝ) (hg : ∀ j, 0 ≤ g j ∧ g j ≤ 1) (i j : Fin n)
    (hij : i ≠ j) : ∏ l, g l ≤ g i * g j := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨fun h => hij h.symm, Finset.mem_univ j⟩
  rw [← Finset.mul_prod_erase _ _ hj]
  have h1 : ∏ l ∈ (Finset.univ.erase i).erase j, g l ≤ 1 :=
    Finset.prod_le_one₀ (fun l _ => (hg l).1) (fun l _ => (hg l).2)
  have h0 : 0 ≤ ∏ l ∈ (Finset.univ.erase i).erase j, g l := Finset.prod_nonneg fun l _ => (hg l).1
  apply mul_le_mul_of_nonneg_left _ (hg i).1
  nlinarith [(hg j).1]

/-- A heavy non-constant monomial `p` has `|x^p| · oddP ≤ x_i² x_j²` on the sphere. -/
lemma L5 (p : Mono n d) (hp : p ≠ default) (hh : Multiset.card (gam p.2.1) ≠ k0 p.2.1) :
    ∃ i j : Fin n, ∀ x : Fin n → ℝ, ∑ l, x l ^ 2 = 1 →
      |monoVal x p.2.1| * oddP p.2.1 x ≤ x i ^ 2 * x j ^ 2 := by
  classical
  set e : Fin n → ℕ := fun l => p.2.1.count l / 2 + p.2.1.count l % 2 with he
  have hkey : ∀ x : Fin n → ℝ, |monoVal x p.2.1| * oddP p.2.1 x = ∏ l, (x l ^ 2) ^ e l := by
    intro x
    have habs : |monoVal x p.2.1| = ∏ j, |x j| ^ p.2.1.count j := by
      unfold monoVal; rw [prodMapUniv, Finset.abs_prod]; simp [abs_pow]
    rw [habs]; unfold oddP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro l _
    have h2 : p.2.1.count l + p.2.1.count l % 2 = 2 * e l := by simp only [he]; omega
    rw [← pow_add, h2, pow_mul, sq_abs]
  have hgen : (∃ i, 2 ≤ e i) ∨ (∃ i j, i ≠ j ∧ 1 ≤ e i ∧ 1 ≤ e j) := by
    by_cases hodd : ∃ i, p.2.1.count i % 2 = 1
    · have hk : k0 p.2.1 = 0 := by unfold k0; exact ite_eq_left_of_eq_true _ _ (eq_true hodd)
      rw [hk] at hh
      obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero hh)
      have hcj := Multiset.count_pos.mpr hj
      rw [count_gam] at hcj
      obtain ⟨i, hi⟩ := hodd
      by_cases hij : i = j
      · left; refine ⟨i, ?_⟩; subst hij; simp only [he]; omega
      · right; refine ⟨i, j, hij, ?_, ?_⟩ <;> simp only [he] <;> omega
    · have hk : k0 p.2.1 = 1 := by unfold k0; exact ite_eq_right_of_eq_false _ _ (eq_false hodd)
      rw [hk] at hh
      push Not at hodd
      have h0 : Multiset.card (gam p.2.1) ≠ 0 := by
        intro h0
        apply hp
        apply mono_ext
        show p.2.1 = (default : Mono n d).2.1
        have hg0 : gam p.2.1 = 0 := Multiset.card_eq_zero.mp h0
        have hz : p.2.1 = 0 := by
          ext l
          have h1 := count_gam p.2.1 l
          rw [hg0] at h1
          have h2 := hodd l
          simp only [Multiset.count_zero] at h1 ⊢
          omega
        rw [hz]; rfl
      obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero h0)
      have hcj := Multiset.count_pos.mpr hj
      by_cases h2 : 2 ≤ (gam p.2.1).count j
      · left; refine ⟨j, ?_⟩; rw [count_gam] at h2; simp only [he]; omega
      · have hce : 0 < Multiset.card ((gam p.2.1).erase j) := by
          have h3 := Multiset.card_erase_add_one hj
          omega
        obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.mp hce
        have hij : i ≠ j := by
          intro hij
          subst hij
          have h3 := Multiset.count_pos.mpr hi
          rw [Multiset.count_erase_self] at h3
          omega
        have hci := Multiset.count_pos.mpr (Multiset.mem_of_mem_erase hi)
        rw [count_gam] at hci hcj
        right; refine ⟨i, j, hij, ?_, ?_⟩ <;> simp only [he] <;> omega
  have hb : ∀ x : Fin n → ℝ, ∑ l, x l ^ 2 = 1 → ∀ l, 0 ≤ x l ^ 2 ∧ x l ^ 2 ≤ 1 := by
    intro x hx l
    refine ⟨sq_nonneg _, ?_⟩
    have := Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ l)
    rw [hx] at this
    exact this
  have hbp : ∀ x : Fin n → ℝ, ∑ l, x l ^ 2 = 1 → ∀ l, 0 ≤ (x l ^ 2) ^ e l ∧ (x l ^ 2) ^ e l ≤ 1 :=
    fun x hx l => ⟨pow_nonneg (hb x hx l).1 _, pow_le_one₀ (hb x hx l).1 (hb x hx l).2⟩
  rcases hgen with ⟨i, hi⟩ | ⟨i, j, hij, hi, hj⟩
  · refine ⟨i, i, fun x hx => ?_⟩
    rw [hkey]
    calc ∏ l, (x l ^ 2) ^ e l ≤ (x i ^ 2) ^ e i := prod_le_one_factor _ (hbp x hx) i
      _ ≤ (x i ^ 2) ^ 2 := pow_le_pow_of_le_one (hb x hx i).1 (hb x hx i).2 hi
      _ = x i ^ 2 * x i ^ 2 := by ring
  · refine ⟨i, j, fun x hx => ?_⟩
    rw [hkey]
    calc ∏ l, (x l ^ 2) ^ e l ≤ (x i ^ 2) ^ e i * (x j ^ 2) ^ e j :=
          prod_le_two_factors _ (hbp x hx) i j hij
      _ ≤ x i ^ 2 * x j ^ 2 :=
          mul_le_mul (pow_le_of_le_one (hb x hx i).1 (hb x hx i).2 (by omega))
            (pow_le_of_le_one (hb x hx j).1 (hb x hx j).2 (by omega))
            (hbp x hx j).1 (hb x hx i).1

/-- The weighted row sum is at most the integral of any continuous majorant of
`|x^p| · oddP · ((1 − τ) + τ S) / w_p`. -/
lemma RpW_core (hn : 1 ≤ n) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (p : Mono n d)
    (G : (Fin n → ℝ) → ℝ) (hG : Continuous G)
    (hGb : ∀ x : Fin n → ℝ, ∑ j, x j ^ 2 = 1 →
      |monoVal x p.2.1| * oddP p.2.1 x *
        (((1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) / wt τ p.2.1)
        ≤ G x) :
    ∑ q : Mono n d, wt τ q.2.1 / wt τ p.2.1 * Mpq p q ≤ ∫ x, G x ∂uniformSphere n := by
  classical
  set cls := (Finset.univ : Finset (Mono n d)).filter (fun q => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)
    with hcls
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q : Mono n d => ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2)]
  have hzero : ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter
      (fun q => ¬ ∀ i, q.2.1.count i % 2 = p.2.1.count i % 2),
        wt τ q.2.1 / wt τ p.2.1 * Mpq p q = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    push Not at hq
    obtain ⟨i, hi⟩ := hq
    have hM : Mpq p q = 0 := by
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
    rw [hM, mul_zero]
  rw [hzero, add_zero]
  have hW : 0 < wt τ p.2.1 := wt_pos τ hτ _
  have hint : ∀ q : Mono n d, Integrable
      (fun x => wt τ q.2.1 / wt τ p.2.1 * (monoVal x p.2.1 * monoVal x q.2.1)) (uniformSphere n) := by
    intro q
    simp_rw [← monoVal_add]
    exact (mom hn _).1.const_mul _
  calc ∑ q ∈ cls, wt τ q.2.1 / wt τ p.2.1 * Mpq p q
      = ∫ x, ∑ q ∈ cls, wt τ q.2.1 / wt τ p.2.1 * (monoVal x p.2.1 * monoVal x q.2.1)
          ∂uniformSphere n := by
        rw [integral_finsetSum _ fun q _ => hint q]
        apply Finset.sum_congr rfl; intro q _
        unfold Mpq; simp_rw [monoVal_add]
        rw [integral_const_mul]
    _ ≤ _ := by
        apply integral_mono_ae (integrable_finsetSum _ fun q _ => hint q)
          (BstLean.Part78.sph_int hn hG)
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
        set c : ℕ → ℝ := fun k => if k = k0 p.2.1 then 1 else τ with hc
        have hc0 : ∀ k, 0 ≤ c k := by
          intro k; simp only [hc]; split_ifs <;> linarith
        have hcb := class_boundW (d := d) c hc0 (fun j => x j ^ 2) (fun j => sq_nonneg _) x
          (fun _ => rfl) p
        have hSle : ∀ k, hS53 (fun l => x l ^ 2) k ≤ 1 :=
          fun k => KD.hSLeOne53 _ (fun j => sq_nonneg _) hx k
        have hS0 : ∀ k, 0 ≤ hS53 (fun l => x l ^ 2) k :=
          fun k => hS_nonneg _ (fun j => sq_nonneg _) k
        have hcS : ∑ k ∈ Finset.range (d / 2 + 1), c k * hS53 (fun l => x l ^ 2) k
            ≤ (1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k := by
          have e1 : ∑ k ∈ Finset.range (d / 2 + 1), c k * hS53 (fun l => x l ^ 2) k
              = ∑ k ∈ Finset.range (d / 2 + 1),
                  ((if k = k0 p.2.1 then (1 - τ) * hS53 (fun l => x l ^ 2) k else 0)
                    + τ * hS53 (fun l => x l ^ 2) k) := by
            apply Finset.sum_congr rfl; intro k _
            simp only [hc]; split_ifs <;> ring
          rw [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum]
          have : (if k0 p.2.1 ∈ Finset.range (d / 2 + 1)
              then (1 - τ) * hS53 (fun l => x l ^ 2) (k0 p.2.1) else 0) ≤ 1 - τ := by
            split_ifs
            · nlinarith [hSle (k0 p.2.1), hS0 (k0 p.2.1)]
            · linarith
          linarith
        have hoddp : 0 ≤ oddP p.2.1 x := by unfold oddP; positivity
        have hpre : 0 ≤ |monoVal x p.2.1| / wt τ p.2.1 := div_nonneg (abs_nonneg _) hW.le
        refine le_trans ?_ (hGb x hx)
        calc ∑ q ∈ cls, wt τ q.2.1 / wt τ p.2.1 * (monoVal x p.2.1 * monoVal x q.2.1)
            ≤ ∑ q ∈ cls, |monoVal x p.2.1| / wt τ p.2.1 *
                (c (Multiset.card (gam q.2.1)) * |monoVal x q.2.1|) := by
              apply Finset.sum_le_sum; intro q hq
              simp only [hcls, Finset.mem_filter, Finset.mem_univ, true_and] at hq
              have hk : k0 q.2.1 = k0 p.2.1 := by unfold k0; simp only [hq]
              have hw : wt τ q.2.1 = c (Multiset.card (gam q.2.1)) := by
                simp only [hc]; unfold wt; rw [hk]
              have h1 : wt τ q.2.1 / wt τ p.2.1 * (monoVal x p.2.1 * monoVal x q.2.1)
                  ≤ wt τ q.2.1 / wt τ p.2.1 * |monoVal x p.2.1 * monoVal x q.2.1| :=
                mul_le_mul_of_nonneg_left (le_abs_self _)
                  (div_nonneg (wt_pos τ hτ _).le hW.le)
              refine le_trans h1 (le_of_eq ?_)
              rw [abs_mul, hw]; ring
          _ = |monoVal x p.2.1| / wt τ p.2.1 *
                ∑ q ∈ cls, c (Multiset.card (gam q.2.1)) * |monoVal x q.2.1| := by
              rw [Finset.mul_sum]
          _ ≤ |monoVal x p.2.1| / wt τ p.2.1 * (oddP p.2.1 x *
                ((1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k)) :=
              mul_le_mul_of_nonneg_left
                (hcb.trans (mul_le_mul_of_nonneg_left hcS hoddp)) hpre
          _ = _ := by ring

lemma RpW (hn : 1 ≤ n) (τ Cr : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hrowL : ∀ i : Fin n, ∫ x, x i ^ 2 * (1 + τ *
        ((∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ Cr / (n : ℝ))
    (hrowH : ∀ i j : Fin n, ∫ x, x i ^ 2 * x j ^ 2 * (1 / τ +
        ((∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ Cr / (n : ℝ))
    (p : Mono n d) (hp : p ≠ default) :
    ∑ q : Mono n d, wt τ q.2.1 / wt τ p.2.1 * Mpq p q ≤ Cr / n := by
  classical
  have hScont : Continuous (fun x : Fin n → ℝ =>
      ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) :=
    continuous_finsetSum _ fun k _ => cont_hS k
  have hS0 : ∀ x : Fin n → ℝ, 0 ≤ ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k :=
    fun x => Finset.sum_nonneg fun k _ => hS_nonneg _ (fun j => sq_nonneg _) k
  by_cases hl : Multiset.card (gam p.2.1) = k0 p.2.1
  · have hw : wt τ p.2.1 = 1 := by unfold wt; exact ite_eq_left_of_eq_true _ _ (eq_true hl)
    obtain ⟨i, hi⟩ := L4 p hp
    refine le_trans (RpW_core hn τ hτ hτ1 p _ ?_ ?_) (hrowL i)
    · exact ((continuous_apply i).pow 2).mul
        (continuous_const.add (continuous_const.mul (hScont.sub continuous_const)))
    · intro x hx
      rw [hw, div_one]
      have hnn : 0 ≤ (1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k := by
        have := mul_nonneg hτ.le (hS0 x); linarith
      calc _ ≤ x i ^ 2 * ((1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) :=
            mul_le_mul_of_nonneg_right (hi x hx) hnn
        _ = _ := by ring
  · have hw : wt τ p.2.1 = τ := by unfold wt; exact ite_eq_right_of_eq_false _ _ (eq_false hl)
    obtain ⟨i, j, hij⟩ := L5 p hp hl
    refine le_trans (RpW_core hn τ hτ hτ1 p _ ?_ ?_) (hrowH i j)
    · exact (((continuous_apply i).pow 2).mul ((continuous_apply j).pow 2)).mul
        (continuous_const.add (hScont.sub continuous_const))
    · intro x hx
      rw [hw]
      have hnn : 0 ≤ ((1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) / τ := by
        have := mul_nonneg hτ.le (hS0 x)
        exact div_nonneg (by linarith) hτ.le
      calc _ ≤ x i ^ 2 * x j ^ 2 *
              (((1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) / τ) :=
            mul_le_mul_of_nonneg_right (hij x hx) hnn
        _ = _ := by field_simp; ring

/-- The weighted Schur test with the two row integrals as hypotheses. -/
theorem featureBound_of_rowW (hn : 1 ≤ n) (τ Cr : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hrowL : ∀ i : Fin n, ∫ x, x i ^ 2 * (1 + τ *
        ((∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ Cr / (n : ℝ))
    (hrowH : ∀ i j : Fin n, ∫ x, x i ^ 2 * x j ^ 2 * (1 / τ +
        ((∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ Cr / (n : ℝ))
    (a : Mono n d → ℝ) (ha0 : a default = 0) :
    ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂uniformSphere n ≤ Cr / (n : ℝ) * ∑ p, a p ^ 2 := by
  classical
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
  set w : Mono n d → ℝ := fun p => wt τ p.2.1 with hw
  have hwp : ∀ p, 0 < w p := fun p => wt_pos τ hτ _
  calc ∑ p, ∑ q, a p * a q * ∫ x, monoVal x (p.2.1 + q.2.1) ∂uniformSphere n
      ≤ ∑ p : Mono n d, ∑ q : Mono n d,
          ((a p ^ 2 * (w q / w p) + a q ^ 2 * (w p / w q)) / 2) * Mpq p q := by
        apply Finset.sum_le_sum; intro p _
        apply Finset.sum_le_sum; intro q _
        apply mul_le_mul_of_nonneg_right _ (hM0 p q)
        have h := div_nonneg (sq_nonneg (a p * w q - a q * w p)) (mul_pos (hwp p) (hwp q)).le
        have e : (a p * w q - a q * w p) ^ 2 / (w p * w q)
            = a p ^ 2 * (w q / w p) + a q ^ 2 * (w p / w q) - 2 * (a p * a q) := by
          have h1 := (hwp p).ne'
          have h2 := (hwp q).ne'
          field_simp
          ring
        linarith
    _ = ∑ p : Mono n d, a p ^ 2 * ∑ q : Mono n d, w q / w p * Mpq p q := by
        have e1 : ∑ p : Mono n d, ∑ q : Mono n d,
              ((a p ^ 2 * (w q / w p) + a q ^ 2 * (w p / w q)) / 2) * Mpq p q =
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a p ^ 2 * (w q / w p) * Mpq p q) +
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a q ^ 2 * (w p / w q) * Mpq p q) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro p _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro q _
          ring
        have e2 : ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a q ^ 2 * (w p / w q) * Mpq p q) =
            ∑ p : Mono n d, ∑ q : Mono n d, (1 / 2) * (a p ^ 2 * (w q / w p) * Mpq p q) := by
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
        · exact mul_le_mul_of_nonneg_left (RpW hn τ Cr hτ hτ1 hrowL hrowH p hp) (sq_nonneg _)
    _ = Cr / (n : ℝ) * ∑ p, a p ^ 2 := by rw [← Finset.sum_mul]; ring

end BstLean.Part81.UW

namespace BstLean.Part81
open MeasureTheory
open BstLean.Part29 (uniformSphere)

/-- **Feature operator bound from two weighted row integrals** (Schur test with weight `1` on
the light monomials and `τ` on the heavy ones). -/
theorem featOp_of_rowW (n d : ℕ) (hn : 1 ≤ n) (τ Cr : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hrowL : ∀ i : Fin n, ∫ x, x i ^ 2 * (1 + τ *
        ((∑ k ∈ Finset.range (d / 2 + 1), BstLean.Part53.hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ Cr / (n : ℝ))
    (hrowH : ∀ i j : Fin n, ∫ x, x i ^ 2 * x j ^ 2 * (1 / τ +
        ((∑ k ∈ Finset.range (d / 2 + 1), BstLean.Part53.hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ Cr / (n : ℝ)) :
    FeatOp n d Cr :=
  F3.featOp_of_mono _ fun a ha0 => UW.featureBound_of_rowW hn τ Cr hτ hτ1 hrowL hrowH a ha0

end BstLean.Part81

#print axioms BstLean.Part81.featOp_of_rowW
