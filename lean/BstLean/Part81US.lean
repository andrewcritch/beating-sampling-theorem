import BstLean.Part81UW
import BstLean.Part81KD

/-!
# Part 81 (US): `ss2` from the two weighted row integrals

`ss2 n d = Σ_{p,q} M_pq²` over the non-constant monomials, `M_pq ≤ (s M_pp + M_qq / s)/2`, so
`ss2 ≤ Σ_p M_pp R_p` with the weighted row sums `R_p` of `Part81UW`. The TOP monomials (`x_k` and
`x_k²`) have `R_p ≤ CrL` and `Σ_TOP M_pp ≤ 1 + 3/n`; every other non-constant monomial has
`R_p ≤ CrH`, and `Σ_p M_pp = tG`.
Do not use `sorry`, `native_decide` or `axiom`.
-/
namespace BstLean.Part81.US
open MeasureTheory BstLean.Part53
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM)
open BstLean.Part81.KD (prodMapUniv mom mom_nonneg mom_odd sumJJ)
open BstLean.Part81.UF
open BstLean.Part81.UW
variable {n d : ℕ}

/-- The TOP monomials: `x_k` and `x_k²`. -/
def Top (u : Multiset (Fin n)) : Prop := (∃ k, u = {k}) ∨ (∃ k, u = {k, k})

lemma k0_odd (u : Multiset (Fin n)) (h : ∃ i, u.count i % 2 = 1) : k0 u = 0 := by
  unfold k0; exact ite_eq_left_of_eq_true _ _ (eq_true h)

lemma k0_even (u : Multiset (Fin n)) (h : ¬ ∃ i, u.count i % 2 = 1) : k0 u = 1 := by
  unfold k0; exact ite_eq_right_of_eq_false _ _ (eq_false h)

lemma wt_light (τ : ℝ) (u : Multiset (Fin n)) (h : Multiset.card (gam u) = k0 u) : wt τ u = 1 := by
  unfold wt; exact ite_eq_left_of_eq_true _ _ (eq_true h)

lemma count_pair (i k : Fin n) : Multiset.count i ({k, k} : Multiset (Fin n)) = if i = k then 2 else 0 := by
  classical
  rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  split_ifs <;> rfl

lemma wt_top (τ : ℝ) (u : Multiset (Fin n)) (h : Top u) : wt τ u = 1 := by
  classical
  apply wt_light
  rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [k0_odd _ ⟨k, by simp⟩]
    have := two_card_gam_le ({k} : Multiset (Fin n))
    simp only [Multiset.card_singleton] at this
    omega
  · have hk : k0 ({k, k} : Multiset (Fin n)) = 1 := by
      apply k0_even
      rintro ⟨i, hi⟩
      rw [count_pair] at hi
      split_ifs at hi <;> omega
    rw [hk]
    have h1 := two_card_gam_le ({k, k} : Multiset (Fin n))
    have h2 : Multiset.card ({k, k} : Multiset (Fin n)) = 2 := rfl
    have h3 := Multiset.count_le_card k (gam ({k, k} : Multiset (Fin n)))
    rw [count_gam, count_pair, if_pos rfl] at h3
    omega

/-- A non-constant monomial that is not TOP has `|x^p| · oddP ≤ x_i² x_j²` on the sphere. -/
lemma L6 (p : Mono n d) (hp : p ≠ default) (hT : ¬ Top p.2.1) :
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
    have hne : p.2.1 ≠ 0 := by
      intro h0
      apply hp
      apply mono_ext
      show p.2.1 = (default : Mono n d).2.1
      rw [h0]; rfl
    obtain ⟨k, hk⟩ := Multiset.exists_mem_of_ne_zero hne
    have hck := Multiset.count_pos.mpr hk
    by_cases h3 : 3 ≤ p.2.1.count k
    · left; exact ⟨k, by simp only [he]; omega⟩
    · by_cases hj : ∃ j ∈ p.2.1, j ≠ k
      · obtain ⟨j, hj, hjk⟩ := hj
        have hcj := Multiset.count_pos.mpr hj
        right; refine ⟨j, k, hjk, ?_, ?_⟩ <;> simp only [he] <;> omega
      · push Not at hj
        exfalso
        apply hT
        have hrep : p.2.1 = Multiset.replicate (p.2.1.count k) k := by
          have := (Multiset.eq_replicate (a := k) (n := Multiset.card p.2.1) (s := p.2.1)).mpr
            ⟨rfl, hj⟩
          have hc : p.2.1.count k = Multiset.card p.2.1 := by
            conv_lhs => rw [this]
            simp
          rw [hc]; exact this
        have h12 : p.2.1.count k = 1 ∨ p.2.1.count k = 2 := by omega
        rcases h12 with h1 | h2
        · left; refine ⟨k, ?_⟩; rw [hrep, h1]; rfl
        · right; refine ⟨k, ?_⟩; rw [hrep, h2]; rfl
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

open Classical in
/-- The indicator of the TOP monomials. -/
noncomputable def tI (p : Mono n d) : ℝ := if Top p.2.1 then 1 else 0

lemma tI_nonneg (p : Mono n d) : 0 ≤ tI p := by unfold tI; split_ifs <;> norm_num

/-- The weighted row sum: `≤ CrL` on the TOP monomials, `≤ CrH` on the others. -/
lemma RpS (hn : 1 ≤ n) (τ CrL CrH : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hCrL : 0 ≤ CrL) (hCrH : 0 ≤ CrH)
    (hrowL : ∀ i : Fin n, ∫ x, x i ^ 2 * (1 + τ *
        ((∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ CrL)
    (hrowH : ∀ i j : Fin n, ∫ x, x i ^ 2 * x j ^ 2 * (1 / τ +
        ((∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ CrH)
    (p : Mono n d) (hp : p ≠ default) :
    ∑ q : Mono n d, wt τ q.2.1 / wt τ p.2.1 * Mpq p q ≤ tI p * CrL + CrH := by
  classical
  have hScont : Continuous (fun x : Fin n → ℝ =>
      ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) :=
    continuous_finsetSum _ fun k _ => cont_hS k
  have hS0 : ∀ x : Fin n → ℝ, 0 ≤ ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k :=
    fun x => Finset.sum_nonneg fun k _ => hS_nonneg _ (fun j => sq_nonneg _) k
  by_cases hT : Top p.2.1
  · have ht : tI p = 1 := by unfold tI; exact if_pos hT
    have hw : wt τ p.2.1 = 1 := wt_top τ _ hT
    obtain ⟨i, hi⟩ := L4 p hp
    rw [ht, one_mul]
    refine le_trans (le_trans (RpW_core hn τ hτ hτ1 p _ ?_ ?_) (hrowL i)) (by linarith)
    · exact ((continuous_apply i).pow 2).mul
        (continuous_const.add (continuous_const.mul (hScont.sub continuous_const)))
    · intro x hx
      rw [hw, div_one]
      have hnn : 0 ≤ (1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k := by
        have := mul_nonneg hτ.le (hS0 x); linarith
      calc _ ≤ x i ^ 2 * ((1 - τ) + τ * ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k) :=
            mul_le_mul_of_nonneg_right (hi x hx) hnn
        _ = _ := by ring
  · have ht : tI p = 0 := by unfold tI; exact if_neg hT
    obtain ⟨i, j, hij⟩ := L6 p hp hT
    rw [ht, zero_mul, zero_add]
    refine le_trans (RpW_core hn τ hτ hτ1 p _ ?_ ?_) (hrowH i j)
    · exact (((continuous_apply i).pow 2).mul ((continuous_apply j).pow 2)).mul
        (continuous_const.add (hScont.sub continuous_const))
    · intro x hx
      set S := ∑ k ∈ Finset.range (d / 2 + 1), hS53 (fun l => x l ^ 2) k with hS
      have hS0' : 0 ≤ S := hS0 x
      have hτS : 0 ≤ τ * S := mul_nonneg hτ.le hS0'
      have hfac : ((1 - τ) + τ * S) / wt τ p.2.1 ≤ 1 / τ + (S - 1) := by
        have e1 : ((1 - τ) + τ * S) / τ = 1 / τ + (S - 1) := by field_simp; ring
        have h1 : 1 ≤ 1 / τ := by rw [le_div_iff₀ hτ]; linarith
        unfold wt
        split_ifs
        · rw [div_one]
          have h2 := div_nonneg (sq_nonneg (1 - τ)) hτ.le
          have e2 : (1 - τ) ^ 2 / τ = 1 / τ + τ - 2 := by field_simp; ring
          nlinarith [mul_nonneg (sub_nonneg.mpr hτ1) hS0']
        · rw [e1]
      have hnn : 0 ≤ ((1 - τ) + τ * S) / wt τ p.2.1 :=
        div_nonneg (by linarith) (wt_pos τ hτ _).le
      have hxx : 0 ≤ x i ^ 2 * x j ^ 2 := by positivity
      calc _ ≤ x i ^ 2 * x j ^ 2 * (((1 - τ) + τ * S) / wt τ p.2.1) :=
            mul_le_mul_of_nonneg_right (hij x hx) hnn
        _ ≤ _ := mul_le_mul_of_nonneg_left hfac hxx

lemma Mpq_eq (p q : Mono n d) :
    Mpq p q = ∫ x, monoVal x p.2.1 * monoVal x q.2.1 ∂uniformSphere n := by
  unfold Mpq; simp_rw [monoVal_add]

lemma intM (hn : 1 ≤ n) (p q : Mono n d) :
    Integrable (fun x => monoVal x p.2.1 * monoVal x q.2.1) (uniformSphere n) := by
  simp_rw [← monoVal_add]
  exact (mom hn _).1

/-- `M_pq ≤ ((a/b) M_pp + (b/a) M_qq)/2`. -/
lemma Mpq_amgm (hn : 1 ≤ n) (p q : Mono n d) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Mpq p q ≤ (a / b * Mpq p p + b / a * Mpq q q) / 2 := by
  have hI : Integrable (fun x => (a / b * (monoVal x p.2.1 * monoVal x p.2.1)
      + b / a * (monoVal x q.2.1 * monoVal x q.2.1)) / 2) (uniformSphere n) :=
    (((intM hn p p).const_mul _).add ((intM hn q q).const_mul _)).div_const _
  have h := integral_mono (intM hn p q) hI (fun x => by
    show monoVal x p.2.1 * monoVal x q.2.1 ≤ (a / b * (monoVal x p.2.1 * monoVal x p.2.1)
      + b / a * (monoVal x q.2.1 * monoVal x q.2.1)) / 2
    set u := monoVal x p.2.1
    set v := monoVal x q.2.1
    have h := div_nonneg (sq_nonneg (a * u - b * v)) (mul_pos ha hb).le
    have e : (a * u - b * v) ^ 2 / (a * b) = a / b * (u * u) + b / a * (v * v) - 2 * (u * v) := by
      have h1 := ha.ne'
      have h2 := hb.ne'
      field_simp
      ring
    linarith)
  rw [integral_div, integral_add ((intM hn p p).const_mul _) ((intM hn q q).const_mul _),
    integral_const_mul, integral_const_mul, ← Mpq_eq, ← Mpq_eq, ← Mpq_eq] at h
  exact h

lemma ss2_eq (hn : 1 ≤ n) : ss2 n d = ∑ p : JJ n d, ∑ q : JJ n d, Mpq p.1 q.1 ^ 2 := by
  classical
  unfold ss2
  have hexp : ∀ x y : Fin n → ℝ, kap d x y ^ 2 = ∑ p : JJ n d, ∑ q : JJ n d,
      (monoVal x p.1.2.1 * monoVal x q.1.2.1) * (monoVal y p.1.2.1 * monoVal y q.1.2.1) := by
    intro x y
    unfold kap
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    unfold pf phiM; ring
  have h1 : ∀ x : Fin n → ℝ, ∫ y, kap d x y ^ 2 ∂uniformSphere n = ∑ p : JJ n d, ∑ q : JJ n d,
      (monoVal x p.1.2.1 * monoVal x q.1.2.1) * Mpq p.1 q.1 := by
    intro x
    simp_rw [hexp]
    rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
      (intM hn p.1 q.1).const_mul _]
    apply Finset.sum_congr rfl; intro p _
    rw [integral_finsetSum _ fun q _ => (intM hn p.1 q.1).const_mul _]
    apply Finset.sum_congr rfl; intro q _
    rw [integral_const_mul, ← Mpq_eq]
  simp_rw [h1]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
    (intM hn p.1 q.1).mul_const _]
  apply Finset.sum_congr rfl; intro p _
  rw [integral_finsetSum _ fun q _ => (intM hn p.1 q.1).mul_const _]
  apply Finset.sum_congr rfl; intro q _
  rw [integral_mul_const, ← Mpq_eq, sq]

lemma tG_eq (hn : 1 ≤ n) : tG n d = ∑ p : JJ n d, Mpq p.1 p.1 := by
  unfold tG kap
  have e : ∀ x : Fin n → ℝ, ∑ q : JJ n d, pf x q * pf x q
      = ∑ q : JJ n d, monoVal x q.1.2.1 * monoVal x q.1.2.1 := fun x => rfl
  simp_rw [e]
  rw [integral_finsetSum _ fun q _ => intM hn q.1 q.1]
  apply Finset.sum_congr rfl; intro q _
  rw [← Mpq_eq]

/-- At most one monomial of `Mono n d` has a given multiset. -/
lemma sum_param (u : Fin n → Multiset (Fin n)) (v : Fin n → ℝ) (hv : ∀ k, 0 ≤ v k) :
    ∑ p : Mono n d, ∑ k, (if p.2.1 = u k then v k else 0) ≤ ∑ k, v k := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro k _
  by_cases h : ∃ p0 : Mono n d, p0.2.1 = u k
  · obtain ⟨p0, hp0⟩ := h
    have e : ∀ p : Mono n d, (if p.2.1 = u k then v k else 0) = if p = p0 then v k else 0 := by
      intro p
      by_cases hpp : p = p0
      · rw [if_pos hpp, if_pos (by rw [hpp]; exact hp0)]
      · rw [if_neg hpp, if_neg (fun h => hpp (mono_ext p p0 (h.trans hp0.symm)))]
    simp_rw [e]
    rw [Finset.sum_ite_eq' Finset.univ p0, if_pos (Finset.mem_univ _)]
  · push Not at h
    apply le_trans (le_of_eq _) (hv k)
    apply Finset.sum_eq_zero; intro p _
    rw [if_neg (h p)]

/-- `Σ_{p TOP} M_pp ≤ 1 + 3/n`. -/
lemma top_sum (hn : 1 ≤ n) : ∑ p : Mono n d, tI p * Mpq p p ≤ 1 + 3 / (n : ℝ) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : ∑ p : Mono n d, tI p * Mpq p p
      = ∫ x, ∑ p : Mono n d, tI p * (monoVal x p.2.1 * monoVal x p.2.1) ∂uniformSphere n := by
    rw [integral_finsetSum _ fun p _ => (intM hn p p).const_mul _]
    apply Finset.sum_congr rfl; intro p _
    rw [integral_const_mul, ← Mpq_eq]
  have hq4 : Integrable (fun x : Fin n → ℝ => 1 + BstLean.Part78.q4 x) (uniformSphere n) :=
    BstLean.Part78.sph_int hn (continuous_const.add BstLean.Part78.q4_cont)
  have hR : ∫ x : Fin n → ℝ, (1 + BstLean.Part78.q4 x) ∂uniformSphere n = 1 + 3 / ((n : ℝ) + 2) := by
    have := BstLean.Part29.uniformSphere_isProbability n hn
    rw [integral_add (integrable_const _) (BstLean.Part78.sph_int hn BstLean.Part78.q4_cont),
      BstLean.Part78.integral_q4 hn]
    simp
  rw [hL]
  have hle : (1 : ℝ) + 3 / ((n : ℝ) + 2) ≤ 1 + 3 / (n : ℝ) := by
    have : 3 / ((n : ℝ) + 2) ≤ 3 / (n : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) hnR (by linarith)
    linarith
  refine le_trans ?_ (hR.le.trans hle)
  apply integral_mono_ae (integrable_finsetSum _ fun p _ => (intM hn p p).const_mul _) hq4
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  have h1 := sum_param (d := d) (fun k => ({k} : Multiset (Fin n))) (fun k => x k ^ 2)
    (fun k => sq_nonneg _)
  have h2 := sum_param (d := d) (fun k => ({k, k} : Multiset (Fin n))) (fun k => x k ^ 4)
    (fun k => by positivity)
  have hterm : ∀ p : Mono n d, tI p * (monoVal x p.2.1 * monoVal x p.2.1)
      ≤ ∑ k, (if p.2.1 = ({k} : Multiset (Fin n)) then x k ^ 2 else 0)
        + ∑ k, (if p.2.1 = ({k, k} : Multiset (Fin n)) then x k ^ 4 else 0) := by
    intro p
    have n1 : 0 ≤ ∑ k, (if p.2.1 = ({k} : Multiset (Fin n)) then x k ^ 2 else 0) :=
      Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
    have n2 : 0 ≤ ∑ k, (if p.2.1 = ({k, k} : Multiset (Fin n)) then x k ^ 4 else 0) :=
      Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
    by_cases hT : Top p.2.1
    · have ht : tI p = 1 := by unfold tI; exact if_pos hT
      rw [ht, one_mul]
      rcases hT with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hs := Finset.single_le_sum
          (f := fun k => if p.2.1 = ({k} : Multiset (Fin n)) then x k ^ 2 else 0)
          (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ k)
        simp only [if_pos hk] at hs
        have hv : monoVal x p.2.1 * monoVal x p.2.1 = x k ^ 2 := by
          rw [hk]; simp [monoVal]; ring
        linarith
      · have hs := Finset.single_le_sum
          (f := fun k => if p.2.1 = ({k, k} : Multiset (Fin n)) then x k ^ 4 else 0)
          (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ k)
        simp only [if_pos hk] at hs
        have hv : monoVal x p.2.1 * monoVal x p.2.1 = x k ^ 4 := by
          rw [hk]; simp [monoVal]; ring
        linarith
    · have ht : tI p = 0 := by unfold tI; exact if_neg hT
      rw [ht, zero_mul]; linarith
  calc ∑ p : Mono n d, tI p * (monoVal x p.2.1 * monoVal x p.2.1)
      ≤ ∑ p : Mono n d, (∑ k, (if p.2.1 = ({k} : Multiset (Fin n)) then x k ^ 2 else 0)
        + ∑ k, (if p.2.1 = ({k, k} : Multiset (Fin n)) then x k ^ 4 else 0)) :=
        Finset.sum_le_sum fun p _ => hterm p
    _ ≤ ∑ k, x k ^ 2 + ∑ k, x k ^ 4 := by rw [Finset.sum_add_distrib]; linarith
    _ = 1 + BstLean.Part78.q4 x := by rw [hx]; rfl

end BstLean.Part81.US

namespace BstLean.Part81
open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part41 (Mono)
open BstLean.Part81.UF BstLean.Part81.UW BstLean.Part81.US

/-- **`ss2` from the two weighted row integrals.** -/
theorem ss2_le_rowW (n d : ℕ) (hn : 1 ≤ n) (τ CrL CrH : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hCrL : 0 ≤ CrL) (hCrH : 0 ≤ CrH)
    (hrowL : ∀ i : Fin n, ∫ x, x i ^ 2 * (1 + τ *
        ((∑ k ∈ Finset.range (d / 2 + 1), BstLean.Part53.hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ CrL)
    (hrowH : ∀ i j : Fin n, ∫ x, x i ^ 2 * x j ^ 2 * (1 / τ +
        ((∑ k ∈ Finset.range (d / 2 + 1), BstLean.Part53.hS53 (fun l => x l ^ 2) k) - 1))
          ∂uniformSphere n ≤ CrH) :
    ss2 n d ≤ (1 + 3 / (n : ℝ)) * CrL + tG n d * CrH := by
  classical
  have hM0 : ∀ p q : Mono n d, 0 ≤ Mpq p q := fun p q => KD.mom_nonneg hn _
  set w : Mono n d → ℝ := fun p => wt τ p.2.1 with hw
  have hwp : ∀ p, 0 < w p := fun p => wt_pos τ hτ _
  rw [ss2_eq hn, tG_eq hn]
  calc ∑ p : JJ n d, ∑ q : JJ n d, Mpq p.1 q.1 ^ 2
      ≤ ∑ p : JJ n d, ∑ q : JJ n d,
          ((1 / 2) * (w q.1 / w p.1 * Mpq p.1 q.1 * Mpq p.1 p.1)
            + (1 / 2) * (w p.1 / w q.1 * Mpq p.1 q.1 * Mpq q.1 q.1)) := by
        apply Finset.sum_le_sum; intro p _
        apply Finset.sum_le_sum; intro q _
        have h := mul_le_mul_of_nonneg_left
          (Mpq_amgm hn p.1 q.1 (w q.1) (w p.1) (hwp _) (hwp _)) (hM0 p.1 q.1)
        calc Mpq p.1 q.1 ^ 2 = Mpq p.1 q.1 * Mpq p.1 q.1 := sq _
          _ ≤ _ := h
          _ = _ := by ring
    _ = ∑ p : JJ n d, Mpq p.1 p.1 * ∑ q : JJ n d, w q.1 / w p.1 * Mpq p.1 q.1 := by
        have e2 : ∑ p : JJ n d, ∑ q : JJ n d,
              (1 / 2) * (w p.1 / w q.1 * Mpq p.1 q.1 * Mpq q.1 q.1) =
            ∑ p : JJ n d, ∑ q : JJ n d, (1 / 2) * (w q.1 / w p.1 * Mpq p.1 q.1 * Mpq p.1 p.1) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro q _
          rw [Mpq_symm q.1 p.1]
        simp_rw [Finset.sum_add_distrib]
        rw [e2, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p _
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q _
        ring
    _ ≤ ∑ p : JJ n d, Mpq p.1 p.1 * (tI p.1 * CrL + CrH) := by
        apply Finset.sum_le_sum; intro p _
        apply mul_le_mul_of_nonneg_left _ (hM0 _ _)
        refine le_trans ?_ (RpS hn τ CrL CrH hτ hτ1 hCrL hCrH hrowL hrowH p.1 p.2)
        have hs := KD.sumJJ (fun q : Mono n d => w q / w p.1 * Mpq p.1 q)
        have h0 : 0 ≤ w (default : Mono n d) / w p.1 * Mpq p.1 default :=
          mul_nonneg (div_nonneg (hwp _).le (hwp _).le) (hM0 _ _)
        linarith
    _ = CrL * ∑ p : JJ n d, tI p.1 * Mpq p.1 p.1 + (∑ p : JJ n d, Mpq p.1 p.1) * CrH := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p _
        ring
    _ ≤ (1 + 3 / (n : ℝ)) * CrL + (∑ p : JJ n d, Mpq p.1 p.1) * CrH := by
        have hs := KD.sumJJ (fun q : Mono n d => tI q * Mpq q q)
        have h0 : 0 ≤ tI (default : Mono n d) * Mpq (default : Mono n d) default :=
          mul_nonneg (tI_nonneg _) (hM0 _ _)
        have ht := top_sum (d := d) hn
        have : ∑ p : JJ n d, tI p.1 * Mpq p.1 p.1 ≤ 1 + 3 / (n : ℝ) := by linarith
        nlinarith [mul_le_mul_of_nonneg_left this hCrL]

end BstLean.Part81

#print axioms BstLean.Part81.ss2_le_rowW
