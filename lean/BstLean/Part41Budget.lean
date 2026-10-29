import BstLean.Part41Defs
import BstLean.Part36Index

/-!
# Part 41, wave 1: allocation, budget, and the threshold certificates

Paper: Lemma `C` (allocation, budget), the proof of Theorem TC-LF (existence of `n₀`, explicit `n₀`,
monotonicity). Specification: `delegations/answers/p41-spec-opus.md`, §4 and flag 4.
Scripts: `delegations/checks/p41spec/n0_p41.py` (`n0_p41.out`). Do not use `native_decide`.

Routes.
* `alloc_le`: `O_{j,l} ≤ ⌈x⌉ ≤ x + 1`.
* `budget_le`: if `ε² ≤ 0.455`, `A/(τε²) + B = (0.91P − 0.455B)/ε² + B ≤ 0.91P/ε²`; otherwise it equals `2P`.
* `cert33`, `cert34`: the authorized relaxed thresholds are `200000000000` and `1000000000`.
  Evaluate the generating polynomial at `1/100` and use positivity and monotonicity to bound
  `Ŝ₁ ≤ 3`, `Ŝ₂ ≤ 20`, and `Ŝ₃ ≤ 300`. Then `Afun ≤ 400000 n³`, `GamP ≤ 1000 n²`, and
  `qN ≤ 10¹⁸/nᵈ`. Quantitative floor and radius bounds give `gam41 ≥ 1/50` for degree three
  and `gam41 ≥ 1/1000` for degree four. Bound the individual failure terms by rational constants.
* `exists_n0` (medium): with `x = 10`, `β = β_H = 1/100`, `ϑ = 99/100`, `η = 1/100`: `τ = O(n^{k−1−d})`,
  `θ̃, ρ̄ − 1, h_n = O(1/n)`, `μ_n → 1/(k (d!)^k)`, `η_k² Γ' = O(n^{k−2−d})`, `q_n = O(n^{−d})`,
  `b_Q = O(log n)`; so `Φ_LF(n) → 2e^{−10} + 2/100 < 1/2`.
-/

namespace BstLean.Part41

variable {n d : ℕ}

private lemma corb_nonneg (hn : 2 ≤ n) (a : ℕ) : 0 ≤ Corb n a := by
  unfold Corb
  split_ifs
  · exact le_rfl
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ a := one_le_pow₀ (by linarith)
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

private lemma cs_nonneg (hn : 2 ≤ n) (s : ℕ) : 0 ≤ cS n s := by
  unfold cS
  exact add_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (by linarith [corb_nonneg hn (s - 2 * i)]))

private lemma cs_nonneg_all (n s : ℕ) : 0 ≤ cS n s := by
  rcases n with _ | n
  · have hc (a : ℕ) : -1 ≤ Corb 0 a := by
      by_cases ha : a = 0
      · simp [Corb, ha]
      · simp [Corb, ha, zero_pow ha]
    unfold cS
    exact add_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (by positivity) (by linarith [hc (s - 2 * i)]))
  · rcases n with _ | n
    · unfold cS Corb
      simp
      positivity
    · exact cs_nonneg (by omega) s

private lemma bfix_nonneg (n k : ℕ) : 0 ≤ Bfix n k := by
  have htrace (j m : ℕ) : -1 ≤ (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) := by
    by_cases hn : n = 0
    · subst n
      by_cases hj : j - 2 * m = 0 <;> by_cases hm : m = 0 <;>
        simp [hj, hm, zero_pow]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hp := one_le_pow₀ (n := m) h1
      have : 0 ≤ (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) :=
        mul_nonneg (by positivity) (by linarith)
      linarith

  have hj (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
      -(k : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (j / 2),
        (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) := by
    have hh := Finset.sum_le_sum (s := Finset.Icc 1 (j / 2)) (fun m _ => htrace j m)
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul] at hh
    have hjk : j / 2 ≤ k := le_trans (Nat.div_le_self _ _) (Finset.mem_Icc.mp hj).2
    have hjr : (j / 2 : ℕ) ≤ (k : ℝ) := by exact_mod_cast hjk
    linarith
  have hh := Finset.sum_le_sum hj
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul] at hh
  have hc : 0 ≤ ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) :=
    Finset.sum_nonneg fun jl _ => cs_nonneg_all _ _
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hk3 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
    by_cases h : k = 0
    · simp [h]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
      nlinarith [sq_nonneg (k : ℝ)]
  unfold Bfix
  nlinarith [mul_nonneg hk (show (0 : ℝ) ≤ n by positivity),
    mul_nonneg (pow_nonneg hk 3) (show (0 : ℝ) ≤ n by positivity)]

private lemma sum_finfun_succ {α R : Type*} [Fintype α] [AddCommMonoid R]
    (j : ℕ) (f : (Fin (j + 1) → α) → R) :
    (∑ a, f a) = ∑ x : α, ∑ a : Fin j → α, f (Fin.cons x a) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => α)).sum_comp f]
  exact Fintype.sum_prod_type _

private lemma cons_apply_numeric {α : Type*} {j : ℕ} (x : α) (a : Fin j → α) (i : Fin (j + 1)) :
    Fin.cons (α := fun _ => α) x a i = if h : i.val = 0 then x else a ⟨i.val - 1, by have := i.isLt; omega⟩ := by
  refine Fin.cases (by simp) (fun i => ?_) i
  simp

private lemma gt_one_three : Gt 1 3 =
    MvPolynomial.monomial (Finsupp.single 0 2) (1 : ℚ) := by
  classical
  unfold Gt
  rw [sum_finfun_succ]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, add_zero]
  norm_num
  apply Finsupp.ext
  intro i
  fin_cases i
  simp

private lemma gsm_one_three (s m : ℕ) :
    gsm 1 3 s m = if s = 1 ∧ m = 1 then 1 else if s = 0 ∧ m = 0 then 1 else 0 := by
  classical
  have hsingle : s • (Finsupp.single (0 : Fin 1) 2 : Fin 1 →₀ ℕ) =
      Finsupp.single 0 (2 * s) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp [mul_comm]
  unfold gsm
  rw [gt_one_three, MvPolynomial.monomial_pow]
  rw [hsingle]
  simp [MvPolynomial.support_monomial, MvPolynomial.coeff_monomial]
  rw [← Finsupp.single_mul, Finsupp.sum_single_index (by simp)]
  split_ifs <;> norm_num <;> omega

private lemma shat_one_three (x : ℝ) (hx : x ≠ 0) : Shat 1 3 x = 2 := by
  norm_num [Shat, Finset.sum_Icc_succ_top, gsm_one_three, Finset.sum_range_succ, hx]

/-- The allocation: `Σ c_s O_{j,l} ≤ A/(τ ε*²) + Σ c_s`. -/
theorem alloc_le (hn : 2 ≤ n) (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hτ : 0 < tauF n d k) :
    ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * (Ocnt n d k ε jl.1 jl.2 : ℝ) ≤
      Afun n d k / (tauF n d k * epsS ε) + ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) := by
  classical
  have he : 0 < epsS ε := by unfold epsS; exact lt_min (sq_pos_of_pos hε) (by norm_num)
  rw [Afun, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun jl hjl => ?_
  have hx : 0 ≤ Shat jl.1 d n ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
      (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 * tauF n d k * epsS ε) := by positivity
  have ho : (Ocnt n d k ε jl.1 jl.2 : ℝ) ≤
      Shat jl.1 d n ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
      (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 * tauF n d k * epsS ε) + 1 := by
    exact (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.ceil_lt_add_one hx).le
  calc
    _ ≤ cS n (jl.1 - 2 * jl.2) *
        (Shat jl.1 d n ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
        (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 * tauF n d k * epsS ε) + 1) :=
      mul_le_mul_of_nonneg_left ho (cs_nonneg hn _)
    _ = _ := by simp only [div_div, mul_div_assoc]; ring

/-- The budget: `A/(τ ε*²) + B_fix ≤ max(2P, 0.91 P/ε²)` when `0.455 B_fix < 0.91 P`. -/
theorem budget_le (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hP : 455 / 1000 * Bfix n k < 91 / 100 * Pn n d) :
    Afun n d k / (tauF n d k * epsS ε) + Bfix n k ≤ baseline n d ε := by
  have he : 0 < epsS ε := by unfold epsS; exact lt_min (sq_pos_of_pos hε) (by norm_num)
  have hden : 0 < 91 / 100 * Pn n d - 455 / 1000 * Bfix n k := by linarith
  have hA : Afun n d k / tauF n d k ≤
      91 / 100 * Pn n d - 455 / 1000 * Bfix n k := by
    by_cases ha : Afun n d k = 0
    · simpa [ha] using hden.le
    · unfold tauF
      apply le_of_eq
      field_simp
  have hb : Afun n d k / (tauF n d k * epsS ε) ≤
      (91 / 100 * Pn n d - 455 / 1000 * Bfix n k) / epsS ε := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hA he.le
  unfold baseline
  by_cases hsmall : ε ^ 2 ≤ 455 / 1000
  · have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    rw [epsS, min_eq_left hsmall] at hb ⊢
    apply le_trans (show Afun n d k / (tauF n d k * ε ^ 2) + Bfix n k ≤
      (91 / 100 * Pn n d - 455 / 1000 * Bfix n k) / ε ^ 2 + Bfix n k by linarith)
      (le_trans ?_ (le_max_right _ _))
    apply (le_div_iff₀ he2).mpr
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt he2)]
    nlinarith [mul_nonneg (bfix_nonneg n k) (sub_nonneg.mpr hsmall)]
  · rw [epsS, min_eq_right (le_of_not_ge hsmall)] at hb ⊢
    apply le_trans (show Afun n d k / (tauF n d k * (455 / 1000)) + Bfix n k ≤
      (91 / 100 * Pn n d - 455 / 1000 * Bfix n k) / (455 / 1000) + Bfix n k by linarith)
      (le_trans ?_ (le_max_left _ _))
    linarith

private lemma gt_coeff_nonneg (j d : ℕ) (e : Fin j →₀ ℕ) :
    0 ≤ (Gt j d).coeff e := by
  classical
  unfold Gt
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  split_ifs
  · simp only [MvPolynomial.coeff_monomial]
    split_ifs <;> positivity
  · simp

private lemma gt_pow_coeff_nonneg (j d s : ℕ) (e : Fin j →₀ ℕ) :
    0 ≤ (Gt j d ^ s).coeff e := by
  classical
  induction s generalizing e with
  | zero => simp only [pow_zero, MvPolynomial.coeff_one]; split_ifs <;> norm_num
  | succ s ih =>
    rw [pow_succ, MvPolynomial.coeff_mul]
    exact Finset.sum_nonneg fun a _ => mul_nonneg (ih a.1) (gt_coeff_nonneg j d a.2)

private lemma gt_coeff_eq_zero (j d : ℕ) (e : Fin j →₀ ℕ)
    (he : e.sum (fun _ b => b) < 2) : (Gt j d).coeff e = 0 := by
  classical
  unfold Gt
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with ha
  · rw [MvPolynomial.coeff_monomial]
    split_ifs with hea
    · have hsum : (Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))).sum
          (fun _ b => b) = ∑ i, (a i : ℕ) := by
        rw [Finsupp.sum_fintype]
        · simp
        · intro; rfl
      rw [hea] at hsum
      obtain ⟨r, hr⟩ := ha.2
      omega
    · rfl
  · simp

private lemma gt_pow_coeff_eq_zero (j d s : ℕ) (e : Fin j →₀ ℕ)
    (he : e.sum (fun _ b => b) < 2 * s) : (Gt j d ^ s).coeff e = 0 := by
  classical
  induction s generalizing e with
  | zero => omega
  | succ s ih =>
    rw [pow_succ, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    have hab : a.1 + a.2 = e := by simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using ha
    have hsum : a.1.sum (fun _ b => b) + a.2.sum (fun _ b => b) =
        e.sum (fun _ b => b) := by
      rw [← hab, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    by_cases h1 : a.1.sum (fun _ b => b) < 2 * s
    · rw [ih a.1 h1, zero_mul]
    · rw [gt_coeff_eq_zero j d a.2 (by omega), mul_zero]

private lemma gsm_eq_zero (j d s m : ℕ) (hms : m < s) : gsm j d s m = 0 := by
  classical
  unfold gsm
  refine Finset.sum_eq_zero fun e _ => ?_
  split_ifs with he
  · exact gt_pow_coeff_eq_zero j d s e (by omega)
  · rfl

private lemma gsm_nonneg (j d s m : ℕ) : 0 ≤ gsm j d s m := by
  classical
  unfold gsm
  refine Finset.sum_nonneg fun e _ => ?_
  split_ifs
  · exact gt_pow_coeff_nonneg j d s e
  · exact le_rfl

private lemma shat_ge_one (j d : ℕ) (x : ℝ) (hx : 0 ≤ x) : 1 ≤ Shat j d x := by
  unfold Shat
  have : 0 ≤ ∑ s ∈ Finset.Icc 1 (j * d), ∑ m ∈ Finset.range (j * d + 1),
      (gsm j d s m : ℝ) * x ^ s / (x ^ m * (s.factorial : ℝ)) := by
    refine Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun m _ => ?_
    exact div_nonneg (mul_nonneg (by exact_mod_cast gsm_nonneg j d s m)
      (pow_nonneg hx s)) (mul_nonneg (pow_nonneg hx m) (by positivity))
  linarith

private lemma shat_antitone (j d : ℕ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Shat j d y ≤ Shat j d x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  unfold Shat
  suffices h : (∑ s ∈ Finset.Icc 1 (j * d), ∑ m ∈ Finset.range (j * d + 1),
      (gsm j d s m : ℝ) * y ^ s / (y ^ m * (s.factorial : ℝ))) ≤
      ∑ s ∈ Finset.Icc 1 (j * d), ∑ m ∈ Finset.range (j * d + 1),
      (gsm j d s m : ℝ) * x ^ s / (x ^ m * (s.factorial : ℝ)) by linarith
  refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun m _ => ?_
  by_cases hms : m < s
  · simp [gsm_eq_zero j d s m hms]
  · have heq (z : ℝ) (hz : 0 < z) :
        (gsm j d s m : ℝ) * z ^ s / (z ^ m * (s.factorial : ℝ)) =
        (gsm j d s m : ℝ) / (z ^ (m - s) * (s.factorial : ℝ)) := by
      have hp : z ^ m = z ^ s * z ^ (m - s) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      field_simp
    rw [heq y hy, heq x hx]
    apply div_le_div_of_nonneg_left (by exact_mod_cast gsm_nonneg j d s m) (by positivity)
    gcongr

private lemma cs_pos (hn : 2 ≤ n) (s : ℕ) : 0 < cS n s := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 ≤ ∑ i ∈ Finset.range (s / 2 + 1),
      ((s.choose (2 * i) : ℕ) : ℝ) * (Corb n (s - 2 * i) + 2 * n + 8) := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (by positivity) (by linarith [corb_nonneg hn (s - 2 * i)])
  unfold cS
  linarith

private lemma afun_pos (hn : 2 ≤ n) (hk : 1 ≤ k) : 0 < Afun n d k := by
  classical
  unfold Afun
  apply Finset.sum_pos'
  · intro jl _
    exact div_nonneg (mul_nonneg (mul_nonneg (cs_nonneg hn _) (sq_nonneg _))
      (by positivity)) (by positivity)
  · refine ⟨(1, 0), ?_, ?_⟩
    · simp [levels, hk]
    · have hs : 0 < Shat 1 d n := by
        have := shat_ge_one 1 d (n : ℝ) (by positivity)
        linarith
      have hc := cs_pos hn 1
      have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      simp only [mul_zero, Nat.sub_zero, pow_zero]
      positivity

private lemma tau_pos (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hP : 455 / 1000 * Bfix n k < 91 / 100 * Pn n d) : 0 < tauF n d k := by
  exact div_pos (afun_pos hn hk) (sub_pos.mpr hP)

private lemma levels_three : levels 3 = {(1, 0), (2, 0), (3, 0), (3, 1)} := by decide

private lemma bfix_three (hn : 2 ≤ n) :
    Bfix n 3 = 2 * (n : ℝ)^3 + 4 * (n : ℝ)^2 + 62 * (n : ℝ) + 201 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (n : ℝ) - 1 ≠ 0 := by linarith
  unfold Bfix
  rw [levels_three]
  norm_num [cS, Corb, Finset.sum_range_succ, Finset.sum_Icc_succ_top]
  field_simp
  ring

private lemma choose_prod (a b : ℕ) (hb : b ≤ a) :
    (a.choose b : ℝ) = (∏ i ∈ Finset.range b, ((a : ℝ) - i)) / (b.factorial : ℝ) := by
  have hp : (∏ i ∈ Finset.range b, ((a : ℝ) - i)) = (a.descFactorial b : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (by have := Finset.mem_range.mp hi; omega)]
  rw [hp, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

private lemma pn_three (n : ℕ) :
    Pn n 3 = (n : ℝ) * (n + 1) * (n + 2) * (n + 3) / 6 := by
  unfold Pn
  rw [BstLean.Part36.DD_eq, choose_prod _ _ (by omega)]
  norm_num [Finset.prod_range_succ]
  ring

private lemma pn_four (n : ℕ) :
    Pn n 4 = (n : ℝ) * (n + 1) * (n + 2) * (n + 3) * (n + 4) / 24 := by
  unfold Pn
  rw [BstLean.Part36.DD_eq, choose_prod _ _ (by omega)]
  norm_num [Finset.prod_range_succ]
  ring

private lemma budget_condition_three (hn : 100 ≤ n) :
    455 / 1000 * Bfix n 3 < 91 / 100 * Pn n 3 := by
  have hs : (n : ℝ) = 100 + (n - 100 : ℕ) := by
    exact_mod_cast (show n = 100 + (n - 100) by omega)
  apply sub_pos.mp
  rw [bfix_three (by omega), pn_three, hs]
  ring_nf
  positivity

private lemma budget_condition_four (hn : 100 ≤ n) :
    455 / 1000 * Bfix n 3 < 91 / 100 * Pn n 4 := by
  have hs : (n : ℝ) = 100 + (n - 100 : ℕ) := by
    exact_mod_cast (show n = 100 + (n - 100) by omega)
  apply sub_pos.mp
  rw [bfix_three (by omega), pn_four, hs]
  ring_nf
  positivity

private lemma theta_three (n d : ℕ) :
    thetaT n d 3 = ((d : ℝ) + 1)^2 / (2 * n) := by
  have ht : 0 ≤ ((d : ℝ) + 1)^2 / (2 * n) := by positivity
  have hr : List.range' 1 3 = [1, 2, 3] := by decide
  norm_num [thetaT, maxJ, hr, Ls, cQ, Finset.sum_Icc_succ_top, Finset.filter_singleton]
  ring_nf at ht ⊢
  simp
  positivity

private lemma rhobar_three (n : ℕ) : rhoBar n 3 = 1 + 2 / (n : ℝ) := by
  have ht : 0 ≤ 2 / (n : ℝ) := by positivity
  have hr : List.range' 1 3 = [1, 2, 3] := by decide
  norm_num [rhoBar, maxJ, hr, cQ, Finset.sum_Icc_succ_top, Finset.filter_singleton]
  ring_nf at ht ⊢
  simp [max_eq_left (show (0 : ℝ) ≤ 1 + (n : ℝ)⁻¹ * 2 by positivity)]

private lemma lambda_pos (hn : 2 ≤ n) (hkd : k * d ≤ n) : 0 < lamS n d k := by
  unfold lamS
  refine Finset.prod_pos fun i hi => ?_
  have hin : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hkd
  have hir : (i : ℝ) < n := by exact_mod_cast hin
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact div_pos (sub_pos.mpr hir) (by positivity)

private lemma mu_pos (hn : 2 ≤ n) (hk : 1 ≤ k) (hkd : k * d ≤ n) :
    0 < muN n d k := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  exact div_pos (lambda_pos hn hkd) (by positivity)

private lemma shat_nat_bounds (j d n : ℕ) (hn : 1 ≤ n) :
    1 ≤ Shat j d n ∧ Shat j d n ≤ Shat j d 1 := by
  refine ⟨shat_ge_one j d n (by positivity), ?_⟩
  exact shat_antitone j d (by norm_num) (by exact_mod_cast hn)

private lemma eval_gt_const (j d : ℕ) (z : ℚ) :
    MvPolynomial.eval (fun _ => z) (Gt j d) =
      ∑ a : Fin j → Fin (d + 1),
        if (∑ i, (a i : ℕ)) ≠ 0 ∧ Even (∑ i, (a i : ℕ)) then
          (((∑ i, (a i : ℕ)) - 1).doubleFactorial : ℚ) * z^(∑ i, (a i : ℕ)) else 0 := by
  classical
  unfold Gt
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    have he (i : Fin j) : (Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))) i = (a i : ℕ) := by simp
    simp_rw [he]
    rw [Finset.prod_pow_eq_pow_sum]
  · simp

private lemma gsm_large_s (j d s m : ℕ) (hs : j * d < 2 * s) : gsm j d s m = 0 := by
  classical
  unfold gsm
  apply Finset.sum_eq_zero
  intro e _
  split_ifs with he
  · apply gt_pow_coeff_eq_zero
    have hsum : e.sum (fun _ b => b) ≤ j * d := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin j))) (fun i _ => he.1 i)
      simpa using hh
    omega
  · rfl

private lemma gsm_weight_sum (j d s : ℕ) :
    (∑ m ∈ Finset.range (j * d + 1), gsm j d s m / (10000 : ℚ)^m) ≤
      (MvPolynomial.eval (fun _ => (1 / 100 : ℚ)) (Gt j d))^s := by
  classical
  rw [← MvPolynomial.eval_pow, MvPolynomial.eval_eq]
  unfold gsm
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e _
  have hc := gt_pow_coeff_nonneg j d s e
  have hprod : (∏ i ∈ e.support, (1 / 100 : ℚ)^e i) = (1 / 100 : ℚ)^(e.sum (fun _ b => b)) := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hprod]
  by_cases hh : ∃ m ∈ Finset.range (j * d + 1), (∀ i, e i ≤ d) ∧ e.sum (fun _ b => b) = 2 * m
  · obtain ⟨m, hm, he⟩ := hh
    rw [Finset.sum_eq_single m]
    · rw [if_pos he, he.2]
      have hw : (1 / 100 : ℚ)^(2 * m) = 1 / (10000 : ℚ)^m := by
        rw [pow_mul]
        norm_num [div_pow]
      rw [hw]
      exact le_of_eq (by ring)
    · intro b _ hbm
      have hb : ¬ ((∀ i, e i ≤ d) ∧ e.sum (fun _ b => b) = 2 * b) := by
        intro hb
        have := hb.2
        have := he.2
        omega
      simp [hb]
    · exact fun h => (h hm).elim
  · have hz : ∀ m ∈ Finset.range (j * d + 1),
        ¬ ((∀ i, e i ≤ d) ∧ e.sum (fun _ b => b) = 2 * m) := by
      intro m hm he
      exact hh ⟨m, hm, he⟩
    have hez : (∑ m ∈ Finset.range (j * d + 1),
        (if (∀ i, e i ≤ d) ∧ e.sum (fun _ b => b) = 2 * m then (Gt j d^s).coeff e else 0) /
          (10000 : ℚ)^m) = 0 := Finset.sum_eq_zero (fun m hm => by simp [hz m hm])
    rw [hez]
    positivity

private lemma shat_eval_bound (j d n : ℕ) (hn : 10000 ≤ n) :
    Shat j d n ≤ 1 + ∑ s ∈ Finset.Icc 1 (j * d),
      if 2 * s ≤ j * d then
        (10000 * (MvPolynomial.eval (fun _ => (1 / 100 : ℚ)) (Gt j d) : ℚ) : ℝ)^s /
          (s.factorial : ℝ) else 0 := by
  classical
  apply (shat_antitone j d (by norm_num : (0 : ℝ) < 10000) (by exact_mod_cast hn)).trans
  unfold Shat
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : 2 * s ≤ j * d
  · rw [if_pos hs]
    have hb : (∑ m ∈ Finset.range (j * d + 1), (gsm j d s m : ℝ) / (10000 : ℝ)^m) ≤
        (MvPolynomial.eval (fun _ => (1 / 100 : ℚ)) (Gt j d) : ℝ)^s := by
      exact_mod_cast gsm_weight_sum j d s
    have heq : (∑ m ∈ Finset.range (j * d + 1),
        (gsm j d s m : ℝ) * (10000 : ℝ)^s / ((10000 : ℝ)^m * (s.factorial : ℝ))) =
        (10000 : ℝ)^s / (s.factorial : ℝ) *
          (∑ m ∈ Finset.range (j * d + 1), (gsm j d s m : ℝ) / (10000 : ℝ)^m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (10000 : ℝ)^s / (s.factorial : ℝ) by positivity)
    convert hh using 1 <;> push_cast <;> rw [mul_pow] <;> ring
  · rw [if_neg hs]
    simp [gsm_large_s j d s _ (by omega)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma shat_small_bound (j d n : ℕ) (hj : 1 ≤ j ∧ j ≤ 3)
    (hd : 3 ≤ d ∧ d ≤ 4) (hn : 10000 ≤ n) :
    Shat j d n ≤ if j = 1 then 3 else if j = 2 then 20 else 300 := by
  rcases hj with ⟨hjlo, hjhi⟩
  rcases hd with ⟨hdlo, hdhi⟩
  have heval : MvPolynomial.eval (fun _ => (1 / 100 : ℚ)) (Gt j d) ≤
      if j = 1 then 11 / 100000 else if j = 2 then 31 / 100000 else 61 / 100000 := by
    interval_cases j <;> interval_cases d <;>
      norm_num [eval_gt_const, sum_finfun_succ, Fin.sum_univ_succ, Fin.sum_univ_zero, cons_apply_numeric]
  have heval0 : 0 ≤ MvPolynomial.eval (fun _ => (1 / 100 : ℚ)) (Gt j d) := by
    rw [MvPolynomial.eval_eq]
    exact Finset.sum_nonneg (fun e _ => mul_nonneg (gt_coeff_nonneg j d e) (by positivity))
  have hh := shat_eval_bound j d n hn
  have hb : Shat j d n ≤ 1 + ∑ s ∈ Finset.Icc 1 (j * d),
      if 2 * s ≤ j * d then
        (if j = 1 then (11 / 10 : ℝ) else if j = 2 then 31 / 10 else 61 / 10)^s /
          (s.factorial : ℝ) else 0 := by
    apply hh.trans
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : 2 * s ≤ j * d
    · rw [if_pos hs, if_pos hs]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℚ) ≤ 10000) heval0))
      have he : (10000 * MvPolynomial.eval (fun _ => (1 / 100 : ℚ)) (Gt j d) : ℚ) ≤
          if j = 1 then 11 / 10 else if j = 2 then 31 / 10 else 61 / 10 := by
        split_ifs at heval ⊢ <;> linarith
      split_ifs at he ⊢ <;>
        have hc := (Rat.cast_le (K := ℝ)).mpr he <;> norm_num at hc <;> simpa using hc
    · simp only [if_neg hs, le_refl]
  interval_cases j <;> interval_cases d <;>
    norm_num [Finset.sum_Icc_succ_top] at hb ⊢ <;> linarith

private lemma corb_le (hn : 2 ≤ n) (a : ℕ) : Corb n a ≤ 3 * (n : ℝ)^a := by
  unfold Corb
  split_ifs
  · positivity
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < n - 1)).mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n - 2 by linarith)
      (show (0 : ℝ) ≤ (n : ℝ)^a by positivity)]

private lemma cs_le (hn : 2 ≤ n) (hs : 1 ≤ s) :
    cS n s ≤ (1 + 9 * ∑ i ∈ Finset.range (s / 2 + 1),
      (s.choose (2 * i) : ℝ)) * (n : ℝ)^s := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (n : ℝ) ≤ (n : ℝ)^s := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ n) hs
  have hp : (2 : ℝ) ≤ (n : ℝ)^s := h2.trans hnp
  have hsum : (∑ i ∈ Finset.range (s / 2 + 1),
      (s.choose (2 * i) : ℝ) * (Corb n (s - 2 * i) + 2 * n + 8)) ≤
      ∑ i ∈ Finset.range (s / 2 + 1), (s.choose (2 * i) : ℝ) * (9 * (n : ℝ)^s) := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hc := corb_le hn (s - 2 * i)
    have hpow : (n : ℝ)^(s - 2 * i) ≤ (n : ℝ)^s :=
      pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
    linarith
  rw [← Finset.sum_mul] at hsum
  unfold cS
  nlinarith

private lemma lambda_tendsto (d k : ℕ) :
    Filter.Tendsto (fun n : ℕ => lamS n d k) Filter.atTop (nhds 1) := by
  unfold lamS
  have ht (i : ℕ) : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) - i) / ((n : ℝ) + 2 * i)) Filter.atTop (nhds 1) := by
    simpa [sub_eq_add_neg, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) (2 * (i : ℝ))
        (1 : ℝ) (d := 1) (by norm_num))
  simpa using tendsto_finsetProd (Finset.range (k * d)) (fun i _ => ht i)

private lemma mu_tendsto (d k : ℕ) : Filter.Tendsto
    (fun n : ℕ => muN n d k) Filter.atTop (nhds (1 / (k * (d.factorial : ℝ)^k))) := by
  exact (lambda_tendsto d k).div_const _

private lemma pn_lower (n d : ℕ) : (n : ℝ)^(d + 1) / (d.factorial : ℝ) ≤ Pn n d := by
  have hp : (n : ℝ)^d ≤ ∏ i ∈ Finset.range d, (((n + d : ℕ) : ℝ) - i) := by
    calc
      (n : ℝ)^d = ∏ _i ∈ Finset.range d, (n : ℝ) := by simp
      _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i hi => ?_
        have hdi : (i : ℝ) ≤ d := by
          exact_mod_cast (le_of_lt (Finset.mem_range.mp hi))
        push_cast
        linarith
  unfold Pn
  rw [BstLean.Part36.DD_eq, choose_prod _ _ (by omega), pow_succ]
  have hh := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ d.factorial))
    (show (0 : ℝ) ≤ n by positivity)
  simpa only [mul_div_assoc, mul_comm] using hh

private lemma theta33_lt (hn : 35800000 ≤ n) :
    (1 + 1 / prm33.eta) * thetaT n 3 3 < 1 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (35800000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [theta_three]
  norm_num [prm33]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  linarith

private lemma theta34_lt (hn : 7420000 ≤ n) :
    (1 + 1 / prm34.eta) * thetaT n 4 3 < 1 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (7420000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [theta_three]
  norm_num [prm34]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  linarith

private lemma lambda_lower (n d k : ℕ) (hn : 1 ≤ n) (hsize : 3 * (k * d) ≤ n) :
    1 - 3 * (k * d : ℕ)^2 / (n : ℝ) ≤ lamS n d k := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsizeR : 3 * ((k * d : ℕ) : ℝ) ≤ n := by exact_mod_cast hsize
  let z : ℝ := 1 - 3 * (k * d : ℕ) / n
  have hz : 0 ≤ z := by dsimp [z]; exact sub_nonneg.mpr ((div_le_one hnp).mpr hsizeR)
  have hprod : z^(k * d) ≤ lamS n d k := by
    unfold lamS
    calc
      z^(k * d) = ∏ i ∈ Finset.range (k * d), z := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun _ _ => hz)
        intro i hi
        have hip : (i : ℝ) ≤ (k * d : ℕ) := by exact_mod_cast (Finset.mem_range.mp hi).le
        have hi0 : (0 : ℝ) ≤ i := by positivity
        have hden : 0 < (n : ℝ) + 2 * i := by positivity
        have heq : z = ((n : ℝ) - 3 * (k * d : ℕ)) / n := by dsimp [z]; field_simp
        rw [heq]
        apply (div_le_div_iff₀ hnp hden).mpr
        nlinarith [mul_nonneg (show 0 ≤ (k * d : ℕ) - (i : ℝ) by linarith) hnp.le,
          mul_nonneg (show 0 ≤ (k * d : ℕ) * (i : ℝ) by positivity) (by norm_num : (0 : ℝ) ≤ 6)]
  have hb := one_add_mul_le_pow (a := -(3 * (k * d : ℕ) / (n : ℝ)))
    (by have := hz; dsimp [z] at this; linarith : -2 ≤ -(3 * (k * d : ℕ) / (n : ℝ))) (k * d)
  have heq : 1 + (k * d : ℕ) * -(3 * (k * d : ℕ) / (n : ℝ)) =
      1 - 3 * (k * d : ℕ)^2 / (n : ℝ) := by ring
  rw [heq] at hb
  exact hb.trans hprod

private lemma mu_lower (n d k : ℕ) (hn : 1 ≤ n) (hsize : 300 * (k * d)^2 ≤ n) :
    (99 / 100 : ℝ) / (k * (d.factorial : ℝ)^k) ≤ muN n d k := by
  by_cases hp : k * d = 0
  · unfold muN
    have he : lamS n d k = 1 := by simp [lamS, hp]
    rw [he]
    exact div_le_div_of_nonneg_right (by norm_num : (99 / 100 : ℝ) ≤ 1) (by positivity)
  have hkd : 3 * (k * d) ≤ n := by
    have ha : 1 ≤ k * d := Nat.one_le_iff_ne_zero.mpr hp
    have : k * d ≤ (k * d)^2 := by nlinarith
    omega
  have hh := lambda_lower n d k hn hkd
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsizeR : 300 * ((k * d : ℕ) : ℝ)^2 ≤ n := by exact_mod_cast hsize
  have hdiv : 3 * ((k * d : ℕ) : ℝ)^2 / n ≤ 1 / 100 :=
    (div_le_iff₀ hnp).mpr (by linarith)
  unfold muN
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

private lemma maxj_three_le_two (g : ℕ → ℝ) : g 2 ≤ maxJ 3 g := by
  have hr : List.range' 1 3 = [1, 2, 3] := by decide
  simp only [maxJ, hr, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  exact (le_max_left _ _).trans (le_max_right _ _)

private lemma xi_three_pos (n d : ℕ) : 0 < XiC n d 3 := by
  have hh := maxj_three_le_two (fun j =>
    ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l + 2 ≤ j),
      ((Ls 3 (j - 2 * l) : ℝ) + 1) * ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ)^2 *
        ((d : ℝ) + 1)^(2 * l) * PsiB n d (j - 2 * l) /
        ((n : ℝ)^l * (j.factorial : ℝ) * j))
  change _ ≤ XiC n d 3 at hh
  norm_num [Ls, cQ, PsiB, Finset.sum_Ico_succ_top, Finset.sum_range_succ,
    Finset.filter_insert, Finset.filter_singleton] at hh
  exact lt_of_lt_of_le (by positivity) hh

private lemma maxj_tendsto (k : ℕ) (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ j, Filter.Tendsto (fun n => f n j) Filter.atTop (nhds (g j))) :
    Filter.Tendsto (fun n => maxJ k (f n)) Filter.atTop (nhds (maxJ k g)) := by
  have hh (l : List ℕ) : Filter.Tendsto
      (fun n => (l.map (f n)).foldr max 0) Filter.atTop (nhds ((l.map g).foldr max 0)) := by
    induction l with
    | nil => exact tendsto_const_nhds
    | cons j l ih => simpa using (hf j).max ih
  exact hh _

private lemma maxj_zero (k : ℕ) : maxJ k (fun _ => 0) = 0 := by
  have hh (l : List ℕ) : (l.map (fun _ => (0 : ℝ))).foldr max 0 = 0 := by
    induction l with
    | nil => rfl
    | cons j l ih => simp only [List.map_cons, List.foldr_cons, ih, max_self]
  exact hh _

private lemma theta_tendsto (d k : ℕ) :
    Filter.Tendsto (fun n : ℕ => thetaT n d k) Filter.atTop (nhds 0) := by
  have hj (j : ℕ) : Filter.Tendsto (fun n : ℕ =>
      ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
        (Ls k (j - 2 * l) : ℝ) * (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) *
          ((d : ℝ) + 1)^(2 * l) * (cQ j l : ℝ)^2 / ((j.factorial : ℝ) * j)) /
          (n : ℝ)^l) Filter.atTop (nhds 0) := by
    have ht (l : ℕ) (hl : l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j)) :
        Filter.Tendsto (fun n : ℕ =>
          (Ls k (j - 2 * l) : ℝ) * (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) *
            ((d : ℝ) + 1)^(2 * l) * (cQ j l : ℝ)^2 / ((j.factorial : ℝ) * j)) /
            (n : ℝ)^l) Filter.atTop (nhds 0) := by
      have hl0 : l ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1).1; omega
      have hh := ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow l).const_mul
          ((Ls k (j - 2 * l) : ℝ) * (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) *
            ((d : ℝ) + 1)^(2 * l) * (cQ j l : ℝ)^2 / ((j.factorial : ℝ) * j)))
      simp only [div_eq_mul_inv, inv_pow, zero_pow hl0, mul_zero] at hh ⊢
      exact hh
    simpa using tendsto_finsetSum _ ht
  simpa only [thetaT, maxj_zero] using maxj_tendsto k _ (fun _ => 0) hj

private lemma afun_growth (d k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    Afun n d k ≤ C * (n : ℝ)^k := by
  classical
  let W (jl : ℕ × ℕ) : ℝ :=
    (1 + 9 * ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1),
      ((jl.1 - 2 * jl.2).choose (2 * i) : ℝ)) * Shat jl.1 d 1 ^ 2
  have hW (jl : ℕ × ℕ) : 0 ≤ W jl := by dsimp [W]; positivity
  refine ⟨1 + ∑ jl ∈ levels k, W jl, ?_, ?_⟩
  · have := Finset.sum_nonneg (s := levels k) (fun jl _ => hW jl)
    linarith
  · intro n hn
    have hterm (jl : ℕ × ℕ) (hjl : jl ∈ levels k) :
        cS n (jl.1 - 2 * jl.2) * Shat jl.1 d n ^ 2 * (n : ℝ)^(k - (jl.1 - 2 * jl.2)) /
          (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2) ≤ W jl * (n : ℝ)^k := by
      have hmem := Finset.mem_filter.mp hjl
      have hjk := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem.1).1).2
      have hs : 1 ≤ jl.1 - 2 * jl.2 := by omega
      have hsk : jl.1 - 2 * jl.2 ≤ k := by omega
      have hsr : (1 : ℝ) ≤ (jl.1 - 2 * jl.2 : ℕ) := by exact_mod_cast hs
      have h4 : (1 : ℝ) ≤ 4 ^ jl.2 := one_le_pow₀ (by norm_num)
      have hd : (1 : ℝ) ≤ 4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 := by
        calc (1 : ℝ) ≤ 4 * 1 * 1 := by norm_num
          _ ≤ _ := by gcongr
      have hsb := shat_nat_bounds jl.1 d n (by omega)
      have hsq : Shat jl.1 d n ^ 2 ≤ Shat jl.1 d 1 ^ 2 := by nlinarith
      have hc := cs_le hn hs
      have hp : (n : ℝ)^k = (n : ℝ)^(jl.1 - 2 * jl.2) *
          (n : ℝ)^(k - (jl.1 - 2 * jl.2)) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ ≤ cS n (jl.1 - 2 * jl.2) * Shat jl.1 d n ^ 2 *
            (n : ℝ)^(k - (jl.1 - 2 * jl.2)) :=
          div_le_self (mul_nonneg (mul_nonneg (cs_nonneg hn _) (sq_nonneg _))
            (by positivity)) hd
        _ ≤ ((1 + 9 * ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1),
            ((jl.1 - 2 * jl.2).choose (2 * i) : ℝ)) * (n : ℝ)^(jl.1 - 2 * jl.2)) *
            Shat jl.1 d 1 ^ 2 * (n : ℝ)^(k - (jl.1 - 2 * jl.2)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hc hsq (sq_nonneg _) (by positivity)) (by positivity)
        _ = W jl * (n : ℝ)^k := by dsimp [W]; rw [hp]; ring
    calc
      Afun n d k ≤ ∑ jl ∈ levels k, W jl * (n : ℝ)^k := Finset.sum_le_sum hterm
      _ = (∑ jl ∈ levels k, W jl) * (n : ℝ)^k := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

private lemma maxj_nonneg (k : ℕ) (g : ℕ → ℝ) : 0 ≤ maxJ k g := by
  have hh (l : List ℕ) : 0 ≤ (l.map g).foldr max 0 := by
    induction l with
    | nil => exact le_rfl
    | cons j l ih => exact ih.trans (le_max_right _ _)
  exact hh _

private lemma maxj_le (k : ℕ) (g : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ j, 1 ≤ j → j ≤ k → g j ≤ C) : maxJ k g ≤ C := by
  have hh (l : List ℕ) (hl : ∀ j ∈ l, g j ≤ C) : (l.map g).foldr max 0 ≤ C := by
    induction l with
    | nil => exact hC
    | cons j l ih => exact max_le (hl j (by simp)) (ih fun i hi => hl i (by simp [hi]))
  apply hh
  intro j hj
  have := List.mem_range'.mp hj
  exact hg j (by omega) (by omega)

private lemma maxj_ge (k : ℕ) (g : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    g j ≤ maxJ k g := by
  have hh (l : List ℕ) (hl : j ∈ l) : g j ≤ (l.map g).foldr max 0 := by
    induction l with
    | nil => simp at hl
    | cons i l ih =>
      rcases List.mem_cons.mp hl with h | h
      · subst i; exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)
  exact hh (List.range' 1 k) (List.mem_range'.mpr ⟨j - 1, by omega, by omega⟩)

private lemma bfix_growth (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    Bfix n k ≤ C * (n : ℝ)^k := by
  classical
  let W (jl : ℕ × ℕ) : ℝ := 1 + 9 * ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1),
    ((jl.1 - 2 * jl.2).choose (2 * i) : ℝ)
  let R : ℝ := ∑ j ∈ Finset.Icc 1 k, ((Finset.Icc 1 (j / 2)).card : ℝ)
  have hW (jl : ℕ × ℕ) : 0 ≤ W jl := by dsimp [W]; positivity
  refine ⟨1 + (∑ jl ∈ levels k, W jl) + R + 6 * (k : ℝ)^3 + 4 * k, ?_, ?_⟩
  · have hsum := Finset.sum_nonneg (s := levels k) (fun jl _ => hW jl)
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hk3 : (0 : ℝ) ≤ (k : ℝ)^3 := by positivity
    linarith
  · intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpow : (n : ℝ) ≤ (n : ℝ)^k := by simpa using pow_le_pow_right₀ hn1 hk
    have hpow1 : (1 : ℝ) ≤ (n : ℝ)^k := one_le_pow₀ hn1
    have hc : (∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2)) ≤
        (∑ jl ∈ levels k, W jl) * (n : ℝ)^k := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun jl hjl => ?_
      have hm := Finset.mem_filter.mp hjl
      have hj := (Finset.mem_Icc.mp (Finset.mem_product.mp hm.1).1).2
      have hs : 1 ≤ jl.1 - 2 * jl.2 := by omega
      have hsk : jl.1 - 2 * jl.2 ≤ k := by omega
      exact (cs_le hn hs).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 hsk) (hW jl))
    have ht : (∑ j ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 (j / 2),
        (n : ℝ)^(j - 2 * m) * ((n : ℝ)^m - 1)) ≤ R * (n : ℝ)^k := by
      dsimp [R]
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have heq : ((Finset.Icc 1 (j / 2)).card : ℝ) * (n : ℝ)^k =
          ∑ _m ∈ Finset.Icc 1 (j / 2), (n : ℝ)^k := by simp
      rw [heq]
      refine Finset.sum_le_sum fun m hm => ?_
      have hjk := (Finset.mem_Icc.mp hj).2
      have hmj := (Finset.mem_Icc.mp hm).2
      have he : j - 2 * m + m ≤ k := by omega
      calc
        _ ≤ (n : ℝ)^(j - 2 * m) * (n : ℝ)^m := by gcongr; linarith
        _ = (n : ℝ)^(j - 2 * m + m) := (pow_add _ _ _).symm
        _ ≤ _ := pow_le_pow_right₀ hn1 he
    unfold Bfix
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have h3 : (k : ℝ)^3 * (n + 5) ≤ 6 * (k : ℝ)^3 * (n : ℝ)^k := by
      have hsmall : (n : ℝ) + 5 ≤ 6 * (n : ℝ)^k := by linarith
      have := mul_le_mul_of_nonneg_left hsmall (pow_nonneg hk0 3)
      nlinarith
    have h4 : (k : ℝ) * (n + 3) ≤ 4 * k * (n : ℝ)^k := by
      have := mul_le_mul_of_nonneg_left (show (n : ℝ) + 3 ≤ 4 * (n : ℝ)^k by linarith) hk0
      nlinarith
    nlinarith

private lemma growth_ratio_tendsto (d k : ℕ) (hkd : k ≤ d) (f : ℕ → ℝ)
    (hf0 : ∀ n, 2 ≤ n → 0 ≤ f n)
    (hfg : ∃ C : ℝ, 0 < C ∧ ∀ n, 2 ≤ n → f n ≤ C * (n : ℝ)^k) :
    Filter.Tendsto (fun n => f n / Pn n d) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hf⟩ := hfg
  have hh : ∀ᶠ n : ℕ in Filter.atTop,
      f n / Pn n d ≤ (C * (d.factorial : ℝ)) / n := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hP : 0 < Pn n d := BstLean.Part36.DD_pos (by omega)
    have hfac : (0 : ℝ) < d.factorial := by positivity
    have hPl := (div_le_iff₀ hfac).mp (pn_lower n d)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hp : (n : ℝ)^k * n ≤ (n : ℝ)^(d + 1) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hn1 (by omega)
    apply (div_le_div_iff₀ hP hnp).mpr
    have h1 := mul_le_mul_of_nonneg_right (hf n hn) hnp.le
    have h2 := mul_le_mul_of_nonneg_left hp hC.le
    have h3 := mul_le_mul_of_nonneg_left hPl hC.le
    nlinarith
  have hz : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ f n / Pn n d := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact div_nonneg (hf0 n hn) (BstLean.Part36.DD_pos (by omega)).le
  have ht : Filter.Tendsto (fun n : ℕ => (C * (d.factorial : ℝ)) / n)
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C * (d.factorial : ℝ))
  exact squeeze_zero' hz hh ht

private lemma bfix_ratio_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    Filter.Tendsto (fun n => Bfix n k / Pn n d) Filter.atTop (nhds 0) :=
  growth_ratio_tendsto d k hkd (fun n => Bfix n k) (fun n _ => bfix_nonneg n k)
    (bfix_growth k hk)

private lemma afun_ratio_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    Filter.Tendsto (fun n => Afun n d k / Pn n d) Filter.atTop (nhds 0) :=
  growth_ratio_tendsto d k hkd (fun n => Afun n d k) (fun _ hn => (afun_pos hn hk).le)
    (afun_growth d k)

private lemma tau_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    Filter.Tendsto (fun n => tauF n d k) Filter.atTop (nhds 0) := by
  have hh := (afun_ratio_tendsto d k hk hkd).div
    (tendsto_const_nhds.sub ((bfix_ratio_tendsto d k hk hkd).const_mul (455 / 1000)))
    (by norm_num : (91 / 100 : ℝ) - (455 / 1000) * 0 ≠ 0)
  have he : (fun n => tauF n d k) =ᶠ[Filter.atTop]
      (fun n => (Afun n d k / Pn n d) / (91 / 100 - 455 / 1000 * (Bfix n k / Pn n d))) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hP : Pn n d ≠ 0 := ne_of_gt (BstLean.Part36.DD_pos (by omega))
    unfold tauF
    field_simp
  have ht : Filter.Tendsto (fun n => (Afun n d k / Pn n d) /
      (91 / 100 - 455 / 1000 * (Bfix n k / Pn n d))) Filter.atTop (nhds 0) := by
    convert hh using 1
    norm_num
  exact ht.congr' he.symm

private lemma maxj_const (k : ℕ) (hk : 1 ≤ k) (c : ℝ) (hc : 0 ≤ c) :
    maxJ k (fun _ => c) = c := by
  exact le_antisymm (maxj_le k _ c hc (fun _ _ _ => le_rfl))
    (maxj_ge k (fun _ => c) 1 le_rfl hk)

private lemma invpow_tendsto (l : ℕ) : Filter.Tendsto (fun n : ℕ => ((n : ℝ)^l)⁻¹)
    Filter.atTop (nhds ((0 : ℝ)^l)) := by
  simpa only [inv_pow] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow l

private lemma rhobar_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun n => rhoBar n k) Filter.atTop (nhds 1) := by
  have hj (j : ℕ) : Filter.Tendsto (fun n : ℕ => 1 +
      ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4^l * (cQ j l : ℝ)^2 /
          ((j.factorial : ℝ) * j * (n : ℝ)^l)) Filter.atTop (nhds 1) := by
    have ht (l : ℕ) (hl : l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j)) :
        Filter.Tendsto (fun n : ℕ =>
          ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4^l * (cQ j l : ℝ)^2 /
            ((j.factorial : ℝ) * j * (n : ℝ)^l)) Filter.atTop (nhds 0) := by
      have hl0 : l ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1).1; omega
      have hh := (invpow_tendsto l).const_mul
        (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4^l * (cQ j l : ℝ)^2 /
          ((j.factorial : ℝ) * j))
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hl0] using hh
    have hh := (tendsto_finsetSum _ ht).const_add 1
    simpa using hh
  simpa only [rhoBar, maxj_const k hk 1 (by norm_num)] using maxj_tendsto k _ (fun _ => 1) hj

private lemma xi_pos (n d k : ℕ) (hk : 2 ≤ k) : 0 < XiC n d k := by
  have hh := maxj_ge k (fun j =>
    ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l + 2 ≤ j),
      ((Ls k (j - 2 * l) : ℝ) + 1) * ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ)^2 *
        ((d : ℝ) + 1)^(2 * l) * PsiB n d (j - 2 * l) /
        ((n : ℝ)^l * (j.factorial : ℝ) * j)) 2 (by omega) hk
  change _ ≤ XiC n d k at hh
  norm_num [cQ, PsiB, Finset.sum_Ico_succ_top, Finset.sum_range_succ,
    Finset.filter_insert, Finset.filter_singleton] at hh
  exact lt_of_lt_of_le (by positivity) hh

private lemma xi_has_limit (d k : ℕ) : ∃ v : ℝ,
    Filter.Tendsto (fun n => XiC n d k) Filter.atTop (nhds v) := by
  classical
  let p (m : ℕ) : ℝ := ((d : ℝ) + 1)^m * ∑ s ∈ Finset.Ico 1 m, (0 : ℝ)^(m - 1 - s)
  have hp (m : ℕ) : Filter.Tendsto (fun n => PsiB n d m) Filter.atTop (nhds (p m)) := by
    have hh := (tendsto_finsetSum (Finset.Ico 1 m) (fun s _ => invpow_tendsto (m - 1 - s))).const_mul
      (((d : ℝ) + 1)^m)
    simpa only [PsiB, p, one_div] using hh
  let c (j l : ℕ) : ℝ := ((Ls k (j - 2 * l) : ℝ) + 1) * ((j - 2 * l).factorial : ℝ) *
    (cQ j l : ℝ)^2 * ((d : ℝ) + 1)^(2 * l)
  let g (j : ℕ) : ℝ := ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l + 2 ≤ j),
    (c j l * p (j - 2 * l) * (0 : ℝ)^l) / ((j.factorial : ℝ) * j)
  have hg (j : ℕ) : Filter.Tendsto (fun n : ℕ =>
      ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l + 2 ≤ j),
        c j l * PsiB n d (j - 2 * l) / ((n : ℝ)^l * (j.factorial : ℝ) * j))
      Filter.atTop (nhds (g j)) := by
    apply tendsto_finsetSum
    intro l _
    have hh := (((hp (j - 2 * l)).const_mul (c j l)).mul (invpow_tendsto l)).div_const
      ((j.factorial : ℝ) * j)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  refine ⟨maxJ k g, ?_⟩
  exact maxj_tendsto k _ g hg

private lemma kc_tendsto (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) :
    Filter.Tendsto (fun n => Kc n d k η) Filter.atTop (nhds (1 + η)) := by
  have hh := ((rhobar_tendsto k hk).mul_const (1 + η)).div
    (tendsto_const_nhds.sub ((theta_tendsto d k).const_mul (1 + 1 / η)))
    (by norm_num : (1 : ℝ) - (1 + 1 / η) * 0 ≠ 0)
  convert hh using 1
  · funext n; rfl
  · simp

private lemma hn_tendsto (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) :
    Filter.Tendsto (fun n => hN n d k η) Filter.atTop (nhds 0) := by
  obtain ⟨v, hv⟩ := xi_has_limit d k
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hμ : (1 / (k * (d.factorial : ℝ)^k) : ℝ) ≠ 0 := by positivity
  have hh := (((hv.mul_const (1 + η)).mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))).div
    (mu_tendsto d k) hμ).div
    (tendsto_const_nhds.sub ((theta_tendsto d k).const_mul (1 + 1 / η)))
    (by norm_num : (1 : ℝ) - (1 + 1 / η) * 0 ≠ 0)
  convert hh using 1
  · funext n
    simp [hN, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  · simp

private lemma gamp_nonneg (n d k : ℕ) : 0 ≤ GamP n d k :=
  mul_nonneg (by positivity) (maxj_nonneg k _)

private lemma gamp_growth (d k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    GamP n d k ≤ C * (n : ℝ)^k := by
  classical
  let W (j : ℕ) : ℝ :=
    ((d : ℝ) + 1)^j * ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
      ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ)^2 +
      (if Even j then (cQ j (j / 2) : ℝ)^2 *
        (Real.sqrt (((d : ℝ) + 1)^j) - Real.sqrt (2^j))^2 / 4 else 0)
  have hW (j : ℕ) : 0 ≤ W j := by
    dsimp [W]
    split_ifs <;> positivity
  let C : ℝ := 1 + k * maxJ k W
  have hC : 0 < C := by
    have hm := maxj_nonneg k W
    have hk0 : (0 : ℝ) ≤ k := by positivity
    dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hj (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) : Gpj n d k j ≤ W j * (n : ℝ)^k := by
    have hsum : (∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ)^2 * (n : ℝ)^l) ≤
        (∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
          ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ)^2) * (n : ℝ)^j := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun l hl => ?_
      have hl2 := (Finset.mem_filter.mp hl).2
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by omega)) (by positivity)
    have heven : (if Even j then (cQ j (j / 2) : ℝ)^2 * (n : ℝ)^(j / 2) *
        (Real.sqrt (((d : ℝ) + 1)^j) - Real.sqrt (2^j))^2 / 4 else 0) ≤
        (if Even j then (cQ j (j / 2) : ℝ)^2 *
          (Real.sqrt (((d : ℝ) + 1)^j) - Real.sqrt (2^j))^2 / 4 else 0) * (n : ℝ)^j := by
      split_ifs
      · have hp := pow_le_pow_right₀ hn1 (Nat.div_le_self j 2)
        have hh := mul_le_mul_of_nonneg_left hp
          (show (0 : ℝ) ≤ (cQ j (j / 2) : ℝ)^2 *
            (Real.sqrt (((d : ℝ) + 1)^j) - Real.sqrt (2^j))^2 / 4 by positivity)
        nlinarith only [hh]
      · simp
    have hb : ((d : ℝ) + 1)^j *
        (∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
          ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ)^2 * (n : ℝ)^l) +
        (if Even j then (cQ j (j / 2) : ℝ)^2 * (n : ℝ)^(j / 2) *
          (Real.sqrt (((d : ℝ) + 1)^j) - Real.sqrt (2^j))^2 / 4 else 0) ≤
        W j * (n : ℝ)^j := by
      have hh := mul_le_mul_of_nonneg_left hsum
        (show (0 : ℝ) ≤ ((d : ℝ) + 1)^j by positivity)
      dsimp [W]
      nlinarith only [hh, heven]
    have hf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hden : (1 : ℝ) ≤ (j.factorial : ℝ) * j := by nlinarith
    have hp : (n : ℝ)^(k - j) * (n : ℝ)^j = (n : ℝ)^k := by
      rw [← pow_add]; congr 1; omega
    unfold Gpj
    calc
      _ ≤ (n : ℝ)^(k - j) * (W j * (n : ℝ)^j) := by
        apply mul_le_mul (div_le_self (by positivity) hden) hb
        · split_ifs <;> positivity
        · positivity
      _ = _ := by rw [← hp]; ring
  have hm : maxJ k (Gpj n d k) ≤ maxJ k W * (n : ℝ)^k := by
    apply maxj_le k _ _ (mul_nonneg (maxj_nonneg k W) (by positivity))
    intro j hj1 hjk
    exact (hj j hj1 hjk).trans
      (mul_le_mul_of_nonneg_right (maxj_ge k W j hj1 hjk) (by positivity))
  have hh := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ k by positivity)
  unfold GamP
  dsimp [C]
  nlinarith [show (0 : ℝ) ≤ (n : ℝ)^k by positivity]

private lemma gamp_ratio_tendsto (d k : ℕ) (hkd : k ≤ d) :
    Filter.Tendsto (fun n => GamP n d k / Pn n d) Filter.atTop (nhds 0) :=
  growth_ratio_tendsto d k hkd (fun n => GamP n d k) (fun n _ => gamp_nonneg n d k)
    (gamp_growth d k)

private lemma pn_tendsto_atTop (d : ℕ) :
    Filter.Tendsto (fun n : ℕ => Pn n d) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono' _ _ tendsto_natCast_atTop_atTop
  apply Filter.Eventually.of_forall
  intro n
  change (n : ℝ) ≤ BstLean.Part36.DD n d
  rw [BstLean.Part36.DD_eq]
  have hc : (1 : ℝ) ≤ (n + d).choose d := by
    exact_mod_cast (Nat.choose_pos (show d ≤ n + d by omega))
  nlinarith [show (0 : ℝ) ≤ n by positivity]

private lemma invsqrt_pn_tendsto (d : ℕ) : Filter.Tendsto
    (fun n : ℕ => (Real.sqrt (Pn n d))⁻¹) Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (pn_tendsto_atTop d))

private lemma etar_formula (hn : 2 ≤ n) (x : ℝ) :
    etaR n d x = (2 * Real.sqrt x + 2 * x / Real.sqrt (Pn n d)) / Real.sqrt (Pn n d) := by
  have hP : 0 < Pn n d := BstLean.Part36.DD_pos (by omega)
  have hs : Real.sqrt (Pn n d) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hP)
  have hsq := Real.sq_sqrt hP.le
  unfold etaR
  change (2 * Real.sqrt (Pn n d * x) + 2 * x) / Pn n d = _
  rw [Real.sqrt_mul hP.le]
  field_simp
  rw [hsq]
  ring

private lemma etar_tendsto (d : ℕ) (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => etaR n d x) Filter.atTop (nhds 0) := by
  have ht := (((invsqrt_pn_tendsto d).const_mul (2 * x)).const_add (2 * Real.sqrt x)).mul
    (invsqrt_pn_tendsto d)
  have h : Filter.Tendsto (fun n : ℕ =>
      (2 * Real.sqrt x + 2 * x / Real.sqrt (Pn n d)) / Real.sqrt (Pn n d))
      Filter.atTop (nhds 0) := by simpa [div_eq_mul_inv] using ht
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  exact (etar_formula hn x).symm

private lemma etar_gamp_tendsto (d k : ℕ) (hkd : k ≤ d) (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => etaR n d x * Real.sqrt (GamP n d k))
      Filter.atTop (nhds 0) := by
  have hg := Real.continuous_sqrt.continuousAt.tendsto.comp (gamp_ratio_tendsto d k hkd)
  have ht := (((invsqrt_pn_tendsto d).const_mul (2 * x)).const_add (2 * Real.sqrt x)).mul hg
  have h : Filter.Tendsto (fun n : ℕ =>
      (2 * Real.sqrt x + 2 * x / Real.sqrt (Pn n d)) * Real.sqrt (GamP n d k / Pn n d))
      Filter.atTop (nhds 0) := by simpa [div_eq_mul_inv] using ht
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  rw [etar_formula hn x, Real.sqrt_div (gamp_nonneg n d k)]
  ring

private lemma etak_bound {k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (he : (k : ℝ) * etaR n d x ≤ 1 / 2) :
    0 ≤ etaK n d k x ∧ etaK n d k x ≤ 2 * k * etaR n d x := by
  have hP : 0 < BstLean.Part36.DD n d := BstLean.Part36.DD_pos (by omega)
  have hr : 0 ≤ etaR n d x := by unfold etaR; positivity
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkle := mul_le_mul_of_nonneg_right hkr hr
  have her : etaR n d x ≤ 1 / 2 := by nlinarith
  have hz0 : 0 ≤ 1 - etaR n d x := by linarith
  have hz1 : 1 - etaR n d x ≤ 1 := by linarith
  have hl := one_add_mul_le_pow (show (-2 : ℝ) ≤ -etaR n d x by linarith) k
  have hu : (1 - etaR n d x)^k ≤ 1 := pow_le_one₀ hz0 hz1
  have hs := Real.sq_sqrt (pow_nonneg hz0 k)
  have hsn := Real.sqrt_nonneg ((1 - etaR n d x)^k)
  have hsu : Real.sqrt ((1 - etaR n d x)^k) ≤ 1 := by nlinarith
  have hsl : 1 / 2 ≤ Real.sqrt ((1 - etaR n d x)^k) := by
    simp only [mul_neg, ← sub_eq_add_neg] at hl
    nlinarith
  have hsp : 0 < Real.sqrt ((1 - etaR n d x)^k) := by linarith
  have hd : 1 - Real.sqrt ((1 - etaR n d x)^k) ≤ k * etaR n d x := by
    simp only [mul_neg, ← sub_eq_add_neg] at hl
    nlinarith [mul_nonneg (show 0 ≤ 1 - Real.sqrt ((1 - etaR n d x)^k) by linarith) hsn]
  unfold etaK
  constructor
  · have hh : (1 : ℝ) ≤ 1 / Real.sqrt ((1 - etaR n d x)^k) :=
      (le_div_iff₀ hsp).mpr (by linarith)
    linarith
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hsp).mpr
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) * etaR n d x by positivity)
      (show 0 ≤ 2 * Real.sqrt ((1 - etaR n d x)^k) - 1 by linarith)]

private lemma etak_gamp_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (x : ℝ) (hx : 0 ≤ x) :
    Filter.Tendsto (fun n : ℕ => etaK n d k x * Real.sqrt (GamP n d k))
      Filter.atTop (nhds 0) := by
  have he : ∀ᶠ n : ℕ in Filter.atTop, (k : ℝ) * etaR n d x ≤ 1 / 2 :=
    ((etar_tendsto d x).const_mul (k : ℝ)).eventually_le_const (by norm_num)
  have hz : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ etaK n d k x * Real.sqrt (GamP n d k) := by
    filter_upwards [he, Filter.eventually_ge_atTop 2] with n hn hn2
    exact mul_nonneg (etak_bound hn2 hk x hx hn).1 (Real.sqrt_nonneg _)
  have hb : ∀ᶠ n : ℕ in Filter.atTop, etaK n d k x * Real.sqrt (GamP n d k) ≤
      2 * k * (etaR n d x * Real.sqrt (GamP n d k)) := by
    filter_upwards [he, Filter.eventually_ge_atTop 2] with n hn hn2
    have hh := mul_le_mul_of_nonneg_right (etak_bound hn2 hk x hx hn).2 (Real.sqrt_nonneg (GamP n d k))
    nlinarith only [hh]
  exact squeeze_zero' hz hb (by simpa using (etar_gamp_tendsto d k hkd x).const_mul (2 * (k : ℝ)))

private lemma choose_shift_tendsto (r s : ℕ) : Filter.Tendsto
    (fun n : ℕ => ((n - r).choose s : ℝ) / (n : ℝ)^s)
    Filter.atTop (nhds (1 / (s.factorial : ℝ))) := by
  have ht (i : ℕ) : Filter.Tendsto (fun n : ℕ => 1 - ((r + i : ℕ) : ℝ) / n)
      Filter.atTop (nhds 1) := by
    have hh := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((r + i : ℕ) : ℝ)
    simpa [div_eq_mul_inv] using hh.const_sub 1
  have hh := (tendsto_finsetProd (Finset.range s) (fun i _ => ht i)).div_const (s.factorial : ℝ)
  have h : Filter.Tendsto (fun n : ℕ =>
      (∏ i ∈ Finset.range s, (1 - ((r + i : ℕ) : ℝ) / n)) / (s.factorial : ℝ))
      Filter.atTop (nhds (1 / (s.factorial : ℝ))) := by simpa using hh
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (r + s + 1)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : (∏ i ∈ Finset.range s, (1 - ((r + i : ℕ) : ℝ) / n)) =
      (∏ i ∈ Finset.range s, (((n - r : ℕ) : ℝ) - i)) / (n : ℝ)^s := by
    calc
      _ = ∏ i ∈ Finset.range s, ((((n - r : ℕ) : ℝ) - i) / (n : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [Nat.cast_sub (by omega)]
        push_cast
        field_simp
        ring
      _ = _ := by rw [Finset.prod_div_distrib]; simp
  rw [hp, choose_prod _ _ (by omega)]
  ring

private lemma qn_tendsto (d k : ℕ) (hd : 1 ≤ d) :
    Filter.Tendsto (fun n => qN n d k) Filter.atTop (nhds 0) := by
  have ht (i : ℕ) (hi : i ∈ Finset.Icc d (k * d)) : Filter.Tendsto
      (fun n : ℕ => ((k * d).choose i : ℝ) * ((n - k * d).choose (k * d - i) : ℝ) /
        (n.choose (k * d) : ℝ)) Filter.atTop (nhds 0) := by
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    have hir : i ≤ k * d := (Finset.mem_Icc.mp hi).2
    have hh := (((choose_shift_tendsto (k * d) (k * d - i)).const_mul
      (((k * d).choose i : ℝ))).mul (invpow_tendsto i)).div
      (choose_shift_tendsto 0 (k * d))
      (by positivity : (1 / ((k * d).factorial : ℝ)) ≠ 0)
    have h : Filter.Tendsto (fun n : ℕ =>
        (((k * d).choose i : ℝ) * (((n - k * d).choose (k * d - i) : ℝ) /
          (n : ℝ)^(k * d - i)) * ((n : ℝ)^i)⁻¹) /
          ((n.choose (k * d) : ℝ) / (n : ℝ)^(k * d))) Filter.atTop (nhds 0) := by
      convert hh using 1
      norm_num [hi0]
    apply h.congr'
    filter_upwards [Filter.eventually_ge_atTop (k * d + 1)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hc : (n.choose (k * d) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.choose_pos (show k * d ≤ n by omega)))
    have hp : (n : ℝ)^(k * d) = (n : ℝ)^(k * d - i) * (n : ℝ)^i := by
      rw [← pow_add, Nat.sub_add_cancel hir]
    rw [hp]
    field_simp
  simpa [qN] using tendsto_finsetSum _ ht

private lemma pin_tendsto (d k : ℕ) (hd : 1 ≤ d) (th : ℝ) (hth : th ≠ 1) :
    Filter.Tendsto (fun n => piN n d k th) Filter.atTop (nhds 0) := by
  have hh := ((qn_tendsto d k hd).const_mul (9^k - 1)).div
    (((qn_tendsto d k hd).const_mul (9^k - 1)).add_const ((1 - th)^2))
    (by simpa using (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hth))) :
      (9^k - 1) * (0 : ℝ) + (1 - th)^2 ≠ 0)
  convert hh using 1
  · funext n; rfl
  · simp

private lemma card_mono (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose,
    ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

private lemma gamp_three_bound (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 100 ≤ n) :
    GamP n d 3 ≤ 1000 * (n : ℝ)^2 := by
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  unfold GamP
  apply (mul_le_mul_of_nonneg_left (maxj_le _ _ ((1000 / 3) * (n : ℝ)^2) (by positivity) ?_) (by norm_num : (0 : ℝ) ≤ 3)).trans
  · exact le_of_eq (by ring)
  intro j hj1 hj3
  rcases hd with ⟨hdlo, hdhi⟩
  interval_cases j <;> interval_cases d <;>
    norm_num [Gpj, cQ, Finset.range_add_one, Finset.range_zero,
      Finset.filter_insert, Finset.filter_singleton] <;> nlinarith

private lemma afun_three_bound (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 10000 ≤ n) :
    Afun n d 3 ≤ 400000 * (n : ℝ)^3 := by
  classical
  have hn2 : 2 ≤ n := by omega
  have h1 := shat_small_bound 1 d n (by norm_num) hd hn
  have h2 := shat_small_bound 2 d n (by norm_num) hd hn
  have h3 := shat_small_bound 3 d n (by norm_num) hd hn
  norm_num at h1 h2 h3
  have hs1 := shat_ge_one 1 d n (by positivity)
  have hs2 := shat_ge_one 2 d n (by positivity)
  have hs3 := shat_ge_one 3 d n (by positivity)
  have hc1 := cs_le (n := n) hn2 (by norm_num : 1 ≤ 1)
  have hc2 := cs_le (n := n) hn2 (by norm_num : 1 ≤ 2)
  have hc3 := cs_le (n := n) hn2 (by norm_num : 1 ≤ 3)
  norm_num [Finset.sum_range_succ] at hc1 hc2 hc3
  have hb1 : cS n 1 * Shat 1 d n^2 ≤ 90 * n := by
    calc _ ≤ (10 * (n : ℝ)) * 3^2 := mul_le_mul hc1 (by nlinarith) (sq_nonneg _) (by positivity)
         _ = _ := by ring
  have hb2 : cS n 2 * Shat 2 d n^2 ≤ 7600 * (n : ℝ)^2 := by
    calc _ ≤ (19 * (n : ℝ)^2) * 20^2 := mul_le_mul hc2 (by nlinarith) (sq_nonneg _) (by positivity)
         _ = _ := by ring
  have hb3 : cS n 3 * Shat 3 d n^2 ≤ 3330000 * (n : ℝ)^3 := by
    calc _ ≤ (37 * (n : ℝ)^3) * 300^2 := mul_le_mul hc3 (by nlinarith) (sq_nonneg _) (by positivity)
         _ = _ := by ring
  have hb31 : cS n 1 * Shat 3 d n^2 ≤ 900000 * n := by
    calc _ ≤ (10 * (n : ℝ)) * 300^2 := mul_le_mul hc1 (by nlinarith) (sq_nonneg _) (by positivity)
         _ = _ := by ring
  unfold Afun
  rw [levels_three]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right hb1 (show 0 ≤ (n : ℝ)^2 by positivity),
    mul_le_mul_of_nonneg_right hb2 (show (0 : ℝ) ≤ n by positivity),
    mul_le_mul_of_nonneg_right hb31 (show 0 ≤ (n : ℝ)^2 by positivity)]

private lemma pn_quartic_lower (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 1 ≤ n) :
    (n : ℝ)^4 / 24 ≤ Pn n d := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := pn_lower n d
  rcases hd with ⟨hdlo, hdhi⟩
  interval_cases d
  · norm_num at hp
    nlinarith [show 0 ≤ (n : ℝ)^4 by positivity]
  · norm_num at hp
    have hh := pow_le_pow_right₀ hnR (by norm_num : 4 ≤ 5)
    linarith

private lemma etar_three_upper (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 10000 ≤ n)
    (x : ℝ) (hx0 : 0 ≤ x) (hx12 : x ≤ 12) : etaR n d x ≤ 50 / (n : ℝ)^2 := by
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hP := pn_quartic_lower d n hd (by omega)
  have hP0 : 0 ≤ Pn n d := le_trans (by positivity) hP
  have hroot : (n : ℝ)^2 / 5 ≤ Real.sqrt (Pn n d) := by
    apply (Real.le_sqrt (by positivity) hP0).mpr
    nlinarith [show 0 ≤ (n : ℝ)^4 by positivity]
  have hroot12 : 12 ≤ Real.sqrt (Pn n d) := by nlinarith
  have hroot0 : 0 < Real.sqrt (Pn n d) := by linarith
  have hsx : Real.sqrt x ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hxdiv : 2 * x / Real.sqrt (Pn n d) ≤ 2 := (div_le_iff₀ hroot0).mpr (by linarith)
  have hbound : 10 ≤ (50 / (n : ℝ)^2) * Real.sqrt (Pn n d) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2)).mpr
    linarith
  rw [etar_formula (by omega)]
  apply (div_le_iff₀ hroot0).mpr
  linarith

private lemma radius_error_upper (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 10000 ≤ n)
    (x : ℝ) (hx0 : 0 ≤ x) (hx12 : x ≤ 12) :
    etaK n d 3 x * Real.sqrt (GamP n d 3 / (1 / 1000)) ≤ 300000 / (n : ℝ) := by
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr := etar_three_upper d n hd hn x hx0 hx12
  have hsmall : (3 : ℝ) * etaR n d x ≤ 1 / 2 := by
    have hp : 3 * (50 / (n : ℝ)^2) ≤ 1 / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2)).mpr
      nlinarith
    linarith
  have hk := (etak_bound (by omega : 2 ≤ n) (by norm_num : 1 ≤ 3) x hx0 hsmall).2
  have hg := gamp_three_bound d n hd (by omega)
  have hs : Real.sqrt (GamP n d 3 / (1 / 1000)) ≤ 1000 * n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · norm_num
      nlinarith
  have her : 0 ≤ etaR n d x := by rw [etar_formula (by omega)]; positivity
  calc
    _ ≤ (6 * etaR n d x) * (1000 * n) :=
      mul_le_mul (by norm_num at hk; exact hk) hs (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) her)
    _ ≤ (6 * (50 / (n : ℝ)^2)) * (1000 * n) := by gcongr
    _ = _ := by field_simp [ne_of_gt hn0]; ring

private lemma budget_den_lower (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 100 ≤ n) :
    Pn n d / 2 ≤ 91 / 100 * Pn n d - 455 / 1000 * Bfix n 3 := by
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn2 : 100 * (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 100) hn0]
  have hn3 : 100 * (n : ℝ)^2 ≤ (n : ℝ)^3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 100) (sq_nonneg (n : ℝ))]
  have hn4 : 100 * (n : ℝ)^3 ≤ (n : ℝ)^4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 100) (pow_nonneg hn0 3)]
  have hB : Bfix n 3 ≤ 3 * (n : ℝ)^3 := by
    rw [bfix_three (by omega)]
    nlinarith
  have hP := pn_quartic_lower d n hd (by omega)
  nlinarith

private lemma tau_three_upper (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 10000 ≤ n) :
    tauF n d 3 ≤ 800000 * (n : ℝ)^3 / Pn n d := by
  have hP : 0 < Pn n d := BstLean.Part36.DD_pos (by omega)
  have hden := budget_den_lower d n hd (by omega)
  have hden0 : 0 < 91 / 100 * Pn n d - 455 / 1000 * Bfix n 3 := by linarith
  unfold tauF
  calc
    _ ≤ Afun n d 3 / (Pn n d / 2) :=
      div_le_div_of_nonneg_left (le_of_lt (afun_pos (by omega) (by norm_num))) (by positivity) hden
    _ ≤ (400000 * (n : ℝ)^3) / (Pn n d / 2) :=
      div_le_div_of_nonneg_right (afun_three_bound d n hd hn) (by positivity)
    _ = _ := by ring

private lemma hgt_bound (d k n : ℕ) (hn : 1 ≤ n) :
    Hgt n d k ≤
      ((∏ t ∈ Finset.range (k * d), (1 + 2 * t)) *
        ((d + 1)^d + 2 * k)^(2 * k) * k.factorial^3 *
        ((d + 1)^d)^k * (d + 1)^k) *
        n^(k * d + (d + 1) * (2 * k) + d * k) := by
  classical
  let CN := (d + 1)^d
  let CR := ∏ t ∈ Finset.range (k * d), (1 + 2 * t)
  let C := CR * (CN + 2 * k)^(2 * k) * k.factorial^3 * CN^k * (d + 1)^k
  let E := k * d + (d + 1) * (2 * k) + d * k
  have hCN : 0 < CN := by dsimp [CN]; positivity
  have hCR : 0 < CR := Finset.prod_pos (fun _ _ => by positivity)
  change Hgt n d k ≤ C * n^E
  have hN : Fintype.card (Mono n d) ≤ CN * n^d := by
    rw [card_mono]
    calc
      _ ≤ (n + d)^d := Nat.choose_le_pow _ _
      _ ≤ ((d + 1) * n)^d := by gcongr; nlinarith
      _ = _ := by dsimp [CN]; rw [mul_pow]
  have hD : Fintype.card (BstLean.Part36.CoefIdxD n d) ≤ CN * n^(d + 1) := by
    rw [BstLean.Part36.card_coefIdxD]
    have hh := Nat.mul_le_mul_left n (by simpa only [card_mono] using hN)
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh
  have hnp : 1 ≤ n^(d + 1) := one_le_pow₀ hn
  have hplus : Fintype.card (BstLean.Part36.CoefIdxD n d) + 2 * k ≤ (CN + 2 * k) * n^(d + 1) := by
    nlinarith
  have hrho : (∏ t ∈ Finset.range (k * d), (n + 2 * t)) ≤ CR * n^(k * d) := by
    calc
      _ ≤ ∏ t ∈ Finset.range (k * d), ((1 + 2 * t) * n) := by
        apply Finset.prod_le_prod
        intro t _
        nlinarith
      _ = _ := by rw [Finset.prod_mul_distrib]; simp [CR]
  calc
    Hgt n d k ≤ (CR * n^(k * d)) * ((CN + 2 * k) * n^(d + 1))^(2 * k) *
        k.factorial^3 * (CN * n^d)^k * (d + 1)^k := by unfold Hgt; gcongr
    _ = C * (n^(k * d) * n^((d + 1) * (2 * k)) * n^(d * k)) := by
      dsimp [C]
      simp only [mul_pow, pow_mul]
      ring
    _ = C * n^E := by dsimp [E]; rw [← pow_add, ← pow_add]

private lemma hgt_growth (d k : ℕ) : ∃ C E : ℕ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → Hgt n d k ≤ C * n^E := by
  refine ⟨_, _, ?_, fun n hn => hgt_bound d k n hn⟩
  apply mul_pos
  · apply mul_pos
    · apply mul_pos
      · apply mul_pos
        · exact Finset.prod_pos (fun _ _ => by positivity)
        · positivity
      · positivity
    · positivity
  · positivity

private lemma hgt_three_bound (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 1 ≤ n) :
    Hgt n d 3 ≤ 2^256 * n^54 := by
  have h := hgt_bound d 3 n hn
  rcases hd with ⟨hdlo, hdhi⟩
  interval_cases d
  · norm_num [Finset.prod_range_succ] at h
    apply h.trans
    apply Nat.mul_le_mul
    · norm_num
    · exact Nat.pow_le_pow_right hn (by norm_num)
  · norm_num [Finset.prod_range_succ] at h
    apply h.trans
    apply Nat.mul_le_mul_right
    norm_num

private lemma linear_le_two_pow (l : ℕ) (hl : 16 ≤ l) : 512 * l ≤ 2^l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
    rw [pow_succ]
    have : 512 * (l + 1) ≤ 2 * (512 * l) := by omega
    nlinarith

private lemma bq_three_bound (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 65536 ≤ n) :
    4 * bQ n d 3 ≤ n := by
  let l := Nat.log 2 n
  have hn0 : n ≠ 0 := by omega
  have hl : 16 ≤ l := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hpow := Nat.pow_log_le_self 2 hn0
  have hlinear := linear_le_two_pow l hl
  have hnlt : n < 2^(l + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hH := hgt_three_bound d n hd (by omega)
  have hHlt : Hgt n d 3 < 2^(256 + (l + 1) * 54) := by
    calc
      Hgt n d 3 ≤ 2^256 * n^54 := hH
      _ < 2^256 * (2^(l + 1))^54 := by gcongr
      _ = _ := by rw [← pow_mul, ← pow_add]
  have hlog := Nat.log_lt_of_lt_pow' (by omega : 256 + (l + 1) * 54 ≠ 0) hHlt
  unfold bQ
  change 4 * (Nat.log 2 (Hgt n d 3) + 1) ≤ n
  have hp : 512 * l ≤ n := hlinear.trans hpow
  omega

private lemma etar_lt_one (n d : ℕ) (hn : 1000 ≤ n) (x : ℝ) (hx : x ≤ 12) :
    etaR n d x < 1 := by
  have hP : (n : ℝ) ≤ BstLean.Part36.DD n d := by
    rw [BstLean.Part36.DD_eq]
    have hc : (1 : ℝ) ≤ (n + d).choose d := by
      exact_mod_cast (Nat.choose_pos (show d ≤ n + d by omega))
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < BstLean.Part36.DD n d := by linarith
  have hs : Real.sqrt (BstLean.Part36.DD n d * x) ≤ BstLean.Part36.DD n d / 4 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [mul_nonneg hD.le (show 0 ≤ BstLean.Part36.DD n d - 192 by linarith),
        mul_nonneg hD.le (show 0 ≤ 12 - x by linarith)]
  unfold etaR
  apply (div_lt_iff₀ hD).mpr
  nlinarith

private lemma xi_three_bound (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 100 ≤ n) :
    XiC n d 3 ≤ ((d : ℝ) + 1)^3 * (101 / 300) := by
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hi : 1 / (n : ℝ) ≤ 1 / 100 := (div_le_iff₀ hnp).mpr (by linarith)
  simp only [one_div] at hi
  unfold XiC
  apply maxj_le _ _ _ (by positivity)
  intro j hj1 hj3
  rcases hd with ⟨hdlo, hdhi⟩
  interval_cases d <;> interval_cases j <;>
    norm_num [Ls, cQ, PsiB, Finset.sum_Ico_succ_top, Finset.sum_range_succ,
      Finset.range_add_one, Finset.range_zero, Finset.filter_insert, Finset.filter_singleton] <;> nlinarith

private lemma floor_three_bound (d n : ℕ) (q : Params) (hd : 3 ≤ d ∧ d ≤ 4)
    (hn : 100 ≤ n) (hsize : 300 * (3 * d)^2 ≤ n)
    (hη : 0 < q.eta) (hθ : (1 + 1 / q.eta) * thetaT n d 3 ≤ 1 / 100)
    (hβ : 0 < q.betaH) (hth : 0 < q.th)
    (hnum : (((d : ℝ) + 1)^3 * (101 / 300)) * (1 + q.eta) <
      (n : ℝ) * ((99 / 100 : ℝ) / (3 * (d.factorial : ℝ)^3)) * (99 / 100) * q.betaH * q.th) :
    Real.sqrt (hN n d 3 q.eta / q.betaH) < Real.sqrt q.th := by
  have hn1 : 1 ≤ n := by omega
  have hμ := mu_lower n d 3 hn1 hsize
  have hμ0 : 0 < muN n d 3 := lt_of_lt_of_le (by positivity) hμ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 99 / 100 ≤ 1 - (1 + 1 / q.eta) * thetaT n d 3 := by linarith
  have hden0 : 0 < 1 - (1 + 1 / q.eta) * thetaT n d 3 := by linarith
  apply Real.sqrt_lt_sqrt (div_nonneg (le_of_lt (by
    unfold hN
    exact div_pos (mul_pos (xi_three_pos n d) (by linarith))
      (mul_pos (mul_pos hn0 hμ0) hden0))) hβ.le)
  apply (div_lt_iff₀ hβ).mpr
  unfold hN
  apply (div_lt_iff₀ (mul_pos (mul_pos hn0 hμ0) hden0)).mpr
  have hnumle := mul_le_mul_of_nonneg_right (xi_three_bound d n hd hn)
    (show 0 ≤ 1 + q.eta by linarith)
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hμ hn0.le) hden
    (by norm_num : (0 : ℝ) ≤ 99 / 100) (by positivity : 0 ≤ (n : ℝ) * muN n d 3)
  have hprod' := mul_le_mul_of_nonneg_right hprod (mul_nonneg hβ.le hth.le)
  nlinarith only [hnum, hnumle, hprod']

private lemma floor33_lt (hn : 35800000 ≤ n) :
    Real.sqrt (hN n 3 3 prm33.eta / prm33.betaH) < Real.sqrt prm33.th := by
  have hnr : (35800000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  apply floor_three_bound 3 n prm33 (by norm_num) (by omega) (by norm_num; omega)
    (by norm_num [prm33])
  · rw [theta_three]
    norm_num [prm33]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    linarith
  · norm_num [prm33]
  · norm_num [prm33]
  · norm_num [prm33]
    linarith

private lemma floor34_lt (hn : 7420000 ≤ n) :
    Real.sqrt (hN n 4 3 prm34.eta / prm34.betaH) < Real.sqrt prm34.th := by
  have hnr : (7420000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  apply floor_three_bound 4 n prm34 (by norm_num) (by omega) (by norm_num; omega)
    (by norm_num [prm34])
  · rw [theta_three]
    norm_num [prm34]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    linarith
  · norm_num [prm34]
  · norm_num [prm34]
  · norm_num [prm34]
    linarith

private lemma gam_large_lower (d n : ℕ) (q : Params) (hd : 3 ≤ d ∧ d ≤ 4)
    (hn : 1000000000 ≤ n) (hx0 : 0 ≤ q.x) (hx12 : q.x ≤ 12)
    (hηlo : 3 / 10000 ≤ q.eta) (hηhi : q.eta ≤ 1 / 1000)
    (hβ : q.beta = 1 / 1000) (hβH : 1 / 20 ≤ q.betaH) (hth : q.th = 999 / 1000) :
    (if d = 3 then 1 / 50 else 1 / 1000) ≤ gam41 n d 3 q := by
  have hnR : (1000000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hη0 : 0 < q.eta := by linarith
  have hi : q.eta⁻¹ ≤ 10000 / 3 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 10000) hηlo
    norm_num at hh
    exact hh
  have hθ : (1 + 1 / q.eta) * thetaT n d 3 ≤ 1 / 100 := by
    rw [theta_three, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    rcases hd with ⟨hdlo, hdhi⟩
    interval_cases d <;> norm_num <;> nlinarith
  have hden : 99 / 100 ≤ 1 - (1 + 1 / q.eta) * thetaT n d 3 := by linarith
  have hden0 : 0 < 1 - (1 + 1 / q.eta) * thetaT n d 3 := by linarith
  have hm0 := mu_pos (d := d) (by omega : 2 ≤ n) (by norm_num : 1 ≤ 3)
    (by omega : 3 * d ≤ n)
  have hmu : 1 / 50000 ≤ muN n d 3 := by
    have hm := mu_lower n d 3 (by omega) (by rcases hd with ⟨_, _⟩; nlinarith)
    rcases hd with ⟨hdlo, hdhi⟩
    interval_cases d <;> norm_num at hm ⊢ <;> linarith
  have hρ0 : 0 < rhoBar n 3 := by rw [rhobar_three]; positivity
  have hK0 : 0 < Kc n d 3 q.eta := div_pos (mul_pos hρ0 (by linarith)) hden0
  have hρ : rhoBar n 3 ≤ 1002 / 1000 := by
    rw [rhobar_three]
    have hh : 2 / (n : ℝ) ≤ 2 / 1000 := (div_le_iff₀ hn0).mpr (by linarith)
    linarith
  have hK : Kc n d 3 q.eta ≤ 2 := by
    unfold Kc
    apply (div_le_iff₀ hden0).mpr
    have hh := mul_le_mul hρ (show 1 + q.eta ≤ 1001 / 1000 by linarith)
      (show 0 ≤ 1 + q.eta by linarith) (by norm_num : (0 : ℝ) ≤ 1002 / 1000)
    linarith
  let qr : Params := {q with th := 1 / 25}
  have hfloor : Real.sqrt (hN n d 3 q.eta / q.betaH) < 1 / 5 := by
    have hh : Real.sqrt (hN n d 3 qr.eta / qr.betaH) < Real.sqrt qr.th := by
      apply floor_three_bound d n qr hd (by omega)
        (by rcases hd with ⟨_, _⟩; nlinarith) hη0 hθ (by dsimp [qr]; linarith) (by norm_num [qr])
      have hbN : (1000000000 : ℝ) * (1 / 20) ≤ (n : ℝ) * q.betaH :=
        mul_le_mul hnR hβH (by norm_num) (by positivity)
      dsimp [qr]
      rcases hd with ⟨hdlo, hdhi⟩
      interval_cases d <;> norm_num <;> nlinarith
    norm_num [qr] at hh
    exact hh
  have hs : (if d = 3 then 27 / 1000 else 3 / 1000) ≤
      Real.sqrt (muN n d 3 / Kc n d 3 q.eta) := by
    apply (Real.le_sqrt (by split_ifs <;> norm_num) (div_nonneg hm0.le hK0.le)).mpr
    apply (le_div_iff₀ hK0).mpr
    have hm := mu_lower n d 3 (by omega) (by rcases hd with ⟨_, _⟩; nlinarith)
    rcases hd with ⟨hdlo, hdhi⟩
    interval_cases d <;> norm_num at hm ⊢ <;> nlinarith
  have hsth : 99 / 100 ≤ Real.sqrt q.th := by
    rw [hth]
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have herr := radius_error_upper d n hd (by omega) q.x hx0 hx12
  have herr' : etaK n d 3 q.x * Real.sqrt (GamP n d 3 / q.beta) ≤ 1 / 1000 := by
    rw [hβ]
    have hh : 300000 / (n : ℝ) ≤ 1 / 1000 := (div_le_iff₀ hn0).mpr (by linarith)
    exact herr.trans hh
  have hdiff : 79 / 100 ≤ Real.sqrt q.th - Real.sqrt (hN n d 3 q.eta / q.betaH) := by linarith
  have hprod := mul_le_mul hs hdiff (by norm_num : (0 : ℝ) ≤ 79 / 100) (Real.sqrt_nonneg _)
  unfold gam41
  rcases hd with ⟨hdlo, hdhi⟩
  interval_cases d <;> norm_num at hprod ⊢ <;> linarith

private lemma choose_normalized_lower (n p : ℕ) (hn : 1 ≤ n) (hp : 2 * p ≤ n) :
    1 / ((2 : ℝ)^p * (p.factorial : ℝ)) ≤ (n.choose p : ℝ) / (n : ℝ)^p := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : (n.choose p : ℝ) / (n : ℝ)^p =
      (∏ i ∈ Finset.range p, (((n : ℝ) - i) / n)) / (p.factorial : ℝ) := by
    rw [choose_prod n p (by omega), Finset.prod_div_distrib]
    simp
    ring
  rw [he]
  have hh : (1 / 2 : ℝ)^p ≤ ∏ i ∈ Finset.range p, (((n : ℝ) - i) / n) := by
    calc
      _ = ∏ _i ∈ Finset.range p, (1 / 2 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun _ _ => by norm_num)
        intro i hi
        apply (le_div_iff₀ hn0).mpr
        have hiR : (i : ℝ) ≤ p := by exact_mod_cast (Finset.mem_range.mp hi).le
        have hpR : 2 * (p : ℝ) ≤ n := by exact_mod_cast hp
        linarith
  have hf : 0 ≤ (p.factorial : ℝ) := by positivity
  have hb := div_le_div_of_nonneg_right hh hf
  simpa [div_pow, div_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb

private lemma qn_three_upper (d n : ℕ) (hd : 3 ≤ d ∧ d ≤ 4) (hn : 24 ≤ n) :
    qN n d 3 ≤ (1000000000000000000 : ℝ) / (n : ℝ)^d := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpn : 2 * (3 * d) ≤ n := by omega
  have hden := choose_normalized_lower n (3 * d) (by omega) hpn
  have hden0 : 0 < (n.choose (3 * d) : ℝ) / (n : ℝ)^(3 * d) := lt_of_lt_of_le (by positivity) hden
  have ht (i : ℕ) (hi : i ∈ Finset.Icc d (3 * d)) :
      ((3 * d).choose i : ℝ) * ((n - 3 * d).choose (3 * d - i) : ℝ) /
        (n.choose (3 * d) : ℝ) ≤
          (2 : ℝ)^(3 * d) * 2^(3 * d) * ((3 * d).factorial : ℝ) / (n : ℝ)^d := by
    have hid := (Finset.mem_Icc.mp hi).1
    have hip := (Finset.mem_Icc.mp hi).2
    have hc : ((3 * d).choose i : ℝ) ≤ (2 : ℝ)^(3 * d) := by exact_mod_cast Nat.choose_le_two_pow (3 * d) i
    have hnum : ((n - 3 * d).choose (3 * d - i) : ℝ) / (n : ℝ)^(3 * d - i) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)^(3 * d - i))).mpr
      have hh : (n - 3 * d).choose (3 * d - i) ≤ n^(3 * d - i) :=
        (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
      exact_mod_cast hh
    have hinv : ((n : ℝ)^i)⁻¹ ≤ 1 / (n : ℝ)^d := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (by positivity : (0 : ℝ) < (n : ℝ)^d) (pow_le_pow_right₀ hn1 hid)
    have he : ((3 * d).choose i : ℝ) * ((n - 3 * d).choose (3 * d - i) : ℝ) /
        (n.choose (3 * d) : ℝ) =
        (((3 * d).choose i : ℝ) * (((n - 3 * d).choose (3 * d - i) : ℝ) /
          (n : ℝ)^(3 * d - i)) * ((n : ℝ)^i)⁻¹) /
          ((n.choose (3 * d) : ℝ) / (n : ℝ)^(3 * d)) := by
      have hp : (n : ℝ)^(3 * d) = (n : ℝ)^(3 * d - i) * (n : ℝ)^i := by
        rw [← pow_add, Nat.sub_add_cancel hip]
      rw [hp]
      field_simp [ne_of_gt hn0]
    rw [he]
    have hmul := mul_le_mul hc hnum (by positivity) (by positivity : (0 : ℝ) ≤ 2^(3 * d))
    have hmul' := mul_le_mul hmul hinv (by positivity) (by positivity : (0 : ℝ) ≤ 2^(3 * d) * 1)
    calc
      _ ≤ ((2 : ℝ)^(3 * d) * 1 * (1 / (n : ℝ)^d)) /
          ((n.choose (3 * d) : ℝ) / (n : ℝ)^(3 * d)) :=
        div_le_div_of_nonneg_right hmul' hden0.le
      _ ≤ ((2 : ℝ)^(3 * d) * 1 * (1 / (n : ℝ)^d)) /
          (1 / ((2 : ℝ)^(3 * d) * ((3 * d).factorial : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by simp only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  unfold qN
  have hh := Finset.sum_le_sum ht
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hh
  apply hh.trans
  rcases hd with ⟨hdlo, hdhi⟩
  interval_cases d <;> norm_num <;>
    rw [← mul_div_assoc] <;>
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

private lemma nat_poly_lt_exp (C E : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * n^E < 2^(n / 4) := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt E (by norm_num : (1 : ℝ) < 2)).const_mul
    ((C * 8^E : ℕ) : ℝ)
  have hh : ∀ᶠ t : ℕ in Filter.atTop, ((C * 8^E : ℕ) : ℝ) * ((t : ℝ)^E / 2^t) < 1 :=
    ht.eventually_lt_const (by simp)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hh
  refine ⟨4 * max T 1, ?_⟩
  intro n hn
  have htn : max T 1 ≤ n / 4 := by omega
  have ht1 : 1 ≤ n / 4 := le_trans (le_max_right _ _) htn
  have hbound := hT (n / 4) (le_trans (le_max_left _ _) htn)
  have hlt : (C * 8^E) * (n / 4)^E < 2^(n / 4) := by
    have hr := (div_lt_iff₀ (show (0 : ℝ) < 2^(n / 4) by positivity)).mp
      (show (((C * 8^E : ℕ) : ℝ) * (n / 4 : ℕ)^E) / 2^(n / 4) < 1 by
        simpa only [mul_div_assoc] using hbound)
    simp only [one_mul] at hr
    exact_mod_cast hr
  have hn8 : n ≤ 8 * (n / 4) := by omega
  apply lt_of_le_of_lt _ hlt
  calc C * n^E ≤ C * (8 * (n / 4))^E := by gcongr
    _ = (C * 8^E) * (n / 4)^E := by rw [mul_pow]; ring

private lemma bq_eventually (d k : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, 4 * bQ n d k ≤ n := by
  obtain ⟨C, E, hC, hH⟩ := hgt_growth d k
  obtain ⟨N, hN⟩ := nat_poly_lt_exp C E
  filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_ge_atTop 4] with n hn hn4
  have hlt : Hgt n d k < 2^(n / 4) := lt_of_le_of_lt (hH n (by omega)) (hN n hn)
  have hl := Nat.log_lt_of_lt_pow' (show n / 4 ≠ 0 by omega) hlt
  unfold bQ
  omega

private lemma gam_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (q : Params)
    (hx : 0 ≤ q.x) (hη : 0 < q.eta) : Filter.Tendsto (fun n => gam41 n d k q)
      Filter.atTop (nhds (Real.sqrt ((1 / (k * (d.factorial : ℝ)^k)) / (1 + q.eta)) * Real.sqrt q.th)) := by
  have hη1 : (1 : ℝ) + q.eta ≠ 0 := by linarith
  have hf := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((mu_tendsto d k).div (kc_tendsto d k hk q.eta) hη1)
  have hH := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((hn_tendsto d k hk q.eta).div_const q.betaH)
  have herr := (etak_gamp_tendsto d k hk hkd q.x hx).div_const (Real.sqrt q.beta)
  have he : Filter.Tendsto (fun n => etaK n d k q.x * Real.sqrt (GamP n d k / q.beta))
      Filter.atTop (nhds 0) := by
    convert herr using 1
    · funext n
      rw [Real.sqrt_div (gamp_nonneg n d k)]
      ring
    · simp
  have ht := (hf.mul (hH.const_sub (Real.sqrt q.th))).sub he
  convert ht using 1
  · funext n; rfl
  · simp

private lemma phi_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (q : Params)
    (hx : 0 ≤ q.x) (hη : 0 < q.eta) (hth : q.th ≠ 1)
    (hγ : Real.sqrt ((1 / (k * (d.factorial : ℝ)^k)) / (1 + q.eta)) * Real.sqrt q.th ≠ 0) :
    Filter.Tendsto (fun n => PhiLF n d k q) Filter.atTop
      (nhds (2 * Real.exp (-q.x) + q.beta + q.betaH)) := by
  have hd : 1 ≤ d := le_trans hk hkd
  have herror := ((tau_tendsto d k hk hkd).const_mul (Lk k : ℝ)).div
    ((gam_tendsto d k hk hkd q hx hη).pow 2) (pow_ne_zero 2 hγ)
  have hb := ((pin_tendsto d k hd q.th hth).const_add (2 * Real.exp (-q.x))).add_const q.beta
  have ht := (hb.add_const q.betaH).add herror
  convert ht using 1
  · funext n; rfl
  · simp

private lemma exp_ten_bound : Real.exp (-10) ≤ 1 / 1000 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10) 10
  have hb : (1000 : ℝ) ≤ Real.exp 10 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht
    linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000) hb

private lemma phi_large_upper (d n : ℕ) (q : Params) (hd : 3 ≤ d ∧ d ≤ 4)
    (hn : (if d = 3 then 200000000000 else 1000000000) ≤ n) (hxlo : 10 ≤ q.x) (hxhi : q.x ≤ 12)
    (hηlo : 3 / 10000 ≤ q.eta) (hηhi : q.eta ≤ 1 / 1000)
    (hβ : q.beta = 1 / 1000) (hβHlo : 1 / 20 ≤ q.betaH)
    (hβHhi : q.betaH ≤ 1 / 4) (hth : q.th = 999 / 1000) :
    PhiLF n d 3 q ≤ 1 / 2 := by
  have hnB : 1000000000 ≤ n := by split_ifs at hn <;> omega
  have hnR : (1000000000 : ℝ) ≤ n := by exact_mod_cast hnB
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hγ := gam_large_lower d n q hd hnB (by linarith) hxhi hηlo hηhi hβ hβHlo hth
  have hγ0 : 0 < gam41 n d 3 q := by split_ifs at hγ <;> linarith
  have hτ : tauF n d 3 ≤ if d = 3 then 1 / 25000 else 1 / 10000000 := by
    have hp := pn_lower n d
    have ht := tau_three_upper d n hd (by omega)
    have ht' : tauF n d 3 ≤ 800000 * (n : ℝ)^3 / ((n : ℝ)^(d + 1) / (d.factorial : ℝ)) := by
      calc
        _ ≤ 800000 * (n : ℝ)^3 / Pn n d := ht
        _ ≤ 800000 * (n : ℝ)^3 / ((n : ℝ)^(d + 1) / (d.factorial : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    rcases hd with ⟨hdlo, hdhi⟩
    interval_cases d
    · norm_num at hn ⊢
      have hn3 : (200000000000 : ℝ) ≤ n := by exact_mod_cast hn
      have he : 800000 * (n : ℝ)^3 / ((n : ℝ)^4 / ((3 : ℕ).factorial : ℝ)) = 4800000 / (n : ℝ) := by norm_num; field_simp [ne_of_gt hn0]; ring
      rw [he] at ht'
      exact ht'.trans ((div_le_iff₀ hn0).mpr (by linarith))
    · norm_num at hn ⊢
      have he : 800000 * (n : ℝ)^3 / ((n : ℝ)^5 / ((4 : ℕ).factorial : ℝ)) = 19200000 / (n : ℝ)^2 := by norm_num; field_simp [ne_of_gt hn0]; ring
      rw [he] at ht'
      exact ht'.trans ((div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2)).mpr (by nlinarith [sq_nonneg ((n : ℝ) - 1000000000)]))
  have hq0 : 0 ≤ qN n d 3 := by unfold qN; positivity
  have hq : qN n d 3 ≤ 1 / 1000000000000 := by
    have hh := qn_three_upper d n hd (by omega)
    have hp' : (1000000000000000000000000000000 : ℝ) ≤ (n : ℝ)^d := by
      rcases hd with ⟨hdlo, hdhi⟩
      interval_cases d
      · norm_num at hn
        have hn3 : (10000000000 : ℝ) ≤ n := by exact_mod_cast (show 10000000000 ≤ n by omega)
        have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000000000) hn3 3
        norm_num at hp
        exact hp
      · have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1000000000) hnR 4
        norm_num at hp
        linarith
    have hb : (1000000000000000000 : ℝ) / (n : ℝ)^d ≤ 1 / 1000000000000 :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^d)).mpr (by linarith)
    exact hh.trans hb
  have hπ : piN n d 3 q.th ≤ 1 / 1000 := by
    unfold piN
    rw [hth]
    norm_num
    apply (div_le_iff₀ (by nlinarith : 0 < 728 * qN n d 3 + 1 / 1000000)).mpr
    nlinarith
  have herror : Lk 3 * tauF n d 3 / gam41 n d 3 q^2 ≤ 1 / 5 := by
    apply (div_le_iff₀ (sq_pos_of_pos hγ0)).mpr
    norm_num [Lk]
    by_cases hd3 : d = 3
    · simp only [if_pos hd3] at hτ hγ
      nlinarith [sq_nonneg (gam41 n d 3 q - 1 / 50)]
    · simp only [if_neg hd3] at hτ hγ
      nlinarith [sq_nonneg (gam41 n d 3 q - 1 / 1000)]
  have he : Real.exp (-q.x) ≤ 1 / 1000 :=
    (Real.exp_le_exp.mpr (by linarith : -q.x ≤ -10)).trans exp_ten_bound
  unfold PhiLF
  rw [hβ]
  linarith

/-- **Certificate `(3,3)`**: every clause holds at every `n ≥ 200 000 000 000`. -/
theorem cert33 (hn : 200000000000 ≤ n) : BudgetOK n 3 3 prm33 := by
  have hn2 : 2 ≤ n := by omega
  have hb := budget_condition_three (show 100 ≤ n by omega)
  have hτ := tau_pos hn2 (by norm_num : 1 ≤ 3) hb
  have hθ := theta33_lt (show 35800000 ≤ n by omega)
  have hμ := mu_pos (d := 3) hn2 (by norm_num : 1 ≤ 3) (by omega : 3 * 3 ≤ n)
  have hρ : 0 < rhoBar n 3 := by rw [rhobar_three]; positivity
  have hη : 0 < prm33.eta := by norm_num [prm33]
  have hden : 0 < 1 - (1 + 1 / prm33.eta) * thetaT n 3 3 := sub_pos.mpr hθ
  have hK : 0 < Kc n 3 3 prm33.eta := div_pos (mul_pos hρ (by linarith)) hden
  have hH : 0 < hN n 3 3 prm33.eta := by
    unfold hN
    exact div_pos (mul_pos (xi_three_pos n 3) (by linarith))
      (mul_pos (mul_pos (by positivity : (0 : ℝ) < n) hμ) hden)
  have hr : etaR n 3 prm33.x < 1 := etar_lt_one n 3 (by omega) _ (by norm_num [prm33])
  have hbits : 4 * bQ n 3 3 ≤ n := bq_three_bound 3 n (by norm_num) (by omega)
  have hfloor := floor33_lt (show 35800000 ≤ n by omega)
  have hγ := gam_large_lower 3 n prm33 (by norm_num) (by omega)
    (by norm_num [prm33]) (by norm_num [prm33]) (by norm_num [prm33])
    (by norm_num [prm33]) (by norm_num [prm33]) (by norm_num [prm33]) (by norm_num [prm33])
  have hΦ := phi_large_upper 3 n prm33 (by norm_num) (by simpa using hn)
    (by norm_num [prm33]) (by norm_num [prm33]) (by norm_num [prm33])
    (by norm_num [prm33]) (by norm_num [prm33]) (by norm_num [prm33])
    (by norm_num [prm33]) (by norm_num [prm33])
  norm_num at hγ
  have htail : 0 < gam41 n 3 3 prm33 ∧ PhiLF n 3 3 prm33 ≤ 1 / 2 := by
    exact ⟨by linarith, hΦ⟩
  refine ⟨hn2, by norm_num, by omega, hτ, ?_, ?_, ?_, ?_, ?_, hη,
    hθ, hr, hμ, hK, hH, hfloor, htail.1, hb, hbits, htail.2⟩ <;> norm_num [prm33]

/-- **Certificate `(3,4)`**: every clause holds at every `n ≥ 1 000 000 000`. -/
theorem cert34 (hn : 1000000000 ≤ n) : BudgetOK n 4 3 prm34 := by
  have hn2 : 2 ≤ n := by omega
  have hb := budget_condition_four (show 100 ≤ n by omega)
  have hτ := tau_pos hn2 (by norm_num : 1 ≤ 3) hb
  have hθ := theta34_lt (show 7420000 ≤ n by omega)
  have hμ := mu_pos (d := 4) hn2 (by norm_num : 1 ≤ 3) (by omega : 3 * 4 ≤ n)
  have hρ : 0 < rhoBar n 3 := by rw [rhobar_three]; positivity
  have hη : 0 < prm34.eta := by norm_num [prm34]
  have hden : 0 < 1 - (1 + 1 / prm34.eta) * thetaT n 4 3 := sub_pos.mpr hθ
  have hK : 0 < Kc n 4 3 prm34.eta := div_pos (mul_pos hρ (by linarith)) hden
  have hH : 0 < hN n 4 3 prm34.eta := by
    unfold hN
    exact div_pos (mul_pos (xi_three_pos n 4) (by linarith))
      (mul_pos (mul_pos (by positivity : (0 : ℝ) < n) hμ) hden)
  have hr : etaR n 4 prm34.x < 1 := etar_lt_one n 4 (by omega) _ (by norm_num [prm34])
  have hbits : 4 * bQ n 4 3 ≤ n := bq_three_bound 4 n (by norm_num) (by omega)
  have hfloor := floor34_lt (show 7420000 ≤ n by omega)
  have hγ := gam_large_lower 4 n prm34 (by norm_num) (by omega)
    (by norm_num [prm34]) (by norm_num [prm34]) (by norm_num [prm34])
    (by norm_num [prm34]) (by norm_num [prm34]) (by norm_num [prm34]) (by norm_num [prm34])
  have hΦ := phi_large_upper 4 n prm34 (by norm_num) (by simpa using hn)
    (by norm_num [prm34]) (by norm_num [prm34]) (by norm_num [prm34])
    (by norm_num [prm34]) (by norm_num [prm34]) (by norm_num [prm34])
    (by norm_num [prm34]) (by norm_num [prm34])
  norm_num at hγ
  have htail : 0 < gam41 n 4 3 prm34 ∧ PhiLF n 4 3 prm34 ≤ 1 / 2 := by
    exact ⟨by linarith, hΦ⟩
  refine ⟨hn2, by norm_num, by omega, hτ, ?_, ?_, ?_, ?_, ?_, hη,
    hθ, hr, hμ, hK, hH, hfloor, htail.1, hb, hbits, htail.2⟩ <;> norm_num [prm34]

/-- **Existence of `n₀`** for every `d ≥ k ≥ 2` (the limit argument). -/
theorem exists_n0 (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) : ∃ q : Params, ∃ n0 : ℕ, ∀ n, n0 ≤ n → BudgetOK n d k q := by
  let q : Params := ⟨10, 1 / 100, 1 / 100, 99 / 100, 1 / 100⟩
  have hk1 : 1 ≤ k := by omega
  have hd1 : 1 ≤ d := by omega
  have hx : 0 ≤ q.x := by norm_num [q]
  have hη : 0 < q.eta := by norm_num [q]
  have hβH : 0 < q.betaH := by norm_num [q]
  have hth : 0 < q.th := by norm_num [q]
  have hthne : q.th ≠ 1 := by norm_num [q]
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hγ : 0 < Real.sqrt ((1 / (k * (d.factorial : ℝ)^k)) / (1 + q.eta)) * Real.sqrt q.th := by
    apply mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hth)
  have hph : 2 * Real.exp (-q.x) + q.beta + q.betaH < 1 / 2 := by
    dsimp [q]
    linarith [exp_ten_bound]
  have hbudget : ∀ᶠ n : ℕ in Filter.atTop, 455 / 1000 * Bfix n k < 91 / 100 * Pn n d := by
    have hh := (bfix_ratio_tendsto d k hk1 hkd).eventually_lt_const (by norm_num : (0 : ℝ) < 2)
    filter_upwards [hh, Filter.eventually_ge_atTop 2] with n hn hn2
    have hP : 0 < Pn n d := BstLean.Part36.DD_pos (by omega)
    have hb := (div_lt_iff₀ hP).mp hn
    linarith
  have hθ : ∀ᶠ n : ℕ in Filter.atTop, (1 + 1 / q.eta) * thetaT n d k < 1 := by
    exact ((theta_tendsto d k).const_mul (1 + 1 / q.eta)).eventually_lt_const (by simp)
  have hr : ∀ᶠ n : ℕ in Filter.atTop, etaR n d q.x < 1 :=
    (etar_tendsto d q.x).eventually_lt_const (by norm_num)
  have hρ : ∀ᶠ n : ℕ in Filter.atTop, 0 < rhoBar n k :=
    (rhobar_tendsto k hk1).eventually_const_lt (by norm_num)
  have hH := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((hn_tendsto d k hk1 q.eta).div_const q.betaH)
  have hfloor : ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt (hN n d k q.eta / q.betaH) < Real.sqrt q.th := by
    exact hH.eventually_lt_const (by simpa using Real.sqrt_pos.mpr hth)
  have hγn : ∀ᶠ n : ℕ in Filter.atTop, 0 < gam41 n d k q :=
    (gam_tendsto d k hk1 hkd q hx hη).eventually_const_lt hγ
  have hΦ : ∀ᶠ n : ℕ in Filter.atTop, PhiLF n d k q ≤ 1 / 2 :=
    (phi_tendsto d k hk1 hkd q hx hη hthne (ne_of_gt hγ)).eventually_le_const hph
  have hOK : ∀ᶠ n : ℕ in Filter.atTop, BudgetOK n d k q := by
    filter_upwards [Filter.eventually_ge_atTop (max 2 (k * d)), hbudget, hθ, hr, hρ,
      hfloor, hγn, hΦ, bq_eventually d k] with n hn hb hθn hrn hρn hfn hγpos hΦn hbn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hkdn : k * d ≤ n := le_trans (le_max_right _ _) hn
    have hμ := mu_pos hn2 hk1 hkdn
    have hden : 0 < 1 - (1 + 1 / q.eta) * thetaT n d k := sub_pos.mpr hθn
    have hK : 0 < Kc n d k q.eta := div_pos (mul_pos hρn (by linarith)) hden
    have hhn : 0 < hN n d k q.eta := by
      have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      exact div_pos (mul_pos (xi_pos n d k hk) (by linarith)) (mul_pos (mul_pos hnp hμ) hden)
    refine ⟨hn2, hd1, hkdn, tau_pos hn2 hk1 hb, ?_, ?_, ?_, ?_, ?_, hη,
      hθn, hrn, hμ, hK, hhn, hfn, hγpos, hb, hbn, hΦn⟩ <;> norm_num [q]
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hOK
  exact ⟨q, n0, hn0⟩

end BstLean.Part41

