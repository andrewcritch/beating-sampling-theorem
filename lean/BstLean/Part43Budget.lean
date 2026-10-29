import BstLean.Part43Defs
import BstLean.Part36Index

/-!
# Part 43, wave 1: allocation, budget and the existence of n₀

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`.
Specification: `delegations/answers/p43-spec-opus.md`.

The allocation follows from the ceiling bound. The budget reserves the share `nu43`.
For each fixed `d ≥ k ≥ 2`, the growth estimates give `tau43 → 0`. Chebyshev
positivity gives `tsb k prm43.psb > 0`; the remaining limits give an eventual
positive `gam43` and `Phi43 < 1/2`.
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)

open BstLean.Part41

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

theorem alloc43_le (hn : 2 ≤ n) (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hτ : 0 < tau43 n d k) :
    ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * (Ocnt43 n d k ε jl.1 jl.2 : ℝ) ≤
      AU n d k / (tau43 n d k * epsS ε) + ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) := by
  classical
  have he : 0 < epsS ε := by unfold epsS; exact lt_min (sq_pos_of_pos hε) (by norm_num)
  rw [AU, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun jl hjl => ?_
  have hx : 0 ≤ Upp jl.1 d ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
      (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 * tau43 n d k * epsS ε) := by positivity
  have ho : (Ocnt43 n d k ε jl.1 jl.2 : ℝ) ≤
      Upp jl.1 d ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
      (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 * tau43 n d k * epsS ε) + 1 := by
    exact (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.ceil_lt_add_one hx).le
  calc
    _ ≤ cS n (jl.1 - 2 * jl.2) *
        (Upp jl.1 d ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
        (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 * tau43 n d k * epsS ε) + 1) :=
      mul_le_mul_of_nonneg_left ho (cs_nonneg hn _)
    _ = _ := by simp only [div_div, mul_div_assoc]; ring

theorem budget43_le (hn : 2 ≤ n) (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hP : 455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d) :
    AU n d k / (tau43 n d k * epsS ε) + Bfix n k ≤ (1 - nu43) * baseline n d ε := by
  have he : 0 < epsS ε := by unfold epsS; exact lt_min (sq_pos_of_pos hε) (by norm_num)
  have hden : 0 < (1 - nu43) * (91 / 100) * Pn n d - 455 / 1000 * Bfix n k := by linarith
  have hA : AU n d k / tau43 n d k ≤
      (1 - nu43) * (91 / 100) * Pn n d - 455 / 1000 * Bfix n k := by
    by_cases ha : AU n d k = 0
    · simpa [ha] using hden.le
    · unfold tau43
      apply le_of_eq
      field_simp
  have hb : AU n d k / (tau43 n d k * epsS ε) ≤
      ((1 - nu43) * (91 / 100) * Pn n d - 455 / 1000 * Bfix n k) / epsS ε := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hA he.le
  have hnu : 0 ≤ 1 - nu43 := by norm_num [nu43]
  unfold baseline
  by_cases hsmall : ε ^ 2 ≤ 455 / 1000
  · have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    rw [epsS, min_eq_left hsmall] at hb ⊢
    apply le_trans (show AU n d k / (tau43 n d k * ε ^ 2) + Bfix n k ≤
      ((1 - nu43) * (91 / 100) * Pn n d - 455 / 1000 * Bfix n k) / ε ^ 2 + Bfix n k by linarith)
      (le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_right _ _) hnu))
    rw [← mul_div_assoc (1 - nu43) (91 / 100 * Pn n d) (ε ^ 2)]
    apply (le_div_iff₀ he2).mpr
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt he2)]
    nlinarith [mul_nonneg (bfix_nonneg n k) (sub_nonneg.mpr hsmall)]
  · rw [epsS, min_eq_right (le_of_not_ge hsmall)] at hb ⊢
    apply le_trans (show AU n d k / (tau43 n d k * (455 / 1000)) + Bfix n k ≤
      ((1 - nu43) * (91 / 100) * Pn n d - 455 / 1000 * Bfix n k) / (455 / 1000) + Bfix n k by linarith)
      (le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_left _ _) hnu))
    linarith

private lemma cs_pos (hn : 2 ≤ n) (s : ℕ) : 0 < cS n s := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 ≤ ∑ i ∈ Finset.range (s / 2 + 1),
      ((s.choose (2 * i) : ℕ) : ℝ) * (Corb n (s - 2 * i) + 2 * n + 8) := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (by positivity) (by linarith [corb_nonneg hn (s - 2 * i)])
  unfold cS
  linarith

private lemma UppTerm_nonneg (j d m : ℕ) : 0 ≤ UppTerm j d m := by
  unfold UppTerm
  generalize (((Finset.univ : Finset (Fin m → Fin (m + 1))).filter
    fun β => ∑ a, (β a : ℕ) = m).toList.map
    fun β => (Nj j d m (fun a => (β a : ℕ)) : ℝ) *
      (∏ a, ((β a : ℕ).factorial : ℝ)) / (m.factorial : ℝ)) = L
  induction L with
  | nil => simp
  | cons a L ih => exact le_max_of_le_right ih

private lemma upp_one (j d : ℕ) : 1 ≤ Upp j d := by
  classical
  have hz : UppTerm j d 0 = 1 := by
    simp [UppTerm, Nj]
  unfold Upp
  rw [← hz]
  exact Finset.single_le_sum (fun m _ => UppTerm_nonneg j d m) (by simp)

private lemma au_pos (hn : 2 ≤ n) (hk : 1 ≤ k) : 0 < AU n d k := by
  classical
  unfold AU
  apply Finset.sum_pos'
  · intro jl _
    exact div_nonneg (mul_nonneg (mul_nonneg (cs_nonneg hn _) (sq_nonneg _))
      (by positivity)) (by positivity)
  · refine ⟨(1, 0), ?_, ?_⟩
    · simp [levels, hk]
    · have hs : 0 < Upp 1 d := by
        have := upp_one 1 d
        linarith
      have hc := cs_pos hn 1
      have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      simp only [mul_zero, Nat.sub_zero, pow_zero]
      positivity

private lemma tau_pos (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hP : 455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d) : 0 < tau43 n d k := by
  exact div_pos (au_pos hn hk) (sub_pos.mpr hP)

private lemma choose_prod (a b : ℕ) (hb : b ≤ a) :
    (a.choose b : ℝ) = (∏ i ∈ Finset.range b, ((a : ℝ) - i)) / (b.factorial : ℝ) := by
  have hp : (∏ i ∈ Finset.range b, ((a : ℝ) - i)) = (a.descFactorial b : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (by have := Finset.mem_range.mp hi; omega)]
  rw [hp, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

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

private lemma au_growth (d k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    AU n d k ≤ C * (n : ℝ)^k := by
  classical
  let W (jl : ℕ × ℕ) : ℝ :=
    (1 + 9 * ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1),
      ((jl.1 - 2 * jl.2).choose (2 * i) : ℝ)) * Upp jl.1 d ^ 2
  have hW (jl : ℕ × ℕ) : 0 ≤ W jl := by dsimp [W]; positivity
  refine ⟨1 + ∑ jl ∈ levels k, W jl, ?_, ?_⟩
  · have := Finset.sum_nonneg (s := levels k) (fun jl _ => hW jl)
    linarith
  · intro n hn
    have hterm (jl : ℕ × ℕ) (hjl : jl ∈ levels k) :
        cS n (jl.1 - 2 * jl.2) * Upp jl.1 d ^ 2 * (n : ℝ)^(k - (jl.1 - 2 * jl.2)) /
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
      have hsq : Upp jl.1 d ^ 2 ≤ Upp jl.1 d ^ 2 := le_rfl
      have hc := cs_le hn hs
      have hp : (n : ℝ)^k = (n : ℝ)^(jl.1 - 2 * jl.2) *
          (n : ℝ)^(k - (jl.1 - 2 * jl.2)) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ ≤ cS n (jl.1 - 2 * jl.2) * Upp jl.1 d ^ 2 *
            (n : ℝ)^(k - (jl.1 - 2 * jl.2)) :=
          div_le_self (mul_nonneg (mul_nonneg (cs_nonneg hn _) (sq_nonneg _))
            (by positivity)) hd
        _ ≤ ((1 + 9 * ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1),
            ((jl.1 - 2 * jl.2).choose (2 * i) : ℝ)) * (n : ℝ)^(jl.1 - 2 * jl.2)) *
            Upp jl.1 d ^ 2 * (n : ℝ)^(k - (jl.1 - 2 * jl.2)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hc hsq (sq_nonneg _) (by positivity)) (by positivity)
        _ = W jl * (n : ℝ)^k := by dsimp [W]; rw [hp]; ring
    calc
      AU n d k ≤ ∑ jl ∈ levels k, W jl * (n : ℝ)^k := Finset.sum_le_sum hterm
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

private lemma au_ratio_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    Filter.Tendsto (fun n => AU n d k / Pn n d) Filter.atTop (nhds 0) :=
  growth_ratio_tendsto d k hkd (fun n => AU n d k) (fun _ hn => (au_pos hn hk).le)
    (au_growth d k)

private lemma tau_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    Filter.Tendsto (fun n => tau43 n d k) Filter.atTop (nhds 0) := by
  have hh := (au_ratio_tendsto d k hk hkd).div
    (tendsto_const_nhds.sub ((bfix_ratio_tendsto d k hk hkd).const_mul (455 / 1000)))
    (by norm_num [nu43] : ((1 - nu43) * (91 / 100) : ℝ) - (455 / 1000) * 0 ≠ 0)
  have he : (fun n => tau43 n d k) =ᶠ[Filter.atTop]
      (fun n => (AU n d k / Pn n d) / ((1 - nu43) * (91 / 100) - 455 / 1000 * (Bfix n k / Pn n d))) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hP : Pn n d ≠ 0 := ne_of_gt (BstLean.Part36.DD_pos (by omega))
    unfold tau43
    field_simp
  have ht : Filter.Tendsto (fun n => (AU n d k / Pn n d) /
      ((1 - nu43) * (91 / 100) - 455 / 1000 * (Bfix n k / Pn n d))) Filter.atTop (nhds 0) := by
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

private lemma kc_tendsto (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) :
    Filter.Tendsto (fun n => Kc n d k η) Filter.atTop (nhds (1 + η)) := by
  have hh := ((rhobar_tendsto k hk).mul_const (1 + η)).div
    (tendsto_const_nhds.sub ((theta_tendsto d k).const_mul (1 + 1 / η)))
    (by norm_num : (1 : ℝ) - (1 + 1 / η) * 0 ≠ 0)
  convert hh using 1
  · funext n; rfl
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



private lemma cheb_eval_ge_one (h : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ (Polynomial.Chebyshev.T ℝ (h : ℤ)).eval x := by
  have H (a : ℕ) : 1 ≤ (Polynomial.Chebyshev.T ℝ (a : ℤ)).eval x ∧
      (Polynomial.Chebyshev.T ℝ (a : ℤ)).eval x ≤
        (Polynomial.Chebyshev.T ℝ ((a : ℤ) + 1)).eval x := by
    induction a with
    | zero => simpa using (show (1 : ℝ) ≤ 1 ∧ 1 ≤ x from ⟨le_rfl, hx⟩)
    | succ a ih =>
      have hr := congrArg (fun p : Polynomial ℝ => p.eval x)
        (Polynomial.Chebyshev.T_add_two ℝ (a : ℤ))
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X] at hr
      have hm := mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ (Polynomial.Chebyshev.T ℝ ((a : ℤ) + 1)).eval x by linarith [ih.1, ih.2])
      push_cast
      simp only [add_assoc, one_add_one_eq_two]
      constructor <;> nlinarith [ih.1, ih.2]
  exact (H h).1

private lemma cheb_deriv_nonneg (h m : ℕ) :
    0 ≤ (Polynomial.derivative^[m] (Polynomial.Chebyshev.T ℝ (h : ℤ))).eval 1 := by
  have H := Polynomial.Chebyshev.T_iterate_derivative_mem_span_T (R := ℝ) h m
  refine Submodule.span_induction (fun p hp => ?_) ?_
    (fun p q _ _ hp hq => ?_) (fun r p _ hp => ?_) H
  · rcases hp with ⟨a, _, rfl⟩
    simp [Polynomial.Chebyshev.T_eval_one]
  · simp
  · simpa only [Polynomial.eval_add] using add_nonneg hp hq
  · simpa [Polynomial.eval_smul, nsmul_eq_mul] using
      mul_nonneg (show (0 : ℝ) ≤ r by positivity) hp

private lemma deriv_comp_affine (p : Polynomial ℝ) (m : ℕ) :
    Polynomial.derivative^[m] (p.comp (2 * Polynomial.X - 1)) =
      Polynomial.C ((2 : ℝ)^m) *
        (Polynomial.derivative^[m] p).comp (2 * Polynomial.X - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Polynomial.derivative_C_mul,
      Polynomial.derivative_comp, Function.iterate_succ_apply']
    simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_ofNat, Polynomial.derivative_X, Polynomial.derivative_one,
      zero_mul, zero_add, sub_zero]
    rw [pow_succ, Polynomial.C_mul]
    simp only [Polynomial.C_ofNat]
    ring

private lemma ch_pos (h : ℕ) : 0 < Ch h := by
  have H : 0 ≤ ∑ m ∈ Finset.Icc 1 h,
      (Polynomial.derivative^[m] (chebP h)).eval 1 := by
    refine Finset.sum_nonneg fun m _ => ?_
    rw [chebP, deriv_comp_affine]
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one, mul_one, show (2 : ℝ) - 1 = 1 by norm_num]
      using mul_nonneg (show (0 : ℝ) ≤ 2^m by positivity) (cheb_deriv_nonneg h m)
  unfold Ch
  positivity

private lemma exp_twelve_bound : Real.exp (-12) ≤ 1 / 1000 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 12) 10
  have hb : (1000 : ℝ) ≤ Real.exp 12 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht
    linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000) hb

private lemma psb_lt : (46 / 100 : ℝ) < 1 - Real.exp (-1) := by
  have ht := Real.add_one_le_exp (1 : ℝ)
  have hb : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ Real.exp 1)
  linarith

private lemma tsb_pos (k : ℕ) : 0 < tsb k prm43.psb := by
  have hl : -1 < Real.log (1 - prm43.psb) := by
    apply (Real.exp_lt_exp).mp
    rw [Real.exp_log (by norm_num [prm43] : 0 < 1 - prm43.psb)]
    have := psb_lt
    norm_num [prm43] at *
    linarith
  have hu : Real.log (1 - prm43.psb) < 0 :=
    Real.log_neg (by norm_num [prm43]) (by norm_num [prm43])
  have hlam : 1 < lamP prm43.psb := by
    unfold lamP
    apply (lt_div_iff_of_neg hu).mpr
    linarith
  have hp := cheb_eval_ge_one (2 * k) (2 * lamP prm43.psb - 1) (by linarith)
  have hev : 0 < (chebP (2 * k)).eval (lamP prm43.psb) := by
    simpa [chebP] using (show 0 < (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval
      (2 * lamP prm43.psb - 1) by linarith)
  exact one_div_pos.mpr (mul_pos (ch_pos _) hev)

private lemma gam_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    Filter.Tendsto (fun n => gam43 n d k prm43) Filter.atTop
      (nhds (Real.sqrt (tsb k prm43.psb / (1 + prm43.eta)))) := by
  have hf := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := tsb k prm43.psb)).div (kc_tendsto d k hk prm43.eta)
      (by norm_num [prm43] : (1 : ℝ) + prm43.eta ≠ 0))
  have herr := (etak_gamp_tendsto d k hk hkd prm43.x
    (by norm_num [prm43])).div_const (Real.sqrt prm43.beta)
  have he : Filter.Tendsto (fun n => etaK n d k prm43.x *
      Real.sqrt (GamP n d k / prm43.beta)) Filter.atTop (nhds 0) := by
    convert herr using 1
    · funext n
      rw [Real.sqrt_div (gamp_nonneg n d k)]
      ring
    · simp
  simpa only [gam43, Function.comp_apply, Pi.div_apply, sub_zero] using hf.sub he

private lemma phi_tendsto (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    Filter.Tendsto (fun n => Phi43 n d k prm43) Filter.atTop
      (nhds (prm43.psb + 2 * Real.exp (-prm43.x) + prm43.beta)) := by
  have hγ : Real.sqrt (tsb k prm43.psb / (1 + prm43.eta)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (div_pos (tsb_pos k) (by norm_num [prm43])))
  have herror := ((tau_tendsto d k hk hkd).const_mul (Lk k : ℝ)).div
    (((gam_tendsto d k hk hkd).pow 2).const_mul ((1 - xi43)^2))
    (mul_ne_zero (by norm_num [xi43]) (pow_ne_zero 2 hγ))
  simpa [Phi43] using herror.const_add
    (prm43.psb + 2 * Real.exp (-prm43.x) + prm43.beta)


/-- **Existence of `n₀`** for every `d ≥ k ≥ 2`, with the parameters `prm43`. -/
theorem exists_n0_43 (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) :
    ∃ n0 : ℕ, ∀ n, n0 ≤ n → BudgetOK43 n d k prm43 := by
  have hk1 : 1 ≤ k := by omega
  have hγ : 0 < Real.sqrt (tsb k prm43.psb / (1 + prm43.eta)) :=
    Real.sqrt_pos.mpr (div_pos (tsb_pos k) (by norm_num [prm43]))
  have hph : prm43.psb + 2 * Real.exp (-prm43.x) + prm43.beta < 1 / 2 := by
    norm_num [prm43]
    linarith [exp_twelve_bound]
  have hbudget : ∀ᶠ n : ℕ in Filter.atTop,
      455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d := by
    have hh := (bfix_ratio_tendsto d k hk1 hkd).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hh, Filter.eventually_ge_atTop 2] with n hn hn2
    have hP : 0 < Pn n d := BstLean.Part36.DD_pos (by omega)
    have hb := (div_lt_iff₀ hP).mp hn
    norm_num [nu43]
    nlinarith
  have hθ : ∀ᶠ n : ℕ in Filter.atTop,
      (1 + 1 / prm43.eta) * thetaT n d k < 1 :=
    ((theta_tendsto d k).const_mul (1 + 1 / prm43.eta)).eventually_lt_const (by simp)
  have hr : ∀ᶠ n : ℕ in Filter.atTop, etaR n d prm43.x < 1 :=
    (etar_tendsto d prm43.x).eventually_lt_const (by norm_num)
  have hK : ∀ᶠ n : ℕ in Filter.atTop, 0 < Kc n d k prm43.eta :=
    (kc_tendsto d k hk1 prm43.eta).eventually_const_lt (by norm_num [prm43])
  have hγn : ∀ᶠ n : ℕ in Filter.atTop, 0 < gam43 n d k prm43 :=
    (gam_tendsto d k hk1 hkd).eventually_const_lt hγ
  have hΦ : ∀ᶠ n : ℕ in Filter.atTop, Phi43 n d k prm43 ≤ 1 / 2 :=
    (phi_tendsto d k hk1 hkd).eventually_le_const hph
  have hOK : ∀ᶠ n : ℕ in Filter.atTop, BudgetOK43 n d k prm43 := by
    filter_upwards [Filter.eventually_ge_atTop 2, hbudget, hθ, hr, hK, hγn, hΦ]
      with n hn hb hθn hrn hKn hγpos hΦn
    refine ⟨hn, by omega, tau_pos hn hk1 hb, ?_, ?_, ?_, ?_, ?_,
      hθn, hrn, hKn, hγpos, hb, hΦn⟩
    · norm_num [prm43]
    · exact psb_lt
    · norm_num [prm43]
    · norm_num [prm43]
    · norm_num [prm43]
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hOK
  exact ⟨n0, hn0⟩



end BstLean.Part43
