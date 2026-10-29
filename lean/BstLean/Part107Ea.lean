import BstLean.Part107Defs5

/-!
# Part 107 (item 5), first file: the value of `λ_0` at degree 8 and the variance of a mean of
independent samples

* `lam8_107 : Lam8_107`.
* `iid_mean_sq`: for `k ≥ 1` independent samples of a probability measure `P` and a bounded
  measurable `f`, `E ((1/k) Σ_i f(s_i) − c)² = Var_P f / k + (E_P f − c)²`.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

theorem lam0_eight (N : ℕ) (hN : 1 ≤ N) :
    lam0 N 8 = (1 / (N : ℝ) + 3 / ((N : ℝ) * (N + 2)) + 15 / ((N : ℝ) * (N + 2) * (N + 4)) +
      105 / ((N : ℝ) * (N + 2) * (N + 4) * (N + 6))) / 7 := by
  rw [lam0_eq N 8 hN]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hI : Finset.Icc 2 8 = {2, 3, 4, 5, 6, 7, 8} := by decide
  rw [hI]
  simp only [sphMom, BstLean.Part29.gaussMom, BstLean.Part36.rhoD]
  norm_num [Finset.prod_range_succ, Nat.doubleFactorial, Nat.even_iff]
  ring

theorem lam8_107 : Lam8_107 := by
  intro n hn
  rw [lam0_eight (2 * n) (by omega)]
  have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) < n := by linarith
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  have e0 : 1 / (14 * (n : ℝ)) * (1 + 2 / (n : ℝ)) * 7 = 1 / (2 * (n : ℝ)) + 1 / (n : ℝ) ^ 2 := by
    field_simp; ring
  rw [e0]
  have t2 : 3 / (2 * (n : ℝ) * (2 * n + 2)) ≤ (3 / 4) / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have t3 : 15 / (2 * (n : ℝ) * (2 * n + 2) * (2 * n + 4)) ≤ (3 / 16) / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0]
  have t4 : 105 / (2 * (n : ℝ) * (2 * n + 2) * (2 * n + 4) * (2 * n + 6)) ≤
      (1 / 16) / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : (100 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h3 : (n : ℝ) ^ 2 * 1 ≤ (n + 1) * (n + 2) := by nlinarith
    have h4 : (2 * (n : ℝ) * (2 * n + 2) * (2 * n + 4) * (2 * n + 6)) =
        16 * ((n : ℝ) * (n + 3)) * ((n + 1) * (n + 2)) := by ring
    rw [h4]
    have h5 : (100 : ℝ) ≤ (n : ℝ) * (n + 3) := by nlinarith
    have h6 : (100 : ℝ) * (n : ℝ) ^ 2 ≤ ((n : ℝ) * (n + 3)) * ((n + 1) * (n + 2)) := by
      have := mul_le_mul h5 h3 (by positivity) (by positivity)
      linarith
    nlinarith
  have e1 : (1 : ℝ) / (n : ℝ) ^ 2 = (3 / 4) / (n : ℝ) ^ 2 + (3 / 16) / (n : ℝ) ^ 2 +
      (1 / 16) / (n : ℝ) ^ 2 := by ring
  linarith

/-- The mean square of (a mean of `k` independent samples of `f`) minus a constant. -/
theorem iid_mean_sq {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {f : α → ℝ} (hf : BM f) (k : ℕ) (hk : 1 ≤ k) (c : ℝ) :
    ∫ s : Fin k → α, ((1 / (k : ℝ)) * ∑ i, f (s i) - c) ^ 2 ∂(Measure.pi fun _ : Fin k => P) =
      Var[f; P] / (k : ℝ) + (∫ x, f x ∂P - c) ^ 2 := by
  set m := ∫ x, f x ∂P with hm
  set π := Measure.pi fun _ : Fin k => P with hπ
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set h : α → ℝ := fun x => f x - m with hh
  have bh : BM h := hf.sub (BM.const m)
  have h0 : ∫ x, h x ∂P = 0 := by
    simp only [hh]
    rw [integral_sub (hf.integrable P) (integrable_const _)]
    simp [hm]
  have hV : ∫ x, h x ^ 2 ∂P = Var[f; P] := by
    rw [variance_eq_integral hf.meas.aemeasurable]
  have bX : ∀ i : Fin k, BM (fun s : Fin k → α => h (s i)) := fun i =>
    bh.comp (measurable_pi_apply i)
  have hInd : iIndepFun (fun (i : Fin k) (s : Fin k → α) => h (s i)) π :=
    iIndepFun_pi (X := fun _ => h) (fun _ => bh.meas.aemeasurable)
  have hev : ∀ (i : Fin k) (F : α → ℝ), Measurable F → ∫ s, F (s i) ∂π = ∫ x, F x ∂P := by
    intro i F hF
    have := (measurePreserving_eval (fun _ : Fin k => P) i)
    rw [← this.map_eq, integral_map this.measurable.aemeasurable hF.aestronglyMeasurable]
  have hij : ∀ i j : Fin k, ∫ s, h (s i) * h (s j) ∂π = if i = j then Var[f; P] else 0 := by
    intro i j
    split_ifs with e
    · subst e
      rw [← hV, ← hev i (fun x => h x ^ 2) bh.sq.meas]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [pow_two]
    · rw [(hInd.indepFun e).integral_fun_mul_eq_mul_integral (bX i).meas.aestronglyMeasurable
        (bX j).meas.aestronglyMeasurable, hev i h bh.meas, h0, zero_mul]
  have hS1 : ∫ s, ∑ i, h (s i) ∂π = 0 := by
    rw [integral_finsetSum _ fun i _ => (bX i).integrable π]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hev i h bh.meas, h0]
  have hS2 : ∫ s, (∑ i, h (s i)) ^ 2 ∂π = (k : ℝ) * Var[f; P] := by
    have e : ∀ s : Fin k → α, (∑ i, h (s i)) ^ 2 = ∑ i, ∑ j, h (s i) * h (s j) := by
      intro s
      rw [pow_two, Finset.sum_mul_sum]
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((bX i).mul (bX j)).integrable π]
    simp_rw [integral_finsetSum _ fun j _ => ((bX _).mul (bX j)).integrable π, hij]
    simp
  have bS : BM (fun s : Fin k → α => ∑ i, h (s i)) := by
    have : ∀ t : Finset (Fin k), BM (fun s : Fin k → α => ∑ i ∈ t, h (s i)) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using BM.const (α := Fin k → α) 0
      | insert a t ha ih =>
        simp_rw [Finset.sum_insert ha]
        exact (bX a).add ih
    exact this _
  have e : ∀ s : Fin k → α, ((1 / (k : ℝ)) * ∑ i, f (s i) - c) ^ 2 =
      (1 / (k : ℝ)) ^ 2 * (∑ i, h (s i)) ^ 2 + (2 * (m - c) / k) * (∑ i, h (s i)) +
        (m - c) ^ 2 := by
    intro s
    have : ∑ i, h (s i) = ∑ i, f (s i) - k * m := by
      simp [hh, Finset.sum_sub_distrib]
    rw [this]
    field_simp
    ring
  simp_rw [e]
  have I1 : Integrable (fun s : Fin k → α => (1 / (k : ℝ)) ^ 2 * (∑ i, h (s i)) ^ 2) π :=
    (bS.sq.integrable π).const_mul _
  have I2 : Integrable (fun s : Fin k → α => (2 * (m - c) / k) * (∑ i, h (s i))) π :=
    (bS.integrable π).const_mul _
  have I12 : Integrable (fun s : Fin k → α => (1 / (k : ℝ)) ^ 2 * (∑ i, h (s i)) ^ 2 +
      (2 * (m - c) / k) * (∑ i, h (s i))) π := I1.add I2
  rw [integral_add I12 (integrable_const _), integral_add I1 I2, integral_const_mul,
    integral_const_mul, hS1, hS2]
  simp
  field_simp

end BstLean.Part107
