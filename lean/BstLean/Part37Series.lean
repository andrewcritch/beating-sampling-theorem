import BstLean.Part37GenFun
import BstLean.Part33Moments
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Part 37, wave 1: the truncated series is the moment of `D_K` against the uniform sphere

Paper: Lemma `series` (its proof, truncated at degree `K`). Specification §2. The only analytic input is
Part 33's `uniformSphere_prod` (sphere moments at every degree, proved). Route: expand
`q_θ^k = Σ_{|κ|=k} k!/κ! ∏ θᵢ^{κᵢ} xᵢ^{2κᵢ}` (`Finset.sum_pow`-type multinomial; or induction on `k`), and
apply `SphereProd` to each monomial. `numK_eq` uses the statement `phiW_eq_phiCoef` (file
`Part37GenFun`).

Provers: replace each `sorry` by a proof. Do not edit `Part37Defs.lean` or any statement in this file,
and do not use `native_decide` anywhere.
-/

namespace BstLean.Part37

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF frobSq CoefIdx cOf LOf aOf Bof varOf unitOf qformC
  uniformSphere kappa eta)
open BstLean.Part33 (SphereProd floorY4 rawQ Dc)

variable {n : ℕ}

private lemma continuous_sphere_integrable (hn : 1 ≤ n) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  let σ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  have hm : Measurable (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      WithLp.ofLp x.1) := by fun_prop
  have hz : σ Set.univ ≠ 0 := by
    let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact (Measure.measure_univ_ne_zero).2 (Measure.toSphere_ne_zero volume)
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr hz)
  apply (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).2
  have hc : Continuous (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      f (WithLp.ofLp x.1)) := hf.comp (by fun_prop)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma continuous_wmono (w : List (Fin n)) : Continuous (wmono w) := by
  induction w with
  | nil => exact continuous_const
  | cons i w ih =>
    change Continuous (fun x => x i ^ 2 * wmono w x)
    exact ((continuous_apply i).pow 2).mul ih

private lemma count_get (l : List (Fin n)) (i : Fin n) :
    (Finset.univ.filter fun s => l.get s = i).card = l.count i := by
  classical
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [Finset.card_filter, List.length_cons, Fin.sum_univ_succ,
      List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
      List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [Finset.card_filter, List.get_eq_getElem] at ih
    rw [ih]
    by_cases h : j = i <;> simp [h, Nat.add_comm]

private lemma list_moment (hn : 1 ≤ n) (l : List (Fin n)) :
    (∫ x, (l.map (fun i => x i)).prod ∂uniformSphere n) =
      (∏ i, BstLean.Part29.gaussMom (l.count i)) / rhoP n (l.length / 2) := by
  have hp (x : Fin n → ℝ) : (l.map (fun i => x i)).prod = ∏ s, x (l.get s) := by
    simp
  simp_rw [hp]
  rw [(BstLean.Part33.uniformSphere_prod n l.length hn).mom l.length le_rfl l.get]
  simp_rw [count_get]
  rfl

private lemma powers_moment (hn : 1 ≤ n) (a : Fin n → ℕ) :
    (∫ x, ∏ i, x i ^ (2 * a i) ∂uniformSphere n) =
      (∏ i, ((2 * a i - 1).doubleFactorial : ℝ)) / rhoP n (∑ i, a i) := by
  classical
  let l := (List.ofFn (fun i : Fin n => i)).flatMap (fun i => List.replicate (2 * a i) i)
  have hc (i : Fin n) : l.count i = 2 * a i := by
    simp [l, List.count_flatMap, List.count_replicate, List.map_ofFn, List.sum_ofFn]
  have hl : l.length = 2 * ∑ i, a i := by
    simp [l, List.length_flatMap, List.map_ofFn, List.sum_ofFn, Finset.mul_sum]
  have hp (x : Fin n → ℝ) : (l.map (fun i => x i)).prod = ∏ i, x i ^ (2 * a i) := by
    simp [l, List.flatMap_def, List.prod_flatten,
      List.map_ofFn, List.prod_ofFn, Function.comp_def]
  have h := list_moment hn l
  simp_rw [hp, hc] at h
  simpa [hl, BstLean.Part29.gaussMom, show ∀ i, Even (2 * a i) by intro i; exact even_two_mul _] using h

private lemma wmono_powers (w : List (Fin n)) (x : Fin n → ℝ) :
    wmono w x = ∏ i, x i ^ (2 * w.count i) := by
  classical
  unfold wmono
  rw [Finset.prod_list_map_count]
  simp_rw [← pow_mul]
  apply Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => ?_)
  simp only [List.mem_toFinset] at hi
  simp [List.count_eq_zero.mpr hi]

private lemma count_sum (w : List (Fin n)) : (∑ i, w.count i) = w.length := by
  classical
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [List.count_cons, List.length_cons]
    simp_rw [show ∀ i : Fin n, (if j == i then 1 else 0) = (if i = j then 1 else 0)
      by intro i; by_cases h : i = j <;> simp [h, Ne.symm]]
    simp [Finset.sum_add_distrib, ih]

/-- Integrability of `∏_{i∈w} xᵢ² · q_θ^k` under the uniform law. -/
theorem wmono_qpow_integrable (hn : 1 ≤ n) (θ : Fin n → ℝ) (w : List (Fin n)) (k : ℕ) :
    Integrable (fun x => wmono w x * qth θ x ^ k) (uniformSphere n) := by
  apply continuous_sphere_integrable hn
  exact (continuous_wmono w).mul ((by unfold qth; fun_prop : Continuous (qth θ)).pow k)

/-- **The degree-`k` term**: `E_U[∏_{i∈w} xᵢ² q_θ^k] = k! · phiCoef θ w k / ρ_{|w|+k}`. -/
theorem sphere_wq_moment (hn : 1 ≤ n) (θ : Fin n → ℝ) (w : List (Fin n)) (k : ℕ) :
    ∫ x, wmono w x * qth θ x ^ k ∂uniformSphere n =
      (k.factorial : ℝ) * phiCoef θ w k / rhoP n (w.length + k) := by
  classical
  have hexp (x : Fin n → ℝ) : wmono w x * qth θ x ^ k =
      ∑ a ∈ Finset.Nat.antidiagonalTuple n k,
        ((Nat.multinomial Finset.univ a : ℝ) * ∏ i, θ i ^ a i) *
          ∏ i, x i ^ (2 * (w.count i + a i)) := by
    rw [qth, Finset.sum_pow_eq_sum_piAntidiag,
      Finset.piAntidiag_univ_fin_eq_antidiagonalTuple, Finset.mul_sum, wmono_powers]
    apply Finset.sum_congr rfl
    intro a ha
    simp_rw [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
    rw [show (∏ i, x i ^ (2 * (w.count i + a i))) =
        (∏ i, x i ^ (2 * w.count i)) * ∏ i, x i ^ (2 * a i) by
      simp_rw [Nat.mul_add, pow_add, Finset.prod_mul_distrib]]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun a _ =>
    (continuous_sphere_integrable hn _ (by fun_prop)).const_mul _)]
  simp_rw [integral_const_mul, powers_moment hn]
  unfold phiCoef
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : ∑ i, a i = k := Finset.Nat.mem_antidiagonalTuple.mp ha
  rw [Finset.sum_add_distrib, count_sum, ha']
  have hc : (∏ i, (a i).factorial : ℝ) * (Nat.multinomial Finset.univ a : ℝ) =
      (k.factorial : ℝ) := by
    exact_mod_cast (ha' ▸ Nat.multinomial_spec Finset.univ a)
  have hd : (∏ i, ((a i).factorial : ℝ)) ≠ 0 := by positivity
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [← hc]
  field_simp

/-- **The truncated series is an integral**: `E_U[∏_{i∈w} xᵢ² T_K(q_θ)] = N̂_K(w)`. -/
theorem numK_eq (hn : 1 ≤ n) (θ : Fin n → ℝ) (K : ℕ) (w : List (Fin n)) :
    ∫ x, wmono w x * taylorExp K (qth θ x) ∂uniformSphere n = numK n K θ w := by
  classical
  simp only [taylorExp, Finset.mul_sum, ← mul_div_assoc]
  rw [integral_finsetSum _ (fun k _ =>
    (wmono_qpow_integrable hn θ w k).div_const _)]
  simp_rw [integral_div, sphere_wq_moment hn θ w]
  unfold numK
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← phiW_eq_phiCoef θ w k]
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- `Z_K = N̂_K([])`. -/
theorem ZK_eq (hn : 1 ≤ n) (θ : Fin n → ℝ) (K : ℕ) : ZK n K θ = numK n K θ [] := by
  simpa [ZK, wmono] using numK_eq hn θ K []

/-- Integrability of every monomial times `q_θ^k`. -/
theorem mono_qpow_integrable (hn : 1 ≤ n) (θ : Fin n → ℝ) (r : ℕ) (τ : Fin r → Fin n) (k : ℕ) :
    Integrable (fun x : Fin n → ℝ => (∏ s, x (τ s)) * qth θ x ^ k) (uniformSphere n) := by
  apply continuous_sphere_integrable hn
  exact (by fun_prop : Continuous (fun x : Fin n → ℝ => ∏ s, x (τ s))).mul
    ((by unfold qth; fun_prop : Continuous (qth θ)).pow k)

/-- **Sign symmetry**: a monomial with an odd exponent, times `q_θ^k`, has mean `0` under the uniform law. -/
theorem sphere_odd_moment (hn : 1 ≤ n) (θ : Fin n → ℝ) (r : ℕ) (τ : Fin r → Fin n) (k : ℕ)
    (hodd : ∃ i, Odd (Finset.univ.filter fun s => τ s = i).card) :
    ∫ x, (∏ s, x (τ s)) * qth θ x ^ k ∂uniformSphere n = 0 := by
  classical
  induction k generalizing r with
  | zero =>
    simp only [pow_zero, mul_one]
    rw [(BstLean.Part33.uniformSphere_prod n r hn).mom r le_rfl τ]
    obtain ⟨i, hi⟩ := hodd
    have hz : (∏ i, BstLean.Part29.gaussMom
        (Finset.univ.filter fun s => τ s = i).card) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [BstLean.Part29.gaussMom, Nat.not_even_iff_odd.mpr hi]
    rw [hz, zero_div]
  | succ k ih =>
    have heq (x : Fin n → ℝ) :
        (∏ s, x (τ s)) * qth θ x ^ (k + 1) =
        ∑ i, θ i * ((∏ s : Fin (r + 2), x (Fin.append τ (fun _ => i) s)) * qth θ x ^ k) := by
      simp only [pow_succ, qth, Finset.mul_sum, Fin.prod_univ_add,
        Fin.prod_univ_two, Fin.append_left, Fin.append_right]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simp_rw [heq]
    rw [integral_finsetSum _ (fun i _ =>
      (mono_qpow_integrable hn θ (r + 2) (Fin.append τ (fun _ => i)) k).const_mul _)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul, ih (r + 2) (Fin.append τ (fun _ => i))]
    · simp
    · obtain ⟨j, hj⟩ := hodd
      refine ⟨j, ?_⟩
      have hc : (Finset.univ.filter fun s : Fin (r + 2) =>
          Fin.append τ (fun _ => i) s = j).card =
          (Finset.univ.filter fun s => τ s = j).card + (if i = j then 2 else 0) := by
        simp only [Finset.card_filter, Fin.sum_univ_add, Fin.append_left,
          Fin.append_right, Fin.sum_univ_two]
        split_ifs <;> simp
      rw [hc]
      split_ifs
      · exact hj.add_even (by decide)
      · simpa using hj

end BstLean.Part37
