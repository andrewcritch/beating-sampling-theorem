import BstLean.Part152SF
import BstLean.Part148GC
import BstLean.Part130Defs

/-!
# Part 153 (Inv): inverse moments of a shifted Gaussian vector

For `y = c + τ ξ`, `ξ` standard Gaussian in `ℝⁿ` and `2p < n - 1`:
`τ^{2p} E|y|^{-2p} ≤ ∏_{i=1}^p (n-1-2i)^{-1}` (Lemma S, third assertion, of
`proofs/option-n/theorem5-04-standin-structure.tex`).

Route: with `u` a unit vector along `c` and `s(ξ) = |ξ|² − ⟨u,ξ⟩²`, `|c + τξ|² ≥ τ² s(ξ)`; the
inverse moments of `s + ε` satisfy a recursion by Stein's identity; then `ε ↓ 0` by Fatou.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)

section proj

variable {m : ℕ}

/-- The inner product with `u`. -/
def dt (u ζ : Fin (m + 1) → ℝ) : ℝ := ∑ i, u i * ζ i

/-- `|ζ|² − ⟨u,ζ⟩²`: the squared norm of the projection of `ζ` orthogonal to the unit vector
`u`. -/
def sP (u ζ : Fin (m + 1) → ℝ) : ℝ := normSq ζ - dt u ζ ^ 2

lemma sum_update (F : Fin (m + 1) → ℝ → ℝ) (ζ : Fin (m + 1) → ℝ) (k : Fin (m + 1)) (t : ℝ) :
    ∑ i, F i (Function.update ζ k t i) = ∑ i, F i (ζ i) - F k (ζ k) + F k t := by
  rw [← Finset.add_sum_erase Finset.univ (fun i => F i (Function.update ζ k t i))
    (Finset.mem_univ k), ← Finset.add_sum_erase Finset.univ (fun i => F i (ζ i))
    (Finset.mem_univ k)]
  have : ∑ i ∈ Finset.univ.erase k, F i (Function.update ζ k t i) =
      ∑ i ∈ Finset.univ.erase k, F i (ζ i) :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [this, Function.update_self]
  ring

lemma dt_update (u ζ : Fin (m + 1) → ℝ) (k : Fin (m + 1)) (t : ℝ) :
    dt u (Function.update ζ k t) = dt u ζ + u k * (t - ζ k) := by
  unfold dt
  rw [sum_update (fun i x => u i * x)]
  ring

lemma normSq_update (ζ : Fin (m + 1) → ℝ) (k : Fin (m + 1)) (t : ℝ) :
    normSq (Function.update ζ k t) = normSq ζ - ζ k ^ 2 + t ^ 2 := by
  unfold normSq
  rw [sum_update (fun _ x => x ^ 2)]

lemma sum_sub_sq (u ζ : Fin (m + 1) → ℝ) (D : ℝ) :
    ∑ i, (ζ i - D * u i) ^ 2 = normSq ζ - 2 * D * dt u ζ + D ^ 2 * ∑ i, u i ^ 2 := by
  unfold normSq dt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sP_eq_sum {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) (ζ : Fin (m + 1) → ℝ) :
    sP u ζ = ∑ i, (ζ i - dt u ζ * u i) ^ 2 := by
  rw [sum_sub_sq, hu]
  unfold sP
  ring

lemma sP_nonneg {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) (ζ : Fin (m + 1) → ℝ) :
    0 ≤ sP u ζ := by
  rw [sP_eq_sum hu]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

lemma pr_sq_le {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) (ζ : Fin (m + 1) → ℝ)
    (k : Fin (m + 1)) : (ζ k - dt u ζ * u k) ^ 2 ≤ sP u ζ := by
  rw [sP_eq_sum hu]
  exact Finset.single_le_sum (f := fun i => (ζ i - dt u ζ * u i) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ k)

lemma u_sq_le {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) (k : Fin (m + 1)) : u k ^ 2 ≤ 1 := by
  rw [← hu]
  exact Finset.single_le_sum (f := fun i => u i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k)

lemma measurable_dt (u : Fin (m + 1) → ℝ) : Measurable (dt u) := by
  unfold dt
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _

lemma measurable_normSq {ι : Type} [Fintype ι] : Measurable (normSq : (ι → ℝ) → ℝ) := by
  unfold normSq
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2

lemma measurable_sP (u : Fin (m + 1) → ℝ) : Measurable (sP u) := by
  unfold sP
  exact measurable_normSq.sub ((measurable_dt u).pow_const 2)

/-- `w = (s + ε)⁻¹`. -/
noncomputable def wE (u : Fin (m + 1) → ℝ) (ε : ℝ) (ζ : Fin (m + 1) → ℝ) : ℝ := (sP u ζ + ε)⁻¹

lemma measurable_wE (u : Fin (m + 1) → ℝ) (ε : ℝ) : Measurable (wE u ε) := by
  unfold wE
  exact ((measurable_sP u).add_const ε).inv

section bounds

variable {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) {ε : ℝ} (hε : 0 < ε)
include hu hε

lemma wE_pos (ζ : Fin (m + 1) → ℝ) : 0 < wE u ε ζ :=
  inv_pos.2 (add_pos_of_nonneg_of_pos (sP_nonneg hu ζ) hε)

lemma wE_le (ζ : Fin (m + 1) → ℝ) : wE u ε ζ ≤ ε⁻¹ := by
  unfold wE
  exact inv_anti₀ hε (le_add_of_nonneg_left (sP_nonneg hu ζ))

lemma sP_mul_wE_le (ζ : Fin (m + 1) → ℝ) : sP u ζ * wE u ε ζ ≤ 1 := by
  unfold wE
  have h := add_pos_of_nonneg_of_pos (sP_nonneg hu ζ) hε
  rw [← div_eq_mul_inv, div_le_one h]
  linarith

lemma wE_pow_le (ζ : Fin (m + 1) → ℝ) (j : ℕ) : wE u ε ζ ^ j ≤ ε⁻¹ ^ j :=
  pow_le_pow_left₀ (wE_pos hu hε ζ).le (wE_le hu hε ζ) j

lemma sP_wE_pow_le (ζ : Fin (m + 1) → ℝ) (j : ℕ) :
    sP u ζ * wE u ε ζ ^ (j + 1) ≤ wE u ε ζ ^ j := by
  have h := mul_le_mul_of_nonneg_right (sP_mul_wE_le hu hε ζ) (pow_nonneg (wE_pos hu hε ζ).le j)
  rw [one_mul] at h
  calc sP u ζ * wE u ε ζ ^ (j + 1) = sP u ζ * wE u ε ζ * wE u ε ζ ^ j := by ring
    _ ≤ _ := h

end bounds

lemma integrable_of_bdd {f : (Fin (m + 1) → ℝ) → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ ζ, |f ζ| ≤ C) : Integrable f (stdGauss (Fin (m + 1))) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (ae_of_all _ fun ζ => hb ζ)

/-- The derivative of `s` in one coordinate. -/
lemma sP_hasDerivAt (u ζ : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    HasDerivAt (fun t => sP u (Function.update ζ k t)) (2 * (ζ k - dt u ζ * u k)) (ζ k) := by
  have e : (fun t => sP u (Function.update ζ k t)) =
      fun t => (normSq ζ - ζ k ^ 2) + t ^ 2 - (dt u ζ + u k * (t - ζ k)) ^ 2 := by
    funext t
    unfold sP
    rw [normSq_update, dt_update]
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * ζ k) (ζ k) := by
    simpa using hasDerivAt_pow 2 (ζ k)
  have h2 : HasDerivAt (fun t : ℝ => dt u ζ + u k * (t - ζ k)) (u k) (ζ k) := by
    simpa using (((hasDerivAt_id (ζ k)).sub_const (ζ k)).const_mul (u k)).const_add (dt u ζ)
  have h3 := h2.pow 2
  have h := (h1.const_add (normSq ζ - ζ k ^ 2)).sub h3
  convert h using 1
  simp
  ring

/-- Stein's identity for the field `(Pζ)_k (s+ε)^{-(q+1)}` in coordinate `k`. -/
lemma stein_k {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) {ε : ℝ} (hε : 0 < ε) (q : ℕ)
    (k : Fin (m + 1)) :
    Integrable (fun ζ => ζ k * ((ζ k - dt u ζ * u k) * wE u ε ζ ^ (q + 1)))
      (stdGauss (Fin (m + 1))) ∧
    ∫ ζ, ζ k * ((ζ k - dt u ζ * u k) * wE u ε ζ ^ (q + 1)) ∂stdGauss (Fin (m + 1)) =
      ∫ ζ, ((1 - u k ^ 2) * wE u ε ζ ^ (q + 1) -
        2 * ((q : ℝ) + 1) * ((ζ k - dt u ζ * u k) ^ 2 * wE u ε ζ ^ (q + 2)))
        ∂stdGauss (Fin (m + 1)) := by
  have hεi : 0 < ε⁻¹ := inv_pos.2 hε
  set C1 : ℝ := (ε⁻¹ + 1) * ε⁻¹ ^ q with hC1
  set C2 : ℝ := ε⁻¹ ^ (q + 1) + 2 * ((q : ℝ) + 1) * ε⁻¹ ^ (q + 1) with hC2
  have hC1n : 0 ≤ C1 := by positivity
  have hC2n : 0 ≤ C2 := by positivity
  have hΦm : Measurable (fun ζ : Fin (m + 1) → ℝ => (ζ k - dt u ζ * u k) * wE u ε ζ ^ (q + 1)) :=
    ((measurable_pi_apply k).sub ((measurable_dt u).mul_const _)).mul
      ((measurable_wE u ε).pow_const _)
  have hΦ'm : Measurable (fun ζ : Fin (m + 1) → ℝ => (1 - u k ^ 2) * wE u ε ζ ^ (q + 1) -
        2 * ((q : ℝ) + 1) * ((ζ k - dt u ζ * u k) ^ 2 * wE u ε ζ ^ (q + 2))) :=
    (((measurable_wE u ε).pow_const _).const_mul _).sub
      (((((measurable_pi_apply k).sub ((measurable_dt u).mul_const _)).pow_const 2).mul
        ((measurable_wE u ε).pow_const _)).const_mul _)
  have hb : ∀ ζ : Fin (m + 1) → ℝ,
      |(ζ k - dt u ζ * u k) * wE u ε ζ ^ (q + 1)| ≤ C1 + C2 := by
    intro ζ
    have hw := wE_pos hu hε ζ
    have hwl := wE_le hu hε ζ
    have hpr := pr_sq_le hu ζ k
    have hsw := sP_mul_wE_le hu hε ζ
    set a := ζ k - dt u ζ * u k with ha
    set w := wE u ε ζ with hw'
    have h1 : |a| * w ≤ ε⁻¹ + 1 := by
      have : |a| ≤ 1 + a ^ 2 := by
        have := sq_nonneg (|a| - 1)
        rw [sub_sq, sq_abs] at this
        nlinarith [abs_nonneg a]
      have h2 : a ^ 2 * w ≤ 1 := (mul_le_mul_of_nonneg_right hpr hw.le).trans hsw
      calc |a| * w ≤ (1 + a ^ 2) * w := mul_le_mul_of_nonneg_right this hw.le
        _ = w + a ^ 2 * w := by ring
        _ ≤ ε⁻¹ + 1 := add_le_add hwl h2
    have h3 : |a * w ^ (q + 1)| = |a| * w * w ^ q := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hw.le _)]
      ring
    rw [h3]
    have h4 : |a| * w * w ^ q ≤ C1 :=
      mul_le_mul h1 (wE_pow_le hu hε ζ q) (pow_nonneg hw.le _) (by positivity)
    linarith
  have hb' : ∀ ζ : Fin (m + 1) → ℝ, |(1 - u k ^ 2) * wE u ε ζ ^ (q + 1) -
        2 * ((q : ℝ) + 1) * ((ζ k - dt u ζ * u k) ^ 2 * wE u ε ζ ^ (q + 2))| ≤ C1 + C2 := by
    intro ζ
    have hw := wE_pos hu hε ζ
    have hpr := pr_sq_le hu ζ k
    have hsw := sP_mul_wE_le hu hε ζ
    have huk := u_sq_le hu k
    have hwp := wE_pow_le hu hε ζ (q + 1)
    set a := ζ k - dt u ζ * u k with ha
    set w := wE u ε ζ with hw'
    have hwq : 0 ≤ w ^ (q + 1) := pow_nonneg hw.le _
    have h2 : a ^ 2 * w ≤ 1 := (mul_le_mul_of_nonneg_right hpr hw.le).trans hsw
    have t1 : 0 ≤ (1 - u k ^ 2) * w ^ (q + 1) := mul_nonneg (by linarith) hwq
    have t1' : (1 - u k ^ 2) * w ^ (q + 1) ≤ ε⁻¹ ^ (q + 1) := by
      calc (1 - u k ^ 2) * w ^ (q + 1) ≤ 1 * w ^ (q + 1) :=
            mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (u k)]) hwq
        _ ≤ _ := by rw [one_mul]; exact hwp
    have t2 : 0 ≤ a ^ 2 * w ^ (q + 2) := mul_nonneg (sq_nonneg _) (pow_nonneg hw.le _)
    have t2' : a ^ 2 * w ^ (q + 2) ≤ ε⁻¹ ^ (q + 1) := by
      calc a ^ 2 * w ^ (q + 2) = a ^ 2 * w * w ^ (q + 1) := by ring
        _ ≤ 1 * w ^ (q + 1) := mul_le_mul_of_nonneg_right h2 hwq
        _ ≤ _ := by rw [one_mul]; exact hwp
    have hq : (0 : ℝ) ≤ 2 * ((q : ℝ) + 1) := by positivity
    have t3 : 2 * ((q : ℝ) + 1) * (a ^ 2 * w ^ (q + 2)) ≤ 2 * ((q : ℝ) + 1) * ε⁻¹ ^ (q + 1) :=
      mul_le_mul_of_nonneg_left t2' hq
    have t4 : 0 ≤ 2 * ((q : ℝ) + 1) * (a ^ 2 * w ^ (q + 2)) := mul_nonneg hq t2
    rw [abs_le]
    constructor <;> linarith
  have hd : ∀ ζ : Fin (m + 1) → ℝ, HasDerivAt
      (fun t => (Function.update ζ k t k - dt u (Function.update ζ k t) * u k) *
        wE u ε (Function.update ζ k t) ^ (q + 1))
      ((1 - u k ^ 2) * wE u ε ζ ^ (q + 1) -
        2 * ((q : ℝ) + 1) * ((ζ k - dt u ζ * u k) ^ 2 * wE u ε ζ ^ (q + 2))) (ζ k) := by
    intro ζ
    have hpos : 0 < sP u ζ + ε := add_pos_of_nonneg_of_pos (sP_nonneg hu ζ) hε
    have e : (fun t => (Function.update ζ k t k - dt u (Function.update ζ k t) * u k) *
        wE u ε (Function.update ζ k t) ^ (q + 1)) =
        fun t => (t - (dt u ζ + u k * (t - ζ k)) * u k) *
          ((sP u (Function.update ζ k t) + ε)⁻¹) ^ (q + 1) := by
      funext t
      rw [Function.update_self, dt_update]
      rfl
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => t - (dt u ζ + u k * (t - ζ k)) * u k) (1 - u k * u k)
        (ζ k) := by
      have h2 : HasDerivAt (fun t : ℝ => dt u ζ + u k * (t - ζ k)) (u k) (ζ k) := by
        simpa using (((hasDerivAt_id (ζ k)).sub_const (ζ k)).const_mul (u k)).const_add (dt u ζ)
      exact (hasDerivAt_id (ζ k)).sub (h2.mul_const (u k))
    have h3 : HasDerivAt (fun t => sP u (Function.update ζ k t) + ε)
        (2 * (ζ k - dt u ζ * u k)) (ζ k) := (sP_hasDerivAt u ζ k).add_const ε
    have h30 : sP u (Function.update ζ k (ζ k)) + ε ≠ 0 := by
      rw [Function.update_eq_self]
      exact hpos.ne'
    have h4 : HasDerivAt (fun t => ((sP u (Function.update ζ k t) + ε)⁻¹) ^ (q + 1))
        (((q + 1 : ℕ) : ℝ) * ((sP u ζ + ε)⁻¹) ^ q *
          (-(2 * (ζ k - dt u ζ * u k)) / (sP u ζ + ε) ^ 2)) (ζ k) := by
      have := (h3.inv h30).pow (q + 1)
      simp only [Function.update_eq_self, Pi.inv_apply, add_tsub_cancel_right] at this
      exact this
    have h5 : HasDerivAt (fun t => (t - (dt u ζ + u k * (t - ζ k)) * u k) *
          ((sP u (Function.update ζ k t) + ε)⁻¹) ^ (q + 1))
        ((1 - u k * u k) * ((sP u ζ + ε)⁻¹) ^ (q + 1) +
          (ζ k - (dt u ζ + u k * (ζ k - ζ k)) * u k) *
          (((q + 1 : ℕ) : ℝ) * ((sP u ζ + ε)⁻¹) ^ q *
          (-(2 * (ζ k - dt u ζ * u k)) / (sP u ζ + ε) ^ 2))) (ζ k) := by
      have := h1.mul h4
      rw [Function.update_eq_self] at this
      exact this
    convert h5 using 1
    have hne := hpos.ne'
    have hw2 : ∀ x : ℝ, x / (sP u ζ + ε) ^ 2 = x * ((sP u ζ + ε)⁻¹) ^ 2 := fun x => by
      rw [div_eq_mul_inv, inv_pow]
    simp only [wE, sub_self, mul_zero, add_zero, hw2]
    push_cast
    generalize (sP u ζ + ε)⁻¹ = w
    ring
  have hst := BstLean.Part152.stein_coord k hΦm hΦ'm hd hb hb'
  refine ⟨?_, hst⟩
  refine Integrable.mono' ((BstLean.Part152.integrable_coord k).norm.const_mul (C1 + C2))
    (((measurable_pi_apply k).mul hΦm).aestronglyMeasurable) (ae_of_all _ fun ζ => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb ζ) (abs_nonneg _)

lemma sum_u_compl {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) :
    ∑ k : Fin (m + 1), (1 - u k ^ 2) = (m : ℝ) := by
  rw [Finset.sum_sub_distrib, hu]
  simp

/-- The recursion: `(m − 2(q+1))·E(s+ε)^{-(q+1)} ≤ E(s+ε)^{-q}`. -/
lemma rec_step {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    ((m : ℝ) - 2 * ((q : ℝ) + 1)) * ∫ ζ, wE u ε ζ ^ (q + 1) ∂stdGauss (Fin (m + 1)) ≤
      ∫ ζ, wE u ε ζ ^ q ∂stdGauss (Fin (m + 1)) := by
  have hwm : ∀ j : ℕ, Measurable fun ζ => wE u ε ζ ^ j := fun j =>
    (measurable_wE u ε).pow_const j
  have hwi : ∀ j : ℕ, Integrable (fun ζ => wE u ε ζ ^ j) (stdGauss (Fin (m + 1))) := fun j =>
    integrable_of_bdd (hwm j) (C := ε⁻¹ ^ j) fun ζ => by
      rw [abs_of_nonneg (pow_nonneg (wE_pos hu hε ζ).le _)]
      exact wE_pow_le hu hε ζ j
  have hswi : ∀ j : ℕ, Integrable (fun ζ => sP u ζ * wE u ε ζ ^ (j + 1))
      (stdGauss (Fin (m + 1))) := fun j =>
    integrable_of_bdd ((measurable_sP u).mul (hwm _)) (C := ε⁻¹ ^ j) fun ζ => by
      rw [abs_of_nonneg (mul_nonneg (sP_nonneg hu ζ) (pow_nonneg (wE_pos hu hε ζ).le _))]
      exact (sP_wE_pow_le hu hε ζ j).trans (wE_pow_le hu hε ζ j)
  -- the summed Stein identity
  have key : ∫ ζ, sP u ζ * wE u ε ζ ^ (q + 1) ∂stdGauss (Fin (m + 1)) =
      ∫ ζ, ((m : ℝ) * wE u ε ζ ^ (q + 1) -
        2 * ((q : ℝ) + 1) * (sP u ζ * wE u ε ζ ^ (q + 2))) ∂stdGauss (Fin (m + 1)) := by
    have e1 : ∀ ζ : Fin (m + 1) → ℝ, sP u ζ * wE u ε ζ ^ (q + 1) =
        ∑ k, ζ k * ((ζ k - dt u ζ * u k) * wE u ε ζ ^ (q + 1)) := by
      intro ζ
      have : ∑ k, ζ k * ((ζ k - dt u ζ * u k) * wE u ε ζ ^ (q + 1)) =
          (∑ k, ζ k ^ 2 - dt u ζ * ∑ k, u k * ζ k) * wE u ε ζ ^ (q + 1) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      unfold sP normSq dt
      ring
    have e2 : ∀ ζ : Fin (m + 1) → ℝ, ((m : ℝ) * wE u ε ζ ^ (q + 1) -
        2 * ((q : ℝ) + 1) * (sP u ζ * wE u ε ζ ^ (q + 2))) =
        ∑ k, ((1 - u k ^ 2) * wE u ε ζ ^ (q + 1) -
          2 * ((q : ℝ) + 1) * ((ζ k - dt u ζ * u k) ^ 2 * wE u ε ζ ^ (q + 2))) := by
      intro ζ
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_u_compl hu, ← Finset.mul_sum,
        ← Finset.sum_mul, ← sP_eq_sum hu]
    simp_rw [e1, e2]
    rw [integral_finsetSum _ fun k _ => (stein_k hu hε q k).1]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun k _ => (stein_k hu hε q k).2
    · intro k _
      refine ((hwi (q + 1)).const_mul _).sub (Integrable.const_mul ?_ _)
      refine integrable_of_bdd ((((measurable_pi_apply k).sub
        ((measurable_dt u).mul_const _)).pow_const 2).mul (hwm _)) (C := ε⁻¹ ^ (q + 1))
        fun ζ => ?_
      have hw := wE_pos hu hε ζ
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hw.le _))]
      calc (ζ k - dt u ζ * u k) ^ 2 * wE u ε ζ ^ (q + 2)
          ≤ sP u ζ * wE u ε ζ ^ (q + 1 + 1) :=
            mul_le_mul_of_nonneg_right (pr_sq_le hu ζ k) (pow_nonneg hw.le _)
        _ ≤ wE u ε ζ ^ (q + 1) := sP_wE_pow_le hu hε ζ (q + 1)
        _ ≤ _ := wE_pow_le hu hε ζ (q + 1)
  have hI : Integrable (fun ζ => ((m : ℝ) * wE u ε ζ ^ (q + 1) -
        2 * ((q : ℝ) + 1) * (sP u ζ * wE u ε ζ ^ (q + 2)))) (stdGauss (Fin (m + 1))) :=
    ((hwi (q + 1)).const_mul _).sub ((hswi (q + 1)).const_mul _)
  calc ((m : ℝ) - 2 * ((q : ℝ) + 1)) * ∫ ζ, wE u ε ζ ^ (q + 1) ∂stdGauss (Fin (m + 1))
      = ∫ ζ, ((m : ℝ) - 2 * ((q : ℝ) + 1)) * wE u ε ζ ^ (q + 1) ∂stdGauss (Fin (m + 1)) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ ζ, ((m : ℝ) * wE u ε ζ ^ (q + 1) -
        2 * ((q : ℝ) + 1) * (sP u ζ * wE u ε ζ ^ (q + 2))) ∂stdGauss (Fin (m + 1)) := by
        refine integral_mono ((hwi (q + 1)).const_mul _) hI fun ζ => ?_
        have h := sP_wE_pow_le hu hε ζ (q + 1)
        have hq : (0 : ℝ) ≤ 2 * ((q : ℝ) + 1) := by positivity
        have := mul_le_mul_of_nonneg_left h hq
        show ((m : ℝ) - 2 * ((q : ℝ) + 1)) * wE u ε ζ ^ (q + 1) ≤
          (m : ℝ) * wE u ε ζ ^ (q + 1) - 2 * ((q : ℝ) + 1) * (sP u ζ * wE u ε ζ ^ (q + 2))
        linarith
    _ = ∫ ζ, sP u ζ * wE u ε ζ ^ (q + 1) ∂stdGauss (Fin (m + 1)) := key.symm
    _ ≤ ∫ ζ, wE u ε ζ ^ q ∂stdGauss (Fin (m + 1)) :=
        integral_mono (hswi q) (hwi q) fun ζ => sP_wE_pow_le hu hε ζ q

/-- The product bound. -/
noncomputable def invBd (m p : ℕ) : ℝ :=
  ∏ i ∈ Finset.range p, ((m : ℝ) - 2 * ((i : ℝ) + 1))⁻¹

lemma invBd_nonneg {m p : ℕ} (hp : 2 * p < m) : 0 ≤ invBd m p := by
  unfold invBd
  refine Finset.prod_nonneg fun i hi => inv_nonneg.2 ?_
  have : i + 1 ≤ p := Finset.mem_range.1 hi
  have h2 : ((2 * (i + 1) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * (i + 1) ≤ m)
  push_cast at h2
  linarith

/-- `E (s+ε)^{-p} ≤ ∏_{i=1}^p (m − 2i)^{-1}` for `2p < m`. -/
lemma wE_moment_le {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) {ε : ℝ} (hε : 0 < ε) (p : ℕ)
    (hp : 2 * p < m) :
    ∫ ζ, wE u ε ζ ^ p ∂stdGauss (Fin (m + 1)) ≤ invBd m p := by
  induction p with
  | zero => simp [invBd]
  | succ q ih =>
    have ihq := ih (by omega)
    have hpos : (0 : ℝ) < (m : ℝ) - 2 * ((q : ℝ) + 1) := by
      have h2 : ((2 * (q + 1) : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hp
      push_cast at h2
      linarith
    have hr := rec_step hu hε q
    unfold invBd
    rw [Finset.prod_range_succ]
    change _ ≤ invBd m q * _
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    calc (∫ ζ, wE u ε ζ ^ (q + 1) ∂stdGauss (Fin (m + 1))) * ((m : ℝ) - 2 * ((q : ℝ) + 1))
        = ((m : ℝ) - 2 * ((q : ℝ) + 1)) * ∫ ζ, wE u ε ζ ^ (q + 1) ∂stdGauss (Fin (m + 1)) :=
          mul_comm _ _
      _ ≤ _ := hr
      _ ≤ _ := ihq

/-- The limit `ε ↓ 0` (Fatou), with values in `[0, ∞]`. -/
lemma lintegral_sP_inv_le {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) (p : ℕ)
    (hp : 2 * p < m) :
    ∫⁻ ζ, (ENNReal.ofReal (sP u ζ))⁻¹ ^ p ∂stdGauss (Fin (m + 1)) ≤
      ENNReal.ofReal (invBd m p) := by
  set e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with he
  have hepos : ∀ k, 0 < e k := fun k => by positivity
  have hF : ∀ (k : ℕ) (ζ : Fin (m + 1) → ℝ),
      ENNReal.ofReal (wE u (e k) ζ ^ p) = (ENNReal.ofReal (sP u ζ + e k))⁻¹ ^ p := by
    intro k ζ
    have hpos : 0 < sP u ζ + e k := add_pos_of_nonneg_of_pos (sP_nonneg hu ζ) (hepos k)
    rw [ENNReal.ofReal_pow (wE_pos hu (hepos k) ζ).le]
    unfold wE
    rw [ENNReal.ofReal_inv_of_pos hpos]
  have hlim : ∀ ζ : Fin (m + 1) → ℝ, Tendsto (fun k => ENNReal.ofReal (wE u (e k) ζ ^ p)) atTop
      (𝓝 ((ENNReal.ofReal (sP u ζ))⁻¹ ^ p)) := by
    intro ζ
    simp_rw [hF]
    have h0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun k => sP u ζ + e k) atTop (𝓝 (sP u ζ)) := by
      simpa using h0.const_add (sP u ζ)
    have h2 := (ENNReal.continuous_ofReal.tendsto (sP u ζ)).comp h1
    have h3 := (continuous_inv.tendsto (ENNReal.ofReal (sP u ζ))).comp h2
    exact ((ENNReal.continuous_pow p).tendsto _).comp h3
  have hmeas : ∀ k, Measurable fun ζ => ENNReal.ofReal (wE u (e k) ζ ^ p) := fun k =>
    ((measurable_wE u (e k)).pow_const p).ennreal_ofReal
  have hk : ∀ k, ∫⁻ ζ, ENNReal.ofReal (wE u (e k) ζ ^ p) ∂stdGauss (Fin (m + 1)) ≤
      ENNReal.ofReal (invBd m p) := by
    intro k
    have hi : Integrable (fun ζ => wE u (e k) ζ ^ p) (stdGauss (Fin (m + 1))) :=
      integrable_of_bdd ((measurable_wE u (e k)).pow_const p) (C := (e k)⁻¹ ^ p) fun ζ => by
        rw [abs_of_nonneg (pow_nonneg (wE_pos hu (hepos k) ζ).le _)]
        exact wE_pow_le hu (hepos k) ζ p
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun ζ => pow_nonneg (wE_pos hu (hepos k) ζ).le _)]
    exact ENNReal.ofReal_le_ofReal (wE_moment_le hu (hepos k) p hp)
  calc ∫⁻ ζ, (ENNReal.ofReal (sP u ζ))⁻¹ ^ p ∂stdGauss (Fin (m + 1))
      = ∫⁻ ζ, liminf (fun k => ENNReal.ofReal (wE u (e k) ζ ^ p)) atTop
          ∂stdGauss (Fin (m + 1)) :=
        lintegral_congr fun ζ => (hlim ζ).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ ζ, ENNReal.ofReal (wE u (e k) ζ ^ p) ∂stdGauss (Fin (m + 1))) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (invBd m p)) atTop :=
        liminf_le_liminf (Eventually.of_forall hk)
    _ = ENNReal.ofReal (invBd m p) := liminf_const _

/-- `|a u + τ ξ|² − ⟨u, a u + τ ξ⟩² = τ² s(ξ)`. -/
lemma sP_shift {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) (a τ : ℝ) (ξ : Fin (m + 1) → ℝ) :
    sP u (a • u + τ • ξ) = τ ^ 2 * sP u ξ := by
  have h1 : dt u (a • u + τ • ξ) = a + τ * dt u ξ := by
    have : dt u (a • u + τ • ξ) = a * ∑ i, u i ^ 2 + τ * dt u ξ := by
      unfold dt
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    rw [this, hu, mul_one]
  have h2 : normSq (a • u + τ • ξ) = a ^ 2 * ∑ i, u i ^ 2 + 2 * a * τ * dt u ξ + τ ^ 2 * normSq ξ := by
    unfold normSq dt
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  unfold sP
  rw [h1, h2, hu]
  ring

lemma sP_le_normSq (u ζ : Fin (m + 1) → ℝ) : sP u ζ ≤ normSq ζ := by
  unfold sP
  linarith [sq_nonneg (dt u ζ)]

/-- The bound in `[0, ∞]` for `c = a u`. -/
lemma lintegral_inv_le {u : Fin (m + 1) → ℝ} (hu : ∑ i, u i ^ 2 = 1) (a : ℝ) {τ : ℝ}
    (hτ : 0 < τ) {p : ℕ} (hp0 : p ≠ 0) (hp : 2 * p < m) :
    ∫⁻ ξ, ENNReal.ofReal (τ ^ (2 * p) * (normSq (a • u + τ • ξ))⁻¹ ^ p)
      ∂stdGauss (Fin (m + 1)) ≤ ENNReal.ofReal (invBd m p) := by
  refine (lintegral_mono fun ξ => ?_).trans (lintegral_sP_inv_le hu p hp)
  rcases (sP_nonneg hu ξ).eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero, ENNReal.inv_zero, ENNReal.top_pow hp0]
    exact le_top
  · have hτ2 : 0 < τ ^ 2 * sP u ξ := by positivity
    have hle : τ ^ 2 * sP u ξ ≤ normSq (a • u + τ • ξ) := by
      rw [← sP_shift hu]
      exact sP_le_normSq _ _
    have h1 : (normSq (a • u + τ • ξ))⁻¹ ≤ (τ ^ 2 * sP u ξ)⁻¹ := inv_anti₀ hτ2 hle
    have h2 : (normSq (a • u + τ • ξ))⁻¹ ^ p ≤ (τ ^ 2 * sP u ξ)⁻¹ ^ p :=
      pow_le_pow_left₀ (inv_nonneg.2 (hτ2.le.trans hle)) h1 p
    have h3 : τ ^ (2 * p) * (τ ^ 2 * sP u ξ)⁻¹ ^ p = (sP u ξ)⁻¹ ^ p := by
      rw [mul_inv, mul_pow, ← mul_assoc, pow_mul, ← mul_pow,
        mul_inv_cancel₀ (pow_ne_zero 2 hτ.ne'), one_pow, one_mul]
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_pow (inv_nonneg.2 hpos.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← h3]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Every vector is a multiple of a unit vector. -/
lemma exists_unit (c : Fin (m + 1) → ℝ) :
    ∃ (u : Fin (m + 1) → ℝ) (a : ℝ), ∑ i, u i ^ 2 = 1 ∧ c = a • u := by
  by_cases hc : normSq c = 0
  · refine ⟨Pi.single 0 1, 0, ?_, ?_⟩
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        simp [hi]
      · simp
    · have h := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (c i)).1 hc
      funext i
      have := h i (Finset.mem_univ i)
      simpa using this
  · have hn : 0 ≤ normSq c := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hpos : 0 < normSq c := lt_of_le_of_ne hn (Ne.symm hc)
    have hs : 0 < √(normSq c) := Real.sqrt_pos.2 hpos
    refine ⟨(√(normSq c))⁻¹ • c, √(normSq c), ?_, ?_⟩
    · have : ∑ i, ((√(normSq c))⁻¹ • c) i ^ 2 = (√(normSq c))⁻¹ ^ 2 * normSq c := by
        unfold normSq
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
      rw [this, inv_pow, Real.sq_sqrt hn, inv_mul_cancel₀ hc]
    · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

end proj

/-- The norm of a shifted Gaussian vector does not vanish, almost surely. -/
theorem ae_normSq_ne_zero {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    ∀ᵐ ξ ∂stdGauss (Fin n), normSq (c + τ • ξ) ≠ 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsub : {ξ : Fin n → ℝ | ¬ normSq (c + τ • ξ) ≠ 0} ⊆ {(-τ⁻¹) • c} := by
    intro ξ hξ
    simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hξ
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ((c + τ • ξ) i)).1 hξ
    rw [mem_singleton_iff]
    funext i
    have hi := h i (Finset.mem_univ i)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_eq_zero_iff (two_ne_zero)] at hi
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  have h0 : (volume : Measure (Fin n → ℝ)) {(-τ⁻¹) • c} = 0 := measure_singleton _
  exact measure_mono_null hsub (BstLean.Part148.stdGauss_ac h0)

/-- **Inverse moments of a shifted Gaussian vector** (Lemma S, third assertion):
`τ^{2p} E|c + τξ|^{-2p} ≤ ∏_{i=1}^p (n-1-2i)^{-1}` for `2p < n - 1`. -/
theorem invMoment_le {n p : ℕ} (hp : 2 * p + 1 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹ ^ p) (stdGauss (Fin n)) ∧
    τ ^ (2 * p) * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ p ∂stdGauss (Fin n) ≤
      ∏ i ∈ Finset.range p, ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpm : 2 * p < m := by omega
  have hprod : ∏ i ∈ Finset.range p, (((m + 1 : ℕ) : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹ =
      invBd m p := by
    unfold invBd
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  rw [hprod]
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp [invBd]
  obtain ⟨u, a, hu, rfl⟩ := exists_unit c
  have hmeas : Measurable fun ξ : Fin (m + 1) → ℝ => (normSq (a • u + τ • ξ))⁻¹ ^ p :=
    ((measurable_normSq.comp (measurable_const.add (measurable_id.const_smul τ))).inv).pow_const p
  have hnn : ∀ ξ : Fin (m + 1) → ℝ, 0 ≤ (normSq (a • u + τ • ξ))⁻¹ ^ p := fun ξ =>
    pow_nonneg (inv_nonneg.2 (Finset.sum_nonneg fun i _ => sq_nonneg _)) p
  have hτp : 0 < τ ^ (2 * p) := by positivity
  have hL := lintegral_inv_le hu a hτ hp0.ne' hpm
  have hnn' : ∀ ξ : Fin (m + 1) → ℝ, 0 ≤ τ ^ (2 * p) * (normSq (a • u + τ • ξ))⁻¹ ^ p :=
    fun ξ => mul_nonneg hτp.le (hnn ξ)
  have hint : Integrable (fun ξ : Fin (m + 1) → ℝ =>
      τ ^ (2 * p) * (normSq (a • u + τ • ξ))⁻¹ ^ p) (stdGauss (Fin (m + 1))) := by
    refine ⟨(hmeas.const_mul _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn')]
    exact hL.trans_lt ENNReal.ofReal_lt_top
  have hint' : Integrable (fun ξ : Fin (m + 1) → ℝ => (normSq (a • u + τ • ξ))⁻¹ ^ p)
      (stdGauss (Fin (m + 1))) := by
    have := hint.const_mul (τ ^ (2 * p))⁻¹
    refine this.congr (ae_of_all _ fun ξ => ?_)
    show (τ ^ (2 * p))⁻¹ * (τ ^ (2 * p) * (normSq (a • u + τ • ξ))⁻¹ ^ p) = _
    rw [← mul_assoc, inv_mul_cancel₀ hτp.ne', one_mul]
  refine ⟨hint', ?_⟩
  rw [← integral_const_mul]
  have h1 := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn')
  rw [← h1] at hL
  exact (ENNReal.ofReal_le_ofReal_iff (invBd_nonneg hpm)).1 hL

/-- `p = 1`: `τ² E|c + τξ|^{-2} ≤ 1/(n-3)` for `n ≥ 4`. -/
theorem invMoment_one_le {n : ℕ} (hn : 4 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)) ∧
    τ ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n) ≤ 1 / ((n : ℝ) - 3) := by
  have h := invMoment_le (p := 1) (by omega) c hτ
  simp only [pow_one, mul_one, Finset.prod_range_one, Nat.cast_zero, zero_add] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [one_div]
  congr 1
  ring

/-- `p = 2`: `τ⁴ E|c + τξ|^{-4} ≤ 1/((n-3)(n-5))` for `n ≥ 6`. -/
theorem invMoment_two_le {n : ℕ} (hn : 6 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹ ^ 2) (stdGauss (Fin n)) ∧
    τ ^ 4 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n) ≤
      1 / (((n : ℝ) - 3) * ((n : ℝ) - 5)) := by
  have h := invMoment_le (p := 2) (by omega) c hτ
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, zero_add,
    Nat.cast_one, one_mul] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [one_div, mul_inv]
  congr 2 <;> ring

end BstLean.Part153

open BstLean.Part153 in
#print axioms invMoment_le
open BstLean.Part153 in
#print axioms invMoment_one_le
open BstLean.Part153 in
#print axioms invMoment_two_le
open BstLean.Part153 in
#print axioms ae_normSq_ne_zero
