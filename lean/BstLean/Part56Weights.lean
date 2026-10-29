import BstLean.Part56Defs

/-!
# Part 56, wave 1: the weight form equals the heat form (Wick expansion, algebra)

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56Weights`). Status: proved (no `sorry`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route: expand `fvA k (heatA k a A) y = Σ_c Σ_{i} (a/2)^i/i! (c+2i)!/c! (tr^i A_{c+2i})[y^c]`,
re-index by `i_tot = c + 2l` (coefficient `a^l · wickC i_tot l`), expand `y = μ_x = Σ_j β_j(x) u_j`
multilinearly in `contr`, take `a = σ² τ(x)`, and integrate in `x` (all integrands are continuous, `μ`
is carried by the sphere). Only the identity of finite sums and the linearity of the integral are
needed; no Gaussian fact is used.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob Tens TSymm Pn NN baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (LemmaR53 GaussPolar53)
open BstLean.Part48 (SBLevel)

open BstLean.Part41 (phiM contr trL)
open BstLean.Part53 (fvA heatA)

section
variable {n : ℕ}
theorem contr_expand (d m : ℕ) (B : (Fin m → Fin n) → ℝ) (b : ℕ → ℝ) (u : ℕ → Fin n → ℝ) :
    contr B (fun _ => ∑ j ∈ Finset.range (d + 1), b j • u j) =
      ∑ jv : Fin m → Fin (d + 1), (∏ r, b (jv r)) * contr B (fun r => u (jv r)) := by
  unfold contr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ∀ t : Fin m, (∑ j ∈ Finset.range (d + 1), b j • u j) (w t) =
      ∑ j : Fin (d + 1), b j * u j (w t) := by
    intro t
    rw [Finset.sum_apply, ← Fin.sum_univ_eq_sum_range (fun j => (b j • u j) (w t))]
    rfl
  simp only [this]
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun jv _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem contr_cast (m c : ℕ) (h : m = c) (B : (Fin m → Fin n) → ℝ) (hp : ∀ t : Fin m, t.1 < c)
    (y : Fin n → ℝ) :
    contr (fun w : Fin c → Fin n => B (fun t => w ⟨t.1, hp t⟩)) (fun _ => y) = contr B (fun _ => y) := by
  subst h; rfl

theorem contr_lin {m : ℕ} {ι : Type*} (s : Finset ι) (a : ι → ℝ) (B : ι → (Fin m → Fin n) → ℝ)
    (v : Fin m → Fin n → ℝ) :
    contr (fun w => ∑ i ∈ s, a i * B i w) v = ∑ i ∈ s, a i * contr (B i) v := by
  unfold contr
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by ring

theorem shift_sum (k l : ℕ) (F : ℕ → ℝ) :
    ∑ c ∈ Finset.range (k + 1), (if c + 2 * l ≤ k then F (c + 2 * l) else 0) =
      ∑ i ∈ Finset.range (k + 1), (if 2 * l ≤ i then F i else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have : (Finset.range (k + 1)).filter (fun i => 2 * l ≤ i) =
      ((Finset.range (k + 1)).filter (fun c => c + 2 * l ≤ k)).map (addRightEmbedding (2 * l)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, addRightEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨i - 2 * l, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩; omega
  rw [this, Finset.sum_map]
  rfl

theorem wickC_coef (a : ℝ) (c l : ℕ) :
    (a / 2) ^ l / (l.factorial : ℝ) * (((c + 2 * l).factorial : ℝ) / (c.factorial : ℝ)) =
      wickC (c + 2 * l) l * a ^ l := by
  unfold wickC
  rw [show c + 2 * l - 2 * l = c by omega]
  have h1 : (0 : ℝ) < l.factorial := by positivity
  have h2 : (0 : ℝ) < c.factorial := by positivity
  field_simp
  rw [← mul_pow, div_mul_cancel₀ a two_ne_zero]

theorem contr_heat (k : ℕ) (a : ℝ) (A : Tens n) (c : ℕ) (y : Fin n → ℝ) :
    contr (heatA k a A c) (fun _ => y) =
      ∑ l ∈ (Finset.range (k + 1)).filter (fun l => c + 2 * l ≤ k),
        wickC (c + 2 * l) l * a ^ l * contr (trL l (A (c + 2 * l))) (fun _ => y) := by
  have h := contr_lin ((Finset.range (k + 1)).filter (fun l => c + 2 * l ≤ k))
    (fun i => (a / 2) ^ i / (i.factorial : ℝ) * (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ)))
    (fun i (w : Fin c → Fin n) => trL i (A (c + 2 * i)) (fun t => w ⟨t.1, by have := t.2; omega⟩))
    (fun _ => y)
  unfold heatA
  refine h.trans (Finset.sum_congr rfl fun l _ => ?_)
  rw [wickC_coef, contr_cast (c + 2 * l - 2 * l) c (by omega)]

theorem pointwise56 (k d : ℕ) (A : Tens n) (a : ℝ) (b : ℕ → ℝ) (u : ℕ → Fin n → ℝ) :
    ∑ κ : KeyRK k d, (if 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) then
      wickC κ.1.1 κ.1.2 * a ^ (κ.1.2 : ℕ) *
        ((∏ r, b (κ.2 r)) * contr (trL (κ.1.2 : ℕ) (A κ.1.1)) (fun r => u (κ.2 r))) else 0) =
      fvA k (heatA k a A) (∑ j ∈ Finset.range (d + 1), b j • u j) := by
  set y := ∑ j ∈ Finset.range (d + 1), b j • u j with hy
  set G : ℕ → ℕ → ℝ := fun i l => wickC i l * a ^ l * contr (trL l (A i)) (fun _ => y) with hG
  have hL : ∀ il : Fin (k + 1) × Fin (k + 1),
      ∑ jv : Fin ((il.1 : ℕ) - 2 * (il.2 : ℕ)) → Fin (d + 1),
        (if 2 * (il.2 : ℕ) ≤ (il.1 : ℕ) then
          wickC il.1 il.2 * a ^ (il.2 : ℕ) *
            ((∏ r, b (jv r)) * contr (trL (il.2 : ℕ) (A il.1)) (fun r => u (jv r))) else 0) =
        if 2 * (il.2 : ℕ) ≤ (il.1 : ℕ) then G il.1 il.2 else 0 := by
    intro il
    split_ifs with h
    · rw [← Finset.mul_sum, hG]
      simp only
      rw [hy, contr_expand]
    · simp
  rw [Fintype.sum_sigma]
  simp only [hL]
  rw [Fintype.sum_prod_type]
  have e : ∀ F : ℕ → ℕ → ℝ, ∑ i : Fin (k + 1), ∑ l : Fin (k + 1), F i l =
      ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1), F i l := by
    intro F
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ l : Fin (k + 1), F i l)]
    exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (fun l => F i l) _
  refine (e (fun i l => if 2 * l ≤ i then G i l else 0)).trans ?_
  rw [Finset.sum_comm]
  unfold fvA
  simp only [contr_heat]
  simp only [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact (shift_sum k l (fun i => G i l)).symm

theorem integrable_cont_sph56 {μ : Measure (Fin n → ℝ)} (hμ : BstLean.Part40.SphLaw n μ)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f μ := by
  have := hμ.prob
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℝ) 1).exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [hμ.sphere] with x hx
  apply hC
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, Real.sqrt_le_one]
  rw [← hx]
  exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem continuous_phiM56 {d : ℕ} (p : Mono n d) : Continuous fun x : Fin n → ℝ => phiM x p := by
  unfold phiM BstLean.Part36.monoVal
  exact continuous_multiset_prod _ fun i _ => continuous_apply i

theorem continuous_kJ56 (d j : ℕ) {f g : (Fin n → ℝ) → (Fin n → ℝ)} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => kJ d j (f x) (g x) := by
  unfold kJ phiB
  refine continuous_finsetSum _ fun p _ => ?_
  split_ifs
  · exact ((continuous_phiM56 p).comp hf).mul ((continuous_phiM56 p).comp hg)
  · simp only [mul_zero]; exact continuous_const

theorem continuous_tauR56 (d : ℕ) (v : Fin n → ℝ) : Continuous fun x => tauR d v x := by
  unfold tauR KR
  refine continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun x : Fin n → ℝ => kJ d j x x :=
    continuous_kJ56 d j (f := id) (g := id) continuous_id continuous_id
  have h2 : Continuous fun x : Fin n → ℝ => kJ d j x v :=
    continuous_kJ56 d j (f := id) (g := fun _ => v) continuous_id continuous_const
  exact h1.sub ((h2.mul h2).div_const _)

theorem continuous_betaJ56 (d j : ℕ) (v : Fin n → ℝ) : Continuous fun x => betaJ d j v x := by
  unfold betaJ
  exact (continuous_kJ56 d j (f := id) (g := fun _ => v) continuous_id continuous_const).div_const _

/-- **Weights.** -/
theorem propWeights56 (d k : ℕ) : PropWeights56 d k := by
  intro n μ hμ v hv f0 T hT M
  set A := BstLean.Part53.TF k f0 T
  set s2 := BstLean.Part53.sg n d ^ 2
  have hint : ∀ κ : KeyRK k d, Integrable (fun x => tauR d v x ^ (κ.1.2 : ℕ) *
      ∏ r, betaJ d (κ.2 r) v x) μ := fun κ =>
    integrable_cont_sph56 hμ (((continuous_tauR56 d v).pow _).mul
      (continuous_finsetProd _ fun r _ => continuous_betaJ56 d _ v))
  unfold gLineH mux
  have hpt : ∀ x, fvA k (heatA k (s2 * tauR d v x) A)
      (∑ j ∈ Finset.range (d + 1), betaJ d j v x • ancRK M v j) =
      ∑ κ : KeyRK k d, (if 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) then
        wickC κ.1.1 κ.1.2 * (s2 * tauR d v x) ^ (κ.1.2 : ℕ) *
        ((∏ r, betaJ d (κ.2 r) v x) * contr (trL (κ.1.2 : ℕ) (A κ.1.1))
          (fun r => ancRK M v (κ.2 r))) else 0) :=
    fun x => (pointwise56 k d A _ (fun j => betaJ d j v x) (fun j => ancRK M v j)).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum _ (fun κ _ => ?_)]
  · unfold gLineW gW
    refine Finset.sum_congr rfl fun κ _ => ?_
    split_ifs with h
    · unfold wRK
      have : (fun x => wickC κ.1.1 κ.1.2 * (s2 * tauR d v x) ^ (κ.1.2 : ℕ) *
          ((∏ r, betaJ d (κ.2 r) v x) * contr (trL (κ.1.2 : ℕ) (A κ.1.1)) (fun r => ancRK M v (κ.2 r)))) =
          fun x => (wickC κ.1.1 κ.1.2 * s2 ^ (κ.1.2 : ℕ) *
            contr (trL (κ.1.2 : ℕ) (A κ.1.1)) (fun r => ancRK M v (κ.2 r))) *
            (tauR d v x ^ (κ.1.2 : ℕ) * ∏ r, betaJ d (κ.2 r) v x) := by
        funext x; rw [mul_pow]; ring
      rw [this, integral_const_mul]
      ring
    · simp
  · split_ifs
    · have : (fun x => wickC κ.1.1 κ.1.2 * (s2 * tauR d v x) ^ (κ.1.2 : ℕ) *
          ((∏ r, betaJ d (κ.2 r) v x) * contr (trL (κ.1.2 : ℕ) (A κ.1.1)) (fun r => ancRK M v (κ.2 r)))) =
          fun x => (wickC κ.1.1 κ.1.2 * s2 ^ (κ.1.2 : ℕ) *
            contr (trL (κ.1.2 : ℕ) (A κ.1.1)) (fun r => ancRK M v (κ.2 r))) *
            (tauR d v x ^ (κ.1.2 : ℕ) * ∏ r, betaJ d (κ.2 r) v x) := by
        funext x; rw [mul_pow]; ring
      rw [this]
      exact (hint κ).const_mul _
    · exact integrable_zero _ _ _

end

end BstLean.Part56
