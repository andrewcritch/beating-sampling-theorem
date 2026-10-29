import BstLean.Part72Cor
import BstLean.Part72Tilt

/-!
# Part 72: Theorem 4 under the overlap conditions, and for rank-one tilts below `n/2`

* `part72_ov` (**Theorem 4-OV**, omOV-opus §2): Theorem 4's conclusion for every `μ` carried by
  the sphere with `Mean μ ≤ A/n`, directional second moments `E_μ (v·x)² ≤ A/n` for every unit
  `v`, and the trace moments `E_μ δ°^{2i} ≤ w(i)·d^{2i}/n^{2i}` for `1 ≤ i`, `2i ≤ k`.
  Every `d ≥ 1` and `k ≥ 1`. No feature-operator inequality and no fourth-moment lemma is used.
* `part72_rank1`: Theorem 4's conclusion, with one program and one threshold, for every rank-one
  tilt `D_{t,v} ∝ exp(t(v·x)²)` with `|v| = 1` and `0 ≤ t ≤ τn`, for a fixed `0 ≤ τ < 1/2`.
  Every `d ≥ 1` and `k ≥ 1`. This covers the band `t ∈ [n/8, n/2)` that Part 71 left open.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part59
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono heavyCount phiSq)
open BstLean.Part53 (c0)

/-- The overlap conditions (omOV-opus `OV`, with directional second moments in place of the
Frobenius norm of the covariance). -/
def OVcond (n : ℕ) (μ : Measure (Fin n → ℝ)) (d k : ℕ) (w : ℕ → ℝ) (A : ℝ) : Prop :=
  SphLaw n μ ∧ Mean μ ≤ A / n ∧
  (∀ v : Fin n → ℝ, ∑ i, v i ^ 2 = 1 → ∫ x, (∑ i, v i * x i) ^ 2 ∂μ ≤ A / n) ∧
  ∀ i : ℕ, 1 ≤ i → 2 * i ≤ k →
    (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤ w i * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i)

/-- **Theorem 4-OV.** -/
theorem part72_ov (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (w : ℕ → ℝ) (A ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : 0 ≤ A) (hε : 0 < ε) :
    100 ≤ N72 d k w (Fov d A) A ε ∧ ∀ n : ℕ, N72 d k w (Fov d A) A ε ≤ n →
      ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), OVcond n μ d k w A →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  obtain ⟨h100, h⟩ := part72_general k d hd hk w (Fov d A) A ε hw hA hε
  refine ⟨h100, fun n hn => ?_⟩
  obtain ⟨pg, h1, h2, h3, h4, h5⟩ := h n hn
  exact ⟨pg, h1, h2, h3, h4, fun μ ⟨hs, hm, hdir, hdev⟩ =>
    h5 μ (good_of_ov hs d k hd w A hm hdir hdev)⟩

/-- **Theorem 4 for rank-one tilts below the critical point.** For `0 ≤ τ < 1/2`, one program
`g₀` and one threshold `N72 d k (wR τ) (Fov d (AR τ)) (AR τ) ε` serve every unit `v` and every
`t ∈ [0, τn]`. -/
theorem part72_rank1 (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (τ ε : ℝ) (hτ0 : 0 ≤ τ)
    (hτ : τ < 1 / 2) (hε : 0 < ε) :
    100 ≤ N72 d k (wR τ) (Fov d (AR τ)) (AR τ) ε ∧
      ∀ n : ℕ, N72 d k (wR τ) (Fov d (AR τ)) (AR τ) ε ≤ n →
      ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ v : Fin n → ℝ, ∑ i, v i ^ 2 = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ τ * n →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP (r1Tilt n v t) k c (unitOfD Z) <
              (BP (r1Tilt n v t) k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  obtain ⟨h100, h⟩ := part72_general k d hd hk (wR τ) (Fov d (AR τ)) (AR τ) ε (wR_nonneg hτ)
    (AR_nonneg τ) hε
  refine ⟨h100, fun n hn => ?_⟩
  obtain ⟨pg, h1, h2, h3, h4, h5⟩ := h n hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) (h100.trans hn)
  exact ⟨pg, h1, h2, h3, h4, fun v hv t ht0 ht =>
    h5 _ (r1_good hn1 d k hd v hv hτ0 hτ ht0 ht)⟩

end BstLean.Part72
