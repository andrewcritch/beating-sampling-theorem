import BstLean.Part48SmallBall
import BstLean.Part62Kappa5
import BstLean.Part62Interp

/-!
# Part 62: an explicit small-ball level (deliverable 2 of `p62-spec`)

`Part48SmallBall.sb_level_exists` gives some `t > 0` with `SBLevel h p t`, through the inexplicit
`fourth_moment` and the hidden constant of `trig_sublevel`. Here the same route
(`Part48SmallBall.rot_smallball`) runs with `Part62Interp.trig_sublevel_explicit` (`C = 4π N N^{1/(2H)}`), `H = max h 1`, `N = 2H + 1`, for any
fourth-moment constant `K` at degree `H`. The level is

  `tK K h p = p^{2H} / (2 (8 K N)^{2H} N)`,

which is `(p/A)^{2H}/2` with `A = 4KC/(2π) = 8 K N^{1 + 1/(2H)}` (omN0-cx §3).

* `sb_level_of_K`: `SBLevel h p (tK K h p)` from `E P⁴ ≤ K (E P²)²` at degree `≤ max h 1`.
* `sb_level_explicit`: `SBLevel h p (tExp h p)`, `tExp h p = tK (Kexp (max h 1)) h p`
  (`Part62HyperK.fourth_moment_explicit`).
* `sb_level_5_4`, `sb_level_5_6`: the levels `tK 5⁸ 4 p` and `tK 5¹² 6 p`
  (`Part62Kappa5`).

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part62

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part48 (SBLevel rot_smallball mean_sq_le)

/-- The small-ball level for a fourth-moment constant `K`:
`p^{2H} / (2 (8 K N)^{2H} N)`, `H = max h 1`, `N = 2H + 1`. -/
noncomputable def tK (K : ℝ) (h : ℕ) (p : ℝ) : ℝ :=
  p ^ (2 * max h 1) /
    (2 * (8 * K * (2 * (max h 1 : ℕ) + 1)) ^ (2 * max h 1) * (2 * (max h 1 : ℕ) + 1))

lemma tK_pos (K : ℝ) (hK : 0 < K) (h : ℕ) (p : ℝ) (hp : 0 < p) : 0 < tK K h p := by
  unfold tK; positivity

/-- **Small-ball level from a fourth-moment constant**. -/
theorem sb_level_of_K (h : ℕ) (K : ℝ) (hK0 : 0 < K)
    (hKm : ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ), P.totalDegree ≤ max h 1 →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        K * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2)
    (p : ℝ) (hp : 0 < p) : SBLevel h p (tK K h p) := by
  set H := max h 1 with hHdef
  have hH : 1 ≤ H := le_max_right _ _
  set N : ℝ := 2 * (H : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  set α : ℝ := (1 : ℝ) / (2 * H) with hα
  set C := 4 * Real.pi * N * N ^ α with hCdef
  have hC : ∀ F : ℝ → ℝ, BstLean.Part48.IsTrig H F → ∀ ε s0 : ℝ, 0 < ε → 0 < |F s0| →
      BstLean.Part48.circ {s | |F s| < ε} ≤
        ENNReal.ofReal (C * (ε / |F s0|) ^ ((1 : ℝ) / (2 * H))) :=
    trig_sublevel_explicit H hH
  set A := 4 * K * C / (2 * Real.pi) with hA
  have hA0 : 0 < A := by rw [hA]; have := Real.pi_pos; positivity
  set t := tK K h p with htdef
  have ht : 0 < t := tK_pos K hK0 h p hp
  -- `2 t = (p / A)^{2H}`
  have hNa : (N ^ α) ^ (2 * H) = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    have : α * ((2 * H : ℕ) : ℝ) = 1 := by
      rw [hα]; push_cast; field_simp
    rw [this, Real.rpow_one]
  have hAe : A = 8 * K * N * N ^ α := by
    rw [hA, hCdef]; field_simp; ring
  have h2t : 2 * t = (p / A) ^ (2 * H) := by
    have e1 : tK K h p = p ^ (2 * H) / (2 * (8 * K * N) ^ (2 * H) * N) := by
      rw [tK, ← hHdef, hN]
    have e2 : (8 * K * N * N ^ α) ^ (2 * H) = (8 * K * N) ^ (2 * H) * N := by
      rw [mul_pow, hNa]
    rw [htdef, e1, div_pow, hAe, e2]
    have hKN : 0 < (8 * K * N) ^ (2 * H) := by positivity
    field_simp
  intro ι _ P hdeg hnn
  have hdegH : P.totalDegree ≤ H := hdeg.trans (le_max_left _ _)
  have key := rot_smallball H hH C K hC P hdegH (hKm ι P hdegH) t ht
  have hEP : ∫ z, MvPolynomial.eval z P ∂stdGauss ι ≤
      Real.sqrt (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (mean_sq_le P))
  refine le_trans (measure_mono ?_) (key.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [abs_of_nonneg (hnn z)]
    exact lt_of_lt_of_le hz (mul_le_mul_of_nonneg_left hEP ht.le)
  · rw [h2t]
    have hH0 : (2 * H : ℕ) ≠ 0 := by omega
    have h2 : ((p / A) ^ (2 * H)) ^ ((1 : ℝ) / (2 * H)) = p / A := by
      rw [show ((1 : ℝ) / (2 * H)) = ((2 * H : ℕ) : ℝ)⁻¹ by push_cast; ring]
      exact Real.pow_rpow_inv_natCast (by positivity) hH0
    rw [h2, ← hA]
    rw [mul_div_cancel₀ _ hA0.ne']

/-- The explicit general small-ball level `tExp h p = tK (Kexp H) h p`, `H = max h 1`. -/
noncomputable def tExp (h : ℕ) (p : ℝ) : ℝ := tK (Kexp (max h 1)) h p

lemma tExp_pos (h : ℕ) (p : ℝ) (hp : 0 < p) : 0 < tExp h p :=
  tK_pos _ (Kexp_pos _) h p hp

/-- **Explicit small-ball level** (deliverable 2): `SBLevel h p (tExp h p)`. -/
theorem sb_level_explicit (h : ℕ) (p : ℝ) (hp : 0 < p) : SBLevel h p (tExp h p) :=
  sb_level_of_K h _ (Kexp_pos _) (fourth_moment_explicit (max h 1)) p hp

/-- The level at degree `4` with `K = 5⁸`. -/
theorem sb_level_5_4 (p : ℝ) (hp : 0 < p) : SBLevel 4 p (tK (5 ^ 8) 4 p) :=
  sb_level_of_K 4 _ (by norm_num) fourth_moment_5_4 p hp

/-- The level at degree `6` with `K = 5¹²`. -/
theorem sb_level_5_6 (p : ℝ) (hp : 0 < p) : SBLevel 6 p (tK (5 ^ 12) 6 p) :=
  sb_level_of_K 6 _ (by norm_num) fourth_moment_5_6 p hp

end BstLean.Part62
