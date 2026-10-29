import BstLean.Part39Defs

/-!
# Part 39 Theorem B, wave 0: frozen definitions for a single Bingham spike with `lam > n^{3/2}`

Paper: Lemma BR of `delegations/answers/omBR-opus-prover.md` (the Taylor law `Q_N`) and Theorem B
of `proofs/option-m/39-explicit-22-bingham-spike.tex`. Specification:
`delegations/answers/p39b-spec-opus.md`. This file holds definitions only. Provers must not edit
it, and must not use `native_decide` anywhere.

Conventions (as in `Part39Defs`).
* `θ = lam · e₁` is `spikeθ lam`; `t = tperp x = Σ_{i ≠ 0} xᵢ²`; `D = bingham n (spikeθ lam)`.
* `cBR lam k` are the Taylor coefficients of `e^{G(t)}`, `G(t) = lam(−t − log(1 − t))`:
  `c₀ = 1`, `c₁ = 0`, `c_{k+2} = ((k+1) c_{k+1} + lam c_k)/(k+2)`.
* `QN lam N t = Σ_{k ≤ N} c_k t^k`. The Taylor law `brLaw n lam N` has density proportional to
  `brPhi lam N (tperp x) = (1 − t)^lam · Q_N(t)` (real power) with respect to `uniformSphere n`.
  Its `t`-density is `∝ t^β (1−t)^{lam − 1/2} Q_N(t)`, `β = (n−3)/2`.
* The program computes `τ_k = S_k/S₀`, `S_k = Σ_{i ≤ N} c_i R_{i+k}`,
  `R_j = ∏_{r<j} ((n−1)/2 + r)/(lam + n/2 + r)` (`tau1B`, `tau2B`).
* The precision is `NBR n ε`: the least `N` with `(8/7)(3/2)^{n−1}(1001/1000) ≤ (2^N η*)²`,
  `η* = min(ε²/2600, 1/1000)`. This rational test replaces the paper's
  `N = ⌈0.585(n−1)/2 + log₂(1/η*) + 0.1⌉`; the paper's `N` passes the test, so `NBR` is never
  larger.
* The route gate is the paper's: the series route of Theorem A (`gOf39`) when
  `lam ≤ 64 log(73/ε)`, the Taylor route otherwise.
* The Taylor route's moment cost is `CBR N = 15N + 7` (instrumented count of the prover).
-/

namespace BstLean.Part39

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (CoefIdx uniformSphere)
open BstLean.Part37 (EofB)

variable {n : ℕ}

/-! ## §1 The Taylor coefficients and the law -/

/-- `c_k`: the Taylor coefficients of `e^{G}`, `G(t) = lam Σ_{k ≥ 2} t^k/k`. -/
noncomputable def cBR (lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | (k + 2) => (((k : ℝ) + 1) * cBR lam (k + 1) + lam * cBR lam k) / ((k : ℝ) + 2)

/-- `Q_N(t) = Σ_{k ≤ N} c_k t^k`. -/
noncomputable def QN (lam : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), cBR lam k * t ^ k

/-- `G(t) = lam (−t − log(1 − t))`, so `e^{−lam t} = (1 − t)^lam e^{G(t)}` on `[0, 1)`. -/
noncomputable def Gfun (lam t : ℝ) : ℝ := lam * (-t - Real.log (1 - t))

/-- The `t`-profile of the Taylor law: `(1 − t)^lam · Q_N(t)` (real power `Real.rpow`). -/
noncomputable def brPhi (lam : ℝ) (N : ℕ) (t : ℝ) : ℝ := (1 - t) ^ lam * QN lam N t

/-- The law with density `φ(t)/E_U φ(t)` with respect to `uniformSphere n`. -/
noncomputable def tLaw (n : ℕ) (φ : ℝ → ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity
    (fun x => ENNReal.ofReal (φ (tperp x) / ∫ y, φ (tperp y) ∂uniformSphere n))

/-- The `t`-density of `uniformSphere n`, up to a constant: `t^{(n−3)/2} (1 − t)^{−1/2}` on `(0, 1)`. -/
noncomputable def wB (n : ℕ) (t : ℝ) : ℝ := t ^ (((n : ℝ) - 3) / 2) * (1 - t) ^ (-(1 / 2 : ℝ))

/-- `Z_BR = E_U brPhi(t)`. -/
noncomputable def ZBR (n : ℕ) (lam : ℝ) (N : ℕ) : ℝ :=
  ∫ x, brPhi lam N (tperp x) ∂uniformSphere n

/-- The Taylor law `D_BR` of Lemma BR. -/
noncomputable def brLaw (n : ℕ) (lam : ℝ) (N : ℕ) : Measure (Fin n → ℝ) := tLaw n (brPhi lam N)

/-! ## §2 The program's moment computation (Taylor route) -/

/-- `R_j = ∏_{r<j} ((n−1)/2 + r)/(lam + n/2 + r) = B(β+1+j, lam+1/2)/B(β+1, lam+1/2)`. -/
noncomputable def RBR (n : ℕ) (lam : ℝ) (j : ℕ) : ℝ :=
  ∏ r ∈ Finset.range j, ((((n : ℝ) - 1) / 2 + r) / (lam + (n : ℝ) / 2 + r))

/-- `S_k = Σ_{i ≤ N} c_i R_{i+k}`. -/
noncomputable def SBR (n N : ℕ) (lam : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), cBR lam i * RBR n lam (i + k)

/-- `τ₁ = S₁/S₀`, as the program computes it. -/
noncomputable def tau1B (n N : ℕ) (lam : ℝ) : ℝ := SBR n N lam 1 / SBR n N lam 0

/-- `τ₂ = S₂/S₀`, as the program computes it. -/
noncomputable def tau2B (n N : ℕ) (lam : ℝ) : ℝ := SBR n N lam 2 / SBR n N lam 0

/-! ## §3 The precision, the gate and the cost -/

/-- `η* = min(ε²/2600, 1/1000)`. -/
noncomputable def etaStar (ε : ℝ) : ℝ := min (ε ^ 2 / 2600) (1 / 1000)

/-- The rational test on `N`: `(8/7)(3/2)^{n−1}(1001/1000) ≤ (2^N η*)²`. -/
def NTest (n : ℕ) (ε : ℝ) (N : ℕ) : Prop :=
  8 / 7 * (3 / 2 : ℝ) ^ (n - 1) * (1001 / 1000) ≤ ((2 : ℝ) ^ N * etaStar ε) ^ 2

/-- The program's `N`: the least `N` that passes `NTest` (`0` if there is none). -/
noncomputable def NBR (n : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if h : ∃ N : ℕ, NTest n ε N then Nat.find h else 0

/-- The gate: the series route of Theorem A when `lam ≤ 64 log(73/ε)`. -/
def SeriesGate (lam ε : ℝ) : Prop := lam ≤ 64 * Real.log (73 / ε)

/-- The counted cost of the Taylor-route moments: `15N + 7`. -/
noncomputable def CBR (N : ℝ) : ℝ := 15 * N + 7

/-! ## §4 The program of Theorem B and its cost -/

/-- The program for `lam > n^{3/2}`: Theorem A's program `gOf39` on the series route; on the Taylor
  route, E if `ε² < h²`, `H_S` if `h² ≤ ε² < u²`, `U_S` otherwise, at `τ₁, τ₂` of `brLaw` with
  `N = NBR n ε`. -/
noncomputable def gOf39B (lam δ ε : ℝ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (M : CoefIdx n → ℝ) : ℝ := by
  classical
  exact if SeriesGate lam ε then gOf39 lam δ ε f0 g F M
  else if ε ^ 2 < hSq39 n δ then
    EofB f0 g F M (muS n (tau1B n (NBR n ε) lam) (tau2B n (NBR n ε) lam))
      (WS n (tau1B n (NBR n ε) lam) (tau2B n (NBR n ε) lam))
  else if ε ^ 2 < uSq39 n δ then
    HofS f0 g F M (tau1B n (NBR n ε) lam) (tau2B n (NBR n ε) lam)
  else UofS f0 g F M (tau1B n (NBR n ε) lam) (tau2B n (NBR n ε) lam)

/-- The cost of the branch the program takes, moments included. -/
noncomputable def costOf39B (n : ℕ) (lam δ ε : ℝ) : ℝ := by
  classical
  exact if SeriesGate lam ε then costOf39 n lam δ ε
  else if ε ^ 2 < hSq39 n δ then CE39 n + CBR (NBR n ε)
  else if ε ^ 2 < uSq39 n δ then CH39 n + CBR (NBR n ε)
  else CU39 n + CBR (NBR n ε)

/-- The program for every `lam ≥ 0`: Theorem A's when `lam² ≤ n³`, Theorem B's otherwise. -/
noncomputable def gAll39 (lam δ ε : ℝ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (M : CoefIdx n → ℝ) : ℝ := by
  classical
  exact if lam ^ 2 ≤ (n : ℝ) ^ 3 then gOf39 lam δ ε f0 g F M else gOf39B lam δ ε f0 g F M

/-- The cost of `gAll39`. -/
noncomputable def costAll39 (n : ℕ) (lam δ ε : ℝ) : ℝ := by
  classical
  exact if lam ^ 2 ≤ (n : ℝ) ^ 3 then costOf39 n lam δ ε else costOf39B n lam δ ε

end BstLean.Part39
