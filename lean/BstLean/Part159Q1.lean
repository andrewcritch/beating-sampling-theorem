import BstLean.Part159CN

/-!
# Part 159 (file `Q1`): `E_u κ(u₁) = 2N·c_N²`, and the size of `2N·c_N²`

Role: `delegations/statements/p159-spec.md`, item 3 (toward `ConstK`). Do not use `sorry`,
`native_decide` or `axiom`.

`q₁ = q1 (e0 N) = E_u κ(u₁)` (Part 137) is the argument of `κ₁ = kap1 N = κ(q₁)`. The paper's
program uses `r̃ = 2N·c̃_N²`.

* **`q1_eq_cN`**: `q₁ = 2N·c_N²` for every `N ≥ 1` (from two `L²` bounds of Parts 137 and 140 that
  hold for every width `m`: the difference is a constant bounded by `C/√m` for every `m`).
* `radI_logconvex`: `radI (M+1)² ≤ radI M·radI (M+2)`.
* `cN_mul_succ`: `c_{M+1}·c_{M+2} = 1/(2π(M+1))`; `cN_antitone`: `c_{M+2} ≤ c_{M+1}`.
* **`rN_window`**: `1/π ≤ 2N·c_N² ≤ N/(π(N − 1))` for `N ≥ 2`.
-/

namespace BstLean.Part159

open MeasureTheory Real
open BstLean.Part29 (uniformSphere)
open BstLean.Part130
open BstLean.Part133 (L2le)
open BstLean.Part137 (cN q1 GamS GamS_L2x h1bar)
open BstLean.Part140 (h1bar_L2)
open BstLean.Part141 (cN_nonneg normSq_h1bar GamS_rowS rowS)

/-- A constant function with an `L²` bound on a probability space. -/
lemma const_of_L2le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {K a : ℝ} (h : L2le μ (fun _ : Ω => K) a) : K ^ 2 ≤ a ^ 2 := by
  have := h.le
  simpa using this

/-- **`E_u κ(u₁) = 2N·c_N²`.** -/
theorem q1_eq_cN {N : ℕ} (hN : 1 ≤ N) : q1 (e0 N) = 2 * (N : ℝ) * cN N ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 2 / (N : ℝ) := ⟨_, rfl⟩
  have hγpos : 0 < γ := by rw [hγ]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 * (N : ℝ) * cN N ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = R * γ - γ * q1 (e0 N) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = γ ^ 2 * (1 + 2 / (N : ℝ)) + 4 * (R * γ) ^ 2 / (N : ℝ) :=
    ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have key : ∀ m : ℕ, 1 ≤ m → K ^ 2 ≤ D / (m : ℝ) := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have A := h1bar_L2 (N := N) (m := m) hN hm
    have B := ((GamS_L2x (N := N) (m := m) hN hm).const_mul_nonneg hR0).neg
    have C := A.add' B (by positivity) (by positivity)
    have hfun : ∀ M₁ : Matrix (Fin m) (Fin N) ℝ,
        (2 / (m : ℝ) * normSq (h1bar M₁) - 2 / (N : ℝ) * q1 (e0 N)) +
          -(R * (GamS M₁ - 2 / (N : ℝ))) = K := by
      intro M₁
      rw [normSq_h1bar hN, GamS_rowS hN hm, hK, hR, hγ]
      field_simp
      ring
    have C' := C.congr_fun hfun
    have h1 := const_of_L2le C'
    refine h1.trans ?_
    obtain ⟨s1, hs1⟩ : ∃ s1 : ℝ, s1 = √((1 + 2 / (N : ℝ)) / (2 * m)) := ⟨_, rfl⟩
    obtain ⟨s2, hs2⟩ : ∃ s2 : ℝ, s2 = √(2 / ((N : ℝ) * m)) := ⟨_, rfl⟩
    have e1 : s1 ^ 2 = (1 + 2 / (N : ℝ)) / (2 * m) := by
      rw [hs1]; exact Real.sq_sqrt (by positivity)
    have e2 : s2 ^ 2 = 2 / ((N : ℝ) * m) := by
      rw [hs2]; exact Real.sq_sqrt (by positivity)
    rw [← hs1, ← hs2, ← hγ]
    have h2 : (γ * s1 + R * (γ * s2)) ^ 2 ≤ 2 * γ ^ 2 * s1 ^ 2 + 2 * R ^ 2 * γ ^ 2 * s2 ^ 2 := by
      nlinarith [sq_nonneg (γ * s1 - R * (γ * s2))]
    refine h2.trans (le_of_eq ?_)
    rw [e1, e2, hD]
    field_simp
    ring
  have hK0 : K = 0 := by
    by_contra hne
    have hK2 : 0 < K ^ 2 := by positivity
    obtain ⟨m, hm⟩ := exists_nat_gt (D / K ^ 2 + 1)
    have hm1 : 1 ≤ m := by
      have : (1 : ℝ) < m := by
        have : 0 ≤ D / K ^ 2 := by positivity
        linarith
      exact_mod_cast this.le
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have h := key m hm1
    rw [le_div_iff₀ hmpos] at h
    have h3 : D / K ^ 2 < m := by linarith
    rw [div_lt_iff₀ hK2] at h3
    nlinarith
  have h4 : γ * (R - q1 (e0 N)) = 0 := by rw [← hK0, hK]; ring
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h hγpos.ne'
  · linarith

/-! ## The size of `2N·c_N²` -/

lemma radI_integrable (p : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ p * Real.exp (-r ^ 2 / 2)) (Set.Ioi 0) := by
  by_contra h
  have h0 : radI p = 0 := integral_undef h
  exact (radI_pos p).ne' h0

/-- `radI (M+1)² ≤ radI M·radI (M+2)`. -/
theorem radI_logconvex (M : ℕ) : radI (M + 1) ^ 2 ≤ radI M * radI (M + 2) := by
  have hR0 := radI_pos M
  set lam : ℝ := radI (M + 1) / radI M with hlam
  have i0 := radI_integrable M
  have i1 := radI_integrable (M + 1)
  have i2 := radI_integrable (M + 2)
  have hnn : 0 ≤ ∫ r in Set.Ioi (0 : ℝ), (r ^ (M + 2) * Real.exp (-r ^ 2 / 2) -
      2 * lam * (r ^ (M + 1) * Real.exp (-r ^ 2 / 2)) +
      lam ^ 2 * (r ^ M * Real.exp (-r ^ 2 / 2))) := by
    refine setIntegral_nonneg measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    have e : r ^ (M + 2) * Real.exp (-r ^ 2 / 2) -
        2 * lam * (r ^ (M + 1) * Real.exp (-r ^ 2 / 2)) +
        lam ^ 2 * (r ^ M * Real.exp (-r ^ 2 / 2)) =
        r ^ M * (r - lam) ^ 2 * Real.exp (-r ^ 2 / 2) := by ring
    rw [e]
    positivity
  have hs1 := integral_sub i2 (i1.const_mul (2 * lam))
  rw [integral_const_mul] at hs1
  have hs2 := integral_add (i2.sub (i1.const_mul (2 * lam))) (i0.const_mul (lam ^ 2))
  rw [integral_const_mul] at hs2
  have hsplit : ∫ r in Set.Ioi (0 : ℝ), (r ^ (M + 2) * Real.exp (-r ^ 2 / 2) -
      2 * lam * (r ^ (M + 1) * Real.exp (-r ^ 2 / 2)) +
      lam ^ 2 * (r ^ M * Real.exp (-r ^ 2 / 2))) =
      radI (M + 2) - 2 * lam * radI (M + 1) + lam ^ 2 * radI M := by
    unfold radI
    rw [← hs1]
    exact hs2
  rw [hsplit] at hnn
  have e2 : radI (M + 2) - 2 * lam * radI (M + 1) + lam ^ 2 * radI M =
      radI (M + 2) - radI (M + 1) ^ 2 / radI M := by
    rw [hlam]
    field_simp
    ring
  rw [e2] at hnn
  have h3 : radI (M + 1) ^ 2 / radI M ≤ radI (M + 2) := by linarith
  rw [div_le_iff₀ hR0] at h3
  linarith

/-- `c_{M+1}·c_{M+2} = 1/(2π(M+1))`. -/
theorem cN_mul_succ (M : ℕ) : cN (M + 1) * cN (M + 2) = 1 / (2 * π * ((M : ℝ) + 1)) := by
  have hA : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have hA2 : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have h0 := radI_pos M
  have h1 := radI_pos (M + 1)
  rw [cN_radial M, show M + 2 = (M + 1) + 1 by ring, cN_radial (M + 1),
    show M + 1 + 1 = M + 2 by ring, radI_step M]
  have e : radI M / (√(2 * π) * radI (M + 1)) *
      (radI (M + 1) / (√(2 * π) * (((M : ℝ) + 1) * radI M))) =
      1 / (√(2 * π) ^ 2 * ((M : ℝ) + 1)) := by
    field_simp
  rw [e, hA2]

/-- `c_{M+2} ≤ c_{M+1}`. -/
theorem cN_antitone (M : ℕ) : cN (M + 2) ≤ cN (M + 1) := by
  have hA : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have h0 := radI_pos M
  have h1 := radI_pos (M + 1)
  have h2 := radI_pos (M + 2)
  have hl := radI_logconvex M
  rw [show M + 2 = (M + 1) + 1 by ring, cN_radial (M + 1), cN_radial M,
    show M + 1 + 1 = M + 2 by ring, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The size of `c_N²`**: `1/(2πN) ≤ c_N² ≤ 1/(2π(N − 1))` for `N ≥ 2`. -/
theorem cN_sq_window {N : ℕ} (hN : 2 ≤ N) :
    1 / (2 * π * (N : ℝ)) ≤ cN N ^ 2 ∧ cN N ^ 2 ≤ 1 / (2 * π * ((N : ℝ) - 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hpi := Real.pi_pos
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hc1 := cN_nonneg (M + 1)
  have hc2 := cN_nonneg (M + 2)
  have hc3 := cN_nonneg (M + 3)
  have a1 := cN_mul_succ M
  have a2 := cN_mul_succ (M + 1)
  have b1 := cN_antitone M
  have b2 := cN_antitone (M + 1)
  rw [show M + 1 + 1 = M + 2 by ring, show M + 1 + 2 = M + 3 by ring] at a2 b2
  push_cast at a2 ⊢
  constructor
  · have e : 2 * π * ((M : ℝ) + 2) = 2 * π * ((M : ℝ) + 1 + 1) := by ring
    rw [e, ← a2]
    nlinarith
  · have e : (M : ℝ) + 2 - 1 = (M : ℝ) + 1 := by ring
    rw [e, ← a1]
    nlinarith

/-- **The size of `2N·c_N²`**: `1/π ≤ 2N·c_N² ≤ N/(π(N − 1))` for `N ≥ 2`. -/
theorem rN_window {N : ℕ} (hN : 2 ≤ N) :
    1 / π ≤ 2 * (N : ℝ) * cN N ^ 2 ∧
      2 * (N : ℝ) * cN N ^ 2 ≤ (N : ℝ) / (π * ((N : ℝ) - 1)) := by
  obtain ⟨h1, h2⟩ := cN_sq_window hN
  have hpi := Real.pi_pos
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · have e : 1 / π = 2 * (N : ℝ) * (1 / (2 * π * (N : ℝ))) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · have e : (N : ℝ) / (π * ((N : ℝ) - 1)) = 2 * (N : ℝ) * (1 / (2 * π * ((N : ℝ) - 1))) := by
      have : (N : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- For `N = 2n`, `n ≥ 13 225`: `1/(13n) ≤ c_N² ≤ 0.08/n`. -/
theorem cN_even_window {n : ℕ} (hn : 13225 ≤ n) :
    1 / (13 * (n : ℝ)) ≤ cN (2 * n) ^ 2 ∧ cN (2 * n) ^ 2 ≤ 8 / (100 * (n : ℝ)) := by
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨h1, h2⟩ := cN_sq_window (N := 2 * n) (by omega)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hNcast] at h1 h2
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  constructor
  · refine le_trans ?_ h1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · refine h2.trans ?_
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith

end BstLean.Part159

open BstLean.Part159 in
#print axioms q1_eq_cN
open BstLean.Part159 in
#print axioms rN_window
open BstLean.Part159 in
#print axioms cN_even_window
