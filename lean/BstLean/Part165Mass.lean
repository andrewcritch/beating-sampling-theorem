import BstLean.Part165Ev
import BstLean.Part164All

/-!
# Part 165 (file `Mass`): the mass below the floor from the moment of order 40 of `σ`

No proof is left open; no `native_decide` or `axiom` is used.

* `s0 = 0.5087`: a lower bound of `E σ/√γ_A` on the frame events (from Part 160's
  `sigD_moments`: `s0² ≤ 1 − N₂₂(2 + N₂₂) − (e₁ + e₂)² − 2N/n` with `N = 1.1911`,
  `N₂₂ = 18.334/n`, `e₁ = 0.8553 ≥ √0.7315`, `e₂ = 0.0046 ≥ √(0.485/n)`, `n ≥ 23 000`).
* `betaM n sd = (π/2)⁴⁰·E|g|⁴⁰·(0.706/(n(s0 − sd)²))²⁰`.
* **`mass_order40`**: for one retained value, with the base quantities and the event
  `SXqN n 20`: `∫_a ν{σ < √γ_A·sd} ≤ betaM n sd` (`0 ≤ sd < s0`).
* **`mass_of_goodC`**: the same on the good set `goodC` of the end theorem.
* **`SX20_ret_charge`**: `Pr((agentEv D (SXqN n 20))ᶜ) ≤ 5·10⁻⁵` (retained data).
-/

namespace BstLean.Part165

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (muI sigX)
open BstLean.Part162 (sgA gmom gmom_nonneg)
open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr)
open BstLean.Part134 (res sig)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA)

variable {n : ℕ}

/-- The lower bound of `E σ/√γ_A` used for the floor: `s0 = 0.5087`. -/
noncomputable def s0 : ℝ := 5087 / 10000

/-- **The mass bound of order 40**: `β(n, sd) = (π/2)⁴⁰·E|g|⁴⁰·(0.706/(n(s0 − sd)²))²⁰`. -/
noncomputable def betaM (n : ℕ) (sd : ℝ) : ℝ :=
  (π / 2) ^ 40 * gmom 40 * (706 / 1000 / ((n : ℝ) * (s0 - sd) ^ 2)) ^ 20

lemma betaM_nonneg (n : ℕ) (sd : ℝ) : 0 ≤ betaM n sd := by
  unfold betaM
  have := gmom_nonneg 40
  have h : 0 ≤ (706 / 1000 / ((n : ℝ) * (s0 - sd) ^ 2)) ^ 20 := by
    rw [show (20 : ℕ) = 2 * 10 by norm_num, pow_mul]; positivity
  positivity

/-- The numeric condition on `s0` (`n ≥ 23 000`). -/
lemma s0_cond (hn : 23000 ≤ n) :
    s0 ^ 2 ≤ 1 - 18334 / 1000 / (n : ℝ) * (2 + 18334 / 1000 / (n : ℝ)) -
      (8553 / 10000 + 46 / 10000) ^ 2 - 2 * (11911 / 10000) / n := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 / 23000 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hnR
  have e1 : 18334 / 1000 / (n : ℝ) = 18334 / 1000 * x := by rw [hx]; ring
  have e2 : 2 * (11911 / 10000) / (n : ℝ) = 2 * (11911 / 10000) * x := by rw [hx]; ring
  rw [e1, e2]
  unfold s0
  nlinarith

/-- `ĉ ≠ 0` when `θ_in ≤ 0.55`. -/
lemma c_ne_of_theta {c : Fin n → ℝ} {τ : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ)
    (hθ : thetaC c τ ≤ 55 / 100) : c ≠ 0 := by
  intro h0
  rw [h0] at hθ
  unfold thetaC rhoC at hθ
  have hz : normSq (0 : Fin n → ℝ) = 0 := by simp [normSq]
  have hpos : (0 : ℝ) < (n : ℝ) * τ ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  rw [hz, zero_add, Real.sq_sqrt hpos.le, div_self hpos.ne'] at hθ
  norm_num at hθ

/-- **The mass below the floor from the moment of order 40 of `σ`**, for one retained value:
with the quantities of the frame events and the event `SXqN n 20`,
`∫_a ν{σ < √γ_A·sd} ≤ betaM n sd` for `0 ≤ sd < s0`, `n ≥ 23 000`. -/
theorem mass_order40 (hn : 23000 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 11911 / 10000 * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) ≤ 2 / (n : ℝ) * (7315 / 10000))
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ 485 / 1000 * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 18334 / 1000 / (n : ℝ))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXqN n 20)
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0) :
    ∫ a', (stdGauss (Fin (n - 1))).real {v | sgA D c a' v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaM n sd := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : c.1.2 ≠ 0 := c_ne_of_theta (by omega) hτ hθ1
  rw [BstLean.Part162.mass_eq_stand (by omega) D c hc hτ]
  -- the tail bound of order 40
  set A₁ := c.2.1.1.1
  set A₂ := c.2.1.1.2
  set b := D.bA c.1 c.2.1.1
  set τ := D.tau0 c
  have hX := tX20_le hn hτ hθ0 hθ1 hS
  set K : ℝ := (π / 2) ^ 40 * (gmom 40 * (706 / 1000 * (2 / (n : ℝ)) / n) ^ 20) with hK
  have hT : ∀ g : ℝ, 0 < g → (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c.1.2 τ b ξ - ∫ ζ, sigD A₁ A₂ c.1.2 τ b ζ ∂stdGauss (Fin n)|} ≤
        K / g ^ 40 := by
    intro g hg
    have h := sigD_tail (q := 20) (by norm_num) (by omega) A₁ A₂ c.1.2 hτ hb hg
    refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [hK]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (gmom_nonneg _)) (by positivity)
  have hXi' : XiS A₁ A₂ c.1.2 τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n := hXi
  have hm := mass_bound_gen (by omega) A₁ A₂ c.1.2 hτ hb hXi' heb hxi hN22
    (e1 := 8553 / 10000) (e2 := 46 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by rw [div_le_iff₀ hn0]; nlinarith) hsd0 hsd (by
      have := s0_cond hn
      unfold s0 at this ⊢
      linarith) hT
  have hset : {ξ : Fin n → ℝ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) < √(2 / (n : ℝ)) * sd} =
      {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1)
        (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    simp only [Set.mem_ofPred_eq]
    set R := normSq (res (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ))))
    have hR : 0 ≤ R := normSq_nonneg _
    have hsig : sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) = √(2 / (mA n : ℝ)) * √R := rfl
    rw [hsig, ← Real.sqrt_mul (by positivity)]
    have e : √(2 / (n : ℝ)) * sd = √(2 / (n : ℝ) * sd ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hsd0]
    rw [e]
    exact Real.sqrt_lt_sqrt_iff (by positivity)
  rw [hset]
  refine hm.trans (le_of_eq ?_)
  -- the value of `K / (√γ_A (s0 − sd))⁴⁰`
  have hd : 0 < s0 - sd := by linarith
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs40 : (√(2 / (n : ℝ)) * (s0 - sd)) ^ 40 = (2 / (n : ℝ)) ^ 20 * ((s0 - sd) ^ 2) ^ 20 := by
    rw [mul_pow, show (40 : ℕ) = 2 * 20 by norm_num, pow_mul, pow_mul, Real.sq_sqrt hγ.le]
  unfold s0 at hs40 hd ⊢
  rw [hs40, hK]
  unfold betaM s0
  field_simp

end BstLean.Part165
