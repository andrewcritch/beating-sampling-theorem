import BstLean.Part233World
import BstLean.Part233Scalar

/-! The paper group65 and group61 payment under explicit first-layer certificates. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part136 BstLean.Part137 BstLean.Part205
open BstLean.Part153 (nrm nrm_sq)
open BstLean.Part141 (rowS)

noncomputable def cancellationPayment (n : ℕ) (Xc μ ε : ℝ) : ℝ :=
  exp (-((mW n : ℝ) * (√Xc - √μ) ^ 2 /
    ((1 + √(31835 / 100000 : ℝ)) ^ 2 * (1 + ε) * ((2 * n : ℕ) : ℝ))))

noncomputable def outputNormPayment (n : ℕ) (ε : ℝ) : ℝ :=
  let e : ℝ := (10 : ℝ) ^ 8 / (8 * (1 + ε)) - 1
  exp (-(mW n : ℝ) * (e - log (1 + e)) / 2)

/-- The first-layer complement occurs once in the exact paper payment. -/
theorem paper_distanceGroup_charge {n : ℕ} (hn : 4096 ≤ n)
    {E : Set (Matrix (Fin (mW n)) (Fin (2 * n)) ℝ)} (hE : MeasurableSet E)
    {δ Xc μ ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000)
    (hμ : 0 ≤ μ) (hgap : μ < Xc)
    (hδ : (gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).real Eᶜ ≤ δ)
    (hS : ∀ M₁ ∈ E, |rowS M₁ / (mW n : ℝ) / 2 - 1| ≤ ε)
    (hQ0 : ∀ M₁ ∈ E, 0 < firstQ M₁)
    (hQ : ∀ M₁ ∈ E, firstQ M₁ ≤ (1 + ε) * (mW n : ℝ) / ((2 * n : ℕ) : ℝ))
    (hcentre : ∀ M₁ ∈ E, normSq (h1bar M₁) ≤ 31835 / 100000 * firstQ M₁)
    (hmean : ∀ M₁ ∈ E, 2 / (mW n : ℝ) * worldDelta M₁ ≤
      2 * μ / (((2 * n : ℕ) : ℝ) ^ 2)) :
    (hidGauss (2 * n) (mW n)).real (distanceGroup n Xc)ᶜ ≤
      δ + cancellationPayment n Xc μ ε + outputNormPayment n ε := by
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hmp : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hNp : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by positivity
  let K : ℝ := (1 + √(31835 / 100000 : ℝ)) ^ 2
  let e : ℝ := (10 : ℝ) ^ 8 / (8 * (1 + ε)) - 1
  have he : 0 < e := by
    dsimp [e]
    have hd : 0 < 8 * (1 + ε) := by positivity
    have hh : 1 < (10 : ℝ) ^ 8 / (8 * (1 + ε)) := by
      rw [lt_div_iff₀ hd]
      nlinarith
    linarith
  have hM : (√2 * √μ / ((2 * n : ℕ) : ℝ)) ^ 2 =
      2 * μ / (((2 * n : ℕ) : ℝ) ^ 2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hμ]
  have hX : 0 ≤ Xc := hμ.trans hgap.le
  have hA : (√2 * √Xc / ((2 * n : ℕ) : ℝ)) ^ 2 =
      2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hX]
    ring
  have hAcut : 8 * (1 + ε) * (1 + e) = (10 : ℝ) ^ 8 := by
    dsimp [e]
    field_simp <;> ring
  have hexp : exp (-((√2 * √Xc / ((2 * n : ℕ) : ℝ)) -
        (√2 * √μ / ((2 * n : ℕ) : ℝ))) ^ 2 /
        (2 * (K * (1 + ε) / ((mW n : ℝ) * ((2 * n : ℕ) : ℝ))))) =
      cancellationPayment n Xc μ ε := by
    rw [cancellation_exponent hNp hX hμ] <;> rfl
  have hc := distanceGroup_charge_of_concentration hn hE hδ
    (a := √2 * √Xc / ((2 * n : ℕ) : ℝ))
    (M := √2 * √μ / ((2 * n : ℕ) : ℝ))
    (V := K * (1 + ε) / ((mW n : ℝ) * ((2 * n : ℕ) : ℝ)))
    (ε := ε) (e := e)
    (by positivity)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hgap.le) (sqrt_nonneg _)) hNp.le)
    (by dsimp [K]; positivity) hε0 he hε hA.le
    hAcut.le hS
    (by positivity)
    (fun M₁ h₁ => by rw [hM]; exact hmean M₁ h₁)
    (fun M₁ h₁ => div_pos
      (add_pos_of_pos_of_nonneg (sqrt_pos.mpr (hQ0 M₁ h₁))
        (BstLean.Part153.nrm_nonneg _)) hmp)
    (fun M₁ h₁ => cancellation_variance_bound (hQ0 M₁ h₁).le
      (BstLean.Part153.nrm_nonneg _)
      hmp hNp (by norm_num) hε0 (hQ M₁ h₁) (by rw [nrm_sq]; exact hcentre M₁ h₁))
  rw [hexp] at hc
  exact hc

end BstLean.Part233
#print axioms BstLean.Part233.paper_distanceGroup_charge
