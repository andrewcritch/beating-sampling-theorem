import BstLean.Part216MGF

/-! The analytic Bernstein tail, with its exact Chernoff parameter. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Set

lemma bernstein_exponent {V b τ : ℝ} (hV : 0 < V) (hb : 0 ≤ b) (hτ : 0 ≤ τ) :
    let L := sqrt (2 * V * τ)
    let lam := L / V
    let s := lam / (1 + b * lam)
    0 ≤ s ∧ b * s < 1 ∧
      -s * (L + b * τ) + V * s ^ 2 / (2 * (1 - b * s)) = -τ := by
  intro L lam s
  have hL : 0 ≤ L := sqrt_nonneg _
  have hL2 : L ^ 2 = 2 * V * τ := sq_sqrt (by positivity)
  have hl : 0 ≤ lam := div_nonneg hL hV.le
  have hd : 0 < 1 + b * lam := by positivity
  have hbs : b * s < 1 := by
    change b * (lam / (1 + b * lam)) < 1
    rw [mul_div_assoc', div_lt_one hd]
    linarith
  refine ⟨by positivity, hbs, ?_⟩
  have he : 1 - b * s = 1 / (1 + b * lam) := by
    dsimp [s]; field_simp; ring
  have hll : lam * L = 2 * τ := by dsimp [lam]; field_simp; nlinarith [hL2]
  have hvll : V * lam ^ 2 = 2 * τ := by dsimp [lam]; field_simp; nlinarith [hL2]
  rw [he]
  dsimp [s]
  field_simp
  nlinarith [hll, hvll]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One-sided analytic Bernstein tail from the MGF on its full domain. -/
theorem bernstein_upper {Y : Ω → ℝ} {V b τ : ℝ}
    (hV : 0 < V) (hb : 0 ≤ b) (hτ : 0 ≤ τ)
    (hMGF : ∀ s : ℝ, 0 ≤ s → b * s < 1 →
      Integrable (fun x => exp (s * Y x)) μ ∧
      mgf Y μ s ≤ exp (V * s ^ 2 / (2 * (1 - b * s)))) :
    μ.real {x | sqrt (2 * V * τ) + b * τ ≤ Y x} ≤ exp (-τ) := by
  obtain ⟨hs, hbs, he⟩ := bernstein_exponent hV hb hτ
  let s := sqrt (2 * V * τ) / V / (1 + b * (sqrt (2 * V * τ) / V))
  obtain ⟨hi, hm⟩ := hMGF s hs hbs
  have hc := measure_ge_le_exp_mul_mgf (X := Y) (sqrt (2 * V * τ) + b * τ) hs hi
  refine hc.trans ?_
  calc exp (-s * (sqrt (2 * V * τ) + b * τ)) * mgf Y μ s ≤
      exp (-s * (sqrt (2 * V * τ) + b * τ)) *
        exp (V * s ^ 2 / (2 * (1 - b * s))) :=
          mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ = exp (-τ) := by rw [← exp_add, he]

/-- The two signs use the same distribution and the same Bernstein scales. -/
theorem bernstein_tail {Y : Ω → ℝ} {V b τ : ℝ}
    (hV : 0 < V) (hb : 0 ≤ b) (hτ : 0 ≤ τ)
    (hMGF : ∀ sign : ℝ, |sign| = 1 → ∀ s : ℝ, 0 ≤ s → b * s < 1 →
      Integrable (fun x => exp (s * (sign * Y x))) μ ∧
      mgf (fun x => sign * Y x) μ s ≤ exp (V * s ^ 2 / (2 * (1 - b * s)))) :
    μ.real {x | sqrt (2 * V * τ) + b * τ < |Y x|} ≤ 2 * exp (-τ) := by
  have hp := bernstein_upper (Y := fun x => 1 * Y x) hV hb hτ (hMGF 1 (by norm_num))
  have hn := bernstein_upper (Y := fun x => -1 * Y x) hV hb hτ (hMGF (-1) (by norm_num))
  have hsub : {x | sqrt (2 * V * τ) + b * τ < |Y x|} ⊆
      {x | sqrt (2 * V * τ) + b * τ ≤ 1 * Y x} ∪
      {x | sqrt (2 * V * τ) + b * τ ≤ -1 * Y x} := by
    intro x hx
    change sqrt (2 * V * τ) + b * τ < |Y x| at hx
    rcases lt_abs.mp hx with hx | hx
    · left; simpa only [Set.mem_setOf_eq, one_mul] using hx.le
    · right; simpa only [Set.mem_setOf_eq, neg_one_mul] using hx.le
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by linarith))

#print axioms bernstein_exponent
#print axioms bernstein_upper
#print axioms bernstein_tail
end BstLean.Part216
