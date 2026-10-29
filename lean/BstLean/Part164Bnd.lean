import BstLean.Part164Ev

/-!
# Part 164 (file `Bnd`): the hypotheses `|c_A|² ≤ C_A`, `0 < |c_A|²` and `∫∫σ⁸ ≤ E⁸` on the events

No proof is left open; no `native_decide` or `axiom` is used.

* `CAn n = (2/n)·0.7315·(n + 2√(12n) + 24)`: the norm constant (the paper's `nγ_A e_b χ_A⁺` with
  `e_b ≤ 0.7315`, Part 160's `eb16_sharp`).
* `cA_bounds`: on `EcA` with `GoodC16`, `SSc` and the window: `0 < |c_A|² ≤ CAn n` (`n ≥ 16 384`).
* `E0 n = √t_A · √t_A(2n + 5) · √(2/n)(n + 2√n)`; `sgA_le_E0`: on `E_op` and `Eop2`, `σ ≤ E0 n` at
  every latitude point; `sgA8_le`: `∫∫σ⁸ ≤ (E0 n)⁸`.
-/

namespace BstLean.Part164

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (muI latC xLat)
open BstLean.Part162 (sgA sgA_nonneg)

variable {n : ℕ}

/-- **The norm constant**: `C_A(n) = (2/n)·0.7315·(n + 2√(12n) + 24)`. -/
noncomputable def CAn (n : ℕ) : ℝ := 2 / (n : ℝ) * (7315 / 10000) * chiUp n

lemma chiLo_pos (hn : 49 ≤ n) : 0 < chiLo n := by
  unfold chiLo
  have hnR : (49 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ (n : ℝ) * 12 := by positivity
  have hs : √((n : ℝ) * 12) ^ 2 = (n : ℝ) * 12 := Real.sq_sqrt h0
  have hs0 : 0 ≤ √((n : ℝ) * 12) := Real.sqrt_nonneg _
  nlinarith

/-- **`0 < |c_A|² ≤ C_A(n)` on the norm event** with `GoodC16`, `SSc` and the window
(`n ≥ 16 384`). -/
theorem cA_bounds (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) {c : Ret n}
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ BstLean.Part154.GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hc : c ∈ EcA D.toCentres) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CAn n := by
  obtain ⟨-, -, -, hpos, -, -, -⟩ := centre16 hn hτ hθ0 hθ1 hG
  have hup := eb16_sharp hn hτ hθ0 hθ1 hG hS
  have hb : D.bA c.1 c.2.1.1 =
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := hD c
  rw [← hb] at hup hpos
  obtain ⟨h1, h2⟩ := hc
  have hm : (0 : ℝ) < (mA n : ℝ) := by
    have : 0 < mA n := by unfold mA; exact pow_pos (by omega) 2
    exact_mod_cast this
  have hlo := chiLo_pos (n := n) (by omega)
  have hup0 : 0 ≤ chiUp n := by unfold chiUp; positivity
  refine ⟨lt_of_lt_of_le ?_ h2, h1.trans ?_⟩
  · exact mul_pos (mul_pos (div_pos two_pos hm) hpos) hlo
  · unfold CAn
    exact mul_le_mul_of_nonneg_right hup hup0

/-- The constant of the pointwise bound of `σ`: `E0 n = √t_A·(√t_A(2n + 5))·(√(2/n)(n + 2√n))`. -/
noncomputable def E0 (n : ℕ) : ℝ :=
  √(2 / (mA n : ℝ)) * (√(2 / (mA n : ℝ)) * (2 * (n : ℝ) + 5)) *
    (√(2 / (n : ℝ)) * ((n : ℝ) + 2 * √(n : ℝ)))

lemma E0_nonneg (n : ℕ) : 0 ≤ E0 n := by unfold E0; positivity

/-- On `E_op` (for `A₁`) the operator norm of `A₁` is bounded; read from `GoodC16`. -/
lemma eop_of_goodC16 {c : Fin n → ℝ} {τ : ℝ}
    {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : θ ∈ BstLean.Part154.GoodC16 n n c τ) : θ.1 ∈ BstLean.Part153.Eop n := by
  have h1 : θ ∈ BstLean.Part153.GoodAs n c τ := h.1.1
  have h2 := h1.1
  by_contra hc
  exact h2 (Or.inl (Or.inl (Or.inl (Or.inl hc))))

/-- **The pointwise bound of `σ`**: `σ(x) ≤ √t_A‖A₂‖‖A₁‖|x| ≤ E0 n` at every latitude point, on
`E_op` and `Eop2`. -/
theorem sgA_le_E0 (hn : 1 ≤ n) (D : Design n) {c : Ret n}
    (h1 : c.2.1.1.1 ∈ BstLean.Part153.Eop n) (h2 : c ∈ Eop2 n) (a : BstLean.Part161.Ix n)
    (v : Fin (n - 1) → ℝ) : sgA D c a v ≤ E0 n := by
  set x := xLat c (latC D c a) (BstLean.Part53.unitF53 v)
  have hx : normSq x ≤ 1 := BstLean.Part162.normSq_xLat_le hn c (BstLean.Part162.latC_sq_le D c a) v
  set A₁ := c.2.1.1.1
  set A₂ := c.2.1.1.2
  have hO1 : BstLean.Part152.opN A₁ ≤ √(2 / (n : ℝ)) * ((n : ℝ) + 2 * √(n : ℝ)) := h1
  have hO2 : BstLean.Part152.opN A₂ ≤ √(2 / (mA n : ℝ)) * (2 * (n : ℝ) + 5) := h2
  have o1 := BstLean.Part152.opN_nonneg A₁
  have o2 := BstLean.Part152.opN_nonneg A₂
  have hh : normSq (hid2 A₁ A₂ x) ≤ BstLean.Part152.opN A₂ ^ 2 * BstLean.Part152.opN A₁ ^ 2 := by
    unfold hid2
    calc normSq (reluV (A₂.mulVec (reluV (A₁.mulVec x)))) ≤ normSq (A₂.mulVec (reluV (A₁.mulVec x))) :=
          BstLean.Part153.normSq_reluV_le _
      _ ≤ BstLean.Part152.opN A₂ ^ 2 * normSq (reluV (A₁.mulVec x)) :=
          BstLean.Part151.normSq_mulVec_le_opN _ _
      _ ≤ BstLean.Part152.opN A₂ ^ 2 * (BstLean.Part152.opN A₁ ^ 2 * normSq x) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact (BstLean.Part153.normSq_reluV_le _).trans
            (BstLean.Part151.normSq_mulVec_le_opN _ _)
      _ ≤ BstLean.Part152.opN A₂ ^ 2 * (BstLean.Part152.opN A₁ ^ 2 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ = _ := by ring
  have hr : normSq (BstLean.Part134.res (D.bA c.1 c.2.1.1) (hid2 A₁ A₂ x)) ≤
      (BstLean.Part152.opN A₂ * BstLean.Part152.opN A₁) ^ 2 := by
    rw [mul_pow]
    exact (BstLean.Part162.normSq_res_le _ _).trans hh
  have hsq : √(normSq (BstLean.Part134.res (D.bA c.1 c.2.1.1) (hid2 A₁ A₂ x))) ≤
      BstLean.Part152.opN A₂ * BstLean.Part152.opN A₁ := by
    rw [← Real.sqrt_sq (mul_nonneg o2 o1)]
    exact Real.sqrt_le_sqrt hr
  show √(2 / (mA n : ℝ)) * √(normSq (BstLean.Part134.res (D.bA c.1 c.2.1.1) (hid2 A₁ A₂ x))) ≤ E0 n
  unfold E0
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (hsq.trans ?_) (Real.sqrt_nonneg _)
  exact mul_le_mul hO2 hO1 o1 (by positivity)

/-- **The eighth moment of `σ`** on `E_op` and `Eop2`: `∫∫σ⁸ ≤ (E0 n)⁸`. -/
theorem sgA8_le (hn : 1 ≤ n) (D : Design n) {c : Ret n}
    (h1 : c.2.1.1.1 ∈ BstLean.Part153.Eop n) (h2 : c ∈ Eop2 n) :
    ∫ a, ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ E0 n ^ 8 := by
  have hin : ∀ a, ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ≤ E0 n ^ 8 := by
    intro a
    have h := integral_mono_of_nonneg (μ := stdGauss (Fin (n - 1)))
      (f := fun v => sgA D c a v ^ 8) (g := fun _ => E0 n ^ 8)
      (Filter.Eventually.of_forall fun v => pow_nonneg (sgA_nonneg D c a v) 8)
      (integrable_const _)
      (Filter.Eventually.of_forall fun v =>
        pow_le_pow_left₀ (sgA_nonneg D c a v) (sgA_le_E0 hn D h1 h2 a v) 8)
    simpa using h
  have h := integral_mono_of_nonneg (μ := muI n)
    (f := fun a => ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1))) (g := fun _ => E0 n ^ 8)
    (Filter.Eventually.of_forall fun a =>
      integral_nonneg fun v => pow_nonneg (sgA_nonneg D c a v) 8)
    (integrable_const _) (Filter.Eventually.of_forall hin)
  simpa using h

end BstLean.Part164
