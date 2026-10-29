import BstLean.Part278Pert

/-!
# Part 278 (O3, energy table): the perturbation of `ω̃` under a perturbation of the moments

Paper: `theorem7-08-bias.tex`, Lemma `t7:p08:odd` (the energy part; the identity
"(sum)·(difference)").

* `binMean_relu_sq_pert`: `|B_J ReLU(x′ + σ′Z)² − B_J ReLU(x + σZ)²| ≤
  (|x′ − x| + |σ′ − σ|)(|x′| + |x| + σ′ + σ)`.
* `wPassG_pert`: with an operator bound `O` of `A₂`,
  `|ω̃′ − ω̃| ≤ √(2O²|δā|² + 2m|δς²|)·√(4O²(|ā′|² + |ā|²) + 4m(ς′² + ς²))/n`, `m = m_A`.
-/

namespace BstLean.Part278

open Real MeasureTheory
open BstLean.Part130 (relu normSq normSq_nonneg mA)
open BstLean.Part150 (binMean binMean_sub binMean_abs_le binMean_mono binMean_add binMean_const
  binMean_const_mul binMean_sq)
open BstLean.Part157 (Ret)
open BstLean.Part169 (A2 Jz OpB)
open BstLean.Part272 (vsig2G beta2G wPassG)

variable {n : ℕ}

theorem binMean_relu_sq_pert {J : ℕ} (hJ : 1 ≤ J) (x x' : ℝ) {σ σ' : ℝ} (hσ : 0 ≤ σ)
    (hσ' : 0 ≤ σ') :
    |binMean J (fun z => relu (x' + σ' * z) ^ 2) - binMean J (fun z => relu (x + σ * z) ^ 2)| ≤
      (|x' - x| + |σ' - σ|) * (|x'| + |x| + (σ' + σ)) := by
  set A := |x' - x| with hA
  set B := |σ' - σ| with hB
  set C := |x'| + |x| with hC
  set D := σ' + σ with hD
  have hA0 : 0 ≤ A := abs_nonneg _
  have hB0 : 0 ≤ B := abs_nonneg _
  have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hD0 : 0 ≤ D := add_nonneg hσ' hσ
  have hpt : ∀ z : ℝ, |relu (x' + σ' * z) ^ 2 - relu (x + σ * z) ^ 2| ≤
      A * C + (A * D + B * C) * |z| + (B * D) * z ^ 2 := by
    intro z
    have h1 : |relu (x' + σ' * z) - relu (x + σ * z)| ≤ A + B * |z| := by
      refine (relu_lip _ _).trans ?_
      rw [show x' + σ' * z - (x + σ * z) = (x' - x) + (σ' - σ) * z by ring]
      exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul]))
    have hr : ∀ y : ℝ, |relu y| ≤ |y| := fun y => by
      unfold relu
      rw [abs_of_nonneg (le_max_left _ _)]
      exact max_le (abs_nonneg _) (le_abs_self _)
    have h2 : |relu (x' + σ' * z) + relu (x + σ * z)| ≤ C + D * |z| := by
      refine (abs_add_le _ _).trans ?_
      have a1 : |relu (x' + σ' * z)| ≤ |x'| + σ' * |z| :=
        (hr _).trans ((abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_of_nonneg hσ'])))
      have a2 : |relu (x + σ * z)| ≤ |x| + σ * |z| :=
        (hr _).trans ((abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_of_nonneg hσ])))
      rw [hC, hD]
      linarith
    rw [show relu (x' + σ' * z) ^ 2 - relu (x + σ * z) ^ 2 =
      (relu (x' + σ' * z) - relu (x + σ * z)) * (relu (x' + σ' * z) + relu (x + σ * z)) by ring,
      abs_mul]
    calc |relu (x' + σ' * z) - relu (x + σ * z)| * |relu (x' + σ' * z) + relu (x + σ * z)|
        ≤ (A + B * |z|) * (C + D * |z|) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = A * C + (A * D + B * C) * |z| + (B * D) * z ^ 2 := by
          rw [← sq_abs z]; ring
  rw [← binMean_sub]
  refine (binMean_abs_le J _).trans ?_
  refine (binMean_mono J hpt).trans ?_
  rw [binMean_add, binMean_add, binMean_const, binMean_const_mul, binMean_const_mul,
    binMean_sq hJ]
  have hz := binMean_abs_z hJ
  have hAD : 0 ≤ A * D + B * C := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hz hAD]

/-- **The energy table under a perturbation of the moment vectors.** -/
theorem wPassG_pert (hJ : 1 ≤ Jz n) (a a' e e' : Ret n → ℝ → Fin (mA n) → ℝ) (c : Ret n) (s : ℝ)
    {O : ℝ} (hO : OpB (A2 c) O) :
    |wPassG a' e' c s - wPassG a e c s| ≤
      √(2 * (O ^ 2 * normSq (a' c s - a c s)) +
          2 * (mA n : ℝ) * |vsig2G a' e' c s - vsig2G a e c s|) *
        √(4 * (O ^ 2 * (normSq (a' c s) + normSq (a c s))) +
          4 * (mA n : ℝ) * (vsig2G a' e' c s + vsig2G a e c s)) / (n : ℝ) := by
  obtain ⟨u, hu⟩ : ∃ u : Fin (mA n) → ℝ, u = (A2 c).mulVec (a' c s - a c s) := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y : Fin (mA n) → ℝ, y = (A2 c).mulVec (a' c s) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin (mA n) → ℝ, y = (A2 c).mulVec (a c s) := ⟨_, rfl⟩
  have hv0 : ∀ (a e : Ret n → ℝ → Fin (mA n) → ℝ), 0 ≤ vsig2G a e c s :=
    fun a e => le_max_left _ _
  set v' := vsig2G a' e' c s with hv'
  set v := vsig2G a e c s with hv
  have hv'0 : 0 ≤ v' := hv0 _ _
  have hvv0 : 0 ≤ v := hv0 _ _
  set t := |√v' - √v| with ht
  set D := √v' + √v with hD
  have ht0 : 0 ≤ t := abs_nonneg _
  have hD0 : 0 ≤ D := add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  have ht2 : t ^ 2 ≤ |v' - v| := by
    have htv : t ≤ √|v' - v| := sqrt_sub_le hv'0 hvv0
    calc t ^ 2 ≤ (√|v' - v|) ^ 2 := pow_le_pow_left₀ ht0 htv 2
      _ = _ := sq_sqrt (abs_nonneg _)
  have hD2 : D ^ 2 ≤ 2 * (v' + v) := by
    rw [hD]
    nlinarith [sq_nonneg (√v' - √v), sq_sqrt hv'0, sq_sqrt hvv0]
  -- the per-coordinate bound
  have hj : ∀ j, |beta2G a' e' c s j - beta2G a e c s j| ≤
      (|u j| + t) * ((|y' j| + |y j|) + D) := by
    intro j
    have h := binMean_relu_sq_pert hJ (y j) (y' j) (sqrt_nonneg v) (sqrt_nonneg v')
    have hu' : u j = y' j - y j := by rw [hu, hy', hy, Matrix.mulVec_sub]; rfl
    rw [hu']
    rw [hy', hy] at h ⊢
    exact h
  have hsum : |∑ j, beta2G a' e' c s j - ∑ j, beta2G a e c s j| ≤
      √(∑ j, (|u j| + t) ^ 2) * √(∑ j, ((|y' j| + |y j|) + D) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hj j).trans ?_)
    exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |u j| + t)
      (fun j => (|y' j| + |y j|) + D)
  have hm0 : (0:ℝ) ≤ mA n := Nat.cast_nonneg _
  have hU : ∑ j, (|u j| + t) ^ 2 ≤
      2 * (O ^ 2 * normSq (a' c s - a c s)) + 2 * (mA n : ℝ) * |v' - v| := by
    have h1 : ∀ j, (|u j| + t) ^ 2 ≤ 2 * u j ^ 2 + 2 * t ^ 2 := fun j => by
      nlinarith [sq_abs (u j), sq_nonneg (|u j| - t)]
    calc ∑ j, (|u j| + t) ^ 2 ≤ ∑ j, (2 * u j ^ 2 + 2 * t ^ 2) :=
          Finset.sum_le_sum fun j _ => h1 j
      _ = 2 * normSq u + 2 * (mA n : ℝ) * t ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          unfold normSq
          rw [Finset.mul_sum]
          ring
      _ ≤ _ := by
          have h3 := hO (a' c s - a c s)
          rw [← hu] at h3
          nlinarith [mul_le_mul_of_nonneg_left ht2 hm0]
  have hY : ∑ j, ((|y' j| + |y j|) + D) ^ 2 ≤
      4 * (O ^ 2 * (normSq (a' c s) + normSq (a c s))) + 4 * (mA n : ℝ) * (v' + v) := by
    have h1 : ∀ j, ((|y' j| + |y j|) + D) ^ 2 ≤ 4 * y' j ^ 2 + 4 * y j ^ 2 + 2 * D ^ 2 :=
      fun j => by
        nlinarith [sq_abs (y' j), sq_abs (y j), sq_nonneg (|y' j| - |y j|),
          sq_nonneg (|y' j| + |y j| - D)]
    calc ∑ j, ((|y' j| + |y j|) + D) ^ 2 ≤ ∑ j, (4 * y' j ^ 2 + 4 * y j ^ 2 + 2 * D ^ 2) :=
          Finset.sum_le_sum fun j _ => h1 j
      _ = 4 * normSq y' + 4 * normSq y + 2 * (mA n : ℝ) * D ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          unfold normSq
          rw [Finset.mul_sum, Finset.mul_sum]
          ring
      _ ≤ _ := by
          have h3 := hO (a' c s)
          have h4 := hO (a c s)
          rw [← hy'] at h3
          rw [← hy] at h4
          nlinarith [mul_le_mul_of_nonneg_left hD2 hm0]
  have hdiff : wPassG a' e' c s - wPassG a e c s =
      (∑ j, beta2G a' e' c s j - ∑ j, beta2G a e c s j) / (n : ℝ) := by
    unfold wPassG; rw [sub_div]
  rw [hdiff, abs_div, abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  refine hsum.trans ?_
  exact mul_le_mul (sqrt_le_sqrt hU) (sqrt_le_sqrt hY) (sqrt_nonneg _) (sqrt_nonneg _)

end BstLean.Part278
