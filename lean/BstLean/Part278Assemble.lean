import BstLean.Part278PertW

/-!
# Part 278 (O3 and O4 assembled): the odd root from the moment errors

* `e1Bar_le`, `vsig_le`: size bounds of the exact moments and of `ς²`.
* `odd_wPass_err`: `|ω̃^{st}(s) − ω̃(s)| ≤ √(2O²ε²Q + 4ε(7+ε)Q)·√(52O²Q + 8(8 + 3ε)Q)/n`.
* `odd_root_cond`: for odd `n ≥ 8001`, with an operator bound `O` of `A₂`, a bound `Q` of
  `Σ_i a_i²` at every node, a bound `F` of the exact location table, and `δ_S ≤ 1/2`, the root
  `|√q̃(stated) − √q̃(paperDesignP)|` is at most the explicit expression of
  `Part278Mix.odd_root_of_tables` with `δ_f`, `δ_ω` from the two pass bounds.
-/

namespace BstLean.Part278

open Real MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53)
open BstLean.Part130 (relu normSq normSq_nonneg mA measurable_relu)
open BstLean.Part157 (Ret qTilde)
open BstLean.Part169 (A2 bR Jz OpB a1Bar e1Bar nodeS passF passW paperDesignP)
open BstLean.Part272 (vsig2G fPassG wPassG a1St e1St alphaE kappaE a1Bar_reduce e1Bar_reduce
  integrable_coord_comp relu_sq_bound statedDesign passFSt passWSt)

variable {n : ℕ}

theorem e1Bar_le (hn : 2 ≤ n) (c : Ret n) (s : ℝ) (i : Fin (mA n)) :
    |e1Bar c s i| ≤ 4 * aw c s i ^ 2 := by
  have hκ : 0 ≤ kappaE c i := sqrt_nonneg _
  have hk : 0 ≤ √(1 - s ^ 2) * kappaE c i := mul_nonneg (sqrt_nonneg _) hκ
  have hs1 : √(1 - s ^ 2) ≤ 1 :=
    (sqrt_le_sqrt (by nlinarith [sq_nonneg s] : 1 - s ^ 2 ≤ 1)).trans_eq sqrt_one
  have hka : √(1 - s ^ 2) * kappaE c i ≤ kappaE c i := mul_le_of_le_one_left hκ hs1
  rw [e1Bar_reduce hn]
  have hTm : ∀ v : Fin (n-1) → ℝ, unitF53 v ⟨0, by omega⟩ ∈ Set.Icc (-1:ℝ) 1 :=
    fun v => BstLean.Part272.coord_mem v _
  have hI : Integrable (fun v => relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i *
      unitF53 v ⟨0, by omega⟩) ^ 2) (stdGauss (Fin (n-1))) :=
    integrable_coord_comp _
      (g := fun z => relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i * z) ^ 2)
      ((measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id))).pow_const 2)
      (relu_sq_bound _ _ hk)
  rw [abs_of_nonneg (integral_nonneg fun v => sq_nonneg _)]
  have hle : ∀ v : Fin (n-1) → ℝ, relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i *
      unitF53 v ⟨0, by omega⟩) ^ 2 ≤ 4 * aw c s i ^ 2 := by
    intro v
    have hr : relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i * unitF53 v ⟨0, by omega⟩) ≤
        2 * aw c s i := by
      unfold relu aw
      have h0 := mul_nonneg (abs_nonneg s) (abs_nonneg (alphaE c i))
      apply max_le (by linarith)
      have : √(1 - s ^ 2) * kappaE c i * unitF53 v ⟨0, by omega⟩ ≤
          √(1 - s ^ 2) * kappaE c i := by
        nlinarith [(hTm v).2]
      have h2 : |s * alphaE c i| = |s| * |alphaE c i| := abs_mul _ _
      linarith [le_abs_self (s * alphaE c i)]
    have hr0 : 0 ≤ relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i *
        unitF53 v ⟨0, by omega⟩) := le_max_left _ _
    calc relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i * unitF53 v ⟨0, by omega⟩) ^ 2
        ≤ (2 * aw c s i) ^ 2 := pow_le_pow_left₀ hr0 hr 2
      _ = 4 * aw c s i ^ 2 := by ring
  calc ∫ v, relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i * unitF53 v ⟨0, by omega⟩) ^ 2
        ∂stdGauss (Fin (n-1))
      ≤ ∫ _v : Fin (n-1) → ℝ, 4 * aw c s i ^ 2 ∂stdGauss (Fin (n-1)) :=
        integral_mono hI (integrable_const _) hle
    _ = 4 * aw c s i ^ 2 := by simp

theorem vsig_le {m : ℕ} (x y : Fin m → ℝ) :
    max 0 (2 / (m : ℝ) * (∑ i, y i - normSq x)) ≤ 2 / (m : ℝ) * ∑ i, |y i| := by
  have hm : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  apply max_le (mul_nonneg hm (Finset.sum_nonneg fun i _ => abs_nonneg _))
  apply mul_le_mul_of_nonneg_left _ hm
  have h1 : ∑ i, y i ≤ ∑ i, |y i| := Finset.sum_le_sum fun i _ => le_abs_self _
  have h2 := normSq_nonneg x
  linarith

/-- The moment-vector bounds shared by the two tables. -/
theorem odd_vec_bounds (hn : 8001 ≤ n) (ho : Odd n) (c : Ret n) (s : ℝ) :
    normSq (a1St c s - a1Bar c s) ≤ epsO n ^ 2 * ∑ i, aw c s i ^ 2 ∧
    |vsig2G a1St e1St c s - vsig2G a1Bar e1Bar c s| ≤
      2 / (mA n : ℝ) * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2) ∧
    normSq (a1St c s) + normSq (a1Bar c s) ≤ 13 * ∑ i, aw c s i ^ 2 ∧
    vsig2G a1St e1St c s + vsig2G a1Bar e1Bar c s ≤
      2 / (mA n : ℝ) * ((8 + 3 * epsO n) * ∑ i, aw c s i ^ 2) := by
  have hε0 : 0 ≤ epsO n := by unfold epsO; positivity
  have hε1 : epsO n ≤ 1 := by
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have : (n:ℝ) ^ (-10:ℝ) ≤ 1 := by
      rw [rpow_neg_ten]; exact div_le_one_of_le₀ (one_le_pow₀ h1) (by positivity)
    unfold epsO
    have h90 : (1:ℝ) / 10 ^ 90 ≤ 1 := by norm_num
    nlinarith [rpow_nonneg (Nat.cast_nonneg n) (-10:ℝ)]
  have hε3 : 3 / 10 ^ 90 * (n : ℝ) ^ (-10 : ℝ) = 3 * epsO n := by unfold epsO; ring
  have hmom := fun i => mom_err hn ho c s i
  have haw0 : ∀ i, 0 ≤ aw c s i := fun i => by
    unfold aw; exact add_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sqrt_nonneg _)
  have hQ0 : 0 ≤ ∑ i, aw c s i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm2 : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  have hA : ∀ i, |a1Bar c s i| ≤ 2 * aw c s i := fun i => a1Bar_le (by omega) c s i
  have hA' : ∀ i, |a1St c s i| ≤ 3 * aw c s i := fun i => by
    have h1 := (hmom i).1
    have h2 := hA i
    have h3 : |a1St c s i| ≤ |a1St c s i - a1Bar c s i| + |a1Bar c s i| := by
      have := abs_add_le (a1St c s i - a1Bar c s i) (a1Bar c s i)
      rwa [sub_add_cancel] at this
    nlinarith [mul_le_mul_of_nonneg_right hε1 (haw0 i)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold normSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := (hmom i).1
    rw [Pi.sub_apply, ← sq_abs (a1St c s i - a1Bar c s i), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  · refine (vsig_diff (a1Bar c s) (a1St c s) (e1Bar c s) (e1St c s)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hm2
    have hs1 : ∑ i, |e1St c s i - e1Bar c s i| ≤ ∑ i, 3 * epsO n * aw c s i ^ 2 :=
      Finset.sum_le_sum fun i _ => by rw [← hε3]; exact (hmom i).2
    have hs2 : ∑ i, |a1St c s i - a1Bar c s i| * (2 * |a1Bar c s i| + |a1St c s i - a1Bar c s i|)
        ≤ ∑ i, epsO n * (4 + epsO n) * aw c s i ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hA1 := (hmom i).1
      have hB := hA i
      have hd0 := abs_nonneg (a1St c s i - a1Bar c s i)
      calc |a1St c s i - a1Bar c s i| * (2 * |a1Bar c s i| + |a1St c s i - a1Bar c s i|)
          ≤ (epsO n * aw c s i) * (2 * (2 * aw c s i) + epsO n * aw c s i) :=
            mul_le_mul hA1 (by linarith) (by positivity) (mul_nonneg hε0 (haw0 i))
        _ = epsO n * (4 + epsO n) * aw c s i ^ 2 := by ring
    rw [← Finset.mul_sum] at hs1 hs2
    nlinarith
  · unfold normSq
    have h1 : ∑ i, a1St c s i ^ 2 ≤ ∑ i, 9 * aw c s i ^ 2 := Finset.sum_le_sum fun i _ => by
      rw [← sq_abs (a1St c s i)]
      calc |a1St c s i| ^ 2 ≤ (3 * aw c s i) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hA' i) 2
        _ = 9 * aw c s i ^ 2 := by ring
    have h2 : ∑ i, a1Bar c s i ^ 2 ≤ ∑ i, 4 * aw c s i ^ 2 := Finset.sum_le_sum fun i _ => by
      rw [← sq_abs (a1Bar c s i)]
      calc |a1Bar c s i| ^ 2 ≤ (2 * aw c s i) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hA i) 2
        _ = 4 * aw c s i ^ 2 := by ring
    rw [← Finset.mul_sum] at h1 h2
    linarith
  · have h1 := vsig_le (a1St c s) (e1St c s)
    have h2 := vsig_le (a1Bar c s) (e1Bar c s)
    have hE : ∀ i, |e1Bar c s i| ≤ 4 * aw c s i ^ 2 := fun i => e1Bar_le (by omega) c s i
    have hE' : ∀ i, |e1St c s i| ≤ (4 + 3 * epsO n) * aw c s i ^ 2 := fun i => by
      have h1 := (hmom i).2
      rw [hε3] at h1
      have h3 : |e1St c s i| ≤ |e1St c s i - e1Bar c s i| + |e1Bar c s i| := by
        have := abs_add_le (e1St c s i - e1Bar c s i) (e1Bar c s i)
        rwa [sub_add_cancel] at this
      nlinarith [hE i]
    have s1 : ∑ i, |e1St c s i| ≤ (4 + 3 * epsO n) * ∑ i, aw c s i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hE' i
    have s2 : ∑ i, |e1Bar c s i| ≤ 4 * ∑ i, aw c s i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hE i
    have := mul_le_mul_of_nonneg_left s1 hm2
    have := mul_le_mul_of_nonneg_left s2 hm2
    unfold vsig2G
    nlinarith

theorem mA_pos (hn : 1 ≤ n) : (0 : ℝ) < mA n := by
  have : 0 < mA n := by unfold mA; exact pow_pos (by omega) 2
  exact_mod_cast this

/-- **O3 (energy table).** -/
theorem odd_wPass_err (hn : 8001 ≤ n) (ho : Odd n) (hJ : 1 ≤ Jz n) (c : Ret n) (s : ℝ) {O : ℝ}
    (hO : OpB (A2 c) O) :
    |wPassG a1St e1St c s - wPassG a1Bar e1Bar c s| ≤
      √(2 * (O ^ 2 * (epsO n ^ 2 * ∑ i, aw c s i ^ 2)) +
          4 * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2)) *
        √(52 * (O ^ 2 * ∑ i, aw c s i ^ 2) + 8 * ((8 + 3 * epsO n) * ∑ i, aw c s i ^ 2)) /
          (n : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := odd_vec_bounds hn ho c s
  have hm0 := mA_pos (n := n) (by omega)
  have hmm : (mA n : ℝ) * (mA n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hm0.ne'
  have hO2 : 0 ≤ O ^ 2 := sq_nonneg O
  refine (wPassG_pert hJ a1Bar a1St e1Bar e1St c s hO).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul _ _ (sqrt_nonneg _) (sqrt_nonneg _)
  · apply sqrt_le_sqrt
    have e2 : 2 * (mA n : ℝ) * (2 / (mA n : ℝ) * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2)) =
        4 * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2) := by
      calc _ = 4 * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2) *
            ((mA n : ℝ) * (mA n : ℝ)⁻¹) := by ring
        _ = _ := by rw [hmm, mul_one]
    have h5 := mul_le_mul_of_nonneg_left h1 hO2
    have h6 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * (mA n : ℝ))
    rw [e2] at h6
    linarith
  · apply sqrt_le_sqrt
    have e2 : 4 * (mA n : ℝ) * (2 / (mA n : ℝ) * ((8 + 3 * epsO n) * ∑ i, aw c s i ^ 2)) =
        8 * ((8 + 3 * epsO n) * ∑ i, aw c s i ^ 2) := by
      calc _ = 8 * ((8 + 3 * epsO n) * ∑ i, aw c s i ^ 2) *
            ((mA n : ℝ) * (mA n : ℝ)⁻¹) := by ring
        _ = _ := by rw [hmm, mul_one]
    have h5 := mul_le_mul_of_nonneg_left h3 hO2
    have h6 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 4 * (mA n : ℝ))
    rw [e2] at h6
    have hQ0 : 0 ≤ ∑ i, aw c s i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hε0 : 0 ≤ epsO n := by unfold epsO; positivity
    nlinarith [mul_nonneg hε0 hQ0, mul_nonneg hO2 hQ0]

/-- **O3 + O4, assembled (conditional).** The odd root between the stated design and
`paperDesignP` from an operator bound of `A₂`, a bound `Q` of `Σ_i a_i²` at every node and a bound
`F` of the exact location table. -/
theorem odd_root_cond (hn : 8001 ≤ n) (ho : Odd n) (hJ : 1 ≤ Jz n) (t : ℝ) (c : Ret n)
    {O Q F : ℝ} (hO : OpB (A2 c) O)
    (hQ : ∀ g, g ≤ BstLean.Part157.Js n - 1 → ∑ i, aw c (nodeS c g) i ^ 2 ≤ Q)
    (hF : ∀ g, g ≤ BstLean.Part157.Js n - 1 → |passF c g| ≤ F)
    (hδS : 5 * (√(2 * (O ^ 2 * (epsO n ^ 2 * Q)) + 4 * (epsO n * (7 + epsO n) * Q)) *
          √(52 * (O ^ 2 * Q) + 8 * ((8 + 3 * epsO n) * Q)) / (n : ℝ) +
        √(2 * (O ^ 2 * (epsO n ^ 2 * Q)) + 4 * (epsO n * (7 + epsO n) * Q)) / √(n : ℝ) *
          (2 * F + √(2 * (O ^ 2 * (epsO n ^ 2 * Q)) + 4 * (epsO n * (7 + epsO n) * Q)) /
            √(n : ℝ))) ≤ 1 / 2) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      √(n * (5 * (√(2 * (O ^ 2 * (epsO n ^ 2 * Q)) + 4 * (epsO n * (7 + epsO n) * Q)) *
          √(52 * (O ^ 2 * Q) + 8 * ((8 + 3 * epsO n) * Q)) / (n : ℝ) +
        √(2 * (O ^ 2 * (epsO n ^ 2 * Q)) + 4 * (epsO n * (7 + epsO n) * Q)) / √(n : ℝ) *
          (2 * F + √(2 * (O ^ 2 * (epsO n ^ 2 * Q)) + 4 * (epsO n * (7 + epsO n) * Q)) /
            √(n : ℝ)))) ^ 2 +
        (√(2 * (O ^ 2 * (epsO n ^ 2 * Q)) + 4 * (epsO n * (7 + epsO n) * Q)) / √(n : ℝ) /
          √(normSq (bR c) / (n : ℝ))) ^ 2 * normSq c.2.1.2 / (2 * (2 / (n : ℝ) * (1 / 5)))) := by
  have hε0 : 0 ≤ epsO n := by unfold epsO; positivity
  have hO2 : 0 ≤ O ^ 2 := sq_nonneg O
  refine odd_root_of_tables (by omega) t c (fun g hg => ?_) (fun g hg => ?_) hF hδS
  · refine (odd_fPass_err hn ho hJ c (nodeS c g) hO).trans ?_
    refine div_le_div_of_nonneg_right (sqrt_le_sqrt ?_) (sqrt_nonneg _)
    have := hQ g hg
    have h1 := mul_le_mul_of_nonneg_left this (mul_nonneg hO2 (sq_nonneg (epsO n)))
    have h2 := mul_le_mul_of_nonneg_left this (mul_nonneg hε0 (by linarith : (0:ℝ) ≤ 7 + epsO n))
    nlinarith
  · refine (odd_wPass_err hn ho hJ c (nodeS c g) hO).trans ?_
    refine div_le_div_of_nonneg_right
      (mul_le_mul (sqrt_le_sqrt ?_) (sqrt_le_sqrt ?_) (sqrt_nonneg _) (sqrt_nonneg _))
      (Nat.cast_nonneg _)
    · have := hQ g hg
      have h1 := mul_le_mul_of_nonneg_left this (mul_nonneg hO2 (sq_nonneg (epsO n)))
      have h2 := mul_le_mul_of_nonneg_left this
        (mul_nonneg hε0 (by linarith : (0:ℝ) ≤ 7 + epsO n))
      nlinarith
    · have := hQ g hg
      have h1 := mul_le_mul_of_nonneg_left this hO2
      have h2 := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 8 + 3 * epsO n)
      nlinarith

end BstLean.Part278
