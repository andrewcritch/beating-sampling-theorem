import BstLean.Part278Final

/-!
# Part 278 (O3 + O4 on the good set): the odd root on `goodD` and in the World window

* `aw_sq_le`: `a_i(s)² ≤ 2|row_i(A₁)|²` for `s² ≤ 1`.
* `frob_le`: `Σ_i |row_i(A₁)|² ≤ n·O²` from the operator bound `O` of `A₁`.
* `O1n_sq_le`, `O2n_le`, `OpB_mono`, `nodeS_mem`, `qB_nonneg`, `Jz_pos`.
* **`odd_root_good`**: for odd `n ≥ 16 384`, on `goodD n (paperDesignP n) EA` (which carries the
  operator events of `A₁` and `A₂`, `Part169.opB_goodD`), with `τ₀ > 0` and
  `0.46 ≤ θ ≤ 0.55` (the inputs of `Part169.bulk_of_window`), `e_b > 0` and
  `|c_A|² ≤ 2 e_b χ` with `0 ≤ χ ≤ n` (the field `hc` of `Part241.PassInputs`):
  `|√q̃(statedDesign n) − √q̃(paperDesignP n)| ≤ 10⁻²⁰`.
-/

namespace BstLean.Part278

open Real
open BstLean.Part130 (normSq normSq_nonneg mA)
open BstLean.Part157 (Ret qTilde Js)
open BstLean.Part169 (A1 A2 OpB Jz nodeS nodeL nodeH nodeD eR O1n O2n paperDesignP tauR qB
  opB_goodD bulk_of_window)
open BstLean.Part272 (statedDesign alphaE kappaE kappaE_eq normSq_wTail)

variable {n : ℕ}

theorem aw_sq_le (hn : 1 ≤ n) (c : Ret n) (s : ℝ) (hs : s ^ 2 ≤ 1) (i : Fin (mA n)) :
    aw c s i ^ 2 ≤ 2 * ∑ j, A1 c i j ^ 2 := by
  have hk : kappaE c i ^ 2 = ∑ j, A1 c i j ^ 2 - alphaE c i ^ 2 := by
    rw [kappaE_eq hn, sq_sqrt (normSq_nonneg _), normSq_wTail hn]
  have h1 : |s| ^ 2 ≤ 1 := by rw [sq_abs]; exact hs
  have h2 : |s| ^ 2 * |alphaE c i| ^ 2 ≤ alphaE c i ^ 2 := by
    calc |s| ^ 2 * |alphaE c i| ^ 2 ≤ 1 * |alphaE c i| ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = alphaE c i ^ 2 := by rw [one_mul, sq_abs]
  unfold aw
  nlinarith [sq_nonneg (|s| * |alphaE c i| - kappaE c i)]

theorem frob_le (c : Ret n) {O : ℝ} (hO : OpB (A1 c) O) :
    ∑ i, ∑ j, A1 c i j ^ 2 ≤ n * O ^ 2 := by
  have key : ∀ j : Fin n, ∑ i, A1 c i j ^ 2 ≤ O ^ 2 := by
    intro j
    have h := hO (Pi.single j 1)
    have e1 : (A1 c).mulVec (Pi.single j 1) = fun i => A1 c i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have e2 : normSq (Pi.single j (1:ℝ)) = 1 := by
      unfold normSq; simp [Pi.single_apply]
    rw [e1, e2, mul_one] at h
    exact h
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, A1 c i j ^ 2 ≤ ∑ _j : Fin n, O ^ 2 := Finset.sum_le_sum fun j _ => key j
    _ = n * O ^ 2 := by simp

theorem O1n_sq_le (hn : 4 ≤ n) : O1n n ^ 2 ≤ 8 * n := by
  have hn4 : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hsq : √(n:ℝ) ^ 2 = n := sq_sqrt hn0.le
  have hs0 : 0 ≤ √(n:ℝ) := sqrt_nonneg _
  have h2 : 2 ≤ √(n:ℝ) := by nlinarith
  have h3 : 2 * √(n:ℝ) ≤ n := by nlinarith
  unfold O1n
  rw [mul_pow, sq_sqrt (by positivity), div_mul_eq_mul_div, div_le_iff₀ hn0]
  nlinarith

theorem O2n_nonneg : 0 ≤ O2n n := by unfold O2n; positivity

theorem O2n_le (hn : 50 ≤ n) : O2n n ≤ 3 := by
  have hn5 : (50:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have h : O2n n ^ 2 ≤ 3 ^ 2 := by
    unfold O2n mA
    push_cast
    rw [mul_pow, sq_sqrt (by positivity), div_mul_eq_mul_div, div_le_iff₀ (pow_pos hn0 2)]
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) h

theorem OpB_mono {k m : ℕ} {A : Matrix (Fin m) (Fin k) ℝ} {O O' : ℝ} (h : OpB A O) (hO : 0 ≤ O)
    (hOO : O ≤ O') : OpB A O' := fun z =>
  (h z).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hO hOO 2) (normSq_nonneg _))

theorem nodeS_mem (hn : 1 ≤ n) (c : Ret n) (hLH : nodeL c < nodeH c) (g : ℕ)
    (hg : g ≤ Js n - 1) : nodeL c ≤ nodeS c g ∧ nodeS c g ≤ nodeH c := by
  have hJn : 0 < Js n := by unfold Js; omega
  have hJ : (0:ℝ) < Js n := by exact_mod_cast hJn
  have hg1 : g + 1 ≤ Js n := by omega
  have hg' : (g:ℝ) + 1 / 2 ≤ Js n := by
    have := (Nat.cast_le (α := ℝ)).mpr hg1
    push_cast at this
    linarith
  have hD : 0 ≤ (nodeH c - nodeL c) / (Js n : ℝ) := div_nonneg (by linarith) hJ.le
  have hg0 : (0:ℝ) ≤ (g:ℝ) + 1 / 2 := by positivity
  have e : (Js n : ℝ) * ((nodeH c - nodeL c) / (Js n : ℝ)) = nodeH c - nodeL c := by
    field_simp
  unfold nodeS nodeD
  constructor
  · nlinarith [mul_nonneg hg0 hD]
  · have := mul_le_mul_of_nonneg_right hg' hD
    linarith

theorem qB_nonneg (hn : 16384 ≤ n) : 0 ≤ qB n := by
  unfold qB
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 6 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have h4 : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 771 / 1000 := by linarith
  nlinarith

theorem Jz_pos (hn : 2 ≤ n) : 1 ≤ Jz n := by
  have hn2 : (1:ℝ) < n := by exact_mod_cast hn
  have h : (1:ℝ) < (n:ℝ) ^ ((3:ℝ) / 2) := one_lt_rpow hn2 (by norm_num)
  have h2 : 1 < ⌈(n:ℝ) ^ ((3:ℝ) / 2)⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast h)
  unfold Jz
  omega

/-- **The odd root on the good set and in the World window (`n ≥ 16 384`).** -/
theorem odd_root_good (hn : 16384 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n) {EA : Set (Ret n)}
    (hgood : c ∈ BstLean.Part166.goodD n (paperDesignP n) EA) (hτ : 0 < tauR c)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c))
    (hθ1 : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100)
    {χ : ℝ} (he : 0 < eR c) (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ n) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20 := by
  obtain ⟨h1, h2⟩ := opB_goodD hn hgood
  obtain ⟨hLH, hs, -⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  have hq := qB_nonneg hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  refine odd_root_lt (by omega) ho (Jz_pos (by omega)) t c
    (OpB_mono h2 O2n_nonneg (O2n_le (by omega))) (fun g hg => ?_) he hc hχ0 hχ
  obtain ⟨hL, hH⟩ := nodeS_mem (by omega) c hLH g hg
  have hs1 : (nodeS c g) ^ 2 ≤ 1 := by have := hs _ hL hH; linarith
  have hO1 := O1n_sq_le (n := n) (by omega)
  have hF := frob_le c h1
  calc ∑ i, aw c (nodeS c g) i ^ 2 ≤ ∑ i, 2 * ∑ j, A1 c i j ^ 2 :=
        Finset.sum_le_sum fun i _ => aw_sq_le (by omega) c _ hs1 i
    _ = 2 * ∑ i, ∑ j, A1 c i j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (n * O1n n ^ 2) := by linarith
    _ ≤ 2 * (n * (8 * n)) := by
        have := mul_le_mul_of_nonneg_left hO1 (by linarith : (0:ℝ) ≤ n)
        linarith
    _ ≤ 16 * (n : ℝ) ^ 3 := by
        have : (n:ℝ) ^ 2 ≤ (n:ℝ) ^ 3 := pow_le_pow_right₀ hnR (by norm_num)
        nlinarith

end BstLean.Part278
