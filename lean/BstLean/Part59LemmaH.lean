import BstLean.Part59Defs
import BstLean.Part53Floor_Heat
import BstLean.Part53Elem

/-!
# Part 59, wave 1: Lemma H: the size of `h_r = binom(E, r) f` (Lemma Eu)

Specification: `delegations/answers/p59-spec-opus.md` §3.9. Source: `omDL2-opus-prover.md` §3.3,
Lemmas Eu and H; `chDL2-codex.md` ("The hardest checked step") restates the proof on coefficient blocks.

Suggested route (all on coefficient families; no analysis).
* `v = c₀/𝒟`. Lemma Eu on coefficients: `heatA k v (binA r A) = binom(L, r)(heatA k v A)` on the blocks
  `c ≥ 1`, where `(L B)_c = c·B_c + v(c+2)(c+1)·tr B_{c+2}` (`trL 1`). Prove it from the semigroup law
  `heatA k v ∘ heatA k (−v) = id` (on families vanishing above `k`) and `[E, Δ] = −2Δ`, or directly by
  comparing the coefficients of `tr^i A_{c+2i}` (a binomial identity in `C(c+2i, r)`).
* Seminorm `‖B‖_σ² = Σ_{c=1}^k σ^{2c}‖B_c‖²` (`NcA` is `‖heatA k v A‖_σ²`). The block `c` of `L B` uses
  only the blocks `c` and `c+2 ≥ 3`, so the block `0` never enters. With `‖tr B‖ ≤ √n‖B‖`
  (`Part53.lemmaTr53`) and `σ^c v = c₀σ^{c+2}`, `c₀ < 3`: `‖(L − j)B‖_σ ≤ (2k + 3k²√n)‖B‖_σ ≤
  5k²√n‖B‖_σ` for `j < r ≤ k`, `n ≥ 1`. `1/r! ≤ 1`. Square: `(5k²)^{2r} n^r`.
* `chDL2-opus.md` checked the ratio numerically (largest value `14.06` at `n = 4`, `k = 6`).

Replace each `sorry` by a proof. Do not edit the statements or `Part59Defs.lean`. Do not use
`native_decide` or `axiom` anywhere. This file imports `Part59Defs` only; a prover may also import
finished files of Parts 29–58, but no other Part 59 wave-1 file. Name private helpers with the suffix
`59x` or make them `private`, so that `Part59Final` does not see a name clash.
-/

namespace BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

open BstLean.Part53.FloorHeat

private lemma choose_step59x (j r : ℕ) :
    ((r + 1 : ℕ) : ℝ) * (j.choose (r + 1) : ℝ) =
      ((j : ℝ) - r) * (j.choose r : ℝ) := by
  by_cases h : r ≤ j
  · have he := Nat.choose_succ_right_eq j r
    have heR : (j.choose (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) =
        (j.choose r : ℝ) * ((j - r : ℕ) : ℝ) := by exact_mod_cast he
    rw [Nat.cast_sub h] at heR
    nlinarith
  · have hj : j < r := by omega
    simp [Nat.choose_eq_zero_of_lt hj, Nat.choose_eq_zero_of_lt (by omega : j < r + 1)]

private lemma heat_scale59x (k : ℕ) (v a : ℝ) (A : Tens n) :
    heatA k v (fun j w => a * A j w) = fun c w => a * heatA k v A c w := by
  classical
  funext c w
  simp only [heatA, trL, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma bin_step59x (r : ℕ) (A : Tens n) :
    (fun j w => ((r + 1 : ℕ) : ℝ) * binA (r + 1) A j w) =
      (fun (j : ℕ) w => ((j : ℝ) - r) * binA r A j w) := by
  funext j w
  simp only [binA, ← mul_assoc, choose_step59x]

private lemma heat_bin_zero59x (k : ℕ) (v : ℝ) (A : Tens n) :
    heatA k v (binA 0 A) = heatA k v A := by
  congr 1
  funext j w
  simp [binA]

private lemma heatWeight_step59x (c i : ℕ) (v : ℝ) :
    (2 * ((i + 1 : ℕ) : ℝ)) * heatWeight c (i + 1) v =
      v * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) * heatWeight (c + 2) i v := by
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  have hc : (c.factorial : ℝ) ≠ 0 := by positivity
  have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
  have hc1 : ((c : ℝ) + 1) ≠ 0 := by positivity
  have hc2 : ((c : ℝ) + 2) ≠ 0 := by positivity
  unfold heatWeight
  rw [show c + 2 * (i + 1) = c + 2 + 2 * i by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ]
  field_simp
  ring

private lemma heat_euler59x (k c : ℕ) (v a : ℝ) (A : Tens n)
    (w : Fin c → Fin n) :
    heatA k v (fun j z => ((j : ℝ) - a) * A j z) c w =
      ((c : ℝ) - a) * heatA k v A c w +
      v * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) *
        traceFamily 1 (heatA k v A) c w := by
  classical
  let S := (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)
  let U := (Finset.range (k + 1)).filter (fun i => c + 2 + 2 * i ≤ k)
  have hexpand : heatA k v (fun j z => ((j : ℝ) - a) * A j z) c w =
      ∑ i ∈ S, heatWeight c i v * (((c + 2 * i : ℕ) : ℝ) - a) *
        traceFamily i A c w := by
    unfold heatA trL
    simp only [← Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [heatWeight, traceFamily, trL]
    ring
  rw [hexpand]
  change _ = ((c : ℝ) - a) *
    (∑ i ∈ S, heatWeight c i v * traceFamily i A c w) + _
  rw [traceFamily_heat]
  change _ = ((c : ℝ) - a) *
    (∑ i ∈ S, heatWeight c i v * traceFamily i A c w) +
    v * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) *
    (∑ i ∈ U, heatWeight (c + 2) i v * traceFamily (1 + i) A c w)
  have hshift :
      (∑ i ∈ S, (2 * (i : ℝ)) * heatWeight c i v * traceFamily i A c w) =
      ∑ i ∈ U, v * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) *
        (heatWeight (c + 2) i v * traceFamily (1 + i) A c w) := by
    have hz : (∑ i ∈ S, (2 * (i : ℝ)) * heatWeight c i v * traceFamily i A c w) =
        ∑ i ∈ S.erase 0, (2 * (i : ℝ)) * heatWeight c i v * traceFamily i A c w := by
      symm
      apply Finset.sum_subset (Finset.erase_subset _ _)
      intro i hi hn
      have : i = 0 := by simpa [Finset.mem_erase, hi] using hn
      simp [this]
    rw [hz]
    apply Finset.sum_bij (fun i _ => i - 1)
    · intro i hi
      simp only [S, U, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at *
      omega
    · intro i hi j hj he
      simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at *
      omega
    · intro i hi
      refine ⟨i + 1, ?_, by omega⟩
      simp only [S, U, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at *
      omega
    · intro i hi
      have hi0 : 1 ≤ i := by have := (Finset.mem_erase.mp hi).1; omega
      have he := heatWeight_step59x c (i - 1) v
      rw [show i - 1 + 1 = i by omega] at he
      rw [he, show 1 + (i - 1) = i by omega]
      ring
  calc
    _ = ((c : ℝ) - a) * (∑ i ∈ S, heatWeight c i v * traceFamily i A c w) +
        ∑ i ∈ S, (2 * (i : ℝ)) * heatWeight c i v * traceFamily i A c w := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      ring
    _ = _ := by rw [hshift, ← Finset.mul_sum]

private lemma c0_bound59x (d : ℕ) : 0 ≤ c0 d ∧ c0 d ≤ 3 := by
  have hn : ∀ d : ℕ, c0 (d + 1) + 1 / ((d + 1).factorial : ℝ) ≤ 3 := by
    intro d
    induction d with
    | zero => norm_num [c0, Finset.sum_range_succ]
    | succ d ih =>
      have hf : (0 : ℝ) < (d + 1).factorial := by positivity
      have hd : (2 : ℝ) ≤ (d : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
      have he : 2 / ((d + 2).factorial : ℝ) ≤ 1 / ((d + 1).factorial : ℝ) := by
        rw [show d + 2 = (d + 1) + 1 by omega, Nat.factorial_succ]
        push_cast
        apply (div_le_div_iff₀ (by positivity) hf).mpr
        nlinarith
      have hsum : c0 (d + 2) = c0 (d + 1) + 1 / ((d + 2).factorial : ℝ) := by
        simp only [c0, show d + 2 + 1 = (d + 1 + 1) + 1 by omega,
          Finset.sum_range_succ]
      rw [show d + 1 + 1 = d + 2 by omega, hsum]
      have he' : 1 / ((d + 2).factorial : ℝ) + 1 / ((d + 2).factorial : ℝ) ≤
          1 / ((d + 1).factorial : ℝ) := by simpa only [← add_div, one_add_one_eq_two] using he
      linarith
  constructor
  · unfold c0
    positivity
  · cases d with
    | zero => norm_num [c0]
    | succ d =>
      have hh := hn d
      have hp : (0 : ℝ) ≤ 1 / ((d + 1).factorial : ℝ) := by positivity
      linarith

private lemma heat_bin_step59x (k r c : ℕ) (v : ℝ) (A : Tens n)
    (w : Fin c → Fin n) :
    ((r + 1 : ℕ) : ℝ) * heatA k v (binA (r + 1) A) c w =
      ((c : ℝ) - r) * heatA k v (binA r A) c w +
      v * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) *
        traceFamily 1 (heatA k v (binA r A)) c w := by
  have hs := congrFun (congrFun (heat_scale59x k v ((r + 1 : ℕ) : ℝ) (binA (r + 1) A)) c) w
  rw [← hs, bin_step59x]
  exact heat_euler59x k c v r (binA r A) w

private lemma frob_nonneg59x {j : ℕ} (A : (Fin j → Fin n) → ℝ) : 0 ≤ frob A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma shift_sum59x (k : ℕ) (f : ℕ → ℝ) (hf : ∀ c, 0 ≤ f c)
    (hz : ∀ c, k < c → f c = 0) :
    (∑ c ∈ Finset.Icc 1 k, f (c + 2)) ≤ ∑ c ∈ Finset.Icc 1 k, f c := by
  have he : (∑ c ∈ Finset.Icc 1 k, f (c + 2)) =
      ∑ c ∈ Finset.Icc 3 (k + 2), f c := by
    apply Finset.sum_bij (fun c _ => c + 2)
    · intro c hc; simp only [Finset.mem_Icc] at *; omega
    · intro c hc j hj he; omega
    · intro c hc
      refine ⟨c - 2, ?_, ?_⟩ <;> simp only [Finset.mem_Icc] at * <;> omega
    · intro c hc; rfl
  rw [he]
  calc
    _ ≤ ∑ c ∈ Finset.Icc 1 (k + 2), f c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro c hc; simp only [Finset.mem_Icc] at *; omega
      · intro c hc hn; exact hf c
    _ = ∑ c ∈ Finset.Icc 1 k, f c := by
      symm
      apply Finset.sum_subset
      · intro c hc; simp only [Finset.mem_Icc] at *; omega
      · intro c hc hn
        apply hz
        simp only [Finset.mem_Icc] at *
        omega

private lemma plain_step59x (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ k)
    (n : ℕ) (hn : 1 ≤ n) (D b : ℝ) (hD : 0 < D) (hb : 0 ≤ b) (hb3 : b ≤ 3)
    (B C : Tens n) (hzero : ∀ c, k < c → B c = 0)
    (hstep : ∀ c w, ((r + 1 : ℕ) : ℝ) * C c w =
      ((c : ℝ) - r) * B c w +
      (b / D) * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) * traceFamily 1 B c w) :
    (∑ c ∈ Finset.Icc 1 k, frob (C c) / D ^ c) ≤
      (5 * (k : ℝ) ^ 2) ^ 2 * n *
        ∑ c ∈ Finset.Icc 1 k, frob (B c) / D ^ c := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (r : ℝ) ≤ k := by exact_mod_cast hr
  have htr (c : ℕ) : frob (traceFamily 1 B c) ≤ (n : ℝ) * frob (B (c + 2)) := by
    rw [traceFamily_frob]
    simpa using BstLean.Part53.lemmaTr53 n (c + 2) 1 (B (c + 2)) (by omega)
  have hblock (c : ℕ) (hc : c ∈ Finset.Icc 1 k) :
      frob (C c) / D ^ c ≤
        2 * (k : ℝ) ^ 2 * (frob (B c) / D ^ c) +
        18 * (k : ℝ) ^ 4 * n * (frob (B (c + 2)) / D ^ (c + 2)) := by
    have hcK : c ≤ k := (Finset.mem_Icc.mp hc).2
    have hcR : (c : ℝ) ≤ k := by exact_mod_cast hcK
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have hcr : ((c : ℝ) - r) ^ 2 ≤ (k : ℝ) ^ 2 := by
      have hr0 : (0 : ℝ) ≤ r := by positivity
      nlinarith
    have hsq (w : Fin c → Fin n) :
        C c w ^ 2 ≤ 2 * (k : ℝ) ^ 2 * B c w ^ 2 +
          2 * ((b / D) * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ)) ^ 2 *
            traceFamily 1 B c w ^ 2 := by
      have hs := hstep c w
      have hmul : C c w ^ 2 ≤ (((r + 1 : ℕ) : ℝ) * C c w) ^ 2 := by
        have hp : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
        have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 by nlinarith) (sq_nonneg (C c w))
        nlinarith
      rw [hs] at hmul
      have hh := mul_le_mul_of_nonneg_right hcr (sq_nonneg (B c w))
      nlinarith [sq_nonneg (((c : ℝ) - r) * B c w -
        (b / D) * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) * traceFamily 1 B c w)]
    have hF : frob (C c) ≤ 2 * (k : ℝ) ^ 2 * frob (B c) +
        2 * ((b / D) * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ)) ^ 2 *
          frob (traceFamily 1 B c) := by
      calc
        _ ≤ ∑ w, (2 * (k : ℝ) ^ 2 * B c w ^ 2 +
            2 * ((b / D) * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ)) ^ 2 *
              traceFamily 1 B c w ^ 2) := Finset.sum_le_sum (fun w _ => hsq w)
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
    have hF' := hF.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (htr c)
        (show 0 ≤ 2 * ((b / D) * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ)) ^ 2 by positivity)))
    have hweight :
        2 * ((b / D) * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ)) ^ 2 * n *
          frob (B (c + 2)) / D ^ c ≤
        18 * (k : ℝ) ^ 4 * n * (frob (B (c + 2)) / D ^ (c + 2)) := by
      by_cases hh : c + 2 ≤ k
      · have hc2 : ((c + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast hh
        have hc1 : ((c + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (show c + 1 ≤ k by omega)
        have hprod : b * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) ^ 2 := by
          calc
            _ ≤ 3 * (k : ℝ) * (k : ℝ) :=
              mul_le_mul (mul_le_mul hb3 hc2 (by positivity) (by positivity)) hc1
                (by positivity) (by positivity)
            _ = _ := by ring
        have hsquare : (b * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ)) ^ 2 ≤ 9 * (k : ℝ) ^ 4 := by
          have hp := pow_le_pow_left₀
            (show 0 ≤ b * ((c + 2 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) by positivity) hprod 2
          convert hp using 1
          ring
        have hm := mul_le_mul_of_nonneg_right hsquare
          (show 0 ≤ 2 * (n : ℝ) * (frob (B (c + 2)) / D ^ (c + 2)) by
            exact mul_nonneg (by positivity) (div_nonneg (frob_nonneg59x _) (by positivity)))
        have hpow : D ^ (c + 2) = D ^ c * D ^ 2 := by rw [pow_add]
        rw [hpow] at hm ⊢
        convert hm using 1
        field_simp
        all_goals ring
      · rw [hzero (c + 2) (by omega)]
        simp [frob]
    have hh := div_le_div_of_nonneg_right hF' (le_of_lt (pow_pos hD c))
    rw [add_div, mul_div_assoc] at hh
    exact hh.trans (add_le_add le_rfl (by simpa only [mul_assoc] using hweight))
  have hsum := Finset.sum_le_sum hblock
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hshift := shift_sum59x k (fun c => frob (B c) / D ^ c)
    (fun c => div_nonneg (frob_nonneg59x _) (by positivity))
    (fun c hc => by rw [hzero c hc]; simp [frob])
  have hN : 0 ≤ ∑ c ∈ Finset.Icc 1 k, frob (B c) / D ^ c := by
    exact Finset.sum_nonneg (fun c hc => div_nonneg (frob_nonneg59x _) (by positivity))
  have hcoeff : 2 * (k : ℝ) ^ 2 + 18 * (k : ℝ) ^ 4 * n ≤
      (5 * (k : ℝ) ^ 2) ^ 2 * n := by
    have hk2 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by nlinarith [sq_nonneg ((k : ℝ) ^ 2 - 1)]
    have hkn : (k : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 * n := by nlinarith
    nlinarith
  calc
    _ ≤ _ := hsum
    _ ≤ (2 * (k : ℝ) ^ 2 + 18 * (k : ℝ) ^ 4 * n) *
        ∑ c ∈ Finset.Icc 1 k, frob (B c) / D ^ c := by
      have hh := mul_le_mul_of_nonneg_left hshift (show 0 ≤ 18 * (k : ℝ) ^ 4 * n by positivity)
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hN

/-- **Lemma H.** -/
theorem lemmaH59 (d k : ℕ) (hk : 1 ≤ k) : LemmaH59 d k := by
  intro n hn A hA r hr hrk
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn
  have hh : ∀ r : ℕ, r ≤ k →
      NcA n d k (binA r A) ≤
        (5 * (k : ℝ) ^ 2) ^ (2 * r) * (n : ℝ) ^ r * NcA n d k A := by
    intro r
    induction r with
    | zero =>
      intro hrk
      simp only [NcA, heat_bin_zero59x, Nat.mul_zero, pow_zero, one_mul]
      exact le_rfl
    | succ r ih =>
      intro hrk
      have hBzero : ∀ c, k < c → heatA k (c0 d / DD n d) (binA r A) c = 0 := by
        intro c hc
        have he : (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k) = ∅ := by
          ext i
          simp
          omega
        funext w
        simp [heatA, he]
      have hs := plain_step59x k r hk (by omega) n hn (DD n d) (c0 d) hD
        (c0_bound59x d).1 (c0_bound59x d).2
        (heatA k (c0 d / DD n d) (binA r A))
        (heatA k (c0 d / DD n d) (binA (r + 1) A)) hBzero
        (fun c w => heat_bin_step59x k r c (c0 d / DD n d) A w)
      change NcA n d k (binA (r + 1) A) ≤
        (5 * (k : ℝ) ^ 2) ^ 2 * n * NcA n d k (binA r A) at hs
      calc
        _ ≤ _ := hs
        _ ≤ (5 * (k : ℝ) ^ 2) ^ 2 * n *
            ((5 * (k : ℝ) ^ 2) ^ (2 * r) * (n : ℝ) ^ r * NcA n d k A) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
        _ = _ := by
          rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add, pow_succ]
          ring
  exact hh r hrk

end BstLean.Part59
