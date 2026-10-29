import BstLean.Part145K2
import BstLean.Part143Final

/-!
# Part 145 (K3): the `L²` bound of the distance kernel with the sharper centred part

The assembly of `Part143Asm` and `Part143Final` with the bound `cAg_L2x` (file `Part145K2`) of
the centred part `cAg` of the Agent link in the place of `cAg_L2`. The functions `kX1 … kX5`,
`cAg` and the events are NOT changed; only the bound of `X3` changes.

* `asmE3x c0 c1 c1' c2 τ = c0 + c1·(1 − κ^{∘6}(0) + σ₄·τ) − c1'·(1 − κ^{∘4}(0)) +
    c2·(1 − κ(κ(0))) + (c1' + c2)·τ`: the bound of `X3/S`.
* `kX3_L2x`: `‖X3‖₂ ≤ S·asmE3x`.
* `kernDist145_of`: the copy of `kernDist143_of` with the new bound of `cA`.
* `eD145 n`, **`kernDist145`**: `‖kD − S(1 − Q)‖₂ ≤ S·eD145 n`, every `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143

/-! ## The constant -/

/-- The bound of `X3/S` with the negative term of `cAg_L2x`. -/
noncomputable def asmE3x (c0 c1 c1' c2 τ : ℝ) : ℝ :=
  c0 + c1 * (1 - kappa^[6] 0 + sig4 * τ) - c1' * (1 - kappa^[4] 0) +
    c2 * (1 - kappa (kappa 0)) + (c1' + c2) * τ

/-- `asmE3x ≥ 0` if its value at `τ = 0` is `≥ 0`. -/
lemma asmE3x_nonneg {c0 c1 c1' c2 τ : ℝ} (h1 : 0 ≤ c1) (h1' : 0 ≤ c1') (h2 : 0 ≤ c2)
    (hτ : 0 ≤ τ)
    (hC : 0 ≤ c0 + c1 * (1 - kappa^[6] 0) - c1' * (1 - kappa^[4] 0) +
      c2 * (1 - kappa (kappa 0))) :
    0 ≤ asmE3x c0 c1 c1' c2 τ := by
  have hs := sig4_nonneg
  have a1 : 0 ≤ c1 * (sig4 * τ) := by positivity
  have a2 : 0 ≤ (c1' + c2) * τ := by positivity
  unfold asmE3x
  linarith

section General

variable {N mW n mA mF : ℕ}

/-- `‖X3‖₂ ≤ S·asmE3x`. -/
theorem kX3_L2x (hn : 1 ≤ n) (hN : 1 ≤ N)
    {cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hcAm : Measurable (fun p : MlpParam n mA n × (Fin n → ℝ) × (Fin n → ℝ) =>
      cA p.1 p.2.1 p.2.2))
    {c0 c1 c1' c2 τ : ℝ} (h1 : 0 ≤ c1) (h1' : 0 ≤ c1') (h2 : 0 ≤ c2) (hτ : 0 ≤ τ)
    (hC : 0 ≤ c0 + c1 * (1 - kappa^[6] 0) - c1' * (1 - kappa^[4] 0) +
      c2 * (1 - kappa (kappa 0)))
    (hcL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n) (fun A : MlpParam n mA n => cA A x x')
        (2 * (c0 + c1 * (1 - kappa^[4] (dotp x x')) - c1' * (1 - kappa (kappa (dotp x x'))) +
          c2 * (1 - dotp x x'))))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (kX3 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) cA)
      (4 / (n : ℝ) * asmE3x c0 c1 c1' c2 τ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := tX_lin_L2 (mW := mW) hn hN (g0 := c0) (g1 := -c1') (g2 := c2) (g3 := c1) h2 h1 hτ
    (by linarith) hT
  rw [abs_neg, abs_of_nonneg h1'] at hb
  have hXm : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) (x x' : Fin n → ℝ) =>
        2 / (n : ℝ) * cA p.1 x x') z.1 z.2.1 z.2.2) :=
    (hcAm.comp (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (z.1.1, z.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).const_mul _
  have key := lift_L2 (mW := mW) hn hN hXm hb (fun x x' hx hx' => by
    have hg := ((hcL x x' hx hx').const_mul_nonneg (c := 2 / (n : ℝ)) (by positivity)).comp_fst
      (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1))
    refine hg.congr_bound ?_
    unfold linB
    ring)
  refine (key.congr_fun fun ω => rfl).congr_bound ?_
  unfold asmE3x
  ring

/-- **The distance kernel under `(u, u′) ⊗ (W, A, A′, F)`, with the two orthogonality steps and
the bound of the centred part `cA` with a negative term.** The copy of `kernDist143_of`. -/
theorem kernDist145_of (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    {cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hcAm : Measurable (fun p : MlpParam n mA n × (Fin n → ℝ) × (Fin n → ℝ) =>
      cA p.1 p.2.1 p.2.2))
    {c0 c1 c1' c2 r0 r1 r1' r2 τ pW : ℝ}
    (hc1 : 0 ≤ c1) (hc1' : 0 ≤ c1') (hc2 : 0 ≤ c2) (hr1 : 0 ≤ r1) (hr1' : 0 ≤ r1')
    (hr2 : 0 ≤ r2) (hτ : 0 ≤ τ)
    (hcC : 0 ≤ c0 + c1 * (1 - kappa^[6] 0) - c1' * (1 - kappa^[4] 0) +
      c2 * (1 - kappa (kappa 0)))
    (hrC : 0 ≤ r0 + r1 * (1 - kappa^[6] 0) - r1' * (1 - kappa^[4] 0) +
      r2 * (1 - kappa (kappa 0)))
    (hcI : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      Integrable (fun A : MlpParam n mA n => cA A x x') (mlpGauss n mA n) ∧
        ∫ A, cA A x x' ∂mlpGauss n mA n = 0)
    (hcL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n) (fun A : MlpParam n mA n => cA A x x')
        (2 * (c0 + c1 * (1 - kappa^[4] (dotp x x')) - c1' * (1 - kappa (kappa (dotp x x'))) +
          c2 * (1 - dotp x x'))))
    (hrL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
          2 * (1 - kappa^[4] (dotp x x')) - cA A x x')
        (2 * (r0 + r1 * (1 - kappa^[4] (dotp x x')) - r1' * (1 - kappa (kappa (dotp x x'))) +
          r2 * (1 - dotp x x'))))
    {d0 d1 d2 δ2 : ℝ} (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hδ2 : 0 ≤ δ2)
    (hDiff : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => normSq (mlpEval A x - mlpEval A x'))
      (4 * (d0 + d1 * (1 - kappa (kappa (dotp x x'))) + d2 * (1 - dotp x x'))))
    (hDlt : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => dlt (mlpEval A x) (mlpEval A x')) (2 * δ2))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ)
    (hW5 : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        kappa^[4] (tX z) - kappa^[6] 0) pW) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * √(asmE1 mF d0 d1 d2 τ ^ 2 +
        (asmE2 n mA mF d0 d1 d2 δ2 τ + asmE4 r0 r1 r1' r2 τ +
          √(asmE3x c0 c1 c1' c2 τ ^ 2 + pW ^ 2)) ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS0 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
  have g1 := kX1_L2 (mW := mW) (mA := mA) hn hN hmF hd0 hd1 hd2 hτ hDiff hT
  have g2 := kX2_L2 (mW := mW) hn hN hmA hmF hd0 hd1 hd2 hδ2 hτ hDiff hDlt hT
  have g3 := kX3_L2x (mW := mW) (mF := mF) hn hN hcAm hc1 hc1' hc2 hτ hcC hcL hT
  have g4 := kX4_L2 (mW := mW) (mF := mF) hn hN hcAm hr1 hr1' hr2 hτ hrC hrL hT
  have g5 := kX5_L2 (mA := mA) (mF := mF) hN hn hW5
  have e2 := asmE2_nonneg n mA mF hd0 hd1 hd2 hδ2 hτ
  have e4 : 0 ≤ asmE4 r0 r1 r1' r2 τ := by
    have := sig4_nonneg
    have : 0 ≤ (r1 * sig4 + r1' + r2) * τ := by positivity
    unfold asmE4; linarith
  have g35 := L2le.add_orth g3 g5 (cross35 hN hcI hn)
  have gY := (g2.add0 g4 (by positivity) (by positivity)).add0 g35 (by positivity)
    (Real.sqrt_nonneg _)
  have gAll := L2le.add_orth g1 gY (cross1 hN hmF cA)
  refine (gAll.congr_fun fun ω => (kD_split cA ω).symm).congr_bound ?_
  have q1 : √((4 / (n : ℝ) * asmE3x c0 c1 c1' c2 τ) ^ 2 + (4 / (n : ℝ) * pW) ^ 2) =
      4 / (n : ℝ) * √(asmE3x c0 c1 c1' c2 τ ^ 2 + pW ^ 2) := by
    have e : (4 / (n : ℝ) * asmE3x c0 c1 c1' c2 τ) ^ 2 + (4 / (n : ℝ) * pW) ^ 2 =
        (4 / (n : ℝ)) ^ 2 * (asmE3x c0 c1 c1' c2 τ ^ 2 + pW ^ 2) := by ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS0]
  rw [q1]
  set R : ℝ := √(asmE3x c0 c1 c1' c2 τ ^ 2 + pW ^ 2) with hR
  have e : (4 / (n : ℝ) * asmE1 mF d0 d1 d2 τ) ^ 2 +
      (4 / (n : ℝ) * asmE2 n mA mF d0 d1 d2 δ2 τ + 4 / (n : ℝ) * asmE4 r0 r1 r1' r2 τ +
        4 / (n : ℝ) * R) ^ 2 =
      (4 / (n : ℝ)) ^ 2 * (asmE1 mF d0 d1 d2 τ ^ 2 +
        (asmE2 n mA mF d0 d1 d2 δ2 τ + asmE4 r0 r1 r1' r2 τ + R) ^ 2) := by ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS0]

end General

/-! ## The Focus widths -/

/-- `0 ≤ cC0x + cC1·(1 − κ^{∘6}(0)) − cC1x'·(1 − κ^{∘4}(0)) + cC2x·(1 − κ(κ(0)))`. -/
lemma cC_ref_nonneg (n m : ℕ) :
    0 ≤ cC0x n m + cC1 n * (1 - kappa^[6] 0) - cC1x' n * (1 - kappa^[4] 0) +
      cC2x n m * (1 - kappa (kappa 0)) := by
  have h0 := cC0x_nonneg n m
  have h2 := mul_nonneg (cC2x_nonneg n m) a2_nonneg
  have h6 : 222757 / 1000000 ≤ 1 - kappa^[6] 0 := by have := kappa6_zero_le''; linarith
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 := one_sub_k4_nonneg
  have hs2 := sqrt2_geK
  have hs : (0 : ℝ) ≤ 1 / √(n : ℝ) := by positivity
  have e : cC1 n * (1 - kappa^[6] 0) - cC1x' n * (1 - kappa^[4] 0) =
      1 / √(n : ℝ) * (√2 * (1 - kappa^[6] 0) - dK * (1 - kappa^[4] 0)) := by
    unfold cC1 cC1x'; ring
  have h1 : 0 ≤ √2 * (1 - kappa^[6] 0) - dK * (1 - kappa^[4] 0) := by
    have a : dK * (1 - kappa^[4] 0) ≤ 55 / 1000 * (319057 / 1000000) := by
      unfold dK
      exact mul_le_mul_of_nonneg_left h4 (by norm_num)
    have b : 14142 / 10000 * (222757 / 1000000) ≤ √2 * (1 - kappa^[6] 0) :=
      mul_le_mul hs2 h6 (by norm_num) (by positivity)
    linarith
  have := mul_nonneg hs h1
  linarith

/-- `asmE3x` at the constants of the Focus is `≥ 0`. -/
lemma asmE3x_focus_nonneg (n m : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ asmE3x (cC0x n m) (cC1 n) (cC1x' n) (cC2x n m) τ :=
  asmE3x_nonneg (cC1_nonneg n) (cC1x'_nonneg n) (cC2x_nonneg n m) hτ (cC_ref_nonneg n m)

/-- **`kernDist145_of` at the widths of the Focus**, `n ≥ 4096`, with `cA = cAg`; the two facts
of the World network stay hypotheses. -/
theorem kernDist145_focus {n : ℕ} (hn : 4096 ≤ n) {τ pW : ℝ} (hτ : 0 ≤ τ)
    (hT : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) τ)
    (hW5 : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        kappa^[4] (tX z) - kappa^[6] 0) pW) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * √(asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) τ ^ 2 +
        (asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (cAdlt n (mA n)) τ +
          asmE4 (rR0 n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) τ +
          √(asmE3x (cC0x n (mA n)) (cC1 n) (cC1x' n) (cC2x n (mA n)) τ ^ 2 + pW ^ 2)) ^ 2)) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  exact kernDist145_of (cA := cAg) hn1 hN hmA hmF measurable_cAg
    (cC1_nonneg n) (cC1x'_nonneg n) (cC2x_nonneg n (mA n)) (rR1_nonneg n) (rR1'_nonneg n)
    (rR2_nonneg n (mA n)) hτ (cC_ref_nonneg n (mA n)) (rR_ref_nonneg n (mA n))
    (fun x x' hx hx' => cAg_integral hn1 hmA hx hx')
    (fun x x' hx hx' => cAg_L2x hn1 hmA hx hx')
    (fun x x' hx hx' => agent_rem_L2 hn1 hmA hx hx')
    (dA0_nonneg n (mA n)) (dA1_nonneg n (mA n)) (dA2_nonneg n (mA n)) (cAdlt_nonneg n (mA n))
    (fun x x' hx hx' => agent_diff_L2_of reluEDStmt reluPhiStmt hn1 hmA hx hx')
    (fun x x' hx hx' => agent_dlt_L2_of reluSqStmt reluDltStmt linDltStmt hn1 hmA hx hx')
    hT hW5

/-- **The `L²` error of the distance kernel with the orthogonal blocks and the sharper centred
part.** The copy of `eD143` with `asmE3x` in the place of `asmE3`. -/
noncomputable def eD145 (n : ℕ) : ℝ :=
  √(asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (tau143s n) ^ 2 +
    (asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (cAdlt n (mA n))
        (tau143s n) +
      asmE4 (rR0 n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) (tau143s n) +
      √(asmE3x (cC0x n (mA n)) (cC1 n) (cC1x' n) (cC2x n (mA n)) (tau143s n) ^ 2 +
        (sig4 * tau143s n) ^ 2)) ^ 2)

lemma eD145_nonneg (n : ℕ) : 0 ≤ eD145 n := Real.sqrt_nonneg _

/-- **`kernDist145`**: `‖kD − S(1 − Q)‖₂ ≤ S·eD145 n`, every `n ≥ 4096`. -/
theorem kernDist145 {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * eD145 n) := by
  have hT := tX_L2_143s hn
  exact kernDist145_focus hn (tau143s_nonneg n) hT (chord_pW (by omega) hT)

end BstLean.Part145

open BstLean.Part145 in
#print axioms cUnit_L2x
open BstLean.Part145 in
#print axioms cAg_L2x
open BstLean.Part145 in
#print axioms kernDist145_of
open BstLean.Part145 in
#print axioms kernDist145
open BstLean.Part145 in
#print axioms cC0x_le
open BstLean.Part145 in
#print axioms cC2x_le
