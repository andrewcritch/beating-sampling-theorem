import BstLean.Part142AgentS
import BstLean.Part142Big
import BstLean.Part142Core2

/-!
# Part 142, items 2 to 4 (the headlines `kernel142`, `spread142`, `arithProgSucceeds142`,
`arithProg142_99`)

Role: `delegations/statements/p142-spec.md`. The program is `arithProg141 k n` of Part 141,
UNCHANGED; `gProgA` is its output, `okProgA k n` the event `|gProgA − B| ≤ sd/2`.

This file uses the secant link of the last matrix of `A` (`agent_phiS_L2`, `Part142AgentS`) in
the distance kernel, and the variance of the stand-in (`Part142Var2`).

* **`kernDist142`** (`kernel142`): `‖kD − S(1 − Q)‖₂ ≤ S·eD142 n`, `n ≥ 4096`;
  `eD142_scale`: `eD142 n ≤ 1.835/√n` (`n ≥ 4096`); `eD142_big`: `≤ 1.327/√n` (`n ≥ 32768`).
* **`spread142`**: `Pr(sd² < θ·S(1 − Q)) ≤ 3·eD142²/((1 − θ)(1 − Q))²`; with numbers
  `≤ 10.11/((1 − θ)(1 − Q))²/n` (Part 139: `64/…`).
* **`arithProgSucceeds142`** (the headline): `Pr(|gProgA − B| ≤ sd/2) ≥
  1 − (0.002 + 428/n + 134/k)`, every `n ≥ 4096`, `k ≥ 1` (Part 141: `2031/n + 180/k`).
* **`arithProg142_99`**: level `99/100` for every `n ≥ 32768`, `k ≥ 100n` (Part 141:
  `n ≥ 253875`). `32768 = 2·16384` is OUTSIDE the frontier interval `[4096, 16384]`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141

/-- The constants of the distance kernel at fixed inputs with the secant link:
`hD0 + hD1·(1 − κ(κ(t))) + hD2·(1 − t) + hD3·(1 − κ^{∘4}(t))`; `hD1` has no fixed sign. -/
noncomputable def hD0 (n : ℕ) : ℝ :=
  2 * f1 (mF n) * dA0 n (mA n) +
    2 * f2 (mF n) * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) +
    2 * f3 (mF n) * √(eps4 n (mA n)) + f4 * cAdlt n (mA n) + sA0 n (mA n)

noncomputable def hD1 (n : ℕ) : ℝ := 2 * f1 (mF n) * dA1 n (mA n) - sA1' n

noncomputable def hD2 (n : ℕ) : ℝ := 2 * f1 (mF n) * dA2 n (mA n) + sA2 n (mA n)

noncomputable def hD3 (n : ℕ) : ℝ := sA1 n

/-- **The `L²` error of the distance kernel**: `‖kD − S(1 − Q)‖₂ ≤ S·eD142 n`. -/
noncomputable def eD142 (n : ℕ) : ℝ :=
  hD0 n + hD1 n * (1 - kappa^[4] 0) + hD2 n * (1 - kappa (kappa 0)) +
    hD3 n * (1 - kappa^[6] 0) + (|hD1 n| + hD2 n + hD3 n * sig4) * tauW142 n +
    sig4 * tauW142 n

lemma hD_nonneg (n : ℕ) : 0 ≤ hD0 n ∧ 0 ≤ hD2 n ∧ 0 ≤ hD3 n := by
  have a1 := f1_nonneg (mF n)
  have a2 := f2_nonneg (mF n)
  have a3 := f3_nonneg (mF n)
  have a4 := f4_nonneg
  have b0 := dA0_nonneg n (mA n)
  have b2 := dA2_nonneg n (mA n)
  have b3 := cAdlt_nonneg n (mA n)
  have c0 := sA0_nonneg n (mA n)
  have c2 := sA2_nonneg n (mA n)
  have c3 := sA1_nonneg n
  have hs := Real.sqrt_nonneg (eps4 n (mA n))
  have hN : 0 ≤ (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold hD0; positivity
  · unfold hD2; positivity
  · unfold hD3; exact c3

/-- **The distance kernel at fixed unit inputs, with the secant link.** -/
theorem kernD_fixed142 {n : ℕ} (hn : 4096 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) :
    L2le ((mlpGauss n (mA n) n).prod ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)))
      (fun p : MlpParam n (mA n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
        kernD p.2.2 p.1 x x' - 4 / (n : ℝ) * (1 - kappa^[4] (dotp x x')))
      (4 / (n : ℝ) * (hD0 n + hD1 n * (1 - kappa (kappa (dotp x x'))) +
        hD2 n * (1 - dotp x x') + hD3 n * (1 - kappa^[4] (dotp x x')))) := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have ht := dotp_unit_mem hx hx'
  have hkt := kk_memIcc ht
  have u1 : 0 ≤ 1 - kappa (kappa (dotp x x')) := by linarith [hkt.2]
  have u2 : 0 ≤ 1 - dotp x x' := by linarith [ht.2]
  have b0 := dA0_nonneg n (mA n)
  have b1 := dA1_nonneg n (mA n)
  have b2 := dA2_nonneg n (mA n)
  have b3 := cAdlt_nonneg n (mA n)
  have h := kernD_fixed_of (mF := mF n) hn1 hmA hx hx' (f1_nonneg (mF n)) (f2_nonneg (mF n))
    (f3_nonneg (mF n)) f4_nonneg
    (α := sA0 n (mA n) + sA1 n * (1 - kappa^[4] (dotp x x')) -
      sA1' n * (1 - kappa (kappa (dotp x x'))) + sA2 n (mA n) * (1 - dotp x x'))
    (δ1 := dA0 n (mA n) + dA1 n (mA n) * (1 - kappa (kappa (dotp x x'))) +
      dA2 n (mA n) * (1 - dotp x x'))
    (δ2 := cAdlt n (mA n)) (agentS_bound_nonneg n (mA n) hx hx') (by positivity) b3
    (fun y y' => F_dist_L2_of reluEDStmt reluPhiStmt hn1 hmF y y')
    (agent_phiS_L2 hn1 hmA hx hx')
    (agent_diff_L2_of reluEDStmt reluPhiStmt hn1 hmA hx hx')
    (agent_dlt_L2_of reluSqStmt reluDltStmt linDltStmt hn1 hmA hx hx')
  refine h.congr_bound ?_
  unfold hD0 hD1 hD2 hD3
  ring

/-- The bounds that `eD142_scale` and `eD142_big` use, in one statement: with `t = 1/√n`,
`0 < t ≤ T`, and bounds of the constants in the forms `c·t`, `c·t²`. -/
lemma eD142_arith {n : ℕ} (hn : 4096 ≤ n) {t T F1 F2 F3 D0 D1 D2 C5 N0 E4 TW : ℝ}
    (ht : t = 1 / √(n : ℝ)) (hT : t ≤ T) (hT0 : 0 ≤ T)
    (hF1 : f1 (mF n) ≤ F1 * t) (hF2 : f2 (mF n) ≤ F2 * t) (hF3 : f3 (mF n) ≤ F3 * t)
    (qD0 : dA0 n (mA n) ≤ D0 * t ^ 2) (qD1 : dA1 n (mA n) ≤ D1)
    (qD2 : dA2 n (mA n) ≤ D2 * t ^ 2) (hC5 : cAdlt n (mA n) ≤ C5 * t ^ 2)
    (hN0 : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ N0)
    (hE4 : √(eps4 n (mA n)) ≤ E4 * t) (hTW : tauW142 n ≤ TW * t)
    (hF1p : 0 ≤ F1) (hF2p : 0 ≤ F2) (hF3p : 0 ≤ F3) (hD0p : 0 ≤ D0) (hD2p : 0 ≤ D2)
    (hC5p : 0 ≤ C5) (hE4p : 0 ≤ E4) (hTWp : 0 ≤ TW) (hFD : 1 / 2 ≤ 2 * F1 * D1) :
    eD142 n ≤ (2 * F1 * D0 * T ^ 2 + 2 * F2 * N0 + 2 * F3 * E4 * T +
        63662 / 100000 * C5 * T + 86 / 10 * T +
      (2 * F1 * D1 - 3408 / 10000) * (319057 / 1000000) +
      (2 * F1 * D2 * T ^ 2 + 109 / 10 * T) * (50628 / 100000) +
      24143 / 10000 * (2229 / 10000) +
      (2 * F1 * D1 + 2 * F1 * D2 * T ^ 2 + 109 / 10 * T +
        24143 / 10000 * (4404 / 10000)) * (TW * T) + 4404 / 10000 * TW) * t := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have ht0 : 0 < t := by rw [ht]; positivity
  have et2 : t ^ 2 = 1 / (n : ℝ) := by
    rw [ht, div_pow, Real.sq_sqrt hx0.le]; norm_num
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * t ^ 2 := fun c => by rw [et2]; ring
  have ht2 : t ^ 2 ≤ T * t := by nlinarith
  have ht20 : 0 ≤ t ^ 2 := by positivity
  have hTT : t ^ 2 ≤ T ^ 2 := by nlinarith
  have F4 := f4_le
  have f4n := f4_nonneg
  have S0 := sA0_le hn
  have S1 := sA1_le hn
  have S1' := sA1'_ge hn
  have S2 := sA2_le hn
  rw [cn] at S0 S2
  rw [cv] at S1 S1'
  have f1n := f1_nonneg (mF n)
  have b0 := dA0_nonneg n (mA n)
  have b1 := dA1_nonneg n (mA n)
  have b2 := dA2_nonneg n (mA n)
  have b3 := cAdlt_nonneg n (mA n)
  have s0n := sA0_nonneg n (mA n)
  have s1n := sA1_nonneg n
  have s1'n := sA1'_nonneg n
  have s2n := sA2_nonneg n (mA n)
  have hN00 : 0 ≤ (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) := by positivity
  have hE0 := Real.sqrt_nonneg (eps4 n (mA n))
  have hτ0 := tauW142_nonneg hn
  -- constants in the form `c`, `c·t`
  have D0c : dA0 n (mA n) ≤ D0 * T ^ 2 := qD0.trans (mul_le_mul_of_nonneg_left hTT hD0p)
  have D2c : dA2 n (mA n) ≤ D2 * T ^ 2 := qD2.trans (mul_le_mul_of_nonneg_left hTT hD2p)
  have C5c : cAdlt n (mA n) ≤ C5 * T * t := by
    have h := mul_le_mul_of_nonneg_left ht2 hC5p
    linarith
  have S0c : sA0 n (mA n) ≤ 86 / 10 * T * t := by
    have h := mul_le_mul_of_nonneg_left ht2 (by norm_num : (0 : ℝ) ≤ 86 / 10)
    linarith
  have S2c : sA2 n (mA n) ≤ 109 / 10 * T * t := by
    have h := mul_le_mul_of_nonneg_left ht2 (by norm_num : (0 : ℝ) ≤ 109 / 10)
    linarith
  have E4c : √(eps4 n (mA n)) ≤ E4 * T := hE4.trans (mul_le_mul_of_nonneg_left hT hE4p)
  have TWc : tauW142 n ≤ TW * T := hTW.trans (mul_le_mul_of_nonneg_left hT hTWp)
  have hF1t : 0 ≤ F1 * t := by positivity
  have p1 := mul_le_lin hF1 D0c b0 hF1t
  have p2 := mul_le_lin hF2 hN0 hN00 (by positivity)
  have p3 := mul_le_lin hF3 E4c hE0 (by positivity)
  have p4 : f4 * cAdlt n (mA n) ≤ 63662 / 100000 * (C5 * T * t) :=
    mul_le_mul F4 C5c b3 (by norm_num)
  have p5 := mul_le_lin hF1 qD1 b1 hF1t
  have p6 := mul_le_lin hF1 D2c b2 hF1t
  -- the four constants
  have G0 : hD0 n ≤ (2 * F1 * D0 * T ^ 2 + 2 * F2 * N0 + 2 * F3 * E4 * T +
      63662 / 100000 * C5 * T + 86 / 10 * T) * t := by
    unfold hD0
    linarith
  have G1u : hD1 n ≤ (2 * F1 * D1 - 3408 / 10000) * t := by
    unfold hD1
    linarith
  have G1a : |hD1 n| ≤ 2 * F1 * D1 * t := by
    unfold hD1
    have hA0 : 0 ≤ 2 * f1 (mF n) * dA1 n (mA n) := by positivity
    have hS1h : sA1' n ≤ 1 / 2 * t := by
      unfold sA1'
      rw [cv]
      exact mul_le_mul_of_nonneg_right AgS.cg2_le ht0.le
    have hhalf : 1 / 2 * t ≤ 2 * F1 * D1 * t := mul_le_mul_of_nonneg_right hFD ht0.le
    rw [abs_le]
    constructor <;> linarith
  have G2 : hD2 n ≤ (2 * F1 * D2 * T ^ 2 + 109 / 10 * T) * t := by
    unfold hD2
    linarith
  have G3 : hD3 n ≤ 24143 / 10000 * t := S1
  obtain ⟨g0n, g2n, g3n⟩ := hD_nonneg n
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have h2 : 1 - kappa (kappa 0) ≤ 50628 / 100000 := by have := kappa2_zero_ge; linarith
  have h20 : 0 ≤ 1 - kappa (kappa 0) := by have := kappa2_zero_le; linarith
  have h6 : 1 - kappa^[6] 0 ≤ 2229 / 10000 := by have := kappa6_zero_ge'; linarith
  have h60 : 0 ≤ 1 - kappa^[6] 0 := by have := kappa6_zero_le; linarith
  have hs4 := sig4_le
  have hs40 := sig4_nonneg
  -- the products
  have r1 : hD1 n * (1 - kappa^[4] 0) ≤
      (2 * F1 * D1 - 3408 / 10000) * (319057 / 1000000) * t := by
    by_cases hneg : hD1 n ≤ 0
    · have hU : 0 ≤ (2 * F1 * D1 - 3408 / 10000) * (319057 / 1000000) * t :=
        mul_nonneg (mul_nonneg (by linarith) (by norm_num)) ht0.le
      have : hD1 n * (1 - kappa^[4] 0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg h40
      linarith
    · push Not at hneg
      have hU0 : 0 ≤ (2 * F1 * D1 - 3408 / 10000) * t :=
        mul_nonneg (by linarith) ht0.le
      have := mul_le_mul G1u h4 h40 hU0
      linarith
  have r2 := mul_le_lin G2 h2 h20 (by positivity)
  have r3 := mul_le_lin G3 h6 h60 (by positivity)
  have r4a : hD3 n * sig4 ≤ 24143 / 10000 * (4404 / 10000) * t :=
    mul_le_lin G3 hs4 hs40 (by positivity)
  have hsum0 : 0 ≤ |hD1 n| + hD2 n + hD3 n * sig4 := by positivity
  have hsum : |hD1 n| + hD2 n + hD3 n * sig4 ≤
      (2 * F1 * D1 + 2 * F1 * D2 * T ^ 2 + 109 / 10 * T +
        24143 / 10000 * (4404 / 10000)) * t := by linarith
  have r4 := mul_le_lin hsum TWc hτ0 (by linarith)
  have r5 : sig4 * tauW142 n ≤ 4404 / 10000 * (TW * t) :=
    mul_le_mul hs4 hTW hτ0 (by norm_num)
  unfold eD142
  linarith

/-- `0 ≤ hD0 + hD1(1 − κ⁴(0)) + hD2(1 − κ(κ(0))) + hD3(1 − κ⁶(0))`. -/
lemma hD_ref_nonneg {n : ℕ} (hn : 4096 ≤ n) :
    0 ≤ hD0 n + hD1 n * (1 - kappa^[4] 0) + hD2 n * (1 - kappa (kappa 0)) +
      hD3 n * (1 - kappa^[6] 0) := by
  obtain ⟨g0n, g2n, g3n⟩ := hD_nonneg n
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have h20 : 0 ≤ 1 - kappa (kappa 0) := by have := kappa2_zero_le; linarith
  have h6 : 222757 / 1000000 ≤ 1 - kappa^[6] 0 := by have := kappa6_zero_le''; linarith
  have hA0 : 0 ≤ 2 * f1 (mF n) * dA1 n (mA n) := by
    have := f1_nonneg (mF n); have := dA1_nonneg n (mA n); positivity
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hS1h : sA1' n ≤ 1 / 2 * t := by
    unfold sA1'
    rw [ht]
    have := AgS.cg2_le
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hS1 : 2 * t ≤ hD3 n := by
    have h2 : (1 : ℝ) ≤ √2 := by
      rw [Real.le_sqrt' (by norm_num)]
      norm_num
    have e : hD3 n = (1 + √2) * t := by unfold hD3 sA1; rw [ht]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) ht0.le
  have e1 : -(1 / 2 * t) * (319057 / 1000000) ≤ hD1 n * (1 - kappa^[4] 0) := by
    have hlow : -(1 / 2 * t) ≤ hD1 n := by unfold hD1; linarith
    by_cases hneg : hD1 n ≤ 0
    · have : hD1 n * (319057 / 1000000) ≤ hD1 n * (1 - kappa^[4] 0) :=
        mul_le_mul_of_nonpos_left h4 hneg
      nlinarith
    · push Not at hneg
      have : 0 ≤ hD1 n * (1 - kappa^[4] 0) := mul_nonneg hneg.le h40
      nlinarith
  have e3 : 2 * t * (222757 / 1000000) ≤ hD3 n * (1 - kappa^[6] 0) :=
    mul_le_mul hS1 h6 (by norm_num) g3n
  have e2 : 0 ≤ hD2 n * (1 - kappa (kappa 0)) := mul_nonneg g2n h20
  nlinarith

/-- **`kernDist142` (`kernel142`).** For `n ≥ 4096`, at the widths of the Focus:
`‖kD − (4/n)(1 − κ^{∘6}(0))‖₂ ≤ (4/n)·eD142 n`. -/
theorem kernDist142 {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * eD142 n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  obtain ⟨g0, g2, g3⟩ := hD_nonneg n
  have hT := tX_L2_marg (mA := mA n) (mF := mF n) hN
    (tX_L2_focus (mA := mA n) (mF := mF n) hn1 hN hmW)
  exact kernDist_L2_gen hn1 hN g2 g3 (tauW142_nonneg hn) (hD_ref_nonneg hn)
    (fun x x' hx hx' => kernD_fixed142 hn hx hx') hT

lemma eD142_nonneg {n : ℕ} (hn : 4096 ≤ n) : 0 ≤ eD142 n := by
  obtain ⟨g0, g2, g3⟩ := hD_nonneg n
  have h := hD_ref_nonneg hn
  have hτ := tauW142_nonneg hn
  have hs := sig4_nonneg
  have h1 : 0 ≤ (|hD1 n| + hD2 n + hD3 n * sig4) * tauW142 n := by positivity
  have h2 : 0 ≤ sig4 * tauW142 n := by positivity
  unfold eD142
  linarith

/-- `eD142 n ≤ 1.835/√n` for `n ≥ 4096` (the first form `eD142a`: `2.28/√n`). -/
lemma eD142_scale {n : ℕ} (hn : 4096 ≤ n) : eD142 n ≤ 1835 / 1000 / √(n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht64 : t ≤ 1 / 64 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have et2 : t ^ 2 = 1 / (n : ℝ) := by
    rw [ht, div_pow, Real.sq_sqrt hx0.le]; norm_num
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * t ^ 2 := fun c => by rw [et2]; ring
  have F1 := f1_scale hn
  have F2 := f2_scale hn
  have F3 := f3_scale hn
  have D0 := dA0_le hn
  have D1 := dA1_le hn
  have D2 := dA2_le hn
  have C5 := cAdlt_le hn
  have hτ := tauW142_scale hn
  rw [cv] at F1 F2 F3 hτ
  rw [cn] at D0 D2 C5
  have hN0 : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ 100025 / 100000 := by
    have h1 := inv_mA_le hn
    have h10 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
    have h2 := sqrt_one_add_le hn
    have h20 := Real.sqrt_nonneg (1 + 2 / (n : ℝ))
    nlinarith
  have hE : √(eps4 n (mA n)) ≤ 14170 / 10000 * t := by
    have h1 : √(eps4 n (mA n)) ≤ 2214 / 100000 :=
      sqrt_le_of_sq (by norm_num) ((eps4_bound hn).trans (by norm_num))
    -- a constant bound is enough here: `0.02214 ≤ 1.417·t` is false for large `n`, so use
    -- `eps4 ≤ 2.0027/n`
    have hA := inv_mA_le hn
    have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
    have hA' : 5 / (mA n : ℝ) ≤ 5 / 4096 * t ^ 2 := by
      rw [mA_eqR, et2, div_le_iff₀ (by positivity)]
      have : 5 / 4096 * (1 / (n : ℝ)) * (n : ℝ) ^ 2 = 5 / 4096 * (n : ℝ) := by
        field_simp
      nlinarith
    have h2n : 2 / (n : ℝ) = 2 * t ^ 2 := by rw [et2]; ring
    refine sqrt_le_of_sq (by positivity) ?_
    unfold eps4
    rw [h2n]
    have ht2 : t ^ 2 ≤ 1 / 4096 := by nlinarith
    have ht20 : 0 ≤ t ^ 2 := by positivity
    set y := t ^ 2 with hy
    set a := 5 / (mA n : ℝ) with ha
    have ha1 : a ≤ 5 / 4096 * y := hA'
    have ha2 : a ≤ 1 / 100 := by nlinarith
    have e : (14170 / 10000 * t) ^ 2 = (14170 / 10000) ^ 2 * y := by rw [hy]; ring
    rw [e]
    have hsq : (1 + a) ^ 2 ≤ 1 + 3 * a := by nlinarith
    have h3 : (1 + a) ^ 2 * (1 + 2 * y) ≤ (1 + 3 * a) * (1 + 2 * y) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    nlinarith
  have h := eD142_arith hn ht ht64 (by norm_num) F1 F2 F3 D0 D1 D2 C5 hN0 hE hτ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [cv]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ht0.le)
  norm_num

/-- `eD142 n ≤ 1.327/√n` for `n ≥ 32768`. -/
lemma eD142_big {n : ℕ} (hn : 32768 ≤ n) : eD142 n ≤ 1327 / 1000 / √(n : ℝ) := by
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge_big hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht181 : t ≤ 1 / 181 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have et2 : t ^ 2 = 1 / (n : ℝ) := by
    rw [ht, div_pow, Real.sq_sqrt hx0.le]; norm_num
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * t ^ 2 := fun c => by rw [et2]; ring
  have F1 := f1_big hn
  have F2 := f2_big hn
  have F3 := f3_big hn
  have D0 := dA0_big hn
  have D1 := dA1_big hn
  have D2 := dA2_big hn
  have C5 := cAdlt_big hn
  have hτ := tauW142_big hn
  have hE := sqrt_eps4_big hn
  have hN0 := N0_big hn
  rw [cv] at F1 F2 F3 hτ hE
  rw [cn] at D0 D2 C5
  have h := eD142_arith hn4 ht ht181 (by norm_num) F1 F2 F3 D0 D1 D2 C5 hN0 hE hτ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [cv]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ht0.le)
  norm_num

/-- **`spread142` (item 3).** For `n ≥ 4096` and `θ < 1`, with `S = 4/n`, `Q = κ^{∘6}(0)`:
`Pr_{W,A,F}(sd² < θ·S·(1 − Q)) ≤ 3·(eD142 n)²/((1 − θ)(1 − Q))²`. Chebyshev's inequality for
`(sd² − S(1 − Q))²`; Cantelli's inequality is NOT used. -/
theorem spread142 {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ} (hθ : θ < 1) :
    (mlpTriple 2 n).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤
      3 * eD142 n ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 :=
  spreadLow142_of hn (eD142_nonneg hn) (kernDist142 hn) hθ

/-- `v_n = 3·(eD142 n)² ≤ 10.11/n` for `n ≥ 4096` (Part 139: `v_n ≤ 64/n`). -/
lemma vSpread142_scale {n : ℕ} (hn : 4096 ≤ n) : 3 * eD142 n ^ 2 ≤ 1011 / 100 / (n : ℝ) := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have h := eD142_scale hn
  have h0 := eD142_nonneg hn
  have h2 : eD142 n ^ 2 ≤ (1835 / 1000 / √(n : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [div_pow, Real.sq_sqrt hx0.le] at h2
  have e : (1011 : ℝ) / 100 / n = 3 * (337 / 100 / n) := by ring
  rw [e]
  have : ((1835 : ℝ) / 1000) ^ 2 / n ≤ 337 / 100 / n :=
    div_le_div_of_nonneg_right (by norm_num) hx0.le
  linarith

/-- **`arithProgSucceeds142` (the headline, item 4).** For every `n ≥ 4096` and `k ≥ 1`, with
`gProgA` the output of the arithmetic one-pass program `arithProg141 k n` of Part 141
(unchanged) on `(W, A, F)` and `k` independent standard Gaussian vectors:
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + 428/n + 134/k)`. -/
theorem arithProgSucceeds142 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 428 / (n : ℝ) + 134 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := progDist142v hn hk (θ := 135 / 1000) (by norm_num) (by norm_num) (goodHat_compl hn)
    (eD142_nonneg hn) (eD142_scale hn) (kernDist142 hn)
  refine le_trans ?_ h
  have e1 : (2 / 10000 + 256 / 100 / (135 / 1000 * (222757 / 1000000 : ℝ)) +
      3 * (1835 / 1000 : ℝ) ^ 2 / ((1 - 135 / 1000) * (222757 / 1000000)) ^ 2) / (n : ℝ) ≤
      358 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (135 / 1000 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 134 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : (428 : ℝ) / n = 70 / n + 358 / n := by ring
  rw [e3]
  linarith

/-- The rate for `n ≥ 32768`: `Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + 243/n + 106/k)`
(`θ = 0.17`; the bad hidden event with its true rate, `goodHat_big`). -/
theorem arithProgSucceeds142_big {n : ℕ} (hn : 32768 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 243 / (n : ℝ) + 106 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := progDist142v hn4 hk (θ := 17 / 100) (by norm_num) (by norm_num) (goodHat_big hn)
    (eD142_nonneg hn4) (eD142_big hn) (kernDist142 hn4)
  refine le_trans ?_ h
  have e1 : (2 / 10000 + 256 / 100 / (17 / 100 * (222757 / 1000000 : ℝ)) +
      3 * (1327 / 1000 : ℝ) ^ 2 / ((1 - 17 / 100) * (222757 / 1000000)) ^ 2) / (n : ℝ) ≤
      2223 / 10 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (17 / 100 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 106 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : (243 : ℝ) / n = 2063 / 100 / n + 2223 / 10 / n + 7 / 100 / n := by ring
  have e4 : (0 : ℝ) ≤ 7 / 100 / n := by positivity
  rw [e3]
  linarith

/-- **`arithProg142_99` (item 4).** For every `n ≥ 32768` and `k ≥ 100·n`:
`Pr(|gProgA − B| ≤ sd/2) ≥ 99/100`. (`32768 = 2·16384`: outside the frontier interval.) -/
theorem arithProg142_99 {n : ℕ} (hn : 32768 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx : (32768 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk1 : 1 ≤ k := by omega
  have hkR : (100 : ℝ) * n ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have h := arithProgSucceeds142_big hn hk1
  have t1 : 243 / (n : ℝ) ≤ 243 / 32768 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t2 : 106 / (k : ℝ) ≤ 106 / 3276800 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  norm_num at t1 t2
  linarith

end BstLean.Part142

open BstLean.Part142 in
#print axioms kernDist142
open BstLean.Part142 in
#print axioms eD142_scale
open BstLean.Part142 in
#print axioms eD142_big
open BstLean.Part142 in
#print axioms spread142
open BstLean.Part142 in
#print axioms vSpread142_scale
open BstLean.Part142 in
#print axioms arithProgSucceeds142
open BstLean.Part142 in
#print axioms arithProgSucceeds142_big
open BstLean.Part142 in
#print axioms arithProg142_99
