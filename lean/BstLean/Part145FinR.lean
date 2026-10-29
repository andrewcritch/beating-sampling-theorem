import BstLean.Part145BigR
import BstLean.Part145AgentR
import BstLean.Part145C5
import BstLean.Part145B2
import BstLean.Part145L4
import BstLean.Part145G6
import BstLean.Part145TwoStageG0
import BstLean.Part145Cost
import BstLean.Part144Range
import BstLean.Part145K10
import BstLean.Part145C10

/-!
# Part 145 (file `FinR`): level `99/100` for the arithmetic program for every `n ≥ 4096`

Role: `delegations/statements/p145-spec.md`, item 2. The program is `arithProg141 k n` (Part 141),
unchanged; `okProgA k n` is the event `|gProgA − B| ≤ sd/2`. This file is made by a script
(`gf/genfinal2.py` in the scratch directory of the session); the numbers are for
`n ≥ 4096 = 64²`.

All the levers of Part 145 together:
1. the joint assembly of the error and the spread (`Part145Joint`, `progJointG0`);
2. the frame constant of the computed centre as a FUNCTION of `θ` (`LfX`, `Part145L1`) and its
   mean (`LfX_DKV_mean`); the good hidden event is only the window `Gwin n` of `t|b̂|²`
   (`Pr(fails) ≤ 15640/m_W`); the error chain for such an event is `errSampleAF_lint`
   (`Part145G5`); the variance term comes from the distance kernel (`DKV_mean`);
3. the kernel: the exact variance of the centred part of the `A₃` link (`Part145K1` to `K3`);
   the first layer of `F` as one more orthogonal block with the bias `biasK` (`Part145K5`,
   `Part145B2`); the sharper second-order term of the cosine link (`Part145C1` to `C3`).

* `eDBgen_R`: `eDB bK τ n ≤ 0.78728/√n` for `bK ≤ 0.0239/√n`, `τ ≤ 0.90734/√n`.
* **`arithProgSucceeds145R`**: `Pr(ok) ≥ 1 − (33.12002/n + 31.6/k)`, every `n ≥ 4096`,
  `k ≥ 1` (no constant term).
* **`arithProg145R_99`**: level `99/100` for every `n ≥ 4096`, `k ≥ 100n`.
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

/-! ## Arithmetic of the constants (real numbers only) -/

section arith

variable {t τ a4 a2 aQ sg d0 d1 d2 : ℝ}

lemma dl_arithR (ht0 : 0 < t) (ht1 : t ≤ 1 / 64) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 90734 / 100000 * t)
    (ha40 : 0 ≤ a4) (ha4 : a4 ≤ 319057 / 1000000) (ha20 : 0 ≤ a2) (ha2 : a2 ≤ 50628 / 100000)
    (hd00 : 0 ≤ d0) (hd0 : d0 ≤ 81412 / 100000 * (t * t)) (hd10 : 0 ≤ d1)
    (hd1 : d1 ≤ 1 + 1 / 4096) (hd20 : 0 ≤ d2) (hd2 : d2 ≤ 103949 / 10000 * (t * t)) :
    0 ≤ d0 + d1 * (a4 + τ) + d2 * (a2 + τ) ∧ d0 + d1 * (a4 + τ) + d2 * (a2 + τ) ≤ 33484 / 100000 := by
  have hτ1 : τ ≤ 90734 / 100000 * (1 / 64) := by nlinarith
  have p1 : d1 * (a4 + τ) ≤ (1 + 1 / 4096) * (319057 / 1000000 + 90734 / 100000 * (1 / 64)) :=
    mul_le_mul hd1 (by linarith) (by linarith) (by norm_num)
  have p3 : t * t ≤ 1 / 4096 := by nlinarith
  have p2 : d2 * (a2 + τ) ≤
      103949 / 10000 * (1 / 4096) * (50628 / 100000 + 90734 / 100000 * (1 / 64)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have q1 : 0 ≤ d1 * (a4 + τ) := mul_nonneg hd10 (by linarith)
  have q2 : 0 ≤ d2 * (a2 + τ) := mul_nonneg hd20 (by linarith)
  constructor
  · linarith
  · have : d0 ≤ 81412 / 100000 * (1 / 4096) := by nlinarith
    linarith

lemma E2_arithR {dl f1b f2 f3 f4 N0 e4 δ2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 64)
    (hdl0 : 0 ≤ dl) (hdl : dl ≤ 33484 / 100000) (hf1b : f1b ≤ 21651 / 100000 * t)
    (hf2 : f2 ≤ 5146 / 100000 * t) (hN00 : 0 ≤ N0) (hN0 : N0 ≤ 1 + 24444 / 100000000)
    (hf3 : f3 ≤ 8898 / 100000 * t) (he40 : 0 ≤ e4) (he4 : e4 ≤ 141508 / 100000 * t)
    (hf4 : f4 ≤ 63662 / 100000) (hδ0 : 0 ≤ δ2) (hδ : δ2 ≤ 9527 / 5000 * (t * t)) :
    2 * f1b * dl + 2 * f2 * N0 + 2 * f3 * e4 + f4 * δ2 ≤ 27083 / 100000 * t := by
  have p1 : f1b * dl ≤ 21651 / 100000 * t * (33484 / 100000) :=
    mul_le_mul hf1b hdl hdl0 (by positivity)
  have p2 : f2 * N0 ≤ 5146 / 100000 * t * (1 + 24444 / 100000000) :=
    mul_le_mul hf2 hN0 hN00 (by positivity)
  have p3 : f3 * e4 ≤ 8898 / 100000 * t * (141508 / 100000 * t) :=
    mul_le_mul hf3 he4 he40 (by positivity)
  have p4 : f4 * δ2 ≤ 63662 / 100000 * (9527 / 5000 * (t * t)) :=
    mul_le_mul hf4 hδ hδ0 (by norm_num)
  have ht2 : t * t ≤ 1 / 64 * t := mul_le_mul_of_nonneg_right ht1 ht0.le
  have q3 : 8898 / 100000 * t * (141508 / 100000 * t) =
      8898 / 100000 * (141508 / 100000) * (t * t) := by ring
  nlinarith

lemma E3x_arithR {c0 c1 c1' c2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 64) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 90734 / 100000 * t) (ha4l : 319029 / 1000000 ≤ a4) (ha20 : 0 ≤ a2)
    (ha2 : a2 ≤ 50628 / 100000) (haQ0 : 0 ≤ aQ) (haQ : aQ ≤ 2229 / 10000) (hsg0 : 0 ≤ sg)
    (hsg : sg ≤ 4404 / 10000) (hc0 : c0 ≤ 31644 / 1000000 * (t * t))
    (hc1 : c1 ≤ 141422 / 100000 * t) (hc1' : c1' = 55 / 1000 * t)
    (hc2 : c2 ≤ 23858 / 100000 * (t * t)) :
    c0 + c1 * (aQ + sg * τ) - c1' * a4 + c2 * a2 + (c1' + c2) * τ ≤ 30973 / 100000 * t := by
  have hτ1 : τ ≤ 90734 / 100000 * (1 / 64) := by nlinarith
  have s1 : sg * τ ≤ 4404 / 10000 * (90734 / 100000 * (1 / 64)) :=
    mul_le_mul hsg hτ1 hτ0 (by norm_num)
  have s10 : 0 ≤ sg * τ := mul_nonneg hsg0 hτ0
  have p1 : c1 * (aQ + sg * τ) ≤
      141422 / 100000 * t * (2229 / 10000 + 4404 / 10000 * (90734 / 100000 * (1 / 64))) :=
    mul_le_mul hc1 (by linarith) (by linarith) (by positivity)
  have p2 : 55 / 1000 * t * (319029 / 1000000) ≤ c1' * a4 := by
    rw [hc1']
    exact mul_le_mul_of_nonneg_left ha4l (by positivity)
  have p3 : c2 * a2 ≤ 23858 / 100000 * (t * t) * (50628 / 100000) :=
    mul_le_mul hc2 ha2 ha20 (by positivity)
  have p4 : (c1' + c2) * τ ≤
      (55 / 1000 * t + 23858 / 100000 * (t * t)) * (90734 / 100000 * (1 / 64)) := by
    rw [hc1']
    exact mul_le_mul (by linarith) hτ1 hτ0 (by positivity)
  have ht2 : t * t ≤ 1 / 64 * t := mul_le_mul_of_nonneg_right ht1 ht0.le
  nlinarith

lemma E4_arithR {r0 r1' r2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 64) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 90734 / 100000 * t) (ha4l : 319029 / 1000000 ≤ a4) (ha20 : 0 ≤ a2)
    (ha2 : a2 ≤ 50628 / 100000) (haQ : aQ ≤ 2229 / 10000) (hsg0 : 0 ≤ sg)
    (hsg : sg ≤ 4404 / 10000) (hr0 : r0 ≤ 8269 / 2500 * (t * t))
    (hr1'l : 3408 / 10000 * t ≤ r1') (hr1'u : r1' ≤ 3408455 / 10000000 * t) (hr20 : 0 ≤ r2)
    (hr2 : r2 ≤ 10611 / 1000 * (t * t)) :
    r0 + t * aQ - r1' * a4 + r2 * a2 + (t * sg + r1' + r2) * τ ≤ 26323 / 100000 * t := by
  have hτ1 : τ ≤ 90734 / 100000 * (1 / 64) := by nlinarith
  have hr1'0 : 0 ≤ r1' := by nlinarith
  have p1 : t * aQ ≤ t * (2229 / 10000) := mul_le_mul_of_nonneg_left haQ ht0.le
  have p2 : 3408 / 10000 * t * (319029 / 1000000) ≤ r1' * a4 :=
    mul_le_mul hr1'l ha4l (by norm_num) hr1'0
  have p3 : r2 * a2 ≤ 10611 / 1000 * (t * t) * (50628 / 100000) :=
    mul_le_mul hr2 ha2 ha20 (by positivity)
  have p4 : t * sg ≤ t * (4404 / 10000) := mul_le_mul_of_nonneg_left hsg ht0.le
  have p40 : 0 ≤ t * sg := mul_nonneg ht0.le hsg0
  have p5 : (t * sg + r1' + r2) * τ ≤
      (t * (4404 / 10000) + 3408455 / 10000000 * t + 10611 / 1000 * (t * t)) *
        (90734 / 100000 * (1 / 64)) :=
    mul_le_mul (by linarith) hτ1 hτ0 (by positivity)
  have ht2 : t * t ≤ 1 / 64 * t := mul_le_mul_of_nonneg_right ht1 ht0.le
  nlinarith

lemma finalBR {E1 E2 E3 E4 pW B2 : ℝ} (ht0 : 0 < t) (h10 : 0 ≤ E1)
    (h1 : E1 ≤ 14598 / 100000 * t) (h20 : 0 ≤ E2) (h2 : E2 ≤ 27083 / 100000 * t) (h30 : 0 ≤ E3)
    (h3 : E3 ≤ 30973 / 100000 * t) (h40 : 0 ≤ E4) (h4 : E4 ≤ 26323 / 100000 * t) (hp0 : 0 ≤ pW)
    (hp : pW ≤ 15451 / 50000 * t) (hb0 : 0 ≤ B2) (hb : B2 ≤ 23906 / 1000000 * t) :
    √(E1 ^ 2 + E2 ^ 2 + (B2 + E4 + √(E3 ^ 2 + pW ^ 2)) ^ 2) ≤ 78728 / 100000 * t := by
  have hin : √(E3 ^ 2 + pW ^ 2) ≤ 43753 / 100000 * t :=
    sqrt_sq_add_le h30 h3 hp0 hp (by positivity) (by nlinarith [sq_nonneg t])
  have hin0 := Real.sqrt_nonneg (E3 ^ 2 + pW ^ 2)
  have hT0 : 0 ≤ B2 + E4 + √(E3 ^ 2 + pW ^ 2) := by linarith
  have hT : B2 + E4 + √(E3 ^ 2 + pW ^ 2) ≤ 362333 / 500000 * t := by linarith
  have a1 := pow_le_pow_left₀ h10 h1 2
  have a2 := pow_le_pow_left₀ h20 h2 2
  have a3 := pow_le_pow_left₀ hT0 hT 2
  have key : (14598 / 100000 * t) ^ 2 + (27083 / 100000 * t) ^ 2 + (362333 / 500000 * t) ^ 2 ≤
      (78728 / 100000 * t) ^ 2 := by
    have := sq_nonneg t
    nlinarith
  rw [show (78728 / 100000 * t : ℝ) = √((78728 / 100000 * t) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  linarith

lemma B2_arithR {bK N : ℝ} (ht0 : 0 < t) (hbK : bK ≤ 23900 / 1000000 * t) (hN0 : 0 ≤ N)
    (hN : N ≤ 1 + 24444 / 100000000) : bK * N ≤ 23906 / 1000000 * t := by
  have h1 := mul_le_mul hbK hN hN0 (by positivity : (0 : ℝ) ≤ 23900 / 1000000 * t)
  nlinarith

end arith

/-- **The kernel constant for a general `τ` and a general bias constant**, `n ≥ 4096`. -/
theorem eDBgen_R {n : ℕ} (hn : 4096 ≤ n) {bK : ℝ} (hbK0 : 0 ≤ bK)
    (hbK : bK ≤ 23900 / 1000000 / √(n : ℝ)) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ' : τ ≤ 90734 / 100000 / √(n : ℝ)) {pW : ℝ} (hp0 : 0 ≤ pW)
    (hp' : pW ≤ 15451 / 50000 / √(n : ℝ)) : eDBq bK τ pW n ≤ 78728 / 100000 / √(n : ℝ) := by
  have hn4 : 4096 ≤ n := by omega
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geR hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / √(n : ℝ) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 64 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have htt : t * t = 1 / (n : ℝ) := by
    rw [ht, div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have conv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  have conv2 : ∀ c : ℝ, c / (n : ℝ) = c * (t * t) := fun c => by rw [htt]; ring
  obtain ⟨hmF1, hmF2⟩ := inv_mFR hn
  rw [← ht] at hmF1 hmF2
  have h3 := s3_le16
  have hmF10 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have hf1b : f1b (mF n) ≤ 21651 / 100000 * t := by
    have e : f1b (mF n) = √3 * (1 / √(mF n : ℝ)) := by unfold f1b; ring
    rw [e]
    have := mul_le_mul h3 hmF1 hmF10 (by norm_num)
    linarith
  have hf1a : f1a (mF n) ≤ 21798 / 100000 * t := by
    have e : f1a (mF n) = √3 * (1 / √(mF n : ℝ)) + 6 * (1 / (mF n : ℝ)) := by unfold f1a; ring
    rw [e]
    have := mul_le_mul h3 hmF1 hmF10 (by norm_num)
    linarith
  have hf2 : f2 (mF n) ≤ 5146 / 100000 * t := (f2_R hn).trans_eq (conv _)
  have hf3 : f3 (mF n) ≤ 8898 / 100000 * t := (f3_R hn).trans_eq (conv _)
  have hd0 : dA0 n (mA n) ≤ 81412 / 100000 * (t * t) := (dA0_R hn).trans_eq (conv2 _)
  have hd2 : dA2 n (mA n) ≤ 103949 / 10000 * (t * t) := (dA2_R hn).trans_eq (conv2 _)
  have hcd : cAdltx n (mA n) ≤ 9527 / 5000 * (t * t) := (cAdltx_leR hn).trans_eq (conv2 _)
  have he4 : √(eps4 n (mA n)) ≤ 141508 / 100000 * t := (sqrt_eps4_R hn).trans_eq (conv _)
  have hτ : τ ≤ 90734 / 100000 * t := hτ'.trans_eq (conv _)
  have ha4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have ha40 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have ha4l : 319029 / 1000000 ≤ 1 - kappa^[4] 0 := by
    have h : kappa^[4] 0 ≤ 680971 / 1000000 := BstLean.Part139.kappa4_zero_le
    linarith
  have ha2 : 1 - kappa (kappa 0) ≤ 50628 / 100000 := by have := kappa2_zero_ge; linarith
  have ha20 : 0 ≤ 1 - kappa (kappa 0) := a2_nonneg
  have haQ : 1 - kappa^[6] 0 ≤ 2229 / 10000 := by have := kappa6_zero_ge'; linarith
  have haQ0 : 0 ≤ 1 - kappa^[6] 0 := aQ_nonneg
  have hc0 : cC0x n (mA n) ≤ 31644 / 1000000 * (t * t) := (cC0x_leR hn).trans_eq (conv2 _)
  have hc1 : cC1 n ≤ 141422 / 100000 * t := (cC1_le (n := n)).trans_eq (conv _)
  have hc2 : cC2x n (mA n) ≤ 23858 / 100000 * (t * t) := (cC2x_leR hn).trans_eq (conv2 _)
  have hc1' : cC1x' n = 55 / 1000 * t := by rw [cC1x'_eq, ht]; unfold dK; ring
  have hr0 : rR0x n (mA n) ≤ 8269 / 2500 * (t * t) := (rR0x_leR hn).trans_eq (conv2 _)
  have hr2 : rR2 n (mA n) ≤ 10611 / 1000 * (t * t) := (rR2_leR hn).trans_eq (conv2 _)
  have hr1 : rR1 n = t := by rw [rR1_eq, ht]
  have hr1'l : 3408 / 10000 * t ≤ rR1' n := (conv _).symm.trans_le (rR1'_geR hn)
  have hr1'u : rR1' n ≤ 3408455 / 10000000 * t := by
    have e : rR1' n = AgS.cgS (kappa ∘ kappa) * t := by
      unfold rR1' sA1'; rw [ht]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right cg2_le16 ht0.le
  have hd00 := dA0_nonneg n (mA n)
  have hd10 := dA1_nonneg n (mA n)
  have hd20 := dA2_nonneg n (mA n)
  have hcd0 := cAdltx_nonneg n (mA n)
  obtain ⟨hdl0, hdlU⟩ := dl_arithR ht0 ht1 hτ0 hτ ha40 ha4 ha20 ha2 hd00 hd0 hd10 (dA1_R hn)
    hd20 hd2
  have hE1 : asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) τ ≤
      14598 / 100000 * t := by
    unfold asmE1
    have := mul_le_mul hf1a hdlU hdl0 (by positivity)
    nlinarith
  have hE2 : asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n))
      (cAdltx n (mA n)) τ ≤ 27083 / 100000 * t := by
    unfold asmE2
    exact E2_arithR ht0 ht1 hdl0 hdlU hf1b hf2 (by positivity) (N0_R hn) hf3
      (Real.sqrt_nonneg _) he4 f4_le hcd0 hcd
  have hE3 : asmE3x (cC0x n (mA n)) (cC1 n) (cC1x' n) (cC2x n (mA n)) τ ≤ 30973 / 100000 * t := by
    unfold asmE3x
    exact E3x_arithR ht0 ht1 hτ0 hτ ha4l ha20 ha2 haQ0 haQ sig4_nonneg sig4_le hc0
      hc1 hc1' hc2
  have hE4 : asmE4 (rR0x n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) τ ≤
      26323 / 100000 * t := by
    unfold asmE4
    rw [hr1]
    exact E4_arithR ht0 ht1 hτ0 hτ ha4l ha20 ha2 haQ sig4_nonneg sig4_le hr0 hr1'l hr1'u
      (rR2_nonneg n (mA n)) hr2
  have hE40 : 0 ≤ asmE4 (rR0x n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) τ := by
    have h := rRx_ref_nonneg n (mA n)
    have h1 : 0 ≤ (rR1 n * sig4 + rR1' n + rR2 n (mA n)) * τ :=
      mul_nonneg (add_nonneg (add_nonneg (mul_nonneg (rR1_nonneg n) sig4_nonneg)
        (rR1'_nonneg n)) (rR2_nonneg n (mA n))) hτ0
    unfold asmE4
    linarith
  have hpW : pW ≤ 15451 / 50000 * t := hp'.trans_eq (conv _)
  have hB2 : bK * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) ≤ 23906 / 1000000 * t :=
    B2_arithR ht0 (hbK.trans_eq (conv _)) (by positivity) (N0_R hn)
  rw [conv]
  unfold eDBq
  exact finalBR ht0 (asmE1_nonneg (mF n) hd00 hd10 hd20 hτ0) hE1
    (asmE2_nonneg n (mA n) (mF n) hd00 hd10 hd20 hcd0 hτ0) hE2
    (asmE3x_focus_nonneg n (mA n) hτ0) hE3 hE40 hE4 hp0 hpW
    (mul_nonneg hbK0 (by positivity)) hB2

/-- The bias constant of the first layer of `F` at the width `mF n`: `≤ 0.0239/√n` for
`n ≥ 4096`. -/
theorem biasK_R {n : ℕ} (hn : 4096 ≤ n) : biasK (mF n) ≤ 23900 / 1000000 / √(n : ℝ) := by
  have hn4 : 4096 ≤ n := by omega
  obtain ⟨hmF1, hmF2⟩ := inv_mFR hn
  have hs := sqrt_n_geR hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hz : 1 / √(n : ℝ) ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) hs
  have hz0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have hmN := BstLean.Part132.mF_ge hn4
  have hm0 : (0 : ℝ) < mF n := by exact_mod_cast (by omega : 0 < mF n)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = √(mF n : ℝ) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr hm0
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = √a := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr ha0
  rw [← ha] at hmF1
  have h := biasK_le (mF n)
  rw [← ha, ← hb] at h
  have h1a : 1 / a ≤ (8839 / 200000) ^ 2 := by
    have : 10000 / 80000 * (1 / √(n : ℝ)) ≤ 10000 / 80000 * (1 / 64) :=
      mul_le_mul_of_nonneg_left hz (by norm_num)
    have h2 : (10000 / 80000 : ℝ) * (1 / 64) ≤ (8839 / 200000) ^ 2 := by norm_num
    linarith
  have hb1 : 1 / b ≤ 8839 / 200000 := by
    rw [div_le_iff₀ ha0] at h1a
    have h3 : (1 / (8839 / 200000 : ℝ)) ^ 2 ≤ a := by
      rw [div_pow, one_pow, div_le_iff₀ (by norm_num)]
      linarith
    have h4 : 1 / (8839 / 200000 : ℝ) ≤ b := by
      rw [hb]
      exact (Real.le_sqrt' (by norm_num)).2 h3
    rw [div_le_iff₀ hb0]
    rw [div_le_iff₀ (by norm_num)] at h4
    linarith
  have hb10 : (0 : ℝ) ≤ 1 / b := by positivity
  have ha10 : (0 : ℝ) ≤ 1 / a := by positivity
  have e : (3.84 : ℝ) / (a * b) + 11 / (mF n : ℝ) =
      384 / 100 * ((1 / a) * (1 / b)) + 11 * (1 / (mF n : ℝ)) := by
    field_simp
    ring
  rw [e] at h
  have hp : (1 / a) * (1 / b) ≤ 10000 / 80000 * (1 / √(n : ℝ)) * (8839 / 200000) :=
    mul_le_mul hmF1 hb1 hb10 (by positivity)
  have e2 : (23900 / 1000000 : ℝ) / √(n : ℝ) = 23900 / 1000000 * (1 / √(n : ℝ)) := by ring
  rw [e2]
  nlinarith

/-- `eDB (biasK (mF n)) (tau143sC n) n ≤ 0.78728/√n` for `n ≥ 4096`. -/
theorem eD145_R {n : ℕ} (hn : 4096 ≤ n) : eDBq (biasK (mF n)) (tau143sC n) (pWC n) n ≤ 78728 / 100000 / √(n : ℝ) :=
  eDBgen_R hn (biasK_nonneg _) (biasK_R hn) (tau143sC_nonneg n) (tau143sC_leR hn) (pWC_nonneg n) (pWC_leR hn)

/-- The kernel bound with `τ = tau143sC n` and the bias constant `biasK (mF n)`. -/
theorem kernR {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * eDBq (biasK (mF n)) (tau143sC n) (pWC n) n) := by
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  exact kernBq hn (biasK_nonneg _) (fun y y' => rF0_bias (by omega) hmF y y')
    (tau143sC_nonneg n) (tX_L2_145C hn) (chord_pW_loc hn)

/-! ## The good hidden event and the mean of the frame constant -/

/-- The window event with the frame constant `LfX` is a good hidden event (`GoodEvF`). -/
theorem goodEvFR {n : ℕ} (hn : 4096 ≤ n) :
    GoodEvF n (Gwin n) (LfX (47767 / 100000) (4 / 625) (12 / 3125) n) :=
  ⟨Gwin_meas (by omega), fun θ hθ => hθ, LfX_meas (by omega) _ _ _,
    fun θ _ => LfX_nonneg (by norm_num) θ,
    fun θ hθ w => frameLfX hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) hθ w⟩

/-- The constant of the mean of `Lf·(DKV + Lf/n)`. -/
noncomputable def Lam145R : ℝ := 8593 / 50000

/-- **The mean of the frame constant times the variance term**, `n ≥ 4096`. -/
theorem LamVR {n : ℕ} (hn : 4096 ≤ n) :
    Integrable ((Gwin n).indicator fun θ => LfX (47767 / 100000) (4 / 625) (12 / 3125) n θ *
        (DKV n θ + LfX (47767 / 100000) (4 / 625) (12 / 3125) n θ / (n : ℝ)))
      (hidGauss (2 * n) (mW n)) ∧
    ∫ θ, (Gwin n).indicator (fun θ => LfX (47767 / 100000) (4 / 625) (12 / 3125) n θ *
        (DKV n θ + LfX (47767 / 100000) (4 / 625) (12 / 3125) n θ / (n : ℝ))) θ
      ∂hidGauss (2 * n) (mW n) ≤ Lam145R := by
  have hn4 : 4096 ≤ n := by omega
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geR hn
  have he0 : 0 ≤ eDBq (biasK (mF n)) (tau143sC n) (pWC n) n := eDBq_nonneg _ _ _ n
  have he : eDBq (biasK (mF n)) (tau143sC n) (pWC n) n ≤ 78728 / 100000 * (1 / 64) := by
    have h := eD145_R hn
    have h2 : (78728 / 100000 : ℝ) / √(n : ℝ) ≤ 78728 / 100000 / 64 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have e : (78728 / 100000 : ℝ) / 64 = 78728 / 100000 * (1 / 64) := by ring
    linarith
  have hQ : 1 - kappa^[6] 0 ≤ 2229 / 10000 := by have := kappa6_zero_ge'; linarith
  have hQ0 : 0 ≤ 1 - kappa^[6] 0 := aQ_nonneg
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 - kappa^[6] 0 + eDBq (biasK (mF n)) (tau143sC n) (pWC n) n := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; linarith
  have hvU : v ≤ 188161 / 800000 := by rw [hv]; linarith
  obtain ⟨hDi, hDv⟩ := DKV_mean hn4 he0 (kernR hn4)
  rw [← hv] at hDv
  have hDL := DKV_L2 hn4 he0 (kernR hn4)
  rw [← hv] at hDL
  obtain ⟨hI, hB⟩ := LfX_DKV_mean2 hn4 (s := 47767 / 100000) (ε₁ := 4 / 625) (ε₂ := 12 / 3125)
    (by norm_num) hDi hDv (fun θ => DKV_le_two hn4 θ) hv0 hDL
  refine ⟨hI, hB.trans ?_⟩
  have hl := lam0_le (n0 := 4096) (by norm_num) hn (s := 47767 / 100000) (k6 := 42791 / 2000000) (by norm_num)
    (by norm_num) (by norm_num)
  have hl' : lam0 (47767 / 100000) n ≤ 67053 / 100000 := hl.trans (by norm_num)
  have hl0 : 0 ≤ lam0 (47767 / 100000) n := lam0_nonneg (by omega) (by norm_num)
  have hr := rho1_le (n0 := 4096) (by norm_num) hn (s := 47767 / 100000) (r0 := 1 / 262144)
    (kK := 28159 / 5000000) (kD := 172429 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hr' : rho1 (47767 / 100000) n ≤ 47889 / 1000000 := hr.trans (by norm_num)
  have hr0 : 0 ≤ rho1 (47767 / 100000) n := rho1_nonneg hn4 (by norm_num)
  have h2 := r2_le0 (n0 := 4096) (by norm_num) hn (4 / 625) (12 / 3125) (r0 := 1 / 262144)
    (by norm_num) (by norm_num)
  have h2' : r2 (4 / 625) (12 / 3125) n ≤ 5097 / 10000000 := h2.trans (by norm_num)
  have p1 : lam0 (47767 / 100000) n * v ≤ 67053 / 100000 * (188161 / 800000) := mul_le_mul hl' hvU hv0 (by norm_num)
  have p2 : rho1 (47767 / 100000) n * v ≤ 47889 / 1000000 * (188161 / 800000) := mul_le_mul hr' hvU hv0 (by norm_num)
  have p3 : lam0 (47767 / 100000) n ^ 2 ≤ (67053 / 100000) ^ 2 := pow_le_pow_left₀ hl0 hl' 2
  have p4 : rho1 (47767 / 100000) n ^ 2 ≤ (47889 / 1000000) ^ 2 := pow_le_pow_left₀ hr0 hr' 2
  have p5 : 3 / (n : ℝ) ≤ 3 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have p50 : (0 : ℝ) ≤ 3 / (n : ℝ) := by positivity
  have p6 : 3 / (n : ℝ) * (lam0 (47767 / 100000) n ^ 2 + rho1 (47767 / 100000) n ^ 2) ≤
      3 / 4096 * ((67053 / 100000) ^ 2 + (47889 / 1000000) ^ 2) :=
    mul_le_mul p5 (by linarith) (by positivity) (by norm_num)
  have key : (67053 / 100000 : ℝ) * (188161 / 800000) + 47889 / 1000000 * (188161 / 800000) + 5 * (5097 / 10000000) +
      3 / 4096 * ((67053 / 100000) ^ 2 + (47889 / 1000000) ^ 2) ≤ 8593 / 50000 := by norm_num
  unfold Lam145R
  linarith

/-- The constant of the mean squared error for `n ≥ 4096`. -/
lemma XA145_R {n : ℕ} (hn : 4096 ≤ n) :
    XF Lam145R n (1 / 20) (1 / 7) (1 / 29) ≤ 4849 / 20000 * (1 / (n : ℝ)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hy : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hE := EHH_R hn
  have hP := pertA16 (n := n) (by omega)
  have e1 : (93689 / 100000000 : ℝ) / n = 93689 / 100000000 * (1 / n) := by ring
  have e2 : (27501 : ℝ) / 100000000 / n = 27501 / 100000000 * (1 / n) := by ring
  rw [e1] at hE
  rw [e2] at hP
  unfold XF
  rw [hP]
  have e3 : Lam145R / (n : ℝ) = 8593 / 50000 * (1 / (n : ℝ)) := by unfold Lam145R; ring
  rw [e3]
  nlinarith

/-- **The rate**, for the measurable event `okProgEG (Gwin n) k` inside `okProgA k n`. For every
`n ≥ 4096`, `k ≥ 1`: `Pr(…) ≥ 1 − (33.12002/n + 31.6/k)` (`θ = 57 / 100`). -/
theorem arithProgSucceedsE145R {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (1656001 / 50000 / (n : ℝ) + 158 / 5 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgEG (Gwin n) k) := by
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨hΛi, hΛ⟩ := LamVR hn
  have hG1 : (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤ 0 + 1 / 50000 / (n : ℝ) := by
    have h := Gwin_compl_n hn4
    unfold cW at h
    have e : (15640 : ℝ) / 1073741824 / (n : ℝ) ≤ 1 / 50000 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    linarith
  have h := progJointEG0 hn4 hk (θ := 57 / 100) (by norm_num) (by norm_num) (goodEvFR hn4).to0
    hG1
    (XF_nonneg hn4 (by unfold Lam145R; norm_num) (1 / 20) (η := 1 / 7) (by norm_num)
      (η' := 1 / 29) (by norm_num))
    (XA145_R hn)
    (errSampleAF_lint hn4 (goodEvFR hn4) (by unfold Lam145R; norm_num) hΛi hΛ
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)
    (eDBq_nonneg _ _ _ n) (eD145_R hn) (kernR hn4)
  refine le_trans ?_ h
  have e1 : (2 / 10000 + 4 * (4849 / 20000) / (57 / 100 * (222757 / 1000000 : ℝ)) +
      2 * (78728 / 100000 : ℝ) ^ 2 / (4 * (57 / 100) * (1 - 57 / 100) * (222757 / 1000000) ^ 2)) /
        (n : ℝ) ≤ 828 / 25 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (57 / 100 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 158 / 5 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : (1656001 / 50000 : ℝ) / n = 1 / 50000 / n + 828 / 25 / n := by ring
  rw [e3]
  linarith

/-- **The rate for the program output** (`okProgA k n`: `|gProgA − B| ≤ sd/2`), every `n ≥ 4096`,
`k ≥ 1`. -/
theorem arithProgSucceeds145R {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (1656001 / 50000 / (n : ℝ) + 158 / 5 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) :=
  (arithProgSucceedsE145R hn hk).trans
    (measureReal_mono (okProgEG_sub (Gwin n) k) (measure_ne_top _ _))

/-- **Level `99/100` for every `n ≥ 4096` and `k ≥ 100n`.** -/
theorem arithProg145R_99 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hkR : (100 : ℝ) * n ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : 1 ≤ k := by omega
  have h := arithProgSucceeds145R (n := n) (by omega) hk1
  refine le_trans ?_ h
  have a1 : (1656001 / 50000 : ℝ) / n ≤ 1656001 / 50000 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have a2 : (158 / 5 : ℝ) / k ≤ 158 / 5 / (100 * 4096) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  norm_num at a1 a2 ⊢
  linarith

/-- **The two-stage form (the order of Option A) for the program**, every `n ≥ 4096`, `k ≥ 1`,
`q > 0`: `Pr_{W,F}(Pr_{A,γ}(|gProgA − B| ≤ sd/2) > 1 − q) ≥ 1 − (33.12002/n + 31.6/k)/q`. -/
theorem optA145R {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq : 0 < q) :
    1 - (1656001 / 50000 / (n : ℝ) + 158 / 5 / (k : ℝ)) / q ≤
      (lawWF (2 * n) (mW n) n (mF n)).real
        {x | 1 - q < ((mlpGauss n (mA n) n).prod (gamK k n)).real
          {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} :=
  twoStageProgG0 (by omega) (goodEvFR (by omega)).to0 hq (arithProgSucceedsE145R hn hk)

/-- **Two-stage levels `(9/10, 9/10)` for every `n ≥ 4096`, `k ≥ 100n`.** -/
theorem optA145R_levels {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    9 / 10 ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 9 / 10 < ((mlpGauss n (mA n) n).prod (gamK k n)).real
        {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hkR : (100 : ℝ) * n ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have h := optA145R (n := n) (by omega) (k := k) (by omega) (q := 1 / 10) (by norm_num)
  have e : (1 : ℝ) - 1 / 10 = 9 / 10 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  have a1 : (1656001 / 50000 : ℝ) / n ≤ 1656001 / 50000 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have a2 : (158 / 5 : ℝ) / k ≤ 158 / 5 / (100 * 4096) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have : (1656001 / 50000 / (n : ℝ) + 158 / 5 / (k : ℝ)) / (1 / 10) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by norm_num)]
    norm_num at a1 a2 ⊢
    linarith
  linarith

/-- **Two-stage levels `(95/100, 95/100)` for every `n ≥ 16384`, `k ≥ 100n`.** -/
theorem optA145R_levels_16 {n : ℕ} (hn : 16384 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    95 / 100 ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 95 / 100 < ((mlpGauss n (mA n) n).prod (gamK k n)).real
        {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hkR : (100 : ℝ) * n ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have h := optA145R (n := n) (by omega) (k := k) (by omega) (q := 1 / 20) (by norm_num)
  have e : (1 : ℝ) - 1 / 20 = 95 / 100 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  have a1 : (1656001 / 50000 : ℝ) / n ≤ 1656001 / 50000 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have a2 : (158 / 5 : ℝ) / k ≤ 158 / 5 / (100 * 16384) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have : (1656001 / 50000 / (n : ℝ) + 158 / 5 / (k : ℝ)) / (1 / 20) ≤ 1 / 20 := by
    rw [div_le_iff₀ (by norm_num)]
    norm_num at a1 a2 ⊢
    linarith
  linarith

/-- **The comparison for every `n ≥ 4096`** (compare `compare144`, `compare145`): the arithmetic
one-pass program with `100n` cheap points succeeds with probability at least `99/100` at a cost
of at most `2000016/10⁶·m_W²` operations; every mean of `k ≤ 18` independent exact samples
fails with probability above `1/100`; one direct exact sample costs at least `2·m_W²`
operations; the program costs at most `1.001` direct samples, and `19` direct samples cost at
least `18981/1000` times the program. -/
theorem compare145R {n : ℕ} (hn : 4096 ≤ n) :
    (99 / 100 ≤ ((mlpTriple 2 n).prod (gamK (100 * n) n)).real (okProgA (100 * n) n)) ∧
    (1000000 * (arithProg141 (100 * n) n).cost ≤ 2000016 * mW n ^ 2) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 18 →
      1 / 100 < ((mlpTriple 2 n).prod (BstLean.Part144.uniK k (2 * n))).real
        (BstLean.Part144.failSet k)) ∧
    (2 * mW n ^ 2 ≤ (sampleRProg 2 n (mW n) (mA n) (mF n)).cost) ∧
    (1000 * (arithProg141 (100 * n) n).cost ≤
      1001 * (sampleRProg 2 n (mW n) (mA n) (mF n)).cost) ∧
    (18981 * (arithProg141 (100 * n) n).cost ≤
      1000 * (19 * (sampleRProg 2 n (mW n) (mA n) (mF n)).cost)) := by
  have hv := progVsSample145 (n := n) (by omega)
  have hd := BstLean.Part144.directSampleCost144 2 n (mW n) (mA n) (mF n)
  have hc : 1000000 * (arithProg141 (100 * n) n).cost ≤ 2000016 * mW n ^ 2 := by
    have h2 : 4096 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
    exact progCost145_of (n := n) (by omega) (c := 16) (by omega)
  refine ⟨arithProg145R_99 hn le_rfl, hc,
    fun k hk1 hk => BstLean.Part144.sampleFails144_4096 (by omega) hk1 hk, by omega, hv, by omega⟩

end BstLean.Part145

open BstLean.Part145 in
#print axioms optA145R
open BstLean.Part145 in
#print axioms optA145R_levels
open BstLean.Part145 in
#print axioms optA145R_levels_16
open BstLean.Part145 in
#print axioms compare145R
open BstLean.Part145 in
#print axioms eDBgen_R
open BstLean.Part145 in
#print axioms biasK_R
open BstLean.Part145 in
#print axioms kernR
open BstLean.Part145 in
#print axioms LamVR
open BstLean.Part145 in
#print axioms arithProgSucceeds145R
open BstLean.Part145 in
#print axioms arithProg145R_99
