import BstLean.Part143Core
import BstLean.Part143Big
import BstLean.Part143HidC2
import BstLean.Part143Num
import BstLean.Part143World
import BstLean.Part143Asm

/-!
# Part 143: level `99/100` for the arithmetic program of Part 141 INSIDE the frontier interval

Role: `delegations/statements/p143-spec.md`. The program is `arithProg141 k n` (Part 141),
unchanged; `okProgA k n` is the event `|gProgA − B| ≤ sd/2` of Part 141. Only the proof of the
probability changes against Part 142:

* the kernel bound with two orthogonal blocks (`Part143Asm`, `Part143AgentC`, `Part143FC`) and
  the sharper link of the inputs and the World network (`Part143World`): `eD143`;
* the factor 2 of the spread (`Part143Spread`);
* the sharper probabilities of the SAME events `good136`, `goodDist`, `goodT` (`Part143HidK`,
  `Part143HidC2`);
* the stand-in factor `1.37` for `n ≥ 16384` (`Part143Lam`, `Part143Var2`).

* `eD143 n`, `kernDist143`: `‖kD − S(1 − Q)‖₂ ≤ S·eD143 n`; `eD143_16`: `eD143 n ≤ 0.9903/√n`
  for `n ≥ 16384` (Part 142: `1.4406`).
* **`arithProgSucceeds143`**: `Pr(ok) ≥ 1 − (0.000775 + 110.1/n + 85.6/k)`, every `n ≥ 16384`.
* **`arithProg143_99`**: level `99/100` for every `n ≥ 16384`, `k ≥ 100n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-- **The `L²` error of the distance kernel with the orthogonal blocks.** -/
noncomputable def eD143 (n : ℕ) : ℝ :=
  √(asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (tau143s n) ^ 2 +
    (asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (cAdlt n (mA n))
        (tau143s n) +
      asmE4 (rR0 n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) (tau143s n) +
      √(asmE3 (cC0 n (mA n)) (cC1 n) (cC2 n (mA n)) (tau143s n) ^ 2 +
        (sig4 * tau143s n) ^ 2)) ^ 2)

lemma eD143_nonneg (n : ℕ) : 0 ≤ eD143 n := Real.sqrt_nonneg _

/-- **`kernel143`**: `‖kD − S(1 − Q)‖₂ ≤ S·eD143 n`, every `n ≥ 4096`. -/
theorem kernDist143 {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * eD143 n) := by
  have hT := tX_L2_143s hn
  exact kernDist143_focus hn (tau143s_nonneg n) hT (chord_pW (by omega) hT)

/-- `a² + b² ≤ c²` gives `√(a² + b²) ≤ c`. -/
lemma sqrt_sq_add_le {a b A B c : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ A) (hb0 : 0 ≤ b) (hb : b ≤ B)
    (hc : 0 ≤ c) (h : A ^ 2 + B ^ 2 ≤ c ^ 2) : √(a ^ 2 + b ^ 2) ≤ c := by
  refine Real.sqrt_le_iff.mpr ⟨hc, ?_⟩
  have h1 : a ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ ha0 ha 2
  have h2 : b ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hb0 hb 2
  linarith

/-! ## Arithmetic of the constants (real numbers only) -/

section arith

variable {t τ a4 a2 aQ sg d0 d1 d2 : ℝ}

lemma dl_arith (ht0 : 0 < t) (ht1 : t ≤ 1 / 128) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1009 / 1000 * t)
    (ha40 : 0 ≤ a4) (ha4 : a4 ≤ 319057 / 1000000) (ha20 : 0 ≤ a2) (ha2 : a2 ≤ 50628 / 100000)
    (hd00 : 0 ≤ d0) (hd0 : d0 ≤ 81295 / 100000 * (t * t)) (hd10 : 0 ≤ d1)
    (hd1 : d1 ≤ 1 + 1 / 16384) (hd20 : 0 ≤ d2) (hd2 : d2 ≤ 103930 / 10000 * (t * t)) :
    0 ≤ d0 + d1 * (a4 + τ) + d2 * (a2 + τ) ∧ d0 + d1 * (a4 + τ) + d2 * (a2 + τ) ≤ 3274 / 10000 := by
  have hτ1 : τ ≤ 1009 / 1000 * (1 / 128) := by nlinarith
  have p1 : d1 * (a4 + τ) ≤ (1 + 1 / 16384) * (319057 / 1000000 + 1009 / 1000 * (1 / 128)) :=
    mul_le_mul hd1 (by linarith) (by linarith) (by norm_num)
  have p3 : t * t ≤ 1 / 16384 := by nlinarith
  have p2 : d2 * (a2 + τ) ≤
      103930 / 10000 * (1 / 16384) * (50628 / 100000 + 1009 / 1000 * (1 / 128)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have q1 : 0 ≤ d1 * (a4 + τ) := mul_nonneg hd10 (by linarith)
  have q2 : 0 ≤ d2 * (a2 + τ) := mul_nonneg hd20 (by linarith)
  constructor
  · linarith
  · have : d0 ≤ 81295 / 100000 * (1 / 16384) := by nlinarith
    linarith

lemma E2_arith {dl f1b f2 f3 f4 N0 e4 δ2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 128)
    (hdl0 : 0 ≤ dl) (hdl : dl ≤ 3274 / 10000) (hf1b : f1b ≤ 1531 / 10000 * t)
    (hf2 : f2 ≤ 3608 / 100000 * t) (hN00 : 0 ≤ N0) (hN0 : N0 ≤ 1 + 6106 / 100000000)
    (hf3 : f3 ≤ 6292 / 100000 * t) (he40 : 0 ≤ e4) (he4 : e4 ≤ 141444 / 100000 * t)
    (hf4 : f4 ≤ 63662 / 100000) (hδ0 : 0 ≤ δ2) (hδ : δ2 ≤ 70307 / 10000 * (t * t)) :
    2 * f1b * dl + 2 * f2 * N0 + 2 * f3 * e4 + f4 * δ2 ≤ 2088 / 10000 * t := by
  have p1 : f1b * dl ≤ 1531 / 10000 * t * (3274 / 10000) :=
    mul_le_mul hf1b hdl hdl0 (by positivity)
  have p2 : f2 * N0 ≤ 3608 / 100000 * t * (1 + 6106 / 100000000) :=
    mul_le_mul hf2 hN0 hN00 (by positivity)
  have p3 : f3 * e4 ≤ 6292 / 100000 * t * (141444 / 100000 * t) :=
    mul_le_mul hf3 he4 he40 (by positivity)
  have p4 : f4 * δ2 ≤ 63662 / 100000 * (70307 / 10000 * (t * t)) :=
    mul_le_mul hf4 hδ hδ0 (by norm_num)
  have ht2 : t * t ≤ 1 / 128 * t := mul_le_mul_of_nonneg_right ht1 ht0.le
  have q3 : 6292 / 100000 * t * (141444 / 100000 * t) =
      6292 / 100000 * (141444 / 100000) * (t * t) := by ring
  nlinarith

lemma E3_arith {c0 c1 c2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 128) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1009 / 1000 * t) (ha20 : 0 ≤ a2) (ha2 : a2 ≤ 50628 / 100000) (haQ0 : 0 ≤ aQ)
    (haQ : aQ ≤ 2229 / 10000) (hsg0 : 0 ≤ sg) (hsg : sg ≤ 4404 / 10000)
    (hc0 : c0 ≤ 153 / 10000 * (t * t)) (hc1 : c1 ≤ 141422 / 100000 * t)
    (hc2 : c2 ≤ 115 / 1000 * (t * t)) :
    c0 + c1 * (aQ + sg * τ) + c2 * (a2 + τ) ≤ 3208 / 10000 * t := by
  have hτ1 : τ ≤ 1009 / 1000 * (1 / 128) := by nlinarith
  have s1 : sg * τ ≤ 4404 / 10000 * (1009 / 1000 * (1 / 128)) :=
    mul_le_mul hsg hτ1 hτ0 (by norm_num)
  have s10 : 0 ≤ sg * τ := mul_nonneg hsg0 hτ0
  have p1 : c1 * (aQ + sg * τ) ≤
      141422 / 100000 * t * (2229 / 10000 + 4404 / 10000 * (1009 / 1000 * (1 / 128))) :=
    mul_le_mul hc1 (by linarith) (by linarith) (by positivity)
  have p2 : c2 * (a2 + τ) ≤
      115 / 1000 * (t * t) * (50628 / 100000 + 1009 / 1000 * (1 / 128)) :=
    mul_le_mul hc2 (by linarith) (by linarith) (by positivity)
  have ht2 : t * t ≤ 1 / 128 * t := mul_le_mul_of_nonneg_right ht1 ht0.le
  nlinarith

lemma E4_arith {r0 r1' r2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 128) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1009 / 1000 * t) (ha4l : 319029 / 1000000 ≤ a4) (ha20 : 0 ≤ a2)
    (ha2 : a2 ≤ 50628 / 100000) (haQ : aQ ≤ 2229 / 10000) (hsg0 : 0 ≤ sg)
    (hsg : sg ≤ 4404 / 10000) (hr0 : r0 ≤ 838 / 100 * (t * t))
    (hr1'l : 3408 / 10000 * t ≤ r1') (hr1'u : r1' ≤ 3408455 / 10000000 * t) (hr20 : 0 ≤ r2)
    (hr2 : r2 ≤ 1051 / 100 * (t * t)) :
    r0 + t * aQ - r1' * a4 + r2 * a2 + (t * sg + r1' + r2) * τ ≤ 2281 / 10000 * t := by
  have hτ1 : τ ≤ 1009 / 1000 * (1 / 128) := by nlinarith
  have hr1'0 : 0 ≤ r1' := by nlinarith
  have p1 : t * aQ ≤ t * (2229 / 10000) := mul_le_mul_of_nonneg_left haQ ht0.le
  have p2 : 3408 / 10000 * t * (319029 / 1000000) ≤ r1' * a4 :=
    mul_le_mul hr1'l ha4l (by norm_num) hr1'0
  have p3 : r2 * a2 ≤ 1051 / 100 * (t * t) * (50628 / 100000) :=
    mul_le_mul hr2 ha2 ha20 (by positivity)
  have p4 : t * sg ≤ t * (4404 / 10000) := mul_le_mul_of_nonneg_left hsg ht0.le
  have p40 : 0 ≤ t * sg := mul_nonneg ht0.le hsg0
  have p5 : (t * sg + r1' + r2) * τ ≤
      (t * (4404 / 10000) + 3408455 / 10000000 * t + 1051 / 100 * (t * t)) *
        (1009 / 1000 * (1 / 128)) :=
    mul_le_mul (by linarith) hτ1 hτ0 (by positivity)
  have ht2 : t * t ≤ 1 / 128 * t := mul_le_mul_of_nonneg_right ht1 ht0.le
  nlinarith

lemma final_arith {E1 E2 E3 E4 pW : ℝ} (ht0 : 0 < t) (h10 : 0 ≤ E1)
    (h1 : E1 ≤ 1005 / 10000 * t) (h20 : 0 ≤ E2) (h2 : E2 ≤ 2088 / 10000 * t) (h30 : 0 ≤ E3)
    (h3 : E3 ≤ 3208 / 10000 * t) (h40 : 0 ≤ E4) (h4 : E4 ≤ 2281 / 10000 * t) (hp0 : 0 ≤ pW)
    (hp : pW ≤ 4444 / 10000 * t) :
    √(E1 ^ 2 + (E2 + E4 + √(E3 ^ 2 + pW ^ 2)) ^ 2) ≤ 9903 / 10000 * t := by
  have hin : √(E3 ^ 2 + pW ^ 2) ≤ 5482 / 10000 * t :=
    sqrt_sq_add_le h30 h3 hp0 hp (by positivity) (by nlinarith [sq_nonneg t])
  have hin0 := Real.sqrt_nonneg (E3 ^ 2 + pW ^ 2)
  exact sqrt_sq_add_le h10 h1 (by linarith) (by linarith : _ ≤ 9851 / 10000 * t)
    (by positivity) (by nlinarith [sq_nonneg t])

end arith

/-- **`eD143 n ≤ 0.9903/√n`** for `n ≥ 16384`. -/
theorem eD143_16 {n : ℕ} (hn : 16384 ≤ n) : eD143 n ≤ 9903 / 10000 / √(n : ℝ) := by
  have hn4 : 4096 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge16 hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / √(n : ℝ) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 128 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have htt : t * t = 1 / (n : ℝ) := by
    rw [ht, div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have conv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  have conv2 : ∀ c : ℝ, c / (n : ℝ) = c * (t * t) := fun c => by rw [htt]; ring
  obtain ⟨hmF1, hmF2⟩ := inv_mF16 hn
  rw [← ht] at hmF1 hmF2
  have h3 := s3_le16
  have hmF10 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have hf1b : f1b (mF n) ≤ 1531 / 10000 * t := by
    have e : f1b (mF n) = √3 * (1 / √(mF n : ℝ)) := by unfold f1b; ring
    rw [e]
    have := mul_le_mul h3 hmF1 hmF10 (by norm_num)
    linarith
  have hf1a : f1a (mF n) ≤ 15347 / 100000 * t := by
    have e : f1a (mF n) = √3 * (1 / √(mF n : ℝ)) + 6 * (1 / (mF n : ℝ)) := by unfold f1a; ring
    rw [e]
    have := mul_le_mul h3 hmF1 hmF10 (by norm_num)
    linarith
  have hf2 : f2 (mF n) ≤ 3608 / 100000 * t := (f2_16 hn).trans_eq (conv _)
  have hf3 : f3 (mF n) ≤ 6292 / 100000 * t := (f3_16 hn).trans_eq (conv _)
  have hd0 : dA0 n (mA n) ≤ 81295 / 100000 * (t * t) := (dA0_16 hn).trans_eq (conv2 _)
  have hd2 : dA2 n (mA n) ≤ 103930 / 10000 * (t * t) := (dA2_16 hn).trans_eq (conv2 _)
  have hcd : cAdlt n (mA n) ≤ 70307 / 10000 * (t * t) := (cAdlt16 hn).trans_eq (conv2 _)
  have he4 : √(eps4 n (mA n)) ≤ 141444 / 100000 * t := (sqrt_eps4_16 hn).trans_eq (conv _)
  have hτ : tau143s n ≤ 1009 / 1000 * t := (tau143s_le hn).trans_eq (conv _)
  have hτ0 := tau143s_nonneg n
  have ha4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have ha40 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have ha4l : 319029 / 1000000 ≤ 1 - kappa^[4] 0 := by
    have h : kappa^[4] 0 ≤ 680971 / 1000000 := BstLean.Part139.kappa4_zero_le
    linarith
  have ha2 : 1 - kappa (kappa 0) ≤ 50628 / 100000 := by have := kappa2_zero_ge; linarith
  have ha20 : 0 ≤ 1 - kappa (kappa 0) := a2_nonneg
  have haQ : 1 - kappa^[6] 0 ≤ 2229 / 10000 := by have := kappa6_zero_ge'; linarith
  have haQ0 : 0 ≤ 1 - kappa^[6] 0 := aQ_nonneg
  have hc0 : cC0 n (mA n) ≤ 153 / 10000 * (t * t) := (cC0_le hn).trans_eq (conv2 _)
  have hc1 : cC1 n ≤ 141422 / 100000 * t := (cC1_le (n := n)).trans_eq (conv _)
  have hc2 : cC2 n (mA n) ≤ 115 / 1000 * (t * t) := (cC2_le hn).trans_eq (conv2 _)
  have hr0 : rR0 n (mA n) ≤ 838 / 100 * (t * t) := (rR0_le hn).trans_eq (conv2 _)
  have hr2 : rR2 n (mA n) ≤ 1051 / 100 * (t * t) := (rR2_le hn).trans_eq (conv2 _)
  have hr1 : rR1 n = t := by rw [rR1_eq, ht]
  have hr1'l : 3408 / 10000 * t ≤ rR1' n := (conv _).symm.trans_le (rR1'_ge hn)
  have hr1'u : rR1' n ≤ 3408455 / 10000000 * t := by
    have e : rR1' n = AgS.cgS (kappa ∘ kappa) * t := by
      unfold rR1' sA1'; rw [ht]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right cg2_le16 ht0.le
  have hd00 := dA0_nonneg n (mA n)
  have hd10 := dA1_nonneg n (mA n)
  have hd20 := dA2_nonneg n (mA n)
  have hcd0 := cAdlt_nonneg n (mA n)
  obtain ⟨hdl0, hdlU⟩ := dl_arith ht0 ht1 hτ0 hτ ha40 ha4 ha20 ha2 hd00 hd0 hd10 (dA1_16 hn)
    hd20 hd2
  have hE1 : asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (tau143s n) ≤
      1005 / 10000 * t := by
    unfold asmE1
    have := mul_le_mul hf1a hdlU hdl0 (by positivity)
    nlinarith
  have hE2 : asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n))
      (cAdlt n (mA n)) (tau143s n) ≤ 2088 / 10000 * t := by
    unfold asmE2
    exact E2_arith ht0 ht1 hdl0 hdlU hf1b hf2 (by positivity) (N0_16 hn) hf3
      (Real.sqrt_nonneg _) he4 f4_le hcd0 hcd
  have hE3 : asmE3 (cC0 n (mA n)) (cC1 n) (cC2 n (mA n)) (tau143s n) ≤ 3208 / 10000 * t := by
    unfold asmE3
    exact E3_arith ht0 ht1 hτ0 hτ ha20 ha2 haQ0 haQ sig4_nonneg sig4_le hc0 hc1 hc2
  have hE4 : asmE4 (rR0 n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) (tau143s n) ≤
      2281 / 10000 * t := by
    unfold asmE4
    rw [hr1]
    exact E4_arith ht0 ht1 hτ0 hτ ha4l ha20 ha2 haQ sig4_nonneg sig4_le hr0 hr1'l hr1'u
      (rR2_nonneg n (mA n)) hr2
  have hE40 : 0 ≤ asmE4 (rR0 n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) (tau143s n) := by
    have h := rR_ref_nonneg n (mA n)
    have h1 : 0 ≤ (rR1 n * sig4 + rR1' n + rR2 n (mA n)) * tau143s n :=
      mul_nonneg (add_nonneg (add_nonneg (mul_nonneg (rR1_nonneg n) sig4_nonneg)
        (rR1'_nonneg n)) (rR2_nonneg n (mA n))) hτ0
    unfold asmE4
    linarith
  have hpW : sig4 * tau143s n ≤ 4444 / 10000 * t := by
    have := mul_le_mul sig4_le hτ hτ0 (by norm_num)
    nlinarith
  rw [conv]
  unfold eD143
  exact final_arith ht0 (asmE1_nonneg (mF n) hd00 hd10 hd20 hτ0) hE1
    (asmE2_nonneg n (mA n) (mF n) hd00 hd10 hd20 hcd0 hτ0) hE2
    (asmE3_nonneg (cC0_nonneg n (mA n)) (cC1_nonneg n) (cC2_nonneg n (mA n)) hτ0) hE3
    hE40 hE4 (mul_nonneg sig4_nonneg hτ0) hpW

/-- `Pr(goodHat n fails) ≤ 0.000775 + 14.04/n` for `n ≥ 16384` (`Part143HidC2`). -/
lemma goodHat_compl143f {n : ℕ} (hn : 16384 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ 775 / 1000000 + 1404 / 100 / (n : ℝ) := by
  have h := goodHat_compl143s hn
  unfold P143 cExtra143s at h
  exact h

/-- **The headline of Part 143.** For every `n ≥ 16384`, `k ≥ 1`:
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.000775 + 110.1/n + 85.6/k)` (`θ = 0.21`). -/
theorem arithProgSucceeds143 {n : ℕ} (hn : 16384 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (775 / 1000000 + 1101 / 10 / (n : ℝ) + 856 / 10 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := progDist143 hn4 hk (θ := 21 / 100) (by norm_num) (by norm_num)
    (goodHat_compl143f hn)
    (XAL_nonneg hn4 L143_nonneg (1 / 20) (η := 1 / 28) (by norm_num) (η' := 1 / 36)
      (by norm_num))
    (XAL143_16 hn)
    (fun s hs => errSampleTailA143 hn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hk hs)
    (eD143_nonneg n) (eD143_16 hn) (kernDist143 hn4)
  refine le_trans ?_ h
  have e1 : (2 / 10000 + 4 * (3815 / 10000) / (21 / 100 * (222757 / 1000000 : ℝ)) +
      2 * (9903 / 10000 : ℝ) ^ 2 / ((1 - 21 / 100) * (222757 / 1000000)) ^ 2) / (n : ℝ) ≤
      9606 / 100 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (21 / 100 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 856 / 10 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : (1101 : ℝ) / 10 / n = 1404 / 100 / n + 9606 / 100 / n := by ring
  rw [e3]
  linarith

/-- **Level `99/100` inside the frontier interval**: for every `n ≥ 16384` and `k ≥ 100n`. -/
theorem arithProg143_99 {n : ℕ} (hn : 16384 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hkR : (100 : ℝ) * n ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : 1 ≤ k := by omega
  have h := arithProgSucceeds143 hn hk1
  refine le_trans ?_ h
  have a1 : (1101 : ℝ) / 10 / n ≤ 1101 / 10 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have a2 : (856 : ℝ) / 10 / k ≤ 856 / 10 / (100 * 16384) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  norm_num at a1 a2 ⊢
  linarith

end BstLean.Part143

open BstLean.Part143 in
#print axioms kernDist143
open BstLean.Part143 in
#print axioms eD143_16
open BstLean.Part143 in
#print axioms arithProgSucceeds143
open BstLean.Part143 in
#print axioms arithProg143_99
