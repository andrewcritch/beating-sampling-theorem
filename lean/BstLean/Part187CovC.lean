import BstLean.Part186Core
import BstLean.Part186GeoC
import BstLean.Part186CovC

/-!
# Part 187 (file `CovC`): the core covariance lemmas of Part 186 `CovC` at `n ≥ 16 250`

No proof is left open; no `native_decide` or `axiom` is used. Copies (namespace
`BstLean.Part186.R16250`) of `inv_sqrt_le_128`, `geoP`, `SCovP_ret_charge`, `rm_le7`, `Dq_coreP`,
`cov_coreP` with the floor `16 250` and `1/√n ≤ 1/127`.
-/

namespace BstLean.Part186.R16250

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nrm jacT Xi4 nuA)
open BstLean.Part182
open BstLean.Part186

variable {n : ℕ}

lemma inv_sqrt_le_127 (hn : 16250 ≤ n) : (√(n : ℝ))⁻¹ ≤ 1 / 127 := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (127 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  simpa using hs

/-- **The core window geometry** for `n ≥ 16 250`. -/
theorem geoP (hn : 16250 ≤ n) {θl θh cl ch : ℝ} (hθl : 0 ≤ θl) (hθh1 : θh < 1) (hcl : 0 ≤ cl)
    (hch : 0 ≤ ch)
    (hrr : 375 / 100 * (1 / 127) + 2 * θh * (26458 / 10000) * (1 / 127) < 1)
    (hb : (375 / 100) ^ 2 * θh * (1 / 127) ^ 2 < 1 - θh)
    (hup : (1 - θl) + 1 / 127 * (375 / 100 + 375 / 100 * θh + ch * (375 / 100 + 2 * θh * (26458 / 10000))) +
      (1 / 127) ^ 2 * ((375 / 100) ^ 2 * θh + 375 / 100 * (375 / 100) * θh) ≤ ch)
    (hlo : cl * (1 + 1 / 127 * (375 / 100 + 2 * θh * (26458 / 10000)) + (1 / 127) ^ 2 * (2 * θh * 7)) ≤
      (1 - θh) - 1 / 127 * (375 / 100 + 375 / 100 * θh) - (1 / 127) ^ 2 * (375 / 100 * (375 / 100) * θh)) :
    GeoP n θl θh cl ch := by
  intro c τ hτ h0 h1 p hp
  have h7 : √(7 : ℝ) ≤ 26458 / 10000 := sqrt_le_of_sq' (by norm_num) (by norm_num)
  have h7' : √(7 : ℝ) ≤ 375 / 100 := h7.trans (by norm_num)
  exact geo_core (by omega) (t0 := 375 / 100) (z0 := 7) (t1 := 375 / 100) (uM := 1 / 127)
    (a2 := 26458 / 10000) (ag := 375 / 100) (by norm_num) (by norm_num) (by norm_num) hθl hθh1
    hcl hch (inv_sqrt_le_127 hn) h7 (by norm_num) h7' (by norm_num) hrr hb hup hlo hτ h0 h1 hp

/-- **The charge of `SCovP` at one `(c, τ)`.** -/
theorem SCovP_charge (hn : 1 ≤ n) {θl θh cl ch lam1 : ℝ} (hgeo : GeoP n θl θh cl ch)
    (hTI : TI_hyp n cl ch lam1 (1 / 10 ^ 18)) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SCovP n θl θh lam1} ≤ 1 / 10 ^ 6 := by
  by_cases hw : θl ≤ thetaC c τ ∧ thetaC c τ ≤ θh
  · have h := SCov_charge (t0 := 375 / 100) (z0 := 7) (t1 := 375 / 100) (lam := lam1) hn c τ
      (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 18) (by norm_num : (0 : ℝ) < 1 / 10 ^ 6)
      (hgeo c τ hτ hw.1 hw.2) hTI
    have e : (1 / 10 ^ 18 : ℝ) / (1 / 10 ^ 6) = 1 / 10 ^ 12 := by norm_num
    rw [e] at h
    refine le_trans (measureReal_mono (fun θ hθ => ?_) (measure_ne_top _ _)) h
    intro hS
    exact hθ (Or.inr hS)
  · have e : {θ | ((c, τ), θ) ∉ SCovP n θl θh lam1} = ∅ := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl hw
    rw [e, measureReal_empty]
    norm_num

/-- **The charge of `SCovP` for the retained data** of the paper's design. -/
theorem SCovP_ret_charge (hn : 16250 ≤ n) {θl θh cl ch lam1 : ℝ} (hgeo : GeoP n θl θh cl ch)
    (hTI : TI_hyp n cl ch lam1 (1 / 10 ^ 18))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SCovP n θl θh lam1))ᶜ ≤
      1 / 10 ^ 6 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SCovP n θl θh lam1) (by norm_num)
    (fun c τ hτ => SCovP_charge (by omega) hgeo hTI c τ hτ)

lemma rm_le7 (hn : 16250 ≤ n) {θ : ℝ} (_hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 528 / 1000) :
    2 * 5 * √(θ * (1 - θ) / n) + 2 * θ * √(14 / n) ≤ 706 / 10000 := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : √(θ * (1 - θ) / n) ≤ 1 / 254 := by
    refine sqrt_le_of_sq' (by norm_num) ?_
    have hq : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ - 1 / 2)]
    rw [div_le_iff₀ hn0]
    nlinarith
  have h2 : √((14 : ℝ) / n) ≤ 2936 / 100000 := by
    refine sqrt_le_of_sq' (by norm_num) ?_
    rw [div_le_iff₀ hn0]
    nlinarith
  have h3 : θ * √((14 : ℝ) / n) ≤ 528 / 1000 * (2936 / 100000) :=
    mul_le_mul hθ1 h2 (Real.sqrt_nonneg _) (by norm_num)
  have e : 2 * θ * √(14 / n) = 2 * (θ * √((14 : ℝ) / n)) := by ring
  rw [e]
  nlinarith

lemma exp_core_le : 2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) ≤ (1825 / 10 ^ 6 : ℝ) ∧
    2 * exp (-(7 : ℝ)) ≤ (1825 / 10 ^ 6 : ℝ) := by
  have h7 := exp_neg_nat_le 7
  have e7 : (-((7 : ℕ) : ℝ)) = -(7 : ℝ) := by norm_num
  rw [e7] at h7
  have hc : (2 : ℝ) * (3678794412 / 10 ^ 10) ^ 7 ≤ 1825 / 10 ^ 6 := by norm_num
  have hb : 2 * exp (-(7 : ℝ)) ≤ 1825 / 10 ^ 6 := by linarith
  refine ⟨le_trans ?_ hb, hb⟩
  have : exp (-(375 / 100 : ℝ) ^ 2 / 2) ≤ exp (-(7 : ℝ)) := Real.exp_le_exp.mpr (by norm_num)
  linarith

/-- **The quadratic form of `D` on one θ-piece with the core pair set.** -/
theorem Dq_coreP (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ θl θh lam1 lam0 Ke Mx : ℝ} (hτ : 0 < τ)
    (hθl : 46 / 100 ≤ θl) (hθ0 : θl ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    (hl1 : 0 ≤ lam1) (hl0 : 0 ≤ lam0) (hKe : 0 ≤ Ke)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hEw : ∫ ξ, BstLean.Part182.wN c τ ξ ∂stdGauss (Fin n) ≤ Ke * (thetaC c τ / n))
    (hX4 : Xi4 A₁ A₂ c τ ≤ Mx * θh * (2 / (n : ℝ)) / n)
    (hP : ((c, τ), (A₁, A₂)) ∈ SCovP n θl θh lam1)
    (hb0 : badMass n 5 14 8 lam0 ((c, τ), (A₁, A₂)) ≤ 1 / 10 ^ 13)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤ (lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000) +
      Mx * θh * (4933 / 10 ^ 6)) * (2 / (n : ℝ)) / n * normSq v := by
  have hn0 : 0 < n := by omega
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  set θ := thetaC c τ with hθd
  have hθlt : θ < 1 := by linarith
  have hc : c ≠ 0 := ne_zero_of_thetaC_lt hn0 hτ hθlt
  have hθ0' : 0 ≤ θ := by linarith
  have hrm := rm_le7 hn hθ0' (hθ1.trans hθh)
  have hb1 : badMass n (375 / 100) 7 (375 / 100) lam1 ((c, τ), (A₁, A₂)) ≤ 1 / 10 ^ 12 := by
    rcases hP with h | h
    · exact absurd ⟨hθ0, hθ1⟩ h
    · exact h
  have hmain := Dq_core (by omega) hτ hc (t0 := 375 / 100) (z0 := 7) (t1 := 375 / 100)
    (lam1 := lam1) (lam0 := lam0) (Ke := Ke) (M1 := 1 / 10 ^ 12) (M0 := 1 / 10 ^ 13)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hl1 hl0
    (by linarith) hEw hb1 hb0 v
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg v))
  obtain ⟨he1, he2⟩ := exp_core_le
  have hq1 : √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * (1 / 10 ^ 12) + 2 * (1 / 10 ^ 13))) ≤
      1222 / 10 ^ 6 := by
    have := two_exp_neg32
    exact sqrt_sqrt_le_of (by norm_num) (by linarith)
  have hq0 : √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * (1 / 10 ^ 13))) ≤ 690 / 10 ^ 6 := by
    have := two_exp_neg32
    exact sqrt_sqrt_le_of (by norm_num) (by linarith)
  have hq2 : √(2 * exp (-(5 : ℝ) ^ 2 / 2) + 2 * exp (-(14 : ℝ))) ≤ 3021 / 10 ^ 6 :=
    sqrt_le_of_sq' (by norm_num) (Po_le.trans (by norm_num))
  have hX40 : 0 ≤ Xi4 A₁ A₂ c τ := by unfold Xi4; positivity
  have hXq : Xi4 A₁ A₂ c τ * (√(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * (1 / 10 ^ 12) + 2 * (1 / 10 ^ 13))) +
      √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * (1 / 10 ^ 13))) +
      √(2 * exp (-(5 : ℝ) ^ 2 / 2) + 2 * exp (-(14 : ℝ)))) ≤
      Mx * θh * (2 / (n : ℝ)) / n * (4933 / 10 ^ 6) := by
    have hs : √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * (1 / 10 ^ 12) + 2 * (1 / 10 ^ 13))) +
        √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * (1 / 10 ^ 13))) +
        √(2 * exp (-(5 : ℝ) ^ 2 / 2) + 2 * exp (-(14 : ℝ))) ≤ 4933 / 10 ^ 6 := by linarith
    have hs0 : 0 ≤ √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * (1 / 10 ^ 12) + 2 * (1 / 10 ^ 13))) +
        √(√(2 * exp (-(8 : ℝ) ^ 2 / 2) + 2 * (1 / 10 ^ 13))) +
        √(2 * exp (-(5 : ℝ) ^ 2 / 2) + 2 * exp (-(14 : ℝ))) := by positivity
    exact mul_le_mul hX4 hs hs0 (hX40.trans hX4)
  -- the main part
  set rm := 2 * 5 * √(θ * (1 - θ) / n) + 2 * θ * √(14 / n) with hrmd
  have hrm1 : 0 < 1 - rm := by linarith
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hW : θ / n / (1 - rm) ≤ θh / n * (10000 / 9294) := by
    rw [div_le_iff₀ hrm1]
    have h1 : θ / n ≤ θh / n := div_le_div_of_nonneg_right hθ1 hnp.le
    have h2 : (9294 / 10000 : ℝ) ≤ 1 - rm := by linarith
    have h3 : 0 ≤ θh / n := by
      have : 0 ≤ θh := by linarith
      positivity
    calc θ / n ≤ θh / n := h1
      _ = θh / n * (10000 / 9294) * (9294 / 10000) := by ring
      _ ≤ θh / n * (10000 / 9294) * (1 - rm) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hPsum : 2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) +
      2 * exp (-(7 : ℝ))) ≤ 548 / 100000 := by linarith
  have hPp0 : 0 ≤ 2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) := by positivity
  have hPs0 : 0 ≤ 2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + 2 * exp (-(7 : ℝ)) := by positivity
  have hWn : 0 ≤ θ / n / (1 - rm) := by positivity
  have hmain2 : 2 / ((mA n : ℕ) : ℝ) * ((n : ℝ) * lam1 * (Ke * (θ / n)) +
      (n : ℝ) * lam0 * (θ / n / (1 - rm)) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2)) +
      (n : ℝ) * lam0 * (θ / n / (1 - rm)) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + 2 * exp (-(7 : ℝ)))) ≤
      (lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000)) * (2 / (n : ℝ)) / n := by
    rw [hmR]
    have e : 2 / (n : ℝ) ^ 2 * ((n : ℝ) * lam1 * (Ke * (θ / n)) +
        (n : ℝ) * lam0 * (θ / n / (1 - rm)) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2)) +
        (n : ℝ) * lam0 * (θ / n / (1 - rm)) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + 2 * exp (-(7 : ℝ)))) =
        (lam1 * Ke * θ + lam0 * ((θ / n / (1 - rm)) * n) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) +
          (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + 2 * exp (-(7 : ℝ))))) * (2 / (n : ℝ)) / n := by
      field_simp
      ring
    rw [e]
    have hpos : 0 < (2 / (n : ℝ)) / n := by positivity
    have k1 : lam1 * Ke * θ ≤ lam1 * Ke * θh :=
      mul_le_mul_of_nonneg_left hθ1 (mul_nonneg hl1 hKe)
    have k2 : (θ / n / (1 - rm)) * n ≤ θh * (10000 / 9294) := by
      have := mul_le_mul_of_nonneg_right hW hnp.le
      calc (θ / n / (1 - rm)) * n ≤ θh / n * (10000 / 9294) * n := this
        _ = θh * (10000 / 9294) := by field_simp
    have k3 : lam0 * ((θ / n / (1 - rm)) * n) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) +
        (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + 2 * exp (-(7 : ℝ)))) ≤
        lam0 * (θh * (10000 / 9294)) * (548 / 100000) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left k2 hl0) hPsum (by positivity)
      have : 0 ≤ θh := by linarith
      positivity
    have k4 : lam1 * Ke * θ + lam0 * ((θ / n / (1 - rm)) * n) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) +
        (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + 2 * exp (-(7 : ℝ)))) ≤
        lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000) := by
      have e2 : lam0 * (θh * (10000 / 9294)) * (548 / 100000) = lam0 * (10000 / 9294) * θh * (548 / 100000) := by
        ring
      linarith
    calc (lam1 * Ke * θ + lam0 * ((θ / n / (1 - rm)) * n) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) +
          (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + 2 * exp (-(7 : ℝ))))) * (2 / (n : ℝ)) / n
        = (lam1 * Ke * θ + lam0 * ((θ / n / (1 - rm)) * n) * (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) +
          (2 * exp (-(375 / 100 : ℝ) ^ 2 / 2) + 2 * exp (-(7 : ℝ))))) * ((2 / (n : ℝ)) / n) := by ring
      _ ≤ (lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000)) * ((2 / (n : ℝ)) / n) :=
          mul_le_mul_of_nonneg_right k4 hpos.le
      _ = (lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000)) * (2 / (n : ℝ)) / n := by ring
  calc _ ≤ (lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000)) * (2 / (n : ℝ)) / n +
        Mx * θh * (2 / (n : ℝ)) / n * (4933 / 10 ^ 6) := add_le_add hmain2 hXq
    _ = (lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000) + Mx * θh * (4933 / 10 ^ 6)) *
        (2 / (n : ℝ)) / n := by ring

/-- **The covariance hypothesis `COV_at D c N` on one θ-piece with the core pair set.** -/
theorem cov_coreP (hn : 16250 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    {θl θh lam1 lam0 Ke Mx N : ℝ}
    (hθl : 46 / 100 ≤ θl) (hθ0 : θl ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ θh)
    (hθh : θh ≤ 528 / 1000) (hl1 : 0 ≤ lam1) (hl0 : 0 ≤ lam0) (hKe : 0 ≤ Ke)
    (hEw : ∫ ξ, BstLean.Part182.wN c.1.2 (D.tau0 c) ξ ∂stdGauss (Fin n) ≤
      Ke * (thetaC c.1.2 (D.tau0 c) / n))
    (hX4 : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ Mx * θh * (2 / (n : ℝ)) / n)
    (hP : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SCovP n θl θh lam1)
    (hb0 : badMass n 5 14 8 lam0 ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ≤ 1 / 10 ^ 13)
    (hN : lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000) + Mx * θh * (4933 / 10 ^ 6) ≤ N) :
    COV_at D c N := by
  refine cov_at_of_Dq (by omega) D c hτ fun w => ?_
  refine (Dq_coreP hn hτ hθl hθ0 hθ1 hθh hl1 hl0 hKe hEw hX4 hP hb0 w).trans ?_
  have hnR : (0 : ℝ) < n := by
    have : (16250 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h0 : 0 ≤ (2 / (n : ℝ)) / n * normSq w := by
    have := normSq_nonneg w
    positivity
  calc (lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000) + Mx * θh * (4933 / 10 ^ 6)) *
        (2 / (n : ℝ)) / n * normSq w
      = (lam1 * Ke * θh + lam0 * (10000 / 9294) * θh * (548 / 100000) + Mx * θh * (4933 / 10 ^ 6)) *
        ((2 / (n : ℝ)) / n * normSq w) := by ring
    _ ≤ N * ((2 / (n : ℝ)) / n * normSq w) := mul_le_mul_of_nonneg_right hN h0
    _ = N * (2 / (n : ℝ)) / n * normSq w := by ring


end BstLean.Part186.R16250
