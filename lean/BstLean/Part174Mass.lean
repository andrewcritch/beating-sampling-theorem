import BstLean.Part173All

/-!
# Part 174 (file `Mass`): the mass below the floor with the larger lower bound `s0P = 0.5097`

No proof is left open; no `native_decide` or `axiom` is used.

Part 165 proves the floor mass bound `betaM n sd = (π/2)⁴⁰·E|g|⁴⁰·(0.706/(n(s0 − sd)²))²⁰` with
`s0 = 0.5087`, a lower bound of `E σ/√γ_A` from the condition
`s0² ≤ 1 − N₂₂(2 + N₂₂) − (e₁ + e₂)² − 2N/n` (`N₂₂ = 18.334/n`, `e₁ + e₂ = 0.8599`, `N = 1.1911`),
checked at `n ≥ 23 000`. At `n ≥ 54 000` the same condition holds for `s0P = 0.5097`; since
`betaM ∝ (s0 − sd)⁻⁴⁰`, this divides the mass bound at `sd = 0.4691` by about 2.7.

* `s0P`, `betaMP`, `s0P_cond` (`n ≥ 54 000`), `betaMP_nonneg`.
* **`mass_order40P`**, **`mass_of_goodCP`**: Part 165's `mass_order40`, `mass_of_goodC` with `s0P`.
* **`classifier_paper_free23_mass40P`**: Part 165's `classifier_paper_free23_mass40` with `s0P`,
  `betaMP` (every `n ≥ 54 000`).
-/

namespace BstLean.Part174

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI sigX lamX BIAS_hyp)
open BstLean.Part162 (sgA gmom gmom_nonneg psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr)
open BstLean.Part134 (res sig)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA hE8_of_good CAn E0 E0_nonneg roomB
  roomB_ge)

variable {n : ℕ}

/-- The lower bound of `E σ/√γ_A` used for the floor: `s0P = 0.5097`. -/
noncomputable def s0P : ℝ := 5097 / 10000

/-- **The mass bound of order 40**: `β(n, sd) = (π/2)⁴⁰·E|g|⁴⁰·(0.706/(n(s0P − sd)²))²⁰`. -/
noncomputable def betaMP (n : ℕ) (sd : ℝ) : ℝ :=
  (π / 2) ^ 40 * gmom 40 * (706 / 1000 / ((n : ℝ) * (s0P - sd) ^ 2)) ^ 20

lemma betaMP_nonneg (n : ℕ) (sd : ℝ) : 0 ≤ betaMP n sd := by
  unfold betaMP
  have := gmom_nonneg 40
  have h : 0 ≤ (706 / 1000 / ((n : ℝ) * (s0P - sd) ^ 2)) ^ 20 := by
    rw [show (20 : ℕ) = 2 * 10 by norm_num, pow_mul]; positivity
  positivity

/-- The numeric condition on `s0P` (`n ≥ 54 000`). -/
lemma s0P_cond (hn : 54000 ≤ n) :
    s0P ^ 2 ≤ 1 - 18334 / 1000 / (n : ℝ) * (2 + 18334 / 1000 / (n : ℝ)) -
      (8553 / 10000 + 46 / 10000) ^ 2 - 2 * (11911 / 10000) / n := by
  have hnR : (54000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 / 54000 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hnR
  have e1 : 18334 / 1000 / (n : ℝ) = 18334 / 1000 * x := by rw [hx]; ring
  have e2 : 2 * (11911 / 10000) / (n : ℝ) = 2 * (11911 / 10000) * x := by rw [hx]; ring
  rw [e1, e2]
  unfold s0P
  nlinarith

/-- **The mass below the floor from the moment of order 40 of `σ`**, for one retained value:
with the quantities of the frame events and the event `SXqN n 20`,
`∫_a ν{σ < √γ_A·sd} ≤ betaMP n sd` for `0 ≤ sd < s0P`, `n ≥ 23 000`. -/
theorem mass_order40P (hn : 54000 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 11911 / 10000 * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) ≤ 2 / (n : ℝ) * (7315 / 10000))
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ 485 / 1000 * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 18334 / 1000 / (n : ℝ))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXqN n 20)
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0P) :
    ∫ a', (stdGauss (Fin (n - 1))).real {v | sgA D c a' v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaMP n sd := by
  have hnR : (54000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : c.1.2 ≠ 0 := c_ne_of_theta (by omega) hτ hθ1
  rw [BstLean.Part162.mass_eq_stand (by omega) D c hc hτ]
  -- the tail bound of order 40
  set A₁ := c.2.1.1.1
  set A₂ := c.2.1.1.2
  set b := D.bA c.1 c.2.1.1
  set τ := D.tau0 c
  have hX := tX20_le (by omega) hτ hθ0 hθ1 hS
  set K : ℝ := (π / 2) ^ 40 * (gmom 40 * (706 / 1000 * (2 / (n : ℝ)) / n) ^ 20) with hK
  have hT : ∀ g : ℝ, 0 < g → (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c.1.2 τ b ξ - ∫ ζ, sigD A₁ A₂ c.1.2 τ b ζ ∂stdGauss (Fin n)|} ≤
        K / g ^ 40 := by
    intro g hg
    have h := sigD_tail (q := 20) (by norm_num) (by omega) A₁ A₂ c.1.2 hτ hb hg
    refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [hK]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (gmom_nonneg _)) (by positivity)
  have hXi' : XiS A₁ A₂ c.1.2 τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n := hXi
  have hm := mass_bound_gen (by omega) A₁ A₂ c.1.2 hτ hb hXi' heb hxi hN22
    (e1 := 8553 / 10000) (e2 := 46 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by rw [div_le_iff₀ hn0]; nlinarith) hsd0 hsd (by
      have := s0P_cond hn
      unfold s0P at this ⊢
      linarith) hT
  have hset : {ξ : Fin n → ℝ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) < √(2 / (n : ℝ)) * sd} =
      {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1)
        (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    simp only [Set.mem_ofPred_eq]
    set R := normSq (res (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ))))
    have hR : 0 ≤ R := normSq_nonneg _
    have hsig : sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) = √(2 / (mA n : ℝ)) * √R := rfl
    rw [hsig, ← Real.sqrt_mul (by positivity)]
    have e : √(2 / (n : ℝ)) * sd = √(2 / (n : ℝ) * sd ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hsd0]
    rw [e]
    exact Real.sqrt_lt_sqrt_iff (by positivity)
  rw [hset]
  refine hm.trans (le_of_eq ?_)
  -- the value of `K / (√γ_A (s0P − sd))⁴⁰`
  have hd : 0 < s0P - sd := by linarith
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs40 : (√(2 / (n : ℝ)) * (s0P - sd)) ^ 40 = (2 / (n : ℝ)) ^ 20 * ((s0P - sd) ^ 2) ^ 20 := by
    rw [mul_pow, show (40 : ℕ) = 2 * 20 by norm_num, pow_mul, pow_mul, Real.sq_sqrt hγ.le]
  unfold s0P at hs40 hd ⊢
  rw [hs40, hK]
  unfold betaMP s0P
  field_simp

/-- **The mass below the floor on the good set**: `∫_a ν{σ < √γ_A·sd} ≤ betaMP n sd`. -/
theorem mass_of_goodCP (hn : 54000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodC n (paperDesign n fT wT hf hw) EA)
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0P) :
    ∫ a, (stdGauss (Fin (n - 1))).real
        {v | sgA (paperDesign n fT wT hf hw) c a v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaMP n sd := by
  set D := paperDesign n fT wT hf hw
  have hn16 : 16384 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hG := goodC16_of_goodA hn16 fT wT hf hw hc
  have hSc : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hc.2.2.1.1.2 hτ
  have hS20 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXqN n 20 := hc.2.1.2.1.1.2 hτ
  obtain ⟨hxi, -, -, hpos, hX4, hN22, -⟩ := centre16 hn16 hτ hθ0 hθ1 hG
  have heb := eb16_sharp hn16 hτ hθ0 hθ1 hG hSc
  have hb : D.bA c.1 c.2.1.1 =
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) :=
    paperDesign_agentCentre fT wT hf hw c
  rw [← hb] at hxi hpos heb
  have hXi := (BstLean.Part153.XiS_le_Xi4 (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 hτ).trans hX4
  exact mass_order40P hn D c hτ hθ0 hθ1 hpos hXi heb hxi hN22 hS20 hsd0 hsd

/-- **The free-event classifier theorem with the mass below the floor discharged (every
`n ≥ 23 000`).** IF `E_A` is a measurable event with
`Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomC`, and for every `c` in the good set `goodC`
(which contains `E_A ∩ agentEv D (SXqN n 20) ∩ EcA ∩ Eop2 ∩ Eframe D`) there are constants with
the two order-12 certificates, a floor `σ_l = √γ_A·sd` with `0 < sd < s0P = 0.5097`, `ε₀ < 1`, the
root sum with `C_A = CAn n`, `E = E0 n` and `β_low = betaMP n sd` `≤ 0.002159`, and
`BIAS_hyp … 0.004295`, THEN success `≥ 99/100`. The mass bound enters the root sum through its
PROOF `mass_of_goodCP` on the good set. -/
theorem classifier_paper_free23_mass40P (hn : 54000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodC n (paperDesign n fT wT hf hw) EA),
      ∃ (wl ws sd η CL CS : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hsd0 : 0 < sd) (hsd : sd < s0P)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12),
        0 < wl ∧ 0 < ws ∧ eps0 ws (√(2 / (n : ℝ)) * sd) < 1 ∧
        rootFL wl ws η (CAn n) (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          (E0_nonneg n) (betaMP_nonneg n sd) hL12 hS12 (hE8_of_good (by omega) fT wT hf hw hc)
          (mass_of_goodCP hn fT wT hf hw hc hsd0.le hsd)) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws (√(2 / (n : ℝ)) * sd) η h0 h1)
          (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  set S := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  have hEA' : MeasurableSet (EA ∩ agentEv D (SXqN n 20)) :=
    hEA.inter (measurableSet_agentEv D (measurableSet_SXqN n 20))
  have hA' : (retDist (paperCentres n)).real (S ∩ (EA ∩ agentEv D (SXqN n 20))ᶜ) ≤
      δA + 5 / 100000 := by
    have hsub : S ∩ (EA ∩ agentEv D (SXqN n 20))ᶜ ⊆ (S ∩ EAᶜ) ∪ (agentEv D (SXqN n 20))ᶜ := by
      intro c hc
      by_cases h1 : c ∈ EA
      · exact Or.inr fun h2 => hc.2 ⟨h1, h2⟩
      · exact Or.inl ⟨hc.1, h1⟩
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have c1 := SX20_ret_charge (by omega) fT wT hf hw
    linarith
  have hroom' : δA + 5 / 100000 ≤ roomB := by unfold roomC at hroom; linarith
  refine BstLean.Part164.classifier_paper_free23_cA8 (by omega) fT wT hf hw t hEA' hA' hroom'
    fun c hc => ?_
  obtain ⟨wl, ws, sd, η, CL, CS, h0, h1, hCL, hCS, hsd0, hsd, hL12, hS12, hwl, hws, hε, hroot,
    hbias⟩ := hM c hc
  have hσl : 0 < √(2 / (n : ℝ)) * sd := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  exact ⟨wl, ws, √(2 / (n : ℝ)) * sd, η, CL, CS, betaMP n sd, h0, h1, hCL, hCS, betaMP_nonneg n sd,
    hL12, hS12, mass_of_goodCP hn fT wT hf hw hc hsd0.le hsd, hwl, hws, hσl, hε, hroot, hbias⟩

end BstLean.Part174
