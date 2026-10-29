import BstLean.Part169Int

/-!
# Part 169 (file `Op`): the operator events, the bulk, and the end theorem with the exact-rule
errors

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`: the operator events `E_{1op}`, `E_{2op}`; the bulk
`q_{bulk,−} = 1 − s₊²`; formula `t7:p08:grid` with `Δ_{grid,+}`.

* `opB_of_opN`: `opN M ≤ O` gives `OpB M O`.
* **`opB_goodD`**: on `goodD`, `OpB A₁ O₁` and `OpB A₂ O₂` with Lean's events `Eop`
  (`O₁ = √(2/n)(n + 2√n)`) and `Eop2` (`O₂ = √(2/m_A)(2n + 5)`).
* `qB n = 1 − (√0.54 + 6√(0.55/n))²` and **`bulk_of_window`**: in the World window
  (`τ₀ > 0`, `0.46 ≤ θ ≤ 0.55`) and `n ≥ 44`: `L < H`, every `s ∈ [L, H]` has `s² ≤ 1 − qB n`,
  and `Δ ≤ Δ₊ = 12√(0.55/n)/(512n)`. `qB_pos`: `qB n ≥ 0.43` for `n ≥ 80 000`.
* `MomX`: the moment inputs with the exact-rule errors in place of `a_f`, `a_ω`, and the upper
  `ς` bound at the nodes.
* **`momB_of_momX`**: on `goodD`, `MomX` gives `MomB` with
  `a_f = A_f + g_f + r_f`, `a_ω = A_ω + g_ω + r_ω` (explicit `g`, `r`).
* **`classifier_paper_momX80k`**: the end theorem with `MomX`.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI)
open BstLean.Part166 (goodD)
open BstLean.Part150 (c1F c2F rhoC)

variable {n : ℕ}

lemma opB_of_opN {k m : ℕ} (M : Matrix (Fin m) (Fin k) ℝ) {O : ℝ}
    (hO : BstLean.Part152.opN M ≤ O) : OpB M O := by
  intro z
  have h := BstLean.Part152.mulVec_le_opN M z
  have h0 := BstLean.Part152.opN_nonneg M
  have hs : √(normSq (M.mulVec z)) ≤ O * √(normSq z) :=
    h.trans (mul_le_mul_of_nonneg_right hO (Real.sqrt_nonneg _))
  have h1 : normSq (M.mulVec z) = √(normSq (M.mulVec z)) ^ 2 :=
    (Real.sq_sqrt (normSq_nonneg _)).symm
  have h2 : normSq z = √(normSq z) ^ 2 := (Real.sq_sqrt (normSq_nonneg _)).symm
  rw [h1, h2, ← mul_pow]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2

/-- `O₁ = √(2/n)(n + 2√n)` (Lean's event `Eop` for `A₁`). -/
noncomputable def O1n (n : ℕ) : ℝ := √(2 / (n : ℝ)) * ((n : ℝ) + 2 * √(n : ℝ))

/-- `O₂ = √(2/m_A)(2n + 5)` (Lean's event `Eop2` for `A₂`). -/
noncomputable def O2n (n : ℕ) : ℝ := √(2 / (mA n : ℝ)) * (2 * (n : ℝ) + 5)

/-- **The operator bounds on the good set.** -/
theorem opB_goodD (hn : 16384 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) : OpB (A1 c) (O1n n) ∧ OpB (A2 c) (O2n n) := by
  have h1 := BstLean.Part164.eop_of_goodC16 (BstLean.Part164.goodC16_of_goodA hn passF passW
    measurable_passF measurable_passW hc)
  have h2 : c ∈ BstLean.Part164.Eop2 n := hc.2.1.2.2
  exact ⟨opB_of_opN _ h1, opB_of_opN _ h2⟩

/-- `qB n = 1 − (√0.54 + 6√(0.55/n))²`. -/
noncomputable def qB (n : ℕ) : ℝ := 1 - (√(54 / 100) + 6 * √(55 / 100 / (n : ℝ))) ^ 2

/-- `Δ₊ = 12√(0.55/n)/(512 n)`. -/
noncomputable def DeltaP (n : ℕ) : ℝ := 12 * √(55 / 100 / (n : ℝ)) / (512 * n)

lemma qB_pos (hn : 80000 ≤ n) : 43 / 100 ≤ qB n := by
  unfold qB
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 3 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have h4 : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 753 / 1000 := by linarith
  nlinarith

/-- **The bulk in the World window.** -/
theorem bulk_of_window (hn : 44 ≤ n) (c : Ret n) (hτ : 0 < tauR c)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c))
    (hθ1 : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100) :
    nodeL c < nodeH c ∧ (∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - qB n) ∧
      nodeD c ≤ DeltaP n := by
  have hnR : (44 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set ρ := rhoR c with hρ
  have hρ2 : ρ ^ 2 = normSq c.1.2 + n * tauR c ^ 2 := by
    rw [hρ]; unfold rhoR rhoC
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hρ0 : 0 < ρ := by
    rw [hρ]; unfold rhoR rhoC
    exact Real.sqrt_pos.mpr (by have := normSq_nonneg c.1.2; positivity)
  set a := √(normSq c.1.2) / ρ with ha
  set b := tauR c / ρ with hb
  have hb0 : 0 < b := div_pos hτ hρ0
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hθ : BstLean.Part150.thetaC c.1.2 (tauR c) = n * b ^ 2 := by
    unfold BstLean.Part150.thetaC; rw [← rhoR, ← hρ, hb, div_pow]; ring
  have hab : a ^ 2 + n * b ^ 2 = 1 := by
    rw [ha, hb, div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp; rw [hρ2]
  rw [hθ] at hθ0 hθ1
  have hL : nodeL c = a - 6 * b := by unfold nodeL; rw [← hρ]; ring
  have hH : nodeH c = a + 6 * b := by unfold nodeH; rw [← hρ]; ring
  have ha2 : a ^ 2 ≤ 54 / 100 := by linarith
  have hb2 : b ^ 2 ≤ 55 / 100 / n := by rw [le_div_iff₀ hn0]; linarith
  have ha_le : a ≤ √(54 / 100) := Real.le_sqrt_of_sq_le ha2
  have hb_le : b ≤ √(55 / 100 / (n : ℝ)) := Real.le_sqrt_of_sq_le hb2
  have h6 : 6 * b ≤ a := by
    have : (6 * b) ^ 2 ≤ a ^ 2 := by
      have : 36 * (55 / 100 / (n : ℝ)) ≤ 45 / 100 := by
        rw [mul_div_assoc', div_le_iff₀ hn0]; nlinarith
      nlinarith
    nlinarith
  refine ⟨by rw [hL, hH]; linarith, fun s hs1 hs2 => ?_, ?_⟩
  · rw [hL] at hs1; rw [hH] at hs2
    have hs0 : 0 ≤ s := by linarith
    unfold qB
    have : s ≤ √(54 / 100) + 6 * √(55 / 100 / (n : ℝ)) := by linarith
    nlinarith
  · unfold nodeD DeltaP Js
    rw [hL, hH]
    have e : a + 6 * b - (a - 6 * b) = 12 * b := by ring
    rw [e]; push_cast
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-! ## The end theorem with the exact-rule errors -/

lemma measurable_exF (c : Ret n) : Measurable (exF c) :=
  (measurable_from_nat (f := fun g : ℕ => (n : ℝ) * (fbarS c (nodeS c g) -
    fGauss c (nodeS c g)))).comp (measurable_gIdx_lat c)

lemma measurable_exW (c : Ret n) : Measurable (exW c) :=
  (measurable_from_nat (f := fun g : ℕ => (n : ℝ) * (wbarS c (nodeS c g) -
    wGauss c (nodeS c g)))).comp (measurable_gIdx_lat c)

lemma bdd_exF (hn : 1 ≤ n) (c : Ret n) : ∃ M, ∀ a, |exF c a| ≤ M :=
  ⟨∑ g ∈ Finset.range (Js n), |(n : ℝ) * (fbarS c (nodeS c g) - fGauss c (nodeS c g))|,
    fun _a => Finset.single_le_sum
      (f := fun g => |(n : ℝ) * (fbarS c (nodeS c g) - fGauss c (nodeS c g))|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (gIdx_lt c hn _))⟩

lemma bdd_exW (hn : 1 ≤ n) (c : Ret n) : ∃ M, ∀ a, |exW c a| ≤ M :=
  ⟨∑ g ∈ Finset.range (Js n), |(n : ℝ) * (wbarS c (nodeS c g) - wGauss c (nodeS c g))|,
    fun _a => Finset.single_le_sum
      (f := fun g => |(n : ℝ) * (wbarS c (nodeS c g) - wGauss c (nodeS c g))|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (gIdx_lt c hn _))⟩

/-- `a_f = A_f + g_f + r_f` with Lean's operator constants, `Δ₊` and `qB`. -/
noncomputable def aFn (n : ℕ) (Af σ0 : ℝ) : ℝ :=
  Af + ((n : ℝ) * (O2n n * O1n n * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) +
    n * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * σ0 / Jz n)))

/-- `a_ω = A_ω + g_ω + r_ω`. -/
noncomputable def aWn (n : ℕ) (Aw σ0 : ℝ) : ℝ :=
  Aw + ((n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) +
    n * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * σ0 ^ 2 / Jz n)))

/-- **The moment inputs with the exact-rule errors**: the upper `ς` bound at the nodes, the
`L⁸` bounds `A_f`, `A_ω` of the exact-rule errors, and the inputs `v_max`, `H_f`, `C_v`. -/
structure MomX (c : Ret n) (vmax Af Aw Hf Cv σ0 : ℝ) : Prop where
  hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax
  hvs : ∀ a ∈ KR c, vsig2 c (sgR c a) ≤ σ0 ^ 2
  hXF : ∫ a in KR c, exF c a ^ 8 ∂muI n ≤ Af ^ 8
  hXW : ∫ a in KR c, exW c a ^ 8 ∂muI n ≤ Aw ^ 8
  hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2

lemma O1n_pos (hn : 1 ≤ n) : 0 < O1n n := by
  have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold O1n; positivity

lemma O2n_pos (hn : 1 ≤ n) : 0 < O2n n := by
  have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have : (0 : ℝ) < (mA n : ℝ) := by unfold mA; push_cast; positivity
  unfold O2n; positivity

/-- **`MomB` from `MomX` on the good set.** -/
theorem momB_of_momX (hn : 80000 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) {ε vmax Af Aw Hf Cv σ0 : ℝ} (hσ : 0 < σ0)
    (hAf : 0 < Af) (hAw : 0 < Aw) (h : MomX c vmax Af Aw Hf Cv σ0) :
    MomB c ε vmax (aWn n Aw σ0) (aFn n Af σ0) Hf Cv := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := BstLean.Part164.window_goodA (by omega) passF passW measurable_passF
    measurable_passW _ c hc
  obtain ⟨hLH, hbulk, hD⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  obtain ⟨h1, h2⟩ := opB_goodD (by omega) hc
  have hq : 0 < qB n := lt_of_lt_of_le (by norm_num) (qB_pos hn)
  have hO1 := O1n_pos (n := n) hn1
  have hO2 := O2n_pos (n := n) hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJ : (0 : ℝ) < Jz n := by exact_mod_cast (Jz_pos hn2)
  have hpos1 : 0 < √(n : ℝ) * √(qB n) := mul_pos (Real.sqrt_pos.mpr hnR) (Real.sqrt_pos.mpr hq)
  have hpos2 : 0 < (n : ℝ) * √(qB n) := mul_pos hnR (Real.sqrt_pos.mpr hq)
  have hD0 : 0 ≤ nodeD c := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hc1 : 0 ≤ c1F (rexp (1 / 2) / 12) (Jz n) := c1F_nonneg _
  have hc2 : 0 ≤ c2F (rexp (1 / 2) / 12) (Jz n) := c2F_nonneg _
  obtain ⟨MF, bF⟩ := bdd_exF hn1 c
  obtain ⟨MW, bW⟩ := bdd_exW hn1 c
  have iXF := intOn_of_bdd ((measurable_exF c).pow_const 8) (bdd_pow bF 8) (KR c)
  have iXW := intOn_of_bdd ((measurable_exW c).pow_const 8) (bdd_pow bW 8) (KR c)
  obtain ⟨-, hF⟩ := hF8_of_exact hn2 c h1 h2 hO1 hO2 hq hσ hLH hbulk h.hvs hAf iXF h.hXF
  obtain ⟨-, hW⟩ := hW8_of_exact hn2 c h1 h2 hO1 hO2 hq hσ hLH hbulk h.hvs hAw iXW h.hXW
  refine ⟨h.hVm, hW.trans ?_, hF.trans ?_, h.hf4, h.hf24, h.hV⟩
  · unfold aWn
    refine pow_le_pow_left₀ (by positivity) ?_ 8
    have : (n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (nodeD c / 2) / (n * √(qB n))) ≤
        (n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) := by
      refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hpos2.le) hnR.le
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · unfold aFn
    refine pow_le_pow_left₀ (by positivity) ?_ 8
    have : (n : ℝ) * (O2n n * O1n n * (nodeD c / 2) / (√(n : ℝ) * √(qB n))) ≤
        (n : ℝ) * (O2n n * O1n n * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) := by
      refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hpos1.le) hnR.le
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-- **The classifier theorem with the exact-rule moment inputs `MomX`** (every `n ≥ 80 000`).
Remaining: `MomX` on `goodD n D (E_A ∩ E_bias)` (the upper `ς` bound at the nodes, the `L⁸`
bounds `A_f`, `A_ω` of the exact-rule errors, `v_max`, `H_f`, `C_v`), the numerical condition
`P_B ≤ 0.004295²` at `a_f = aFn n A_f σ₀`, `a_ω = aWn n A_ω σ₀`, and the charges. -/
theorem classifier_paper_momX80k (hn : 80000 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ BstLean.Part167.roomE)
    {ε vmax Af Aw Hf Cv σ0 : ℝ} (hε1 : ε < 1) (hT : 0 < ε - vmax / dStar) (hσ : 0 < σ0)
    (hAf : 0 < Af) (hAw : 0 < Aw) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax (aWn n Aw σ0) (aFn n Af σ0) Hf Cv ≤
      (4295 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomX c vmax Af Aw Hf Cv σ0) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < qB n := lt_of_lt_of_le (by norm_num) (qB_pos hn)
  have hO1 := O1n_pos (n := n) hn1
  have hO2 := O2n_pos (n := n) hn1
  have hJ : (0 : ℝ) < Jz n := by exact_mod_cast (Jz_pos (by omega : 2 ≤ n))
  have hDP : 0 ≤ DeltaP n := by unfold DeltaP; positivity
  have hc1 := c1F_nonneg (Jz n)
  have hc2 := c2F_nonneg (Jz n)
  have haf : 0 < aFn n Af σ0 := by unfold aFn; positivity
  have haw : 0 < aWn n Aw σ0 := by unfold aWn; positivity
  exact classifier_paper_momB80k hn t hEA hEb hA hb hroom hε1 hT haw haf hHf hCv hnum
    fun c hc => momB_of_momX hn hc hσ hAf hAw (hM c hc)

end BstLean.Part169
