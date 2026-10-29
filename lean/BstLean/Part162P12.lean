import BstLean.Part162FinE

/-!
# Part 162: the classifier theorem with the order-12 certificates only

Role: `delegations/statements/p162-spec.md`, items 3 and 4. Do not use `sorry`, `native_decide`
or `axiom`.

* `psi_low_of_12`: Lyapunov, `∫∫ Ψ^{12} ≤ (C/n)^{12} ⇒ ∫∫ Ψ^j ≤ (C/n)^j` for `j ∣ 12`.
* `latMomOfPsi12`: the interface `LatMom` (removal order 24) from the two order-12 certificates.
* **`classifier_agent_psi12`**: the classifier theorem with an Agent event `E₁` and the Agent
  replacement reduced to `‖Ψ_λ‖_{12} ≤ C_λ/n`, `‖Ψ_σ‖_{12} ≤ C_σ/n` (the paper's `E_lat`
  conclusion), `V_S`, the mass below the floor, `|c_A|² ≤ C_A`, the root sum and `BIAS_hyp`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161
open BstLean.Part148 (EuLip)

variable {n : ℕ}

/-- **Lyapunov for the realized certificate**: `∫∫ Ψ^{12} ≤ (C/n)^{12}` gives `∫∫ Ψ^j ≤ (C/n)^j`
for `j ∣ 12` (the paper: "use `‖Ψ_φ‖_p ≤ ‖Ψ_φ‖_{12}`"). -/
lemma psi_low_of_12 (hn : 2 ≤ n) (D : Design n) (c : Ret n) {Φ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) {C : ℝ} (hC : 0 ≤ C)
    (h12 : ∫ a, ∫ v, psiA Φ D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (C / n) ^ 12)
    {j m : ℕ} (hj : 1 ≤ j) (hjm : j * m = 12) :
    ∫ a, ∫ v, psiA Φ D c a v ^ j ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (C / n) ^ j := by
  set ν := stdGauss (Fin (n - 1))
  set μ := (muI n).prod ν
  have hc := hL.continuous hL0
  have mP := measurable_psiA hc D c
  have bP := psiA_bounds hn D c hL0 hL hhom
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hjm
    · exact h
  have ib : ∀ k : ℕ, Integrable (fun p : Ix n × (Fin (n - 1) → ℝ) => psiA Φ D c p.1 p.2 ^ k) μ :=
    fun k => Integrable.of_bound (mP.pow_const k).aestronglyMeasurable ((2 * L ^ 2) ^ k)
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (bP p.1 p.2).1 _)]
        exact pow_le_pow_left₀ (bP p.1 p.2).1 (bP p.1 p.2).2 k)
  have e : ∀ k : ℕ, ∫ a, ∫ v, psiA Φ D c a v ^ k ∂ν ∂muI n =
      ∫ p, psiA Φ D c p.1 p.2 ^ k ∂μ := fun k => (integral_prod _ (ib k)).symm
  rw [e] at h12 ⊢
  have hJ := (convexOn_pow m).map_integral_le (μ := μ)
    (f := fun p : Ix n × (Fin (n - 1) → ℝ) => psiA Φ D c p.1 p.2 ^ j)
    (continuous_pow m).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun p => Set.mem_Ici.mpr (pow_nonneg (bP p.1 p.2).1 _)) (ib j)
    (by simpa only [Function.comp_def, ← pow_mul, hjm] using ib 12)
  simp only [Function.comp_def, ← pow_mul, hjm] at hJ
  have h0 : 0 ≤ ∫ p, psiA Φ D c p.1 p.2 ^ j ∂μ :=
    integral_nonneg fun p => pow_nonneg (bP p.1 p.2).1 _
  have h1 : (∫ p, psiA Φ D c p.1 p.2 ^ j ∂μ) ^ m ≤ ((C / n) ^ j) ^ m := by
    rw [← pow_mul, hjm]; exact hJ.trans h12
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) h1

/-- **The latitude-moment interface from the order-12 certificate only** (the paper's
`‖Ψ_φ‖_{L^{12}(x)} ≤ C_lat/n` for `φ = λ, σ`), with removal order `q = 24`. -/
noncomputable def latMomOfPsi12 (hn : 61 ≤ n) (D : Design n) (c : Ret n) {σl CL CS VS βlow : ℝ}
    (hCL : 0 < CL) (hCS : 0 < CS) (hVS0 : 0 ≤ VS) (hβ : 0 ≤ βlow)
    (hL12 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
    (hS12 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
    (hVS : ∫ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} ∂muI n ≤ βlow) :
    LatMom D c σl (2 * 12) :=
  have hn2 : 2 ≤ n := by omega
  have lowL : ∀ {j m : ℕ}, 1 ≤ j → j * m = 12 →
      ∫ a, ∫ v, psiA (lamX D c) D c a v ^ j ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ j :=
    fun hj hjm => psi_low_of_12 hn2 D c (lipLam_nonneg D c) (lamX_euLip D c)
      (fun t x ht => lamX_hom D c t x ht) hCL.le hL12 hj hjm
  have lowS : ∀ {j m : ℕ}, 1 ≤ j → j * m = 12 →
      ∫ a, ∫ v, psiA (sigX D c) D c a v ^ j ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ j :=
    fun hj hjm => psi_low_of_12 hn2 D c (lipSig_nonneg D c) (sigX_euLip D c)
      (fun t x ht => sigX_hom D c t x ht) hCS.le hS12 hj hjm
  latMomOfPsi hn D c (r := 12) (by norm_num) le_rfl hCL hCS hVS0 hβ
    (lowL (m := 6) (by norm_num) (by norm_num)) (lowL (m := 3) (by norm_num) (by norm_num))
    (lowL (m := 2) (by norm_num) (by norm_num)) hL12
    (lowS (m := 6) (by norm_num) (by norm_num)) (lowS (m := 3) (by norm_num) (by norm_num))
    (lowS (m := 2) (by norm_num) (by norm_num)) hS12 hVS hmass

open BstLean.Part130 BstLean.Part156 BstLean.Part159 in
/-- **The classifier theorem with an Agent event `E₁` (every `n ≥ 16 384`) and the Agent
replacement reduced to the order-12 realized certificates** `∫∫ Ψ_λ^{12} ≤ (C_λ/n)^{12}`,
`∫∫ Ψ_σ^{12} ≤ (C_σ/n)^{12}` (Prop. `t7:p07:LG`), `V_S`, the mass below the floor, the norm
of `c_A`, the root sum and the bias. -/
theorem classifier_agent_psi12 (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextraL)
    (hEθ : E₁ ⊆ Ethm (paperCentres n) ∩ Ethp (paperCentres n))
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hM : ∀ c ∈ goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA CL CS VS βlow : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hVS0 : 0 ≤ VS) (hβ : 0 ≤ βlow)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
        (hVS : ∫ a, (∫ v, (sA (paperDesign n fT wT hf hw) c a v -
            ∫ w, sA (paperDesign n fT wT hf hw) c a w ∂stdGauss (Fin (n - 1))) ^ 2
          ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧
        rootFL wl ws η CA (latMomOfPsi12 (by omega) (paperDesign n fT wT hf hw) c hCL hCS hVS0 hβ
          hL12 hS12 hVS hmass) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_agent_mom hn fT wT hf hw t hE₁ hextra hEθ hFA fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, VS, βlow, h0, h1, hCL, hCS, hVS0, hβ, hL12, hS12, hVS, hmass,
    hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨wl, ws, σl, η, CA, 2 * 12, h0, h1, latMomOfPsi12 (by omega) _ c hCL hCS hVS0 hβ hL12 hS12
    hVS hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩

end BstLean.Part162

open BstLean.Part162 in
#print axioms classifier_agent_psi12
