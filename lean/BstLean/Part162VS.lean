import BstLean.Part162LGs

/-!
# Part 162: the scale moment `V_S` from `τ_8` and the eighth moment of `σ`

Role: `delegations/statements/p162-spec.md`, items 3 and 4. Do not use `sorry`, `native_decide`
or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, proof of Proposition `t7:p07:FL`
(`‖z² − z̄(s)²‖_4 ≤ 2‖z‖_8‖z − z̄(s)‖_8 ≤ 2(1 + H_16)τ_8`).

* **`int_VS_le`**: `∫ Var(S|a)² ≤ (4τ²E²)²` from `∫∫|σ − σ̄|^8 ≤ τ⁸` and `∫∫σ^8 ≤ E⁸`.
* `latMomOfPsi12e`: the interface from the two order-12 certificates and `E`.
* **`classifier_agent_psi12e`**: the classifier theorem with the Agent replacement reduced to the
  two certificates, the eighth moment of `σ`, the mass below the floor, `|c_A|² ≤ C_A`, the root
  sum and `BIAS_hyp`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161

variable {n : ℕ}

/-- **The scale moment `V_S` from `τ_8` and the eighth moment of `σ`** (the paper's
`‖z² − z̄²‖_4 ≤ 2‖z‖_8‖z − z̄‖_8`): if `∫∫ |σ − σ̄|^8 ≤ τ⁸` and `∫∫ σ^8 ≤ E⁸`, then
`∫ Var(S | a)² ≤ (4τ²E²)²`. -/
theorem int_VS_le (hn : 1 ≤ n) (D : Design n) (c : Ret n) {τ E : ℝ} (hτ : 0 ≤ τ) (hE : 0 ≤ E)
    (h8 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ τ ^ 8)
    (hE8 : ∫ a, ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ E ^ 8) :
    ∫ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ (4 * τ ^ 2 * E ^ 2) ^ 2 := by
  set ν := stdGauss (Fin (n - 1))
  set μ := (muI n).prod ν
  have mS : ∀ a, Measurable (fun v => sgA D c a v) := fun a => measurable_sgA_left D c a
  set K := lipSig D c
  have hK0 : 0 ≤ K := lipSig_nonneg D c
  have bS : ∀ a v, |sgA D c a v| ≤ K := abs_sgA_le hn D c
  have hgb : ∀ a, |gbar D c a| ≤ K := fun a => by
    unfold gbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |sgA D c a v| ∂ν ≤ ∫ _v, K ∂ν :=
          integral_mono (intB (mS a).abs (M := K) fun v => by rw [abs_abs]; exact bS a v)
            (integrable_const _) (bS a)
      _ = K := by simp
  -- per index: `Var(S|a)² ≤ E_a[(σ − σ̄)⁴ (σ + σ̄)⁴]`
  have hpt : ∀ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν) ^ 2 ≤
      ∫ v, (sgA D c a v - gbar D c a) ^ 4 * (sgA D c a v + gbar D c a) ^ 4 ∂ν := fun a => by
    have b2 : ∀ v, |sA D c a v| ≤ K ^ 2 := fun v => by rw [sA_eq]; exact sq_bound_of_abs (bS a) v
    have h1 := var_le_sq_sub (μ := ν) (measurable_sA_left D c a) b2 (gbar D c a ^ 2)
    have e : ∀ v, (sA D c a v - gbar D c a ^ 2) ^ 2 =
        (sgA D c a v - gbar D c a) ^ 2 * (sgA D c a v + gbar D c a) ^ 2 := fun v => by
      rw [sA_eq]; ring
    simp_rw [e] at h1
    have h0 : 0 ≤ ∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν :=
      integral_nonneg fun v => sq_nonneg _
    have hb : ∀ v, |(sgA D c a v - gbar D c a) ^ 2 * (sgA D c a v + gbar D c a) ^ 2| ≤
        (2 * K) ^ 2 * (2 * K) ^ 2 := fun v => by
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
      · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (by linarith [bS a v, hgb a])) 2
      · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_add_le _ _).trans (by linarith [bS a v, hgb a])) 2
    have hJ := mean_sq_le (μ := ν) ((((mS a).sub_const _).pow_const 2).mul
      (((mS a).add_const _).pow_const 2)) hb
    calc (∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν) ^ 2
        ≤ (∫ v, (sgA D c a v - gbar D c a) ^ 2 * (sgA D c a v + gbar D c a) ^ 2 ∂ν) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ ≤ ∫ v, ((sgA D c a v - gbar D c a) ^ 2 * (sgA D c a v + gbar D c a) ^ 2) ^ 2 ∂ν := hJ
      _ = _ := by congr 1; funext v; ring
  -- integrate over the indices
  have mY : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => sgA D c p.1 p.2 - gbar D c p.1) :=
    (measurable_sgA D c).sub ((measurable_gbar D c).comp measurable_fst)
  have mZ : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => sgA D c p.1 p.2 + gbar D c p.1) :=
    (measurable_sgA D c).add ((measurable_gbar D c).comp measurable_fst)
  have bY : ∀ p : Ix n × (Fin (n - 1) → ℝ), |sgA D c p.1 p.2 - gbar D c p.1| ≤ 2 * K := fun p =>
    (abs_sub _ _).trans (by linarith [bS p.1 p.2, hgb p.1])
  have bZ : ∀ p : Ix n × (Fin (n - 1) → ℝ), |sgA D c p.1 p.2 + gbar D c p.1| ≤ 2 * K := fun p =>
    (abs_add_le _ _).trans (by linarith [bS p.1 p.2, hgb p.1])
  have ipow : ∀ {f : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable f → (∀ p, |f p| ≤ 2 * K) →
      ∀ j : ℕ, Integrable (fun p => f p ^ j) μ := fun {f} hf hb j =>
    intB (hf.pow_const j) (M := (2 * K) ^ j) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb p) j
  have iF : Integrable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
      (sgA D c p.1 p.2 - gbar D c p.1) ^ 4 * (sgA D c p.1 p.2 + gbar D c p.1) ^ 4) μ :=
    intB ((mY.pow_const 4).mul (mZ.pow_const 4)) (M := (2 * K) ^ 4 * (2 * K) ^ 4) fun p => by
      rw [abs_mul, abs_pow, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (bY p) 4)
        (pow_le_pow_left₀ (abs_nonneg _) (bZ p) 4) (by positivity) (by positivity)
  have hVint : Integrable (fun a => (∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν) ^ 2) (muI n) := by
    have mSbar : Measurable (fun a => ∫ w, sA D c a w ∂ν) :=
      ((measurable_sA D c).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have mV : Measurable (fun a => ∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν) :=
      ((((measurable_sA D c).sub (mSbar.comp measurable_fst)).pow_const 2).stronglyMeasurable.integral_prod_right'
        (ν := ν)).measurable
    refine intB (mV.pow_const 2) (M := ((2 * K ^ 2) ^ 2) ^ 2) fun a => ?_
    have b2 : ∀ v, |sA D c a v| ≤ K ^ 2 := fun v => by rw [sA_eq]; exact sq_bound_of_abs (bS a) v
    have hSb : |∫ w, sA D c a w ∂ν| ≤ K ^ 2 := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ v, |sA D c a v| ∂ν ≤ ∫ _v, K ^ 2 ∂ν :=
            integral_mono (intB (measurable_sA_left D c a).abs (M := K ^ 2) fun v => by
              rw [abs_abs]; exact b2 v) (integrable_const _) b2
        _ = _ := by simp
    have h0 : 0 ≤ ∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν :=
      integral_nonneg fun v => sq_nonneg _
    have h1 : ∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν ≤ (2 * K ^ 2) ^ 2 := by
      calc _ ≤ ∫ _v, (2 * K ^ 2) ^ 2 ∂ν := integral_mono
            (intB (((measurable_sA_left D c a).sub_const _).pow_const 2) (M := (2 * K ^ 2) ^ 2)
              fun v => by
                rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
                  (by linarith [b2 v])) 2) (integrable_const _) fun v => by
              show _ ≤ (2 * K ^ 2) ^ 2
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [b2 v])) 2
        _ = _ := by simp
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 h1 2
  have iG : Integrable (fun a => ∫ v, (sgA D c a v - gbar D c a) ^ 4 * (sgA D c a v + gbar D c a) ^ 4 ∂ν)
      (muI n) := iF.integral_prod_left
  have step1 : ∫ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν) ^ 2 ∂muI n ≤
      ∫ p, (sgA D c p.1 p.2 - gbar D c p.1) ^ 4 * (sgA D c p.1 p.2 + gbar D c p.1) ^ 4 ∂μ := by
    rw [integral_prod _ iF]
    exact integral_mono hVint iG hpt
  -- Cauchy–Schwarz on the product
  have h8' : ∫ p, ((sgA D c p.1 p.2 - gbar D c p.1) ^ 4) ^ 2 ∂μ ≤ (τ ^ 4) ^ 2 := by
    have e : ∀ p : Ix n × (Fin (n - 1) → ℝ), ((sgA D c p.1 p.2 - gbar D c p.1) ^ 4) ^ 2 =
        |sgA D c p.1 p.2 - gbar D c p.1| ^ 8 := fun p => by
      rw [← pow_mul, show 4 * 2 = 2 * 4 from rfl, ← pow_abs_two_mul]
    simp_rw [e]
    have iY8 : Integrable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
        |sgA D c p.1 p.2 - gbar D c p.1| ^ 8) μ :=
      intB (mY.abs.pow_const 8) (M := (2 * K) ^ 8) fun p => by
        rw [abs_pow, abs_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bY p) 8
    rw [← integral_prod _ iY8] at h8
    rw [← pow_mul]; exact h8
  have hσ0 : ∀ p : Ix n × (Fin (n - 1) → ℝ), 0 ≤ sgA D c p.1 p.2 := fun p => sgA_nonneg D c p.1 p.2
  have hgb0 : ∀ a, 0 ≤ gbar D c a := fun a => integral_nonneg fun v => sgA_nonneg D c a v
  have iS8 : Integrable (fun p : Ix n × (Fin (n - 1) → ℝ) => sgA D c p.1 p.2 ^ 8) μ :=
    intB ((measurable_sgA D c).pow_const 8) (M := K ^ 8) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (bS p.1 p.2) 8
  have iB8 : Integrable (fun p : Ix n × (Fin (n - 1) → ℝ) => gbar D c p.1 ^ 8) μ :=
    intB (((measurable_gbar D c).comp measurable_fst).pow_const 8) (M := K ^ 8) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgb p.1) 8
  have hS8 : ∫ p, sgA D c p.1 p.2 ^ 8 ∂μ ≤ E ^ 8 := by rw [integral_prod _ iS8]; exact hE8
  have hB8 : ∫ p, gbar D c p.1 ^ 8 ∂μ ≤ E ^ 8 := by
    rw [integral_prod _ iB8]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have iBa : Integrable (fun a => gbar D c a ^ 8) (muI n) :=
      intB ((measurable_gbar D c).pow_const 8) (M := K ^ 8) fun a => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgb a) 8
    refine le_trans (integral_mono iBa (iS8.integral_prod_left) fun a => ?_) hE8
    show gbar D c a ^ 8 ≤ ∫ v, sgA D c a v ^ 8 ∂ν
    have i8 : Integrable (fun v => sgA D c a v ^ 8) ν :=
      intB ((mS a).pow_const 8) (M := K ^ 8) fun v => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (bS a v) 8
    have hJ := (convexOn_pow 8).map_integral_le (μ := ν) (f := fun v => sgA D c a v)
      (continuous_pow 8).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun v => Set.mem_Ici.mpr (sgA_nonneg D c a v))
      (intB (mS a) (bS a)) i8
    exact hJ
  have hZ8 : ∫ p, ((sgA D c p.1 p.2 + gbar D c p.1) ^ 4) ^ 2 ∂μ ≤ ((2 * E) ^ 4) ^ 2 := by
    have hpt2 : ∀ p : Ix n × (Fin (n - 1) → ℝ), ((sgA D c p.1 p.2 + gbar D c p.1) ^ 4) ^ 2 ≤
        2 ^ 7 * (sgA D c p.1 p.2 ^ 8 + gbar D c p.1 ^ 8) := fun p => by
      have h := pow2_le 8 (hσ0 p) (hgb0 p.1) (one_pos) (one_pos)
      rw [← pow_mul]
      norm_num at h ⊢
      linarith
    calc ∫ p, ((sgA D c p.1 p.2 + gbar D c p.1) ^ 4) ^ 2 ∂μ
        ≤ ∫ p, 2 ^ 7 * (sgA D c p.1 p.2 ^ 8 + gbar D c p.1 ^ 8) ∂μ :=
          integral_mono (by simpa only [← pow_mul] using ipow mZ bZ 8)
            ((iS8.add iB8).const_mul _) hpt2
      _ = 2 ^ 7 * (∫ p, sgA D c p.1 p.2 ^ 8 ∂μ + ∫ p, gbar D c p.1 ^ 8 ∂μ) := by
          rw [integral_const_mul, integral_add iS8 iB8]
      _ ≤ 2 ^ 7 * (E ^ 8 + E ^ 8) := by gcongr
      _ = ((2 * E) ^ 4) ^ 2 := by ring
  have hcs := cs_root μ (f := fun p : Ix n × (Fin (n - 1) → ℝ) => (sgA D c p.1 p.2 - gbar D c p.1) ^ 4)
    (g := fun p => (sgA D c p.1 p.2 + gbar D c p.1) ^ 4) (mY.pow_const 4) (mZ.pow_const 4)
    (M := (2 * K) ^ 4) (fun p => by positivity) (fun p => pow_nonneg (by linarith [hσ0 p, hgb0 p.1]) 4)
    (fun p => by
      show (sgA D c p.1 p.2 - gbar D c p.1) ^ 4 ≤ (2 * K) ^ 4
      rw [show (4 : ℕ) = 2 * 2 from rfl, ← pow_abs_two_mul]
      exact pow_le_pow_left₀ (abs_nonneg _) (bY p) _)
    (fun p => pow_le_pow_left₀ (by linarith [hσ0 p, hgb0 p.1]) ((le_abs_self _).trans (bZ p)) 4)
    (by positivity) (by positivity) h8' hZ8
  calc _ ≤ ∫ p, (sgA D c p.1 p.2 - gbar D c p.1) ^ 4 * (sgA D c p.1 p.2 + gbar D c p.1) ^ 4 ∂μ := step1
    _ ≤ τ ^ 4 * (2 * E) ^ 4 := hcs
    _ = (4 * τ ^ 2 * E ^ 2) ^ 2 := by ring

/-- **The latitude interface from the order-12 certificates and the eighth moment of `σ`**
(`V_S = 4τ_8²E²`, the paper's `{2‖z‖_8 τ_8}²`). -/
noncomputable def latMomOfPsi12e (hn : 26 ≤ n) (D : Design n) (c : Ret n) {σl CL CS E βlow : ℝ}
    (hCL : 0 < CL) (hCS : 0 < CS) (hE : 0 ≤ E) (hβ : 0 ≤ βlow)
    (hL12 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
    (hS12 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
    (hE8 : ∫ a, ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ E ^ 8)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} ∂muI n ≤ βlow) :
    LatMom D c σl (2 * 12) :=
  have hS4 := psi_low_of_12 (by omega) D c (lipSig_nonneg D c) (sigX_euLip D c)
    (fun t x ht => sigX_hom D c t x ht) hCS.le hS12 (j := 4) (m := 3) (by norm_num) (by norm_num)
  have hs8 := int_mom_psi_s (by omega) D c (lipSig_nonneg D c) (sigX_euLip D c)
    (fun t x ht => sigX_hom D c t x ht) (q := 4) (by norm_num) (by omega) hCS.le hS4
  have hτ : 0 ≤ kLSs n 4 * √(CS / n) := (mul_pos (kLSs_pos' hn (by norm_num) (by norm_num))
    (pos_div_n hCS hn)).le
  have hVS := int_VS_le (by omega) D c hτ hE hs8 hE8
  latMomOfPsi12s hn D c hCL hCS (by positivity) hβ hL12 hS12 hVS hmass

open BstLean.Part130 BstLean.Part156 BstLean.Part159 in
/-- **The classifier theorem with an Agent event `E₁` (every `n ≥ 16 384`) and the Agent
replacement reduced to: the two order-12 realized certificates, the eighth moment of `σ`, the mass
below the floor, the norm of `c_A`, the root sum and the bias** (paper's LS constants). -/
theorem classifier_agent_psi12e (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextraL)
    (hEθ : E₁ ⊆ Ethm (paperCentres n) ∩ Ethp (paperCentres n))
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hM : ∀ c ∈ goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA CL CS E βlow : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hE : 0 ≤ E) (hβ : 0 ≤ βlow)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
        (hE8 : ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
          E ^ 8)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧
        rootFL wl ws η CA (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS hE hβ
          hL12 hS12 hE8 hmass) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_agent_mom hn fT wT hf hw t hE₁ hextra hEθ hFA fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, E, βlow, h0, h1, hCL, hCS, hE, hβ, hL12, hS12, hE8, hmass,
    hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨wl, ws, σl, η, CA, 2 * 12, h0, h1, latMomOfPsi12e (by omega) _ c hCL hCS hE hβ hL12
    hS12 hE8 hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩

end BstLean.Part162

open BstLean.Part162 in
#print axioms int_VS_le
open BstLean.Part162 in
#print axioms classifier_agent_psi12e
