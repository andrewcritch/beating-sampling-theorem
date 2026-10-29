import BstLean.Part162LSs
import BstLean.Part162P12

/-!
# Part 162: the latitude interface with the paper's LS constants; the main end theorem

Role: `delegations/statements/p162-spec.md`, items 1, 3, 4. Do not use `sorry`, `native_decide`
or `axiom`.

* `kLSs n q = c_q (n − 1 − 2q)^{−1/2}`; `idx_mom_psi_s`, `int_mom_psi_s`: Lemma LS (sharp)
  integrated with the realized `Ψ`: `τ_{2q} = c_q √(C/(n(n − 1 − 2q)))`, the paper's `τ_{2p}`.
* `latMomOfPsi12s`: the interface `LatMom` from the two order-12 certificates.
* **`classifier_agent_psi12s`**: the classifier theorem with an Agent event `E₁` and the Agent
  replacement reduced to `‖Ψ_λ‖_{12} ≤ C_λ/n`, `‖Ψ_σ‖_{12} ≤ C_σ/n`, `V_S`, the mass below the
  floor, `|c_A|² ≤ C_A`, the root sum and `BIAS_hyp`; the interface has the paper's constants.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161
open BstLean.Part151 (gradSq)
open BstLean.Part53 (unitF53)
open BstLean.Part148 (EuLip)

variable {n : ℕ} {Φ : (Fin n → ℝ) → ℝ} {L : ℝ}

/-- `K'_q = c_q (n − 1 − 2q)^{−1/2}` (the paper's factor of Lemma LS). -/
noncomputable def kLSs (n q : ℕ) : ℝ := cLS q * (((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)

lemma kLSs_pos {q : ℕ} (hq : 1 ≤ q) (hqn : 2 * q < n - 1) : 0 < kLSs n q := by
  unfold kLSs
  have h : (0 : ℝ) < (n : ℝ) - 1 - 2 * q := by
    have : (2 * q : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hqn
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  exact mul_pos (cLS_pos hq) (Real.rpow_pos_of_pos (inv_pos.mpr h) _)

/-- **Lemma LS (order `2q`, sharp) with the realized `Ψ`**. -/
lemma idx_mom_psi_s (hn : 2 ≤ n) (D : Design n) (c : Ret n) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) {q : ℕ} (hq : 1 ≤ q)
    (hqn : 2 * q < n - 1) (a : Ix n) :
    ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
          ∂stdGauss (Fin (n - 1)) ≤
      kLSs n q ^ (2 * q) * ∫ v, psiA Φ D c a v ^ q ∂stdGauss (Fin (n - 1)) := by
  have hs := latC_sq_le D c a
  have h := ls_lat_mom_sharp hn c hs hL0 hL hhom hq hqn
  set X := BstLean.Part161.momN (stdGauss (Fin (n - 1))) (2 * q)
    (fun v => Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1)))
  set Y := BstLean.Part161.momN (stdGauss (Fin (n - 1))) (2 * q) (fun v =>
    √(gradSq (fun w => Φ (xLatH c (latC D c a) w)) v - Φ (xLat c (latC D c a) (unitF53 v)) ^ 2))
  have hX0 : 0 ≤ X := BstLean.Part161.momN_nonneg _ _ _
  have hp : 2 * q ≠ 0 := by omega
  have hXY : X ≤ kLSs n q * Y := by
    unfold kLSs; rw [mul_assoc, mul_comm (_ ^ _) Y]; exact h
  have hXp : X ^ (2 * q) = ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
        ∂stdGauss (Fin (n - 1)) := BstLean.Part161.momN_pow _ hp _
  have hYp : Y ^ (2 * q) = ∫ v, psiA Φ D c a v ^ q ∂stdGauss (Fin (n - 1)) := by
    rw [BstLean.Part161.momN_pow _ hp]
    congr 1; funext v
    unfold psiA tanSq
    rw [abs_of_nonneg (Real.sqrt_nonneg _), pow_mul]
  rw [← hXp, ← hYp, ← mul_pow]
  exact pow_le_pow_left₀ hX0 hXY _

/-- **The latitude moments of order `2q` from `Ψ`** (sharp form; Prop. `t7:p07:LG`, `τ_{2q}`):
`∫∫ |Φ − E(Φ|a)|^{2q} ≤ (c_q/(√(n−1) − c_q)·√(C/n))^{2q}` if `∫∫ Ψ^q ≤ (C/n)^q`. -/
lemma int_mom_psi_s (hn : 2 ≤ n) (D : Design n) (c : Ret n) (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) {q : ℕ} (hq : 1 ≤ q)
    (hqn : 2 * q < n - 1) {C : ℝ} (hC : 0 ≤ C)
    (hΨ : ∫ a, ∫ v, psiA Φ D c a v ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (C / n) ^ q) :
    ∫ a, ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))| ^ (2 * q)
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (kLSs n q * √(C / n)) ^ (2 * q) := by
  set ν := stdGauss (Fin (n - 1))
  have hc := hL.continuous hL0
  have mP := measurable_psiA hc D c
  have mInt : ∀ {F : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable F →
      Measurable (fun a => ∫ v, F (a, v) ∂ν) := fun hF =>
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have mX : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
      Φ (xLat c (latC D c p.1) (unitF53 p.2))) :=
    hc.measurable.comp (measurable_xA D c)
  have mE : Measurable (fun a => ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν) := mInt mX
  have bP := psiA_bounds hn D c hL0 hL hhom
  have hbX : ∀ a v, |Φ (xLat c (latC D c a) (unitF53 v))| ≤ L := fun a v => by
    refine (abs_hom_le hL hhom _).trans ?_
    calc L * √(normSq (xLat c (latC D c a) (unitF53 v))) ≤ L * √1 :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
            (normSq_xLat_le (by omega) c (latC_sq_le D c a) v)) hL0
      _ = L := by simp
  have bE : ∀ a, |∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν| ≤ L := fun a => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ w, |Φ (xLat c (latC D c a) (unitF53 w))| ∂ν ≤ ∫ _w, L ∂ν :=
          integral_mono (intB (meas_Xv hc c (latC D c a)).abs (M := L)
            fun w => by rw [abs_abs]; exact hbX a w) (integrable_const _) (hbX a)
      _ = L := by simp
  set K := kLSs n q
  have hK : 0 ≤ K := (kLSs_pos hq hqn).le
  have iL : Integrable (fun a => ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
      ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν| ^ (2 * q) ∂ν) (muI n) := by
    refine intB (mInt ((mX.sub (mE.comp measurable_fst)).abs.pow_const _))
      (M := (2 * L) ^ (2 * q)) fun a => ?_
    have h0 : 0 ≤ ∫ v, |Φ (xLat c (latC D c a) (unitF53 v)) -
        ∫ w, Φ (xLat c (latC D c a) (unitF53 w)) ∂ν| ^ (2 * q) ∂ν :=
      integral_nonneg fun v => pow_nonneg (abs_nonneg _) _
    rw [abs_of_nonneg h0]
    calc _ ≤ ∫ _v, (2 * L) ^ (2 * q) ∂ν := integral_mono
          (intB (((meas_Xv hc c (latC D c a)).sub_const _).abs.pow_const _)
            (M := (2 * L) ^ (2 * q)) fun v => by
              rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
              exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
                (by linarith [hbX a v, bE a])) _) (integrable_const _) fun v =>
            pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [hbX a v, bE a])) _
      _ = _ := by simp
  have iR : Integrable (fun a => K ^ (2 * q) * ∫ v, psiA Φ D c a v ^ q ∂ν) (muI n) := by
    refine (intB (mInt (mP.pow_const q)) (M := (2 * L ^ 2) ^ q) fun a => ?_).const_mul _
    have h0 : 0 ≤ ∫ v, psiA Φ D c a v ^ q ∂ν := integral_nonneg fun v => pow_nonneg (bP a v).1 _
    rw [abs_of_nonneg h0]
    calc ∫ v, psiA Φ D c a v ^ q ∂ν ≤ ∫ _v, (2 * L ^ 2) ^ q ∂ν :=
          integral_mono (intB ((meas_psi_v hc D c a).pow_const q)
            (M := (2 * L ^ 2) ^ q) fun v => by
              rw [abs_of_nonneg (pow_nonneg (bP a v).1 _)]
              exact pow_le_pow_left₀ (bP a v).1 (bP a v).2 q) (integrable_const _)
            fun v => pow_le_pow_left₀ (bP a v).1 (bP a v).2 q
      _ = _ := by simp
  calc _ ≤ ∫ a, K ^ (2 * q) * ∫ v, psiA Φ D c a v ^ q ∂ν ∂muI n :=
        integral_mono iL iR fun a => idx_mom_psi_s hn D c hL0 hL hhom hq hqn a
    _ = K ^ (2 * q) * ∫ a, ∫ v, psiA Φ D c a v ^ q ∂ν ∂muI n := integral_const_mul _ _
    _ ≤ K ^ (2 * q) * (C / n) ^ q := mul_le_mul_of_nonneg_left hΨ (by positivity)
    _ = (K * √(C / n)) ^ (2 * q) := by
        rw [mul_pow, pow_mul (√(C / n)), Real.sq_sqrt (by positivity)]


lemma kLSs_pos' {q : ℕ} (hn : 26 ≤ n) (hq : 1 ≤ q) (hq12 : q ≤ 12) : 0 < kLSs n q :=
  kLSs_pos hq (by omega)

lemma pos_div_n {C : ℝ} (hC : 0 < C) (hn : 26 ≤ n) : 0 < √(C / n) :=
  Real.sqrt_pos.mpr (div_pos hC (by have : (26 : ℝ) ≤ n := by exact_mod_cast hn
                                    linarith))

/-- **The latitude-moment interface from the order-12 certificates, sharp form**: `V = (C/n)/(n−2)`,
`τ_{2q} = c_q √(C/(n(n − 1 − 2q)))` (the paper's `τ_{2p}`), removal order 24. -/
noncomputable def latMomOfPsi12s (hn : 26 ≤ n) (D : Design n) (c : Ret n) {σl CL CS VS βlow : ℝ}
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
  have hn2' : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (26 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  { Vs := CS / n / ((n : ℝ) - 2)
    Vl := CL / n / ((n : ℝ) - 2)
    VS := VS
    ts8 := kLSs n 4 * √(CS / n)
    ts12 := kLSs n 6 * √(CS / n)
    tl8 := kLSs n 4 * √(CL / n)
    tl12 := kLSs n 6 * √(CL / n)
    tlq := kLSs n 12 * √(CL / n)
    tsq := kLSs n 12 * √(CS / n)
    βlow := βlow
    hVs0 := by positivity
    hVl0 := by positivity
    hVS0 := hVS0
    hts8 := mul_pos (kLSs_pos' hn (by norm_num) (by norm_num)) (pos_div_n hCS hn)
    hts12 := mul_pos (kLSs_pos' hn (by norm_num) (by norm_num)) (pos_div_n hCS hn)
    htl8 := mul_pos (kLSs_pos' hn (by norm_num) (by norm_num)) (pos_div_n hCL hn)
    htl12 := mul_pos (kLSs_pos' hn (by norm_num) (by norm_num)) (pos_div_n hCL hn)
    htlq := (mul_pos (kLSs_pos' hn (by norm_num) le_rfl) (pos_div_n hCL hn)).le
    htsq := (mul_pos (kLSs_pos' hn (by norm_num) le_rfl) (pos_div_n hCS hn)).le
    hβl := hβ
    hVs := int_var_psi (by omega) D c (lipSig_nonneg D c) (sigX_euLip D c)
      (fun t x ht => sigX_hom D c t x ht) hCS.le (lowS (m := 6) (by norm_num) (by norm_num))
    hVl := int_var_psi (by omega) D c (lipLam_nonneg D c) (lamX_euLip D c)
      (fun t x ht => lamX_hom D c t x ht) hCL.le (lowL (m := 6) (by norm_num) (by norm_num))
    hVS := hVS
    hs8 := int_mom_psi_s hn2 D c (lipSig_nonneg D c) (sigX_euLip D c)
      (fun t x ht => sigX_hom D c t x ht) (q := 4) (by norm_num) (by omega) hCS.le
      (lowS (m := 3) (by norm_num) (by norm_num))
    hs12 := int_mom_psi_s hn2 D c (lipSig_nonneg D c) (sigX_euLip D c)
      (fun t x ht => sigX_hom D c t x ht) (q := 6) (by norm_num) (by omega) hCS.le
      (lowS (m := 2) (by norm_num) (by norm_num))
    hl8 := int_mom_psi_s hn2 D c (lipLam_nonneg D c) (lamX_euLip D c)
      (fun t x ht => lamX_hom D c t x ht) (q := 4) (by norm_num) (by omega) hCL.le
      (lowL (m := 3) (by norm_num) (by norm_num))
    hl12 := int_mom_psi_s hn2 D c (lipLam_nonneg D c) (lamX_euLip D c)
      (fun t x ht => lamX_hom D c t x ht) (q := 6) (by norm_num) (by omega) hCL.le
      (lowL (m := 2) (by norm_num) (by norm_num))
    hlq := int_mom_psi_s hn2 D c (lipLam_nonneg D c) (lamX_euLip D c)
      (fun t x ht => lamX_hom D c t x ht) (q := 12) (by norm_num) (by omega) hCL.le hL12
    hsq := int_mom_psi_s hn2 D c (lipSig_nonneg D c) (sigX_euLip D c)
      (fun t x ht => sigX_hom D c t x ht) (q := 12) (by norm_num) (by omega) hCS.le hS12
    hmass := hmass }

open BstLean.Part130 BstLean.Part156 BstLean.Part159 in
/-- **The classifier theorem with an Agent event `E₁` (every `n ≥ 16 384`) and the Agent
replacement reduced to the order-12 realized certificates, with the paper's LS constants**
(`latMomOfPsi12s`: `τ_{2q} = c_q √(C/(n(n−1−2q)))`). -/
theorem classifier_agent_psi12s (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
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
        rootFL wl ws η CA (latMomOfPsi12s (by omega) (paperDesign n fT wT hf hw) c hCL hCS hVS0 hβ
          hL12 hS12 hVS hmass) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_agent_mom hn fT wT hf hw t hE₁ hextra hEθ hFA fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, VS, βlow, h0, h1, hCL, hCS, hVS0, hβ, hL12, hS12, hVS, hmass,
    hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨wl, ws, σl, η, CA, 2 * 12, h0, h1, latMomOfPsi12s (by omega) _ c hCL hCS hVS0 hβ hL12
    hS12 hVS hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩

end BstLean.Part162

open BstLean.Part162 in
#print axioms int_mom_psi_s
open BstLean.Part162 in
#print axioms classifier_agent_psi12s
