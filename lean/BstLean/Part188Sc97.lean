import BstLean.Part188R160ScEv
import BstLean.Part188R160ScTab



namespace BstLean.Part188.Sc

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nuA)
open BstLean.Part188.Base160_R

variable {n : ℕ}

def SSc97 (n : ℕ) : Set (AgFam n) :=
  {x | 46 / 100 ≤ thetaC x.1.1 x.1.2 → thetaC x.1.1 x.1.2 ≤ 55 / 100 →
    97 / 100 * scLow n x.1.1 x.1.2 ≤ sO2 x.2.1 x.1.1 x.1.2}

theorem measurableSet_SSc97 (n : ℕ) : MeasurableSet (SSc97 n) := by
  have h1 : MeasurableSet {x : AgFam n | 46 / 100 ≤ thetaC x.1.1 x.1.2} :=
    measurableSet_le measurable_const measurable_thetaC_fam
  have h2 : MeasurableSet {x : AgFam n | thetaC x.1.1 x.1.2 ≤ 55 / 100} :=
    measurableSet_le measurable_thetaC_fam measurable_const
  have h3 : MeasurableSet {x : AgFam n |
      97 / 100 * scLow n x.1.1 x.1.2 ≤ sO2 x.2.1 x.1.1 x.1.2} :=
    measurableSet_le (measurable_scLow_fam.const_mul _) measurable_sO2_fam
  have e : SSc97 n = {x : AgFam n | 46 / 100 ≤ thetaC x.1.1 x.1.2}ᶜ ∪
      ({x : AgFam n | thetaC x.1.1 x.1.2 ≤ 55 / 100}ᶜ ∪
        {x : AgFam n | 97 / 100 * scLow n x.1.1 x.1.2 ≤ sO2 x.2.1 x.1.1 x.1.2}) := by
    ext x
    simp only [SSc97, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  rw [e]
  exact h1.compl.union (h2.compl.union h3)

/-- Chebyshev for `s_h²` around `scLow`, in the window. -/
theorem SSc97_cheb (hn : 16200 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
        {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 97 / 100 * scLow n c τ} ≤
      10667 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hm := BstLean.Part130.one_le_mA hn1
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨hR, hN, hS, hT⟩ := window_facts hn c hτ hθ0 hθ1
  have hge := scLow_ge hn c hτ hθ0 hθ1
  have hmean := scLow_le_mean hn1 c τ
  obtain ⟨LS, hvar⟩ := BstLean.Part153.sO2_var (m := mA n) hn1 hm c τ
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = scLow n c τ := ⟨_, rfl⟩
  rw [← hL] at hge hmean ⊢
  have hτ2 : 0 < τ ^ 2 := by positivity
  -- `L ≥ 1.292 τ²`
  have hLτ : 1292 / 1000 * τ ^ 2 ≤ L := by
    refine le_trans ?_ hge
    have e : 3553 / 10000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) =
        7106 / 10000 * (normSq c + (n : ℝ) * τ ^ 2) / n := by ring
    rw [e, le_div_iff₀ hn0]
    nlinarith
  have hL0 : 0 < L := by nlinarith
  have hc0 : 0 < (3 * L / 100) := by positivity
  have hch := meas_ge_le_variance_div_sq LS hc0
  have hsub : {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 97 / 100 * L} ⊆
      {A₁ | (3 * L / 100) ≤ |sO2 A₁ c τ -
        ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ))|} := by
    intro A₁ hA
    have hA' : sO2 A₁ c τ < 97 / 100 * L := hA
    show (3 * L / 100) ≤ |sO2 A₁ c τ -
        ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ))|
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    linarith
  have h1 : (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 97 / 100 * L} ≤
      (ENNReal.ofReal (variance (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => sO2 A₁ c τ)
        (gaussMat (mA n) n (2 / (n : ℝ))) / ((3 * L / 100)) ^ 2)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hch)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at h1
  refine h1.trans ?_
  rw [hmA] at hvar
  have hw : 1 + 2 / (n : ℝ) ≤ 1 + 2 / 16200 := by
    have : 2 / (n : ℝ) ≤ 2 / 16200 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
    linarith
  have hL2 : (1292 / 1000 * τ ^ 2 * 3 / 100) ^ 2 ≤ ((3 * L / 100)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc variance (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => sO2 A₁ c τ)
        (gaussMat (mA n) n (2 / (n : ℝ))) / ((3 * L / 100)) ^ 2
      ≤ (16 * (1 + 2 / (n : ℝ)) * τ ^ 4 / (n : ℝ) ^ 2) / ((3 * L / 100)) ^ 2 :=
        div_le_div_of_nonneg_right hvar (by positivity)
    _ ≤ (16 * (1 + 2 / 16200) * τ ^ 4 / (n : ℝ) ^ 2) / (1292 / 1000 * τ ^ 2 * 3 / 100) ^ 2 := by
        refine div_le_div₀ (by positivity) ?_ (by positivity) hL2
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num))
          (by positivity)
    _ = (16 * (1 + 2 / 16200) * (10000 / 9) / (1292 / 1000) ^ 2) / (n : ℝ) ^ 2 := by
        field_simp
        norm_num
    _ ≤ 10667 / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- **The charge of the event `SSc97`**: `≤ 10667/n²`, every `c`, `τ > 0`, `n ≥ 16200`. -/
theorem SSc97_charge (hn : 16200 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SSc97 n} ≤ 10667 / (n : ℝ) ^ 2 := by
  by_cases hw : 46 / 100 ≤ thetaC c τ ∧ thetaC c τ ≤ 55 / 100
  · have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        ((c, τ), θ) ∉ SSc97 n} =
        {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 97 / 100 * scLow n c τ} ×ˢ
          (Set.univ : Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ)) := by
      ext θ
      simp only [SSc97, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true, not_forall,
        not_le]
      constructor
      · rintro ⟨-, -, h⟩; exact h
      · intro h; exact ⟨hw.1, hw.2, h⟩
    rw [e]
    unfold nuA
    rw [measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def]
    exact SSc97_cheb hn c hτ hw.1 hw.2
  · have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        ((c, τ), θ) ∉ SSc97 n} = ∅ := by
      ext θ
      simp only [SSc97, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hw
    rw [e]
    simp only [measureReal_empty]
    positivity

theorem SSc97_charge_num (hn : 16200 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SSc97 n} ≤ 41 / 1000000 := by
  refine (SSc97_charge hn c τ hτ).trans ?_
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem sO2_ge_gen97 (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ) {θlo K X : ℝ}
    (hlo : 46 / 100 ≤ θlo) (hlo1 : θlo ≤ 1) (hθ0 : θlo ≤ thetaC c τ)
    (hθ1 : thetaC c τ ≤ 55 / 100)
    (hK : (1 - θlo) * (1 - θlo + 55 / 100 / 16200) / ((1 - 3 / 100) ^ 2 * (99996 / 100000)) +
      (1 - θlo) * (1504 / 10 ^ 6) ^ 2 + 55 / 100 / 16200 ≤ K)
    (hX : X ≤ 97 / 100 * (1 - 31832 / 100000 - (1 - θlo) / 2 - (1 / 2 - 3183 / 10000) * K))
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hS : ((c, τ), (A₁, A₂)) ∈ SSc97 n) :
    2 * X * (normSq c + (n : ℝ) * τ ^ 2) / n ≤ sO2 A₁ c τ := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : 97 / 100 * scLow n c τ ≤ sO2 A₁ c τ := hS (hlo.trans hθ0) hθ1
  have hW := Tcos_window_gen hn c hτ hlo hlo1 hθ0 hθ1 hK
  obtain ⟨hR, -, -, -⟩ := window_facts hn c hτ (hlo.trans hθ0) hθ1
  have hN : normSq c ≤ (1 - θlo) * (normSq c + (n : ℝ) * τ ^ 2) := by
    unfold thetaC at hθ0
    rw [rhoC_sqP, le_div_iff₀ hR] at hθ0
    linarith
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) ≤ (1 - θlo) * (1 - θlo + 55 / 100 / 16200) /
        ((1 - 3 / 100) ^ 2 * (99996 / 100000)) := by
      have : (0 : ℝ) ≤ 1 - θlo := by linarith
      positivity
    have h2 : (0 : ℝ) ≤ (1 - θlo) * (1504 / 10 ^ 6) ^ 2 := by
      have : (0 : ℝ) ≤ 1 - θlo := by linarith
      positivity
    linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / π := ⟨_, rfl⟩
  have hp1 : (3183 : ℝ) / 10000 ≤ p := by
    rw [hp, div_le_div_iff₀ (by norm_num) Real.pi_pos]
    nlinarith [Real.pi_lt_d4]
  have hp2 : p ≤ 31832 / 100000 := by
    rw [hp, div_le_div_iff₀ Real.pi_pos (by norm_num)]
    nlinarith [Real.pi_gt_d4]
  refine le_trans ?_ h1
  unfold scLow
  rw [← hp]
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  rw [← hRd] at hR hN hW ⊢
  have e : 2 * X * R / n = 2 / (n : ℝ) * (X * R) := by ring
  have e' : 97 / 100 * (2 / (n : ℝ) * ((1 - p) * R - normSq c / 2 -
      (1 / 2 - p) * (Tcos c τ + τ ^ 2))) = 2 / (n : ℝ) * (97 / 100 * ((1 - p) * R -
      normSq c / 2 - (1 / 2 - p) * (Tcos c τ + τ ^ 2))) := by ring
  rw [e, e']
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h3 : (1 / 2 - p) * (Tcos c τ + τ ^ 2) ≤ (1 / 2 - 3183 / 10000) * (K * R) := by
    have a : (1 / 2 - p) * (Tcos c τ + τ ^ 2) ≤ (1 / 2 - p) * (K * R) :=
      mul_le_mul_of_nonneg_left hW (by linarith)
    have b : (1 / 2 - p) * (K * R) ≤ (1 / 2 - 3183 / 10000) * (K * R) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have h4 := mul_le_mul_of_nonneg_right hX hR.le
  nlinarith


theorem SSc97_ret_charge (hn : 16200 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real
      (agentEv (paperDesign n fT wT hf hw) (SSc97 n))ᶜ ≤ 41 / 1000000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) (measurableSet_SSc97 n) (by norm_num)
    (fun c τ hτ => SSc97_charge_num hn c τ hτ)

end BstLean.Part188.Sc
