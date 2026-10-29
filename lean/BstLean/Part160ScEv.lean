import BstLean.Part160ScMean

/-!
# Part 160 (file `ScEv`): the event of a large first-layer variance

Do not use `sorry`, `native_decide` or `axiom`.

* `scLow n c τ`: the lower bound of `E s_h²` of `sO2_mean_sharp`.
* `Tcos_window`: `Tcos + τ² ≤ 0.3101·ρ²` for `n ≥ 16384`, `0.46 ≤ θ ≤ 0.55`.
* `scLow_ge`: `scLow ≥ 0.3553·γ_A·ρ²` in the window (Part 153: `E s_h² ≥ 2(1 − 1/π)τ²`, which is
  `(1 − 1/π)θ·γ_Aρ² ≥ 0.3135·γ_Aρ²` at `θ = 0.46`; in units of `τ²`: `≥ 1.292` at `θ = 0.55` and
  `≥ 1.544` at `θ = 0.46`, against `1.363`).
* `SSc n`: the event `{window → s_h² ≥ 0.95·scLow}` as a set of `((c, τ), (A₁, A₂))`;
  `measurableSet_SSc`; `SSc_charge`: complement probability at most `3840/n²`
  (`n ≥ 16384`, `τ > 0`); `SSc_charge_num`: at most `15/10⁶`.
* `sO2_ge_of_SSc`: on the event, in the window: `s_h² ≥ 0.67507·ρ²/n`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC hO gO sO2 rhoC_sqP rhoC_posP)
open BstLean.Part153 (nrm nuA)

variable {n : ℕ}

/-- The lower bound of `E_{A₁} s_h²` of `sO2_mean_sharp`. -/
noncomputable def scLow (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  2 / (n : ℝ) * ((1 - 1 / π) * (normSq c + (n : ℝ) * τ ^ 2) - normSq c / 2 -
    (1 / 2 - 1 / π) * (Tcos c τ + τ ^ 2))

lemma scLow_le_mean (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    scLow n c τ ≤ ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, sO2 A₁ c τ
      ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
  sO2_mean_sharp hn (BstLean.Part130.one_le_mA hn) c τ

/-- The window in the variables `N = |c|²`, `R = ρ²`. -/
lemma window_facts (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    0 < normSq c + (n : ℝ) * τ ^ 2 ∧
    normSq c ≤ 54 / 100 * (normSq c + (n : ℝ) * τ ^ 2) ∧
    (n : ℝ) * τ ^ 2 ≤ 55 / 100 * (normSq c + (n : ℝ) * τ ^ 2) ∧
    τ ^ 2 ≤ 55 / 100 / 16384 * (normSq c + (n : ℝ) * τ ^ 2) := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 0 < normSq c + (n : ℝ) * τ ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg c) (by positivity)
  unfold thetaC at hθ0 hθ1
  rw [rhoC_sqP] at hθ0 hθ1
  rw [le_div_iff₀ hR] at hθ0
  rw [div_le_iff₀ hR] at hθ1
  refine ⟨hR, by linarith, hθ1, ?_⟩
  have h1 : 16384 * τ ^ 2 ≤ (n : ℝ) * τ ^ 2 := mul_le_mul_of_nonneg_right hnR (sq_nonneg τ)
  linarith

/-- `Tcos + τ² ≤ 0.3101·ρ²` in the window, `n ≥ 16384`. -/
theorem Tcos_window (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    Tcos c τ + τ ^ 2 ≤ 3101 / 10000 * (normSq c + (n : ℝ) * τ ^ 2) := by
  obtain ⟨hR, hN, hS, hT⟩ := window_facts hn c hτ hθ0 hθ1
  have hN0 := normSq_nonneg c
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hT' := Tcos_le (by omega : 2 ≤ n) c hτ (ε := 3 / 100) (by norm_num) (by norm_num)
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  rw [← hRd] at hR hN hS hT hT' ⊢
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = normSq c := ⟨_, rfl⟩
  rw [← hNd] at hN hN0 hT'
  obtain ⟨t, htd⟩ : ∃ t : ℝ, t = τ ^ 2 := ⟨_, rfl⟩
  rw [← htd] at hT hτ2 hT' ⊢
  -- `Q = R − t ≥ 0.99996 R`
  have hQ : 99996 / 100000 * R ≤ R - t := by linarith
  have hQ0 : 0 < R - t := by linarith
  -- the exponential
  have hexp : exp (-((3 / 100 : ℝ) ^ 2 * (R - t)) / (2 * t)) ≤ (1504 / 10 ^ 6 : ℝ) ^ 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_13_le
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- the first term
  have hden : 0 < (1 - 3 / 100 : ℝ) ^ 2 * (R - t) := by positivity
  have h1 : (N ^ 2 + t * N) / ((1 - 3 / 100 : ℝ) ^ 2 * (R - t)) ≤ 30995 / 100000 * R := by
    rw [div_le_iff₀ hden]
    have a1 : N ^ 2 + t * N ≤ 54 / 100 * R * (54 / 100 * R + 55 / 100 / 16384 * R) := by
      have : N + t ≤ 54 / 100 * R + 55 / 100 / 16384 * R := by linarith
      calc N ^ 2 + t * N = N * (N + t) := by ring
        _ ≤ 54 / 100 * R * (54 / 100 * R + 55 / 100 / 16384 * R) :=
          mul_le_mul hN this (by linarith) (by positivity)
    have a2 : 30995 / 100000 * R * ((1 - 3 / 100 : ℝ) ^ 2 * (99996 / 100000 * R)) ≤
        30995 / 100000 * R * ((1 - 3 / 100 : ℝ) ^ 2 * (R - t)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ (by positivity)) (by positivity)
    nlinarith [sq_nonneg R]
  have h2 : N * exp (-((3 / 100 : ℝ) ^ 2 * (R - t)) / (2 * t)) ≤ N * (1504 / 10 ^ 6 : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hexp hN0
  nlinarith

/-- `scLow ≥ 0.3553·γ_A·ρ²` in the window, `n ≥ 16384`. -/
theorem scLow_ge (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    3553 / 10000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤ scLow n c τ := by
  obtain ⟨hR, hN, hS, hT⟩ := window_facts hn c hτ hθ0 hθ1
  have hW := Tcos_window hn c hτ hθ0 hθ1
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / π := ⟨_, rfl⟩
  have hp1 : (31830 : ℝ) / 100000 ≤ p := by
    rw [hp, div_le_div_iff₀ (by norm_num) Real.pi_pos]
    nlinarith [Real.pi_lt_d4]
  have hp2 : p ≤ 31832 / 100000 := by
    rw [hp, div_le_div_iff₀ Real.pi_pos (by norm_num)]
    nlinarith [Real.pi_gt_d4]
  unfold scLow
  rw [← hp]
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  rw [← hRd] at hR hN hW ⊢
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ hγ
  have h1 : (1 / 2 - p) * (Tcos c τ + τ ^ 2) ≤ (1 / 2 - p) * (3101 / 10000 * R) :=
    mul_le_mul_of_nonneg_left hW (by linarith)
  nlinarith

/-- **The event of a large first-layer variance**: in the window `0.46 ≤ θ_in ≤ 0.55`,
`s_h² ≥ 0.95·scLow`. -/
def SSc (n : ℕ) : Set (AgFam n) :=
  {x | 46 / 100 ≤ thetaC x.1.1 x.1.2 → thetaC x.1.1 x.1.2 ≤ 55 / 100 →
    95 / 100 * scLow n x.1.1 x.1.2 ≤ sO2 x.2.1 x.1.1 x.1.2}

lemma measurable_thetaC_fam : Measurable (fun x : AgFam n => thetaC x.1.1 x.1.2) := by
  unfold thetaC
  have h1 : Measurable (fun x : AgFam n => rhoC x.1.1 x.1.2) :=
    (BstLean.Part150.measurable_rhoC (n := n)).comp measurable_fst
  have h2 : Measurable (fun x : AgFam n => x.1.2) := measurable_snd.comp measurable_fst
  exact ((h2.pow_const 2).const_mul _).div (h1.pow_const 2)

lemma measurable_Tcos_fam : Measurable (fun q : (Fin n → ℝ) × ℝ => Tcos q.1 q.2) := by
  have hy : Continuous (fun p : ((Fin n → ℝ) × ℝ) × (Fin n → ℝ) => p.1.1 + p.1.2 • p.2) := by
    fun_prop
  have h1 : Measurable (fun p : ((Fin n → ℝ) × ℝ) × (Fin n → ℝ) =>
      ∑ j, (p.1.1 + p.1.2 • p.2) j * p.1.1 j) :=
    Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp hy.measurable).mul
      ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
  have hF : Measurable (fun p : ((Fin n → ℝ) × ℝ) × (Fin n → ℝ) =>
      (∑ j, (p.1.1 + p.1.2 • p.2) j * p.1.1 j) ^ 2 / normSq (p.1.1 + p.1.2 • p.2)) :=
    (h1.pow_const 2).div (measurable_normSq.comp hy.measurable)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

lemma measurable_scLow_fam : Measurable (fun x : AgFam n => scLow n x.1.1 x.1.2) := by
  unfold scLow
  have hc : Measurable (fun x : AgFam n => normSq x.1.1) :=
    measurable_normSq.comp (measurable_fst.comp measurable_fst)
  have hτ : Measurable (fun x : AgFam n => x.1.2 ^ 2) :=
    (measurable_snd.comp measurable_fst).pow_const 2
  have hT : Measurable (fun x : AgFam n => Tcos x.1.1 x.1.2) :=
    measurable_Tcos_fam.comp measurable_fst
  exact ((((hc.add (hτ.const_mul _)).const_mul _).sub (hc.div_const 2)).sub
    ((hT.add hτ).const_mul _)).const_mul _

lemma measurable_sO2_fam : Measurable (fun x : AgFam n => sO2 x.2.1 x.1.1 x.1.2) := by
  simp_rw [BstLean.Part153.sO2_rows]
  refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
  unfold BstLean.Part153.rowV rowOf
  have hc : Continuous (fun x : AgFam n =>
      (x.1.2 * √(∑ j, x.2.1 i j ^ 2), ∑ j, x.2.1 i j * x.1.1 j)) := by fun_prop
  exact BstLean.Part153.measurable_vS.comp hc.measurable

theorem measurableSet_SSc (n : ℕ) : MeasurableSet (SSc n) := by
  have h1 : MeasurableSet {x : AgFam n | 46 / 100 ≤ thetaC x.1.1 x.1.2} :=
    measurableSet_le measurable_const measurable_thetaC_fam
  have h2 : MeasurableSet {x : AgFam n | thetaC x.1.1 x.1.2 ≤ 55 / 100} :=
    measurableSet_le measurable_thetaC_fam measurable_const
  have h3 : MeasurableSet {x : AgFam n |
      95 / 100 * scLow n x.1.1 x.1.2 ≤ sO2 x.2.1 x.1.1 x.1.2} :=
    measurableSet_le (measurable_scLow_fam.const_mul _) measurable_sO2_fam
  have e : SSc n = {x : AgFam n | 46 / 100 ≤ thetaC x.1.1 x.1.2}ᶜ ∪
      ({x : AgFam n | thetaC x.1.1 x.1.2 ≤ 55 / 100}ᶜ ∪
        {x : AgFam n | 95 / 100 * scLow n x.1.1 x.1.2 ≤ sO2 x.2.1 x.1.1 x.1.2}) := by
    ext x
    simp only [SSc, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  rw [e]
  exact h1.compl.union (h2.compl.union h3)

/-- Chebyshev for `s_h²` around `scLow`, in the window. -/
theorem SSc_cheb (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
        {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 95 / 100 * scLow n c τ} ≤
      3840 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hm := BstLean.Part130.one_le_mA hn1
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
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
  have hc0 : 0 < L / 20 := by positivity
  have hch := meas_ge_le_variance_div_sq LS hc0
  have hsub : {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 95 / 100 * L} ⊆
      {A₁ | L / 20 ≤ |sO2 A₁ c τ -
        ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ))|} := by
    intro A₁ hA
    have hA' : sO2 A₁ c τ < 95 / 100 * L := hA
    show L / 20 ≤ |sO2 A₁ c τ -
        ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ))|
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    linarith
  have h1 : (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 95 / 100 * L} ≤
      (ENNReal.ofReal (variance (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => sO2 A₁ c τ)
        (gaussMat (mA n) n (2 / (n : ℝ))) / (L / 20) ^ 2)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hch)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at h1
  refine h1.trans ?_
  rw [hmA] at hvar
  have hw : 1 + 2 / (n : ℝ) ≤ 1 + 2 / 16384 := by
    have : 2 / (n : ℝ) ≤ 2 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
    linarith
  have hL2 : (1292 / 1000 * τ ^ 2 / 20) ^ 2 ≤ (L / 20) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc variance (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => sO2 A₁ c τ)
        (gaussMat (mA n) n (2 / (n : ℝ))) / (L / 20) ^ 2
      ≤ (16 * (1 + 2 / (n : ℝ)) * τ ^ 4 / (n : ℝ) ^ 2) / (L / 20) ^ 2 :=
        div_le_div_of_nonneg_right hvar (by positivity)
    _ ≤ (16 * (1 + 2 / 16384) * τ ^ 4 / (n : ℝ) ^ 2) / (1292 / 1000 * τ ^ 2 / 20) ^ 2 := by
        refine div_le_div₀ (by positivity) ?_ (by positivity) hL2
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num))
          (by positivity)
    _ = (16 * (1 + 2 / 16384) * 400 / (1292 / 1000) ^ 2) / (n : ℝ) ^ 2 := by
        field_simp
        norm_num
    _ ≤ 3840 / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- **The charge of the event `SSc`**: `≤ 3840/n²`, every `c`, `τ > 0`, `n ≥ 16384`. -/
theorem SSc_charge (hn : 16384 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SSc n} ≤ 3840 / (n : ℝ) ^ 2 := by
  by_cases hw : 46 / 100 ≤ thetaC c τ ∧ thetaC c τ ≤ 55 / 100
  · have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        ((c, τ), θ) ∉ SSc n} =
        {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | sO2 A₁ c τ < 95 / 100 * scLow n c τ} ×ˢ
          (Set.univ : Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ)) := by
      ext θ
      simp only [SSc, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true, not_forall,
        not_le]
      constructor
      · rintro ⟨-, -, h⟩; exact h
      · intro h; exact ⟨hw.1, hw.2, h⟩
    rw [e]
    unfold nuA
    rw [measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def]
    exact SSc_cheb hn c hτ hw.1 hw.2
  · have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        ((c, τ), θ) ∉ SSc n} = ∅ := by
      ext θ
      simp only [SSc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hw
    rw [e]
    simp only [measureReal_empty]
    positivity

theorem SSc_charge_num (hn : 16384 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SSc n} ≤ 15 / 1000000 := by
  refine (SSc_charge hn c τ hτ).trans ?_
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- On the event `SSc`, in the window: `s_h² ≥ 0.67507·ρ²/n`. -/
theorem sO2_ge_of_SSc (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hS : ((c, τ), (A₁, A₂)) ∈ SSc n) :
    67507 / 100000 * (normSq c + (n : ℝ) * τ ^ 2) / n ≤ sO2 A₁ c τ := by
  have h1 : 95 / 100 * scLow n c τ ≤ sO2 A₁ c τ := hS hθ0 hθ1
  have h2 := scLow_ge hn c hτ hθ0 hθ1
  refine le_trans ?_ h1
  have e : 67507 / 100000 * (normSq c + (n : ℝ) * τ ^ 2) / n =
      95 / 100 * (3553 / 10000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2))) := by ring
  rw [e]
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms scLow_ge
open BstLean.Part160 in
#print axioms measurableSet_SSc
open BstLean.Part160 in
#print axioms SSc_charge
open BstLean.Part160 in
#print axioms SSc_charge_num
open BstLean.Part160 in
#print axioms sO2_ge_of_SSc
