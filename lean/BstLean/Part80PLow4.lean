import BstLean.Part80Defs2
import BstLean.Part80PLow

/-!
# Part 80: the fourth moment of `s = v·x` for `t ∈ [0, n]`

`E_D s⁴ ≤ E_D s²/2 + 1/(2n)` (hence `≤ (53/100) E_D s² + 1/n`) and `E_D s² ≤ 1/2 + 1/n`.

Route: the surrogate `Q_K = surrRK n K t v` satisfies the bound for every truncation order `K`
(finite-sum Stein identity `stein80`). The bias bound `surrogate_continuous_sq_bias61` holds for
every `e > 0` with `etaQ e ≤ e/20`, so letting `e → 0` transfers any bound `E_Q g ≤ c` that holds
for every `K` to `E_D g ≤ c` with no loss (`transfer80`).
-/

namespace BstLean.Part80

open MeasureTheory
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part56 (UnitV lawRK surrRK KRK rk1)
open BstLean.Part69 (U69 Z69 a69 b69 sv69)

/-- A bound on `E_Q g` valid for every truncation order transfers to the true distribution. -/
lemma transfer80 (n : ℕ) (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (t : ℝ) (ht0 : 0 ≤ t)
    (htn : t ≤ n) (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) (c : ℝ)
    (hQ : ∀ K : ℕ, ∫ x, g x ∂surrRK n K t v ≤ c) : ∫ x, g x ∂lawRK n t v ≤ c := by
  by_contra hcon
  push Not at hcon
  set m := ∫ x, g x ∂lawRK n t v
  set V := varU (lawRK n t v) g
  have hV : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  set δ := m - c
  have hδ : 0 < δ := by simp only [δ]; linarith
  -- choose `e` with `(e/20)² V < δ²`
  set e : ℝ := min 1 (δ / (V + 1)) with he_def
  have he0 : 0 < e := lt_min one_pos (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have he2 : e ≤ δ / (V + 1) := min_le_right _ _
  have hbias := BstLean.Part61.surrogate_continuous_sq_bias61 hn 1 e t he0 ht0
    (by simpa using htn) v hv g hg
  have hq := hQ (KRK 1 n e)
  set q := ∫ x, g x ∂surrRK n (KRK 1 n e) t v
  have heta0 : 0 ≤ BstLean.Part43.etaQ e := by
    unfold BstLean.Part43.etaQ BstLean.Part43.xi43
    exact le_min (by positivity) (by norm_num)
  have heta : BstLean.Part43.etaQ e ≤ e := by
    unfold BstLean.Part43.etaQ BstLean.Part43.xi43
    exact (min_le_left _ _).trans (by linarith)
  have h1 : δ ^ 2 ≤ (q - m) ^ 2 := by
    have : δ ≤ m - q := by simp only [δ]; linarith
    nlinarith
  have h2 : BstLean.Part43.etaQ e ^ 2 * V ≤ e ^ 2 * V :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ heta0 heta 2) hV
  have h3 : e * (V + 1) ≤ δ := by
    rwa [le_div_iff₀ (by linarith)] at he2
  have h4 : e ^ 2 * V < δ ^ 2 := by
    have h8 : e ^ 2 * V < e ^ 2 * (V + 1) := by nlinarith [pow_pos he0 2]
    have h9 : e ^ 2 * (V + 1) ^ 2 ≤ δ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity : 0 ≤ e * (V + 1)) h3 2
      nlinarith
    have h10 : e ^ 2 * (V + 1) ≤ e ^ 2 * (V + 1) ^ 2 := by
      have : (V + 1) ≤ (V + 1) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  linarith

/-- Surrogate Stein inequality: `n a − 1 + 2t (b − a) ≤ 0`. -/
lemma steinIneq80 (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (ht0 : 0 ≤ t) :
    (n : ℝ) * a69 n K t - 1 + 2 * t * (b69 n K t - a69 n K t) ≤ 0 := by
  have hZ : 1 ≤ Z69 n K t 0 := BstLean.Part69.Z0_pos69 K t ht0
  have hZ0 : (0 : ℝ) < Z69 n K t 0 := by linarith
  have hst := stein80 n hn t K
  have hrem : 2 * t * (t ^ K / (K.factorial : ℝ)) * (U69 n (K + 2) - U69 n (K + 1)) ≤ 0 := by
    have := U69_anti80 n hn (K + 1)
    have hc : 0 ≤ 2 * t * (t ^ K / (K.factorial : ℝ)) := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hc (by linarith)
  have : (n : ℝ) * a69 n K t - 1 + 2 * t * (b69 n K t - a69 n K t) =
      ((n : ℝ) * Z69 n K t 1 - Z69 n K t 0 + 2 * t * (Z69 n K t 2 - Z69 n K t 1)) /
        Z69 n K t 0 := by
    unfold a69 b69; field_simp
  rw [this, hst]
  exact div_nonpos_of_nonpos_of_nonneg hrem hZ0.le

/-- `b69 ≤ a69` for `t ≥ 0`. -/
lemma b69_le_a69_80 (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (ht0 : 0 ≤ t) :
    b69 n K t ≤ a69 n K t := by
  have hZ : 1 ≤ Z69 n K t 0 := BstLean.Part69.Z0_pos69 K t ht0
  unfold a69 b69
  apply div_le_div_of_nonneg_right _ (by linarith)
  unfold Z69
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (U69_anti80 n hn (j + 1)) (by positivity)

/-- Surrogate: `b ≤ a/2 + 1/(2n)` for `0 ≤ t ≤ n`. -/
lemma b69_le80 (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ n) :
    b69 n K t - 1 / 2 * a69 n K t ≤ 1 / (2 * (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hS := steinIneq80 n hn K t ht0
  have hba := b69_le_a69_80 n hn K t ht0
  set a := a69 n K t
  set b := b69 n K t
  have key : 2 * (n : ℝ) * b - (n : ℝ) * a ≤ 1 := by
    have h1 : t * (a - b) ≤ (n : ℝ) * (a - b) :=
      mul_le_mul_of_nonneg_right htn (by linarith)
    by_cases hc : 1 ≤ (n : ℝ) * a
    · nlinarith
    · push Not at hc
      nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Sharp fourth-moment bound: `E_D s⁴ ≤ E_D s²/2 + 1/(2n)`. -/
theorem pLow4RK_sharp (n : ℕ) (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (t : ℝ)
    (ht0 : 0 ≤ t) (htn : t ≤ n) :
    ∫ x, (∑ i, v i * x i) ^ 4 ∂lawRK n t v ≤
      1 / 2 * ∫ x, (∑ i, v i * x i) ^ 2 ∂lawRK n t v + 1 / (2 * (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hD : SphLaw n (lawRK n t v) := (BstLean.Part50.binghamA_antipodal hn1 (rk1 t v)).sph
  have hc4 : Continuous (fun x : Fin n → ℝ => (∑ i, v i * x i) ^ 4) := by fun_prop
  have hc2 : Continuous (fun x : Fin n → ℝ => 1 / 2 * (∑ i, v i * x i) ^ 2) := by fun_prop
  have hT := transfer80 n hn1 v hv t ht0 htn
    (fun x => (∑ i, v i * x i) ^ 4 - 1 / 2 * (∑ i, v i * x i) ^ 2) (hc4.sub hc2)
    (1 / (2 * (n : ℝ))) (by
      intro K
      rw [integral_sub (BstLean.Part69.surr_int69 hn K t ht0 v hc4)
        (BstLean.Part69.surr_int69 hn K t ht0 v hc2), integral_const_mul]
      have ha := BstLean.Part69.I_s2_69 hn K t ht0 v hv
      have hb := BstLean.Part69.I_s4_69 hn K t ht0 v hv
      unfold sv69 at ha hb
      rw [ha, hb]
      exact b69_le80 n hn1 K t ht0 htn)
  rw [integral_sub (BstLean.Part56.integrable_cont_sph56 hD hc4)
    (BstLean.Part56.integrable_cont_sph56 hD hc2), integral_const_mul] at hT
  linarith

/-- Sharp second-moment bound: `E_D s² ≤ 1/2 + 1/n`. -/
theorem pLowRK_sharp (n : ℕ) (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (t : ℝ)
    (ht0 : 0 ≤ t) (htn : t ≤ n) :
    ∫ x, (∑ i, v i * x i) ^ 2 ∂lawRK n t v ≤ 1 / 2 + 1 / (n : ℝ) := by
  apply transfer80 n (by omega) v hv t ht0 htn (fun x => (∑ i, v i * x i) ^ 2) (by fun_prop)
  intro K
  have ha := BstLean.Part69.I_s2_69 hn K t ht0 v hv
  unfold sv69 at ha
  rw [ha]
  exact a69_le80 n hn v hv K t ht0 htn

theorem pLow4RK (n : ℕ) (hn : 2 ≤ n) : PLow4RK n := by
  intro v hv t ht0 htn
  have h := pLow4RK_sharp n hn v hv t ht0 htn
  have hnpos : (0 : ℝ) < n := by positivity
  have h0 : 0 ≤ ∫ x, (∑ i, v i * x i) ^ 2 ∂lawRK n t v :=
    integral_nonneg fun x => sq_nonneg _
  have h1 : 1 / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
    apply one_div_le_one_div_of_le hnpos; linarith
  linarith

end BstLean.Part80

#print axioms BstLean.Part80.pLow4RK
#print axioms BstLean.Part80.pLowRK_sharp
