import BstLean.Part80Defs
import BstLean.Part61Sur_Bias
import BstLean.Part61LemmaS_Centering
import BstLean.Part56MomProg_Basic
import BstLean.Part56Weights
import BstLean.Part50Laws
import BstLean.Part69Weights
import BstLean.Part69Prog
import BstLean.Part58Tilt

/-!
# Part 80: the second moment of `s = v·x` for `t ∈ [0, n]`: `E_D s² ≤ 41/80 + 2/n`

Route through the Taylor surrogate `Q = surrRK n K t v`: `E_Q s² = a69`, `E_Q s⁴ = b69`, the
finite-sum Stein identity `n Z₁ − Z₀ + 2t (Z₂ − Z₁) = 2t (t^K/K!) (U_{K+2} − U_{K+1}) ≤ 0`, Jensen
`a² ≤ b`, hence `a ≤ 1/2 + 1/n`; then transfer to `D` by the surrogate bias bound at `e = 1/2`
(`etaQ (1/2) = 1/40`) with `Var_D s² ≤ 1/4`.
-/

namespace BstLean.Part80

open MeasureTheory
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part56 (UnitV lawRK surrRK KRK rk1)
open BstLean.Part69 (U69 Z69 a69 b69 sv69)
open BstLean.Part61 (sx61 s2mom61)

lemma U69_nonneg80 (n j : ℕ) : 0 ≤ U69 n j := by
  unfold U69
  exact Finset.prod_nonneg fun i _ => by positivity

lemma U69_anti80 (n : ℕ) (hn : 1 ≤ n) (j : ℕ) : U69 n (j + 1) ≤ U69 n j := by
  rw [BstLean.Part69.U69_succ]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ) + 2 * (j : ℝ) := by positivity
  have : (2 * (j : ℝ) + 1) / ((n : ℝ) + 2 * (j : ℝ)) ≤ 1 := by
    rw [div_le_one hd]; linarith
  exact mul_le_of_le_one_right (U69_nonneg80 n j) this

/-- The finite-sum Stein identity with remainder. -/
lemma stein80 (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (K : ℕ) :
    (n : ℝ) * Z69 n K t 1 - Z69 n K t 0 + 2 * t * (Z69 n K t 2 - Z69 n K t 1) =
      2 * t * (t ^ K / (K.factorial : ℝ)) * (U69 n (K + 2) - U69 n (K + 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  induction K with
  | zero =>
    have h1 : U69 n 1 = 1 / (n : ℝ) := by
      have := BstLean.Part69.U69_succ n 0
      simp [U69] at this ⊢
    have h0 : U69 n 0 = 1 := by simp [U69]
    simp only [Z69, zero_add, Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, one_mul, h0, h1]
    field_simp
    ring
  | succ K ih =>
    rw [BstLean.Part69.Z69_succ n K t 1, BstLean.Part69.Z69_succ n K t 0,
      BstLean.Part69.Z69_succ n K t 2]
    have hU := BstLean.Part69.U69_succ n (K + 1)
    have hd : ((n : ℝ) + 2 * ((K + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hU' : ((n : ℝ) + 2 * ((K : ℝ) + 1)) * U69 n (K + 2) =
        (2 * ((K : ℝ) + 1) + 1) * U69 n (K + 1) := by
      rw [hU]; push_cast at hd ⊢; field_simp
    have hf : ((K + 1).factorial : ℝ) = ((K : ℝ) + 1) * (K.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hK : (K.factorial : ℝ) ≠ 0 := by positivity
    have hK1 : ((K : ℝ) + 1) ≠ 0 := by positivity
    have hc : t ^ (K + 1) / ((K + 1).factorial : ℝ) * ((K : ℝ) + 1) =
        t * (t ^ K / (K.factorial : ℝ)) := by
      rw [hf, pow_succ]; field_simp
    simp only [show K + 1 + 1 = K + 2 from rfl, show K + 1 + 0 = K + 1 from rfl,
      show K + 1 + 2 = K + 3 from rfl]
    set c := t ^ K / (K.factorial : ℝ)
    set c' := t ^ (K + 1) / ((K + 1).factorial : ℝ)
    have e1 : c' * ((n : ℝ) * U69 n (K + 2) - U69 n (K + 1)) =
        2 * (t * c) * (U69 n (K + 1) - U69 n (K + 2)) := by
      rw [← hc]
      have : (n : ℝ) * U69 n (K + 2) =
          (2 * ((K : ℝ) + 1) + 1) * U69 n (K + 1) - 2 * ((K : ℝ) + 1) * U69 n (K + 2) := by
        linarith
      rw [this]; ring
    linear_combination ih + e1

/-- The surrogate second moment: `a69 ≤ 1/2 + 1/n` for `0 ≤ t ≤ n`. -/
lemma a69_le80 (n : ℕ) (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (K : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (htn : t ≤ n) : a69 n K t ≤ 1 / 2 + 1 / (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hQ : SphLaw n (surrRK n K t v) := BstLean.Part56.MomProg.surrRK_sphLaw hn1 K t ht0 v
  have := hQ.prob
  have ha : ∫ x, sx61 v x ^ 2 ∂surrRK n K t v = a69 n K t :=
    BstLean.Part69.I_s2_69 hn K t ht0 v hv
  have hb : ∫ x, sx61 v x ^ 4 ∂surrRK n K t v = b69 n K t :=
    BstLean.Part69.I_s4_69 hn K t ht0 v hv
  have hr := BstLean.Part61.Concentration.moment_range hQ v hv
  rw [show s2mom61 (surrRK n K t v) v = a69 n K t from ha] at hr
  -- Jensen: a² ≤ b
  have hjen : a69 n K t ^ 2 ≤ b69 n K t := by
    have hid := BstLean.Part61.Concentration.centered_square_identity hQ v 0
    rw [show s2mom61 (surrRK n K t v) v = a69 n K t from ha] at hid
    have h4 : ∫ x, (sx61 v x ^ 2 - 0) ^ 2 ∂surrRK n K t v = b69 n K t := by
      rw [← hb]; congr 1; ext x; ring
    have hnn : 0 ≤ ∫ x, (sx61 v x ^ 2 - a69 n K t) ^ 2 ∂surrRK n K t v :=
      integral_nonneg fun x => sq_nonneg _
    rw [h4] at hid
    nlinarith
  -- Stein
  have hZ : 1 ≤ Z69 n K t 0 := BstLean.Part69.Z0_pos69 K t ht0
  have hZ0 : (0 : ℝ) < Z69 n K t 0 := by linarith
  have hst := stein80 n hn1 t K
  have hrem : 2 * t * (t ^ K / (K.factorial : ℝ)) * (U69 n (K + 2) - U69 n (K + 1)) ≤ 0 := by
    have := U69_anti80 n hn1 (K + 1)
    have hc : 0 ≤ 2 * t * (t ^ K / (K.factorial : ℝ)) := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hc (by linarith)
  have hS : (n : ℝ) * a69 n K t - 1 + 2 * t * (b69 n K t - a69 n K t) ≤ 0 := by
    have : (n : ℝ) * a69 n K t - 1 + 2 * t * (b69 n K t - a69 n K t) =
        ((n : ℝ) * Z69 n K t 1 - Z69 n K t 0 + 2 * t * (Z69 n K t 2 - Z69 n K t 1)) /
          Z69 n K t 0 := by
      unfold a69 b69; field_simp
    rw [this, hst]
    exact div_nonpos_of_nonpos_of_nonneg hrem hZ0.le
  set a := a69 n K t
  set b := b69 n K t
  -- n a ≤ 1 + 2 t (a - b) ≤ 1 + 2 t (a - a²) ≤ 1 + 2 n (a - a²)
  have h1 : (n : ℝ) * a ≤ 1 + 2 * (n : ℝ) * (a - a ^ 2) := by
    have haa : 0 ≤ a - a ^ 2 := by nlinarith [hr.1, hr.2]
    have : t * (a - b) ≤ (n : ℝ) * (a - a ^ 2) := by
      calc t * (a - b) ≤ t * (a - a ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ ht0; linarith
        _ ≤ (n : ℝ) * (a - a ^ 2) := mul_le_mul_of_nonneg_right htn haa
    linarith
  have h2 : 2 * a ^ 2 - a - 1 / (n : ℝ) ≤ 0 := by
    have : (n : ℝ) * (2 * a ^ 2 - a - 1 / (n : ℝ)) ≤ 0 := by
      have : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
      nlinarith
    by_contra hcon
    push Not at hcon
    nlinarith
  by_contra hcon
  push Not at hcon
  have hinv : 0 < 1 / (n : ℝ) := by positivity
  nlinarith [hr.1]

theorem pLowRK (n : ℕ) (hn : 2 ≤ n) : PLowRK n := by
  intro v hv t ht0 htn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hD : SphLaw n (lawRK n t v) := (BstLean.Part50.binghamA_antipodal hn1 (rk1 t v)).sph
  have := hD.prob
  have hc : Continuous (fun x : Fin n → ℝ => sx61 v x ^ 2) := by unfold sx61; fun_prop
  have hbias := BstLean.Part61.surrogate_continuous_sq_bias61 hn1 1 (1 / 2) t (by norm_num) ht0
    (by simpa using htn) v hv (fun x => sx61 v x ^ 2) hc
  have heta : BstLean.Part43.etaQ (1 / 2) = 1 / 40 := by
    unfold BstLean.Part43.etaQ BstLean.Part43.xi43
    rw [min_eq_left (by norm_num)]; norm_num
  have ha : ∫ x, sx61 v x ^ 2 ∂surrRK n (KRK 1 n (1 / 2)) t v = a69 n (KRK 1 n (1 / 2)) t :=
    BstLean.Part69.I_s2_69 hn _ t ht0 v hv
  have hale := a69_le80 n hn v hv (KRK 1 n (1 / 2)) t ht0 htn
  -- Var_D s² ≤ 1/4
  have hvar : varU (lawRK n t v) (fun x => sx61 v x ^ 2) ≤ 1 / 4 := by
    have hid := BstLean.Part61.Concentration.centered_square_identity hD v (1 / 2)
    have hle : ∫ x, (sx61 v x ^ 2 - 1 / 2) ^ 2 ∂lawRK n t v ≤ ∫ _x, (1 / 4 : ℝ) ∂lawRK n t v := by
      apply integral_mono_ae
      · exact BstLean.Part56.integrable_cont_sph56 hD (by unfold sx61; fun_prop)
      · exact integrable_const _
      · filter_upwards [hD.sphere] with x hx
        have hy := BstLean.Part58.yv_bound (v := v) hv hx
        have hy' : 0 ≤ sx61 v x ^ 2 ∧ sx61 v x ^ 2 ≤ 1 := hy
        show (sx61 v x ^ 2 - 1 / 2) ^ 2 ≤ 1 / 4
        nlinarith [hy'.1, hy'.2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
    have : varU (lawRK n t v) (fun x => sx61 v x ^ 2) =
        ∫ x, (sx61 v x ^ 2 - s2mom61 (lawRK n t v) v) ^ 2 ∂lawRK n t v := rfl
    rw [this]
    nlinarith [sq_nonneg (s2mom61 (lawRK n t v) v - 1 / 2)]
  rw [heta, ha] at hbias
  show ∫ x, sx61 v x ^ 2 ∂lawRK n t v ≤ 41 / 80 + 2 / (n : ℝ)
  set m := ∫ x, sx61 v x ^ 2 ∂lawRK n t v
  set a := a69 n (KRK 1 n (1 / 2)) t
  have hsq : (a - m) ^ 2 ≤ (1 / 80) ^ 2 := by nlinarith
  have habs := abs_le_of_sq_le_sq' hsq (by norm_num)
  have h2n : 2 / (n : ℝ) = 1 / (n : ℝ) + 1 / (n : ℝ) := by ring
  have hinv : 0 < 1 / (n : ℝ) := by positivity
  linarith [habs.1, habs.2]

end BstLean.Part80

#print axioms BstLean.Part80.pLowRK
