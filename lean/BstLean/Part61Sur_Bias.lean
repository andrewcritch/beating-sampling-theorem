import BstLean.Part61Defs
import BstLean.Part56Surr
import BstLean.Part53Error_Specialize

namespace BstLean.Part61

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part37 (taylorExp)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Tens varU)
open BstLean.Part43 (etaQ)
open BstLean.Part50
open BstLean.Part56 (UnitV lawRK surrRK KRK rk1)

-- These declarations reuse the kernel-checked generic lemmas behind `surrA_bias`.
elab "sur61Imported" s:str : term => do
  let env ← Lean.getEnv
  let suffix := ".BstLean.Part50." ++ s.getString
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
    name.toString.startsWith "_private.BstLean.Part50Surr." &&
      name.toString.endsWith suffix)
    | throwError "Part50Surr declaration unavailable: {s.getString}"
  Lean.Elab.Term.elabTerm (Lean.mkIdent name) none

/-- The surrogate bias estimate applies to every continuous scalar function. -/
theorem surrogate_continuous_bias61 {n : ℕ} (hn : 1 ≤ n) (C e t : ℝ)
    (he : 0 < e) (ht0 : 0 ≤ t) (ht : t ≤ C * n)
    (v : Fin n → ℝ) (hv : UnitV v) (h : (Fin n → ℝ) → ℝ) (ch : Continuous h) :
    |(∫ x, h x ∂lawRK n t v) - (∫ x, h x ∂surrRK n (KRK C n e) t v)| ≤
      etaQ e * Real.sqrt (varU (lawRK n t v) h) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  let B := rk1 t v
  let K := KRK C n e
  have cq : Continuous (qA B) := (sur61Imported "continuous_qA") B
  have hc : Continuous (fun x => taylorExp K (qA B x)) := by
    unfold taylorExp
    fun_prop
  have hr : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 →
      0 ≤ qA B x ∧ qA B x ≤ C * n := by
    intro x hx
    exact ⟨(BstLean.Part56.qA_rk1_range t ht0 v hv x hx).1,
      (BstLean.Part56.qA_rk1_range t ht0 v hv x hx).2.trans ht⟩
  have hge : ∀ᵐ y ∂uniformSphere n, 1 ≤ taylorExp K (qA B y) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
    exact (sur61Imported "taylor_ge_one") K _ (hr y hy).1
  have hZ : 0 < ZKA n K B := by
    have hi : Integrable (fun x => taylorExp K (qA B x))
        (uniformSphere n) := (sur61Imported "sphere_cont_integrable") hn hc
    have hb := integral_mono_ae (integrable_const (1 : ℝ)) hi hge
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
    exact zero_lt_one.trans_le hb
  exact (sur61Imported "bias_from_ratioA") hn B K (etaQ e)
    (by unfold etaQ BstLean.Part43.xi43; positivity)
    (hge.mono fun x hx => zero_le_one.trans hx) hZ
    ((sur61Imported "surrogate_ratioA") hn B (C * n) hr e he) h ch

/-- Squared bias, in the orientation used by the surrogate rule. -/
theorem surrogate_continuous_sq_bias61 {n : ℕ} (hn : 1 ≤ n) (C e t : ℝ)
    (he : 0 < e) (ht0 : 0 ≤ t) (ht : t ≤ C * n)
    (v : Fin n → ℝ) (hv : UnitV v) (h : (Fin n → ℝ) → ℝ) (ch : Continuous h) :
    ((∫ x, h x ∂surrRK n (KRK C n e) t v) - (∫ x, h x ∂lawRK n t v)) ^ 2 ≤
      etaQ e ^ 2 * varU (lawRK n t v) h := by
  have hb := surrogate_continuous_bias61 hn C e t he ht0 ht v hv h ch
  have hv0 : 0 ≤ varU (lawRK n t v) h := integral_nonneg fun _ => sq_nonneg _
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs, mul_pow, Real.sq_sqrt hv0] at hs
  nlinarith

end BstLean.Part61
