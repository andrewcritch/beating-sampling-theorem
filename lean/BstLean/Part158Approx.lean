import BstLean.Part158Approx2

/-!
# Part 158 (file `Approx`): the inequality `GaussGP` from its form for differentiable functions

Do not use `sorry`, `native_decide` or `axiom`.

* **`gaussGP_of_smooth`**: `GPSmoothStmt → BstLean.Part157.GaussGP`. The inputs with `e x = 0`
  give the same constant factor on both sides; on the other inputs apply `gp_meas_of_smooth` to
  the restricted measure.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134

theorem gaussGP_of_smooth (h : GPSmoothStmt) : BstLean.Part157.GaussGP := by
  intro N q m μ hμ e he hunit f hf a b ha hfa hfb hinact L hL hframe
  have := hμ
  have fpos : ∀ y, 0 < f y := fun y => lt_of_lt_of_le ha (hfa y)
  have logB : ∀ y, |log (f y)| ≤ |log a| + |log b| := by
    intro y
    have g1 := Real.log_le_log ha (hfa y)
    have g2 := Real.log_le_log (fpos y) (hfb y)
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (log a), abs_nonneg (log b)]
    · linarith [le_abs_self (log b), abs_nonneg (log a)]
  have mK : ∀ (e : (Fin N → ℝ) → Fin m → ℝ), Measurable e → ∀ G : Matrix (Fin q) (Fin m) ℝ,
      Measurable (fun x : Fin N → ℝ => log (f (x, G.mulVec (e x)))) := by
    intro e he G
    exact (hf.comp (measurable_id.prodMk (measurable_mulVec_joint.comp
      (measurable_const.prodMk he)))).log
  have mE : Measurable (fun x : Fin N → ℝ => ∫ z, f (x, z) ∂stdGauss (Fin q)) :=
    (hf.stronglyMeasurable.integral_prod_right').measurable
  have Eb : ∀ x : Fin N → ℝ, a ≤ ∫ z, f (x, z) ∂stdGauss (Fin q) ∧
      ∫ z, f (x, z) ∂stdGauss (Fin q) ≤ b := by
    intro x
    have i : Integrable (fun z => f (x, z)) (stdGauss (Fin q)) :=
      integrable_of_bdd (B := |a| + |b|) (hf.comp measurable_prodMk_left) fun z => by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le a, abs_nonneg b, hfa (x, z)]
        · linarith [le_abs_self b, abs_nonneg a, hfb (x, z)]
    have h1 := integral_mono (integrable_const a) i (fun z => hfa (x, z))
    have h2 := integral_mono i (integrable_const b) (fun z => hfb (x, z))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1 h2
    exact ⟨h1, h2⟩
  have iE : Integrable (fun x : Fin N → ℝ => log (∫ z, f (x, z) ∂stdGauss (Fin q))) μ := by
    refine integrable_of_bdd (B := |log a| + |log b|) mE.log fun x => ?_
    obtain ⟨a1, c1⟩ := Eb x
    have g1 := Real.log_le_log ha a1
    have g2 := Real.log_le_log (lt_of_lt_of_le ha a1) c1
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (log a), abs_nonneg (log b)]
    · linarith [le_abs_self (log b), abs_nonneg (log a)]
  have Econst : ∀ x, e x = 0 → ∫ z, f (x, z) ∂stdGauss (Fin q) = f (x, 0) := by
    intro x hx
    simp_rw [hinact x hx]
    simp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have e0 : ∀ x, e x = 0 := fun x => funext fun j => j.elim0
    have h1 : ∀ G : Matrix (Fin q) (Fin 0) ℝ,
        ∫ x, log (f (x, G.mulVec (e x))) ∂μ =
          ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ := by
      intro G
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change log (f (x, G.mulVec (e x))) = log (∫ z, f (x, z) ∂stdGauss (Fin q))
      rw [Econst x (e0 x), hinact x (e0 x)]
    simp_rw [h1]
    simp
  · have : NeZero m := ⟨hm.ne'⟩
    set e0 : Fin m → ℝ := Pi.single 0 1 with he0
    have e0u : normSq e0 = 1 := by
      simp [normSq, he0, Pi.single_apply]
    set S : Set (Fin N → ℝ) := {x | e x = 0}ᶜ with hS
    have mZ : MeasurableSet {x | e x = 0} := he (measurableSet_singleton 0)
    have mS : MeasurableSet S := mZ.compl
    set e' : (Fin N → ℝ) → Fin m → ℝ := fun x => if e x = 0 then e0 else e x with he'
    have me' : Measurable e' := Measurable.ite mZ measurable_const he
    have e'u : ∀ x, normSq (e' x) = 1 := by
      intro x
      simp only [he']
      split_ifs with hx
      · exact e0u
      · rcases hunit x with h1 | h1
        · exact h1
        · exact absurd h1 hx
    have e'S : ∀ x ∈ S, e' x = e x := by
      intro x hx
      have : ¬ e x = 0 := hx
      simp [he', this]
    have eSc : ∀ x ∈ Sᶜ, e x = 0 := by
      intro x hx
      rw [hS, compl_compl] at hx
      exact hx
    have hframe' : ∀ w : Fin m → ℝ,
        ∫ x, (∑ j, e' x j * w j) ^ 2 ∂μ.restrict S ≤ L * ∑ j, w j ^ 2 := by
      intro w
      have h1 : ∫ x in S, (∑ j, e' x j * w j) ^ 2 ∂μ = ∫ x in S, (∑ j, e x j * w j) ^ 2 ∂μ :=
        setIntegral_congr_fun mS fun x hx => by
          rw [e'S x hx]
      have h2 : ∫ x in S, (∑ j, e x j * w j) ^ 2 ∂μ = ∫ x, (∑ j, e x j * w j) ^ 2 ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have : e x = 0 := by
            by_contra h0; exact hx h0
          simp [this]
      rw [h1, h2]
      exact hframe w
    have key := gp_meas_of_smooth h (μ.restrict S) e' me' e'u f hf ha hfa hfb hL hframe'
    set c0 := ∫ x in Sᶜ, log (f (x, 0)) ∂μ with hc0
    have hl : ∀ G : Matrix (Fin q) (Fin m) ℝ, ∫ x, log (f (x, G.mulVec (e x))) ∂μ =
        ∫ x, log (f (x, G.mulVec (e' x))) ∂μ.restrict S + c0 := by
      intro G
      have i : Integrable (fun x => log (f (x, G.mulVec (e x)))) μ :=
        integrable_of_bdd (mK e he G) fun x => logB _
      rw [← integral_add_compl mS i]
      congr 1
      · exact setIntegral_congr_fun mS fun x hx => by
          rw [e'S x hx]
      · exact setIntegral_congr_fun mS.compl fun x hx => by
          rw [hinact x (eSc x hx)]
    have hr : ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ =
        ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ.restrict S + c0 := by
      rw [← integral_add_compl mS iE]
      congr 1
      exact setIntegral_congr_fun mS.compl fun x hx => by
        rw [Econst x (eSc x hx)]
    simp_rw [hl]
    rw [hr]
    simp_rw [mul_add, Real.exp_add]
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right key (exp_pos _).le

end BstLean.Part158

open BstLean.Part158 in
#print axioms gaussGP_of_smooth
