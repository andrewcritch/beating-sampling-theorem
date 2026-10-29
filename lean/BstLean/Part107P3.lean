import BstLean.Part107P3c

/-!
# Part 107 (P3): `Var(ψ(a) | r) ≤ c (2 + 2|r|)/(n − 2)`

From the Gaussian Poincaré inequality (`Poincare107`), `E|g|⁻² ≤ 1/(n−2)` (`InvMom107`) and the
null set of the parallel pairs (`NullPar107`).
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part105

variable {n : ℕ}

lemma measurable_gL : Measurable (gL (n := n)) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply (Sum.inl i)

lemma mpL : MeasurePreserving (gL (n := n)) (stdGauss (Fin n ⊕ Fin n)) (stdGauss (Fin n)) :=
  ⟨measurable_gL, BstLean.Part29.stdGauss_map_restrict Sum.inl Sum.inl_injective⟩

lemma mpE : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ))
    (stdGauss (Fin n ⊕ Fin n)) (gg n) :=
  measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1)

lemma eE_apply (w : Fin n ⊕ Fin n → ℝ) :
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ) w = (gL w, hL w) := rfl

lemma mpR {r : ℝ} (hr : |r| ≤ 1) :
    MeasurePreserving (gR (n := n) r) (stdGauss (Fin n ⊕ Fin n)) (stdGauss (Fin n)) := by
  have h := (ou_mp_snd (ι := Fin n) hr).comp mpE
  have e : (fun w : (Fin n → ℝ) × (Fin n → ℝ) => r • w.1 + sC r • w.2) ∘
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)) = gR r := by
    funext w
    simp only [Function.comp_apply, eE_apply, gR_eq]
  rwa [e] at h

lemma gL_comb (a b : ℝ) (w z : Fin n ⊕ Fin n → ℝ) : gL (a • w + b • z) = a • gL w + b • gL z := by
  funext i
  simp [gL]

lemma gR_comb (r a b : ℝ) (w z : Fin n ⊕ Fin n → ℝ) :
    gR r (a • w + b • z) = a • gR r w + b • gR r z := by
  funext i
  simp [gR]
  ring

lemma path_ae (hN : NullPar107) (hn : 3 ≤ n) {r : ℝ} (hr : |r| ≤ 1) :
    ∀ᵐ p ∂(stdGauss (Fin n ⊕ Fin n)).prod (stdGauss (Fin n ⊕ Fin n)),
      ∀ θ : ℝ, Real.cos θ • p.1 + Real.sin θ • p.2 ∈ Uset r := by
  have h1 := (mpL (n := n)).prod (mpL (n := n)) |>.quasiMeasurePreserving.ae (hN n (by omega))
  have h2 := (mpR (n := n) hr).prod (mpR (n := n) hr) |>.quasiMeasurePreserving.ae
    (hN n (by omega))
  filter_upwards [h1, h2] with p hp1 hp2 θ
  refine ⟨(Af_ne_zero_iff _).2 ?_, (Bf_ne_zero_iff _ _).2 ?_⟩
  · rw [gL_comb]
    exact hp1 θ
  · rw [gR_comb]
    exact hp2 θ

lemma measurable_invsq : Measurable (fun g : Fin n → ℝ => 1 / ∑ i, g i ^ 2) :=
  measurable_const.div (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)

lemma inv_Af_eq : (fun w : Fin n ⊕ Fin n → ℝ => 1 / Af w) =
    (fun g : Fin n → ℝ => 1 / ∑ i, g i ^ 2) ∘ gL := by
  funext w
  simp only [Function.comp_apply, Af_eq]

lemma inv_Bf_eq (r : ℝ) : (fun w : Fin n ⊕ Fin n → ℝ => 1 / Bf r w) =
    (fun g : Fin n → ℝ => 1 / ∑ i, g i ^ 2) ∘ gR r := by
  funext w
  simp only [Function.comp_apply, Bf_eq]

lemma Gam_bound (hI : InvMom107) (hn : 3 ≤ n) {r cκ : ℝ} (hr : |r| ≤ 1) (hc : 0 ≤ cκ) :
    Integrable (Gam (n := n) cκ r) (stdGauss (Fin n ⊕ Fin n)) ∧
      ∫ w, Gam (n := n) cκ r w ∂stdGauss (Fin n ⊕ Fin n) ≤
        cκ * (2 + 2 * |r|) / ((n : ℝ) - 2) := by
  obtain ⟨hint, hle⟩ := hI n hn
  have hm := (measurable_invsq (n := n)).aestronglyMeasurable (μ := stdGauss (Fin n))
  have iA : Integrable (fun w : Fin n ⊕ Fin n → ℝ => 1 / Af w) (stdGauss (Fin n ⊕ Fin n)) := by
    rw [inv_Af_eq]
    exact (mpL.integrable_comp hm).2 hint
  have iB : Integrable (fun w : Fin n ⊕ Fin n → ℝ => 1 / Bf r w) (stdGauss (Fin n ⊕ Fin n)) := by
    rw [inv_Bf_eq]
    exact ((mpR hr).integrable_comp hm).2 hint
  have eA : ∫ w : Fin n ⊕ Fin n → ℝ, 1 / Af w ∂stdGauss (Fin n ⊕ Fin n) =
      ∫ g : Fin n → ℝ, 1 / ∑ i, g i ^ 2 ∂stdGauss (Fin n) := by
    rw [inv_Af_eq]
    exact mp_integral_ae mpL hm
  have eB : ∫ w : Fin n ⊕ Fin n → ℝ, 1 / Bf r w ∂stdGauss (Fin n ⊕ Fin n) =
      ∫ g : Fin n → ℝ, 1 / ∑ i, g i ^ 2 ∂stdGauss (Fin n) := by
    rw [inv_Bf_eq]
    exact mp_integral_ae (mpR hr) hm
  refine ⟨(iA.add iB).const_mul _, ?_⟩
  unfold Gam
  rw [integral_const_mul, integral_add iA iB, eA, eB]
  have hk : 0 ≤ cκ * (1 + |r|) := mul_nonneg hc (by positivity)
  calc cκ * (1 + |r|) * ((∫ g : Fin n → ℝ, 1 / ∑ i, g i ^ 2 ∂stdGauss (Fin n)) +
        ∫ g : Fin n → ℝ, 1 / ∑ i, g i ^ 2 ∂stdGauss (Fin n))
      ≤ cκ * (1 + |r|) * (1 / ((n : ℝ) - 2) + 1 / ((n : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hle hle) hk
    _ = cκ * (2 + 2 * |r|) / ((n : ℝ) - 2) := by ring

/-- **(P3)** -/
theorem p3_107 (hP : Poincare107) (hI : InvMom107) (hN : NullPar107) : P3_107 := by
  intro n r cκ ψ ψ' hn hr hψ hcont hb
  have hc : 0 ≤ cκ := by
    have := hb 0 (by simp)
    nlinarith [sq_nonneg (ψ' 0)]
  obtain ⟨hGi, hGle⟩ := Gam_bound (n := n) hI hn hr hc
  have key := hP (Fin n ⊕ Fin n) (fun w => ψ (qf r w)) (Uset r) (Gam cκ r) (isOpen_Uset r)
    (contDiffOn_f hψ hcont r) (measurable_f hψ r) (memLp_f hψ r) hGi
    (fun w hw => grad_bound hr hψ hb hw) (path_ae hN hn hr)
  have e1 : ∫ q, ψ (aR r q) ∂gg n = ∫ w, ψ (qf r w) ∂stdGauss (Fin n ⊕ Fin n) := by
    rw [← (mpE (n := n)).integral_comp' (fun q => ψ (aR r q))]
    simp only [eE_apply, aR_eq]
  have e2 : ∫ p, (ψ (aR r p) - ∫ q, ψ (aR r q) ∂gg n) ^ 2 ∂gg n =
      ∫ w, (ψ (qf r w) - ∫ y, ψ (qf r y) ∂stdGauss (Fin n ⊕ Fin n)) ^ 2
        ∂stdGauss (Fin n ⊕ Fin n) := by
    rw [e1, ← (mpE (n := n)).integral_comp'
      (fun p => (ψ (aR r p) - ∫ y, ψ (qf r y) ∂stdGauss (Fin n ⊕ Fin n)) ^ 2)]
    simp only [eE_apply, aR_eq]
  rw [e2]
  exact key.trans hGle

#print axioms p3_107

end BstLean.Part107
