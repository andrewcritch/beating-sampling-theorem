import BstLean.Part158Defs

/-!
# Part 158 (file `Ibp`): Gaussian integration by parts along the rotated pair

Do not use `sorry`, `native_decide` or `axiom`.

* `stein_gen`: Stein's identity in one coordinate of a standard Gaussian vector, for every finite
  index type.
* `ibp_star`: `E [W(ξ) A(cξ + sξ') (−s ξ_k + c ξ'_k)] = −s E [∂_k W(ξ) A(cξ + sξ')]` for
  `c² + s² = 1` and independent standard Gaussian vectors `ξ`, `ξ'`.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)

/-- Stein's identity in one coordinate, any finite index type. -/
theorem stein_gen {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι) {Φ Φ' : (ι → ℝ) → ℝ}
    (hΦ : Measurable Φ) (hΦ' : Measurable Φ')
    (hd : ∀ ζ, HasDerivAt (fun t => Φ (Function.update ζ k t)) (Φ' ζ) (ζ k)) {C : ℝ}
    (hb : ∀ ζ, |Φ ζ| ≤ C) (hb' : ∀ ζ, |Φ' ζ| ≤ C) :
    ∫ ζ, ζ k * Φ ζ ∂stdGauss ι = ∫ ζ, Φ' ζ ∂stdGauss ι := by
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨k⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by omega⟩
  set e : ι ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hn with he
  set P := MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) => ℝ) e with hP
  have hp : MeasurePreserving P (stdGauss ι) (stdGauss (Fin (n + 1))) := by
    unfold stdGauss
    exact measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => gaussianReal 0 1) e
  have hPa : ∀ (Z : ι → ℝ) (j : Fin (n + 1)), P Z j = Z (e.symm j) := by
    intro Z j
    obtain ⟨i, rfl⟩ := e.surjective j
    rw [Equiv.symm_apply_apply]
    exact Equiv.piCongrLeft_apply_apply (P := fun _ : Fin (n + 1) => ℝ) e Z i
  have hsym : ∀ ω : Fin (n + 1) → ℝ, P.symm ω = fun i => ω (e i) := by
    intro ω
    apply P.injective
    rw [MeasurableEquiv.apply_symm_apply]
    funext j
    rw [hPa]
    simp
  have me : Measurable (fun ω : Fin (n + 1) → ℝ => fun i : ι => ω (e i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
  have E1 := hp.symm.integral_comp' (fun ζ : ι → ℝ => ζ k * Φ ζ)
  have E2 := hp.symm.integral_comp' Φ'
  rw [← E1, ← E2]
  simp only [hsym]
  refine BstLean.Part152.stein_coord (e k) (Φ := fun ω => Φ fun i => ω (e i))
    (Φ' := fun ω => Φ' fun i => ω (e i)) (hΦ.comp me) (hΦ'.comp me) (fun ω => ?_)
    (fun ω => hb _) (fun ω => hb' _)
  have h := hd (fun i => ω (e i))
  have hu : ∀ t : ℝ, (fun i => Function.update ω (e k) t (e i)) =
      Function.update (fun i => ω (e i)) k t := by
    intro t
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · have : e i ≠ e k := fun h' => hi (e.injective h')
      simp [Function.update_of_ne hi, Function.update_of_ne this]
  simp only [hu]
  exact h

/-- Integration by parts along the rotated pair. -/
theorem ibp_star {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    {W dW A : (ι → ℝ) → ℝ} (mW : Measurable W) (mdW : Measurable dW) (mA : Measurable A)
    (hd : ∀ ξ, HasDerivAt (fun t => W (Function.update ξ k t)) (dW ξ) (ξ k))
    {C : ℝ} (hW : ∀ ξ, |W ξ| ≤ C) (hdW : ∀ ξ, |dW ξ| ≤ C) (hA : ∀ ξ, |A ξ| ≤ C) :
    ∫ ξ, W ξ * ∫ ξ', A (c • ξ + s • ξ') * (-s * ξ k + c * ξ' k) ∂stdGauss ι ∂stdGauss ι =
      -s * ∫ ξ, dW ξ * ∫ ξ', A (c • ξ + s • ξ') ∂stdGauss ι ∂stdGauss ι := by
  set γ := stdGauss ι with hγ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hW 0)
  set R := BstLean.Part148.rotP (ι := ι) c s with hRdef
  have hR : MeasurePreserving R (γ.prod γ) (γ.prod γ) := BstLean.Part148.rotP_preserving hcs
  have mlin : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => c • p.1 + s • p.2) := by fun_prop
  have R1 : ∀ p : (ι → ℝ) × (ι → ℝ), (R p).1 = c • p.1 + s • p.2 := fun p => rfl
  have R2 : ∀ p : (ι → ℝ) × (ι → ℝ), (R p).2 k = s * p.1 k - c * p.2 k := fun p => by
    simp [hRdef, BstLean.Part148.rotP]
  have R3 : ∀ p : (ι → ℝ) × (ι → ℝ), c • (R p).1 + s • (R p).2 = p.1 := fun p => by
    funext i
    simp only [hRdef, BstLean.Part148.rotP, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]
    linear_combination (p.1 i) * hcs
  -- the two functions on the product
  set H : (ι → ℝ) × (ι → ℝ) → ℝ := fun p => -(A p.1 * (p.2 k * W (c • p.1 + s • p.2))) with hH
  set K : (ι → ℝ) × (ι → ℝ) → ℝ := fun p => -s * (dW (c • p.1 + s • p.2) * A p.1) with hK
  have mH : Measurable H :=
    ((mA.comp measurable_fst).mul
      (((measurable_pi_apply k).comp measurable_snd).mul (mW.comp mlin))).neg
  have mK : Measurable K :=
    measurable_const.mul ((mdW.comp mlin).mul (mA.comp measurable_fst))
  have iH : Integrable H (γ.prod γ) := by
    have i0 : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => p.2 k) (γ.prod γ) :=
      (BstLean.Part152.integrable_coord (κ := ι) k).comp_snd γ
    refine Integrable.mono' (i0.norm.const_mul (C * C)) mH.aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [hH, norm_neg, norm_mul, Real.norm_eq_abs]
    have h1 := hA p.1
    have h2 := hW (c • p.1 + s • p.2)
    have h3 := abs_nonneg (p.2 k)
    calc |A p.1| * (|p.2 k| * |W (c • p.1 + s • p.2)|)
        ≤ C * (|p.2 k| * C) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 h3) (by positivity) hC
      _ = C * C * |p.2 k| := by ring
  have iK : Integrable K (γ.prod γ) := by
    refine Integrable.mono' (integrable_const (|s| * (C * C))) mK.aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [hK, norm_mul, norm_neg, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hdW _) (hA _) (abs_nonneg _) hC) (abs_nonneg _)
  have iHR : Integrable (H ∘ R) (γ.prod γ) :=
    (hR.integrable_comp mH.aestronglyMeasurable).mpr iH
  have iKR : Integrable (K ∘ R) (γ.prod γ) :=
    (hR.integrable_comp mK.aestronglyMeasurable).mpr iK
  have eHR : ∀ p : (ι → ℝ) × (ι → ℝ),
      (H ∘ R) p = W p.1 * (A (c • p.1 + s • p.2) * (-s * p.1 k + c * p.2 k)) := by
    intro p
    simp only [Function.comp_apply, hH]
    rw [R3, R2, R1]
    ring
  have eKR : ∀ p : (ι → ℝ) × (ι → ℝ),
      (K ∘ R) p = -s * (dW p.1 * A (c • p.1 + s • p.2)) := by
    intro p
    simp only [Function.comp_apply, hK]
    rw [R3, R1]
  have cv : ∀ G : (ι → ℝ) × (ι → ℝ) → ℝ, Measurable G →
      ∫ p, (G ∘ R) p ∂γ.prod γ = ∫ p, G p ∂γ.prod γ := by
    intro G mG
    have := integral_map (μ := γ.prod γ) hR.measurable.aemeasurable mG.aestronglyMeasurable
    rw [hR.map_eq] at this
    exact this.symm
  -- left side
  have L1 : ∫ ξ, W ξ * ∫ ξ', A (c • ξ + s • ξ') * (-s * ξ k + c * ξ' k) ∂γ ∂γ =
      ∫ p, (H ∘ R) p ∂γ.prod γ := by
    rw [integral_prod _ iHR]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [eHR]
    rw [integral_const_mul]
  have Rt : -s * ∫ ξ, dW ξ * ∫ ξ', A (c • ξ + s • ξ') ∂γ ∂γ = ∫ p, (K ∘ R) p ∂γ.prod γ := by
    rw [integral_prod _ iKR, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [eKR]
    rw [integral_const_mul, integral_const_mul]
  rw [L1, Rt, cv H mH, cv K mK, integral_prod _ iH, integral_prod _ iK]
  refine integral_congr_ae (ae_of_all _ fun α => ?_)
  simp only [hH, hK]
  have st := stein_gen k (Φ := fun β => W (c • α + s • β))
    (Φ' := fun β => s * dW (c • α + s • β))
    (C := max C (|s| * C))
    (mW.comp (by fun_prop)) (measurable_const.mul (mdW.comp (by fun_prop)))
    (fun β => ?_) (fun β => (hW _).trans (le_max_left _ _))
    (fun β => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hdW _) (abs_nonneg _)).trans (le_max_right _ _))
  · rw [integral_neg, integral_const_mul, st, integral_const_mul, integral_const_mul,
      integral_mul_const]
    ring
  · have hu : ∀ t : ℝ, c • α + s • Function.update β k t =
        Function.update (c • α + s • β) k (c * α k + s * t) := by
      intro t
      funext i
      by_cases hi : i = k
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    simp only [hu]
    have h0 := hd (c • α + s • β)
    have hin : HasDerivAt (fun t : ℝ => c * α k + s * t) s (β k) := by
      simpa using ((hasDerivAt_id (β k)).const_mul s).const_add (c * α k)
    have hval : (c • α + s • β) k = c * α k + s * β k := by simp
    rw [hval] at h0
    have := h0.comp (β k) hin
    simpa [Function.comp_def, mul_comm] using this

end BstLean.Part158

open BstLean.Part158 in
#print axioms stein_gen
open BstLean.Part158 in
#print axioms ibp_star
