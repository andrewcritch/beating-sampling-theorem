import BstLean.Part107P4a
import BstLean.Part107Aux

/-!
# Part 107, (P4): the Lipschitz bound of `r ↦ E[ψ(a) | r]`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere gaussMom gaussMom_eq)
open BstLean.Part105

variable {n : ℕ}

lemma coord_pow (i : Fin n) (k : ℕ) :
    Integrable (fun z : Fin n → ℝ => z i ^ k) (stdGauss (Fin n)) ∧
      ∫ z, z i ^ k ∂stdGauss (Fin n) = gaussMom k := by
  constructor
  · have h := BstLean.Part35.stdGauss_prod_integrable (ι := Fin n) k (fun _ => i)
    simpa using h
  · have hmp := measurePreserving_eval (μ := fun _ : Fin n => gaussianReal 0 1) i
    have h := integral_map (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (φ := Function.eval i) (measurable_pi_apply i).aemeasurable (f := fun x : ℝ => x ^ k)
      (measurable_id.pow_const k).aestronglyMeasurable
    rw [hmp.map_eq, gaussMom_eq] at h
    rw [h]
    rfl

lemma sumsq_comb (p q : ℝ) :
    Integrable (fun w : (Fin n → ℝ) × (Fin n → ℝ) => ∑ i, (p * w.1 i + q * w.2 i) ^ 2) (gg n) ∧
      ∫ w, ∑ i, (p * w.1 i + q * w.2 i) ^ 2 ∂gg n = (n : ℝ) * (p ^ 2 + q ^ 2) := by
  have m1 : gaussMom 1 = 0 := by simp [gaussMom]
  have m2 : gaussMom 2 = 1 := by simp [gaussMom]
  have m0 : gaussMom 0 = 1 := by simp [gaussMom]
  have e (w : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) : (p * w.1 i + q * w.2 i) ^ 2 =
      p ^ 2 * (w.1 i ^ 2 * w.2 i ^ 0) + 2 * p * q * (w.1 i ^ 1 * w.2 i ^ 1) +
        q ^ 2 * (w.1 i ^ 0 * w.2 i ^ 2) := by ring
  have hi (i : Fin n) (a b : ℕ) :
      Integrable (fun w : (Fin n → ℝ) × (Fin n → ℝ) => w.1 i ^ a * w.2 i ^ b) (gg n) :=
    (coord_pow i a).1.mul_prod (coord_pow i b).1
  have hv (i : Fin n) (a b : ℕ) :
      ∫ w : (Fin n → ℝ) × (Fin n → ℝ), w.1 i ^ a * w.2 i ^ b ∂gg n = gaussMom a * gaussMom b := by
    rw [integral_prod_mul (fun z : Fin n → ℝ => z i ^ a) (fun z : Fin n → ℝ => z i ^ b),
      (coord_pow i a).2, (coord_pow i b).2]
  have hterm (i : Fin n) : Integrable (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
      (p * w.1 i + q * w.2 i) ^ 2) (gg n) := by
    simp_rw [e]
    exact (((hi i 2 0).const_mul _).add ((hi i 1 1).const_mul _)).add ((hi i 0 2).const_mul _)
  refine ⟨integrable_finsetSum _ fun i _ => hterm i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hterm i]
  have hval (i : Fin n) : ∫ w : (Fin n → ℝ) × (Fin n → ℝ), (p * w.1 i + q * w.2 i) ^ 2 ∂gg n =
      p ^ 2 + q ^ 2 := by
    simp_rw [e]
    have i1 : Integrable (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
        p ^ 2 * (w.1 i ^ 2 * w.2 i ^ 0)) (gg n) := (hi i 2 0).const_mul _
    have i2 : Integrable (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
        2 * p * q * (w.1 i ^ 1 * w.2 i ^ 1)) (gg n) := (hi i 1 1).const_mul _
    have i3 : Integrable (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
        q ^ 2 * (w.1 i ^ 0 * w.2 i ^ 2)) (gg n) := (hi i 0 2).const_mul _
    have i12 : Integrable (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
        p ^ 2 * (w.1 i ^ 2 * w.2 i ^ 0) + 2 * p * q * (w.1 i ^ 1 * w.2 i ^ 1)) (gg n) := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, hv, hv, hv, m0, m1, m2]
    ring
  simp_rw [hval]
  simp
  ring

lemma p4_measurable_aR (r : ℝ) : Measurable (aR (n := n) r) := by
  unfold aR cosA
  exact measurable_dot2.comp ((measurable_sphProj.comp measurable_fst).prodMk
    (measurable_sphProj.comp (meas_comb r (sC r))))

theorem p4_107 (hI : InvMom107) (hZ : NonZero107) : P4_107 := by
  intro n r₁ r₂ rp Lip ψ hn h1 h1p h2 h2p hp hL hψ hLip
  have hr1 : |r₁| ≤ 1 := by rw [abs_of_nonneg h1]; linarith
  have hbd : ∀ a : ℝ, |a| ≤ 1 → |ψ a| ≤ |ψ 0| + Lip := by
    intro a ha
    have h0 := hLip a 0 ha (by simp)
    rw [sub_zero] at h0
    have h3 : |ψ a| ≤ |ψ 0| + |ψ a - ψ 0| := by
      have := abs_add_le (ψ 0) (ψ a - ψ 0)
      simpa using this
    nlinarith
  have hint : ∀ r : ℝ, Integrable (fun p => ψ (aR r p)) (gg n) := fun r =>
    Integrable.mono' (integrable_const (|ψ 0| + Lip)) (hψ.comp (p4_measurable_aR r)).aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs]; exact hbd _ (cosA_abs_le _ _))
  set D : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => ψ (aR r₁ p) - ψ (aR r₂ p) with hDdef
  set U : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p =>
    4 * Lip ^ 2 * ∑ i, ((r₁ - r₂) * p.1 i + (sC r₁ - sC r₂) * p.2 i) ^ 2 with hUdef
  set V : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p =>
    1 / ∑ i, (r₁ • p.1 + sC r₁ • p.2) i ^ 2 with hVdef
  have hD : Integrable D (gg n) := (hint r₁).sub (hint r₂)
  have hS := sumsq_comb (n := n) (r₁ - r₂) (sC r₁ - sC r₂)
  have hU : Integrable U (gg n) := hS.1.const_mul _
  have hUv : ∫ p, U p ∂gg n = 4 * Lip ^ 2 * ((n : ℝ) * ((r₁ - r₂) ^ 2 + (sC r₁ - sC r₂) ^ 2)) := by
    rw [hUdef, integral_const_mul, hS.2]
  have hmp := ou_mp_snd (ι := Fin n) hr1
  obtain ⟨hIi, hIv⟩ := hI n hn
  have hFm : Measurable (fun g : Fin n → ℝ => 1 / ∑ i, g i ^ 2) :=
    measurable_const.div (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)
  have hV : Integrable V (gg n) := (hmp.integrable_comp hFm.aestronglyMeasurable).2 hIi
  have hVv : ∫ p, V p ∂gg n ≤ 1 / ((n : ℝ) - 2) := by
    have := integral_map (μ := gg n) hmp.measurable.aemeasurable
      (f := fun g : Fin n → ℝ => 1 / ∑ i, g i ^ 2) hFm.aestronglyMeasurable
    rw [hmp.map_eq] at this
    rw [hVdef, ← this]
    exact hIv
  have hUnn : ∀ p, 0 ≤ U p := fun p =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hVnn : ∀ p, 0 ≤ V p := fun p =>
    div_nonneg zero_le_one (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hae : ∀ᵐ p ∂gg n, D p ^ 2 ≤ U p * V p := by
    filter_upwards [hmp.quasiMeasurePreserving.ae (hZ n (by omega))] with p hp
    have g1 := cosA_diff_sq p.1 (r₁ • p.1 + sC r₁ • p.2) (r₂ • p.1 + sC r₂ • p.2) hp
    have hs : ∑ i, ((r₁ • p.1 + sC r₁ • p.2) i - (r₂ • p.1 + sC r₂ • p.2) i) ^ 2 =
        ∑ i, ((r₁ - r₂) * p.1 i + (sC r₁ - sC r₂) * p.2 i) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs] at g1
    have g2 : |D p| ≤ Lip * |aR r₁ p - aR r₂ p| :=
      hLip _ _ (cosA_abs_le _ _) (cosA_abs_le _ _)
    have g3 : D p ^ 2 ≤ (Lip * |aR r₁ p - aR r₂ p|) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) g2 2
    have g4 : (Lip * |aR r₁ p - aR r₂ p|) ^ 2 = Lip ^ 2 * (aR r₁ p - aR r₂ p) ^ 2 := by
      rw [mul_pow, sq_abs]
    have g5 : Lip ^ 2 * (aR r₁ p - aR r₂ p) ^ 2 ≤ Lip ^ 2 *
        (4 * (∑ i, ((r₁ - r₂) * p.1 i + (sC r₁ - sC r₂) * p.2 i) ^ 2) *
          (1 / ∑ i, (r₁ • p.1 + sC r₁ • p.2) i ^ 2)) :=
      mul_le_mul_of_nonneg_left g1 (sq_nonneg _)
    calc D p ^ 2 ≤ Lip ^ 2 * (aR r₁ p - aR r₂ p) ^ 2 := g4 ▸ g3
      _ ≤ _ := g5
      _ = U p * V p := by rw [hUdef, hVdef]; ring
  have hcs := cs_sq (gg n) D U V hD hU hV hUnn hVnn hae
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hA := sC_diff h1 h1p h2 h2p hp
  rw [← integral_sub (hint r₁) (hint r₂)]
  have hUi : 0 ≤ ∫ p, U p ∂gg n := integral_nonneg hUnn
  have hc0 : 0 ≤ 4 * Lip ^ 2 * ((n : ℝ) / ((n : ℝ) - 2)) := by positivity
  calc (∫ p, D p ∂gg n) ^ 2 ≤ (∫ p, U p ∂gg n) * ∫ p, V p ∂gg n := hcs
    _ ≤ (∫ p, U p ∂gg n) * (1 / ((n : ℝ) - 2)) := mul_le_mul_of_nonneg_left hVv hUi
    _ = 4 * Lip ^ 2 * ((n : ℝ) / ((n : ℝ) - 2)) * ((r₁ - r₂) ^ 2 + (sC r₁ - sC r₂) ^ 2) := by
        rw [hUv]; ring
    _ ≤ 4 * Lip ^ 2 * ((n : ℝ) / ((n : ℝ) - 2)) * ((r₁ - r₂) ^ 2 / (1 - rp ^ 2)) :=
        mul_le_mul_of_nonneg_left hA hc0
    _ = _ := by ring

theorem p4_107' : P4_107 := p4_107 invMom107 nonZero107

#print axioms p4_107
#print axioms p4_107'

end BstLean.Part107
