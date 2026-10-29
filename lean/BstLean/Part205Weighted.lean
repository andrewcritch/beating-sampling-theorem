import BstLean.Part205Centroid

/-! Restore both radial weights and retain their constant and Lipschitz errors. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part139

lemma kappa_abs_difference {c r : ℝ} (hc : |c| ≤ 1) (hr0 : -1 ≤ r) (hr1 : r ≤ 1) :
    |kappa c - kappa r| ≤ |c - r| := by
  have hc' := abs_le.mp hc
  by_cases h : r ≤ c
  · have hk := kappa_lipschitz hr0 h hc'.2
    rw [abs_of_nonneg hk.1, abs_of_nonneg (sub_nonneg.mpr h)]
    exact hk.2
  · have h' := le_of_not_ge h
    have hk := kappa_lipschitz hc'.1 h' hr1
    rw [abs_sub_comm (kappa c) (kappa r), abs_sub_comm c r,
      abs_of_nonneg hk.1, abs_of_nonneg (sub_nonneg.mpr h')]
    exact hk.2

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma bm_kappa {c : Ω → ℝ} (hc : BM c) (h1 : ∀ x, |c x| ≤ 1) : BM (fun x => kappa (c x)) := by
  refine ⟨continuous_kappa.measurable.comp hc.1, 1, ?_⟩
  intro x
  have h := abs_le.mp (h1 x)
  have hk := kappa_mem h.1 h.2
  rw [abs_of_nonneg hk.1]
  exact hk.2

lemma L2_integral_product {f g : Ω → ℝ} {A B : ℝ} (hf : BM f) (hg : BM g)
    (hF : L2le μ f A) (hG : L2le μ g B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |∫ x, f x * g x ∂μ| ≤ A * B := by
  obtain ⟨-, hc⟩ := integral_mul_le_sqrt hf.1 hg.1 hF.int_sq hG.int_sq
  have ha : √(∫ x, f x ^ 2 ∂μ) ≤ A := by
    exact (Real.sqrt_le_sqrt hF.le).trans_eq (Real.sqrt_sq hA)
  have hb : √(∫ x, g x ^ 2 ∂μ) ≤ B := by
    exact (Real.sqrt_le_sqrt hG.le).trans_eq (Real.sqrt_sq hB)
  calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
    _ = ∫ x, |f x| * |g x| ∂μ := by simp only [abs_mul]
    _ ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := hc
    _ ≤ A * B := mul_le_mul ha hb (Real.sqrt_nonneg _) hA

lemma integral_restore {a c : Ω → ℝ} (ha : BM a) (hc : BM c) (k : ℝ) :
    (∫ x, a x * c x ∂μ) = (∫ x, c x ∂μ) + k * ((∫ x, a x ∂μ) - 1) +
      ∫ x, (a x - 1) * (c x - k) ∂μ := by
  have he : (fun x => a x * c x) = fun x => c x + k * (a x - 1) +
      (a x - 1) * (c x - k) := by funext x; ring
  have iA : Integrable (fun x => c x + k * (a x - 1)) μ :=
    (hc.integrable μ).add (((ha.sub (BM.const 1)).integrable μ).const_mul k)
  have iB := ((ha.sub (BM.const 1)).mul (hc.sub (BM.const k))).integrable μ
  rw [he, integral_add iA iB,
    integral_add (hc.integrable μ) (((ha.sub (BM.const 1)).integrable μ).const_mul k),
    integral_const_mul, integral_sub (ha.integrable μ) (integrable_const 1)]
  simp

end

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : ℕ} (Q : ℝ) (g : Ω → Fin m → ℝ)

noncomputable def weightedDelta : ℝ :=
  (∫ p : Ω × Ω, radialWeight Q g p.1 * radialWeight Q g p.2 * kappa (pairCorr Q g p)
    ∂μ.prod μ) - 2 * (∫ x, radialWeight Q g x * kappa (singleCorr μ Q g x) ∂μ) +
      kappa (normSq (meanV μ g) / Q)

/-- The deterministic mean bound follows from the actual normalized field and covariance moments. -/
theorem weighted_mean_bound (hg : ∀ j, BM (fun x => g x j)) (hm : 1 ≤ m) (hQ : 0 < Q)
    (hQeq : ∫ x, normSq (g x) ∂μ = Q)
    (hr0 : 0 < normSq (meanV μ g) / Q) (hr1 : normSq (meanV μ g) / Q < 1 / 2) :
    weightedDelta μ Q g ≤ meanBound (normSq (meanV μ g) / Q)
      (covarianceT μ g Q) (radialNu μ Q g) := by
  let a := radialWeight Q g
  let c := pairCorr Q g
  let d := singleCorr μ Q g
  let r := normSq (meanV μ g) / Q
  let ν := radialNu μ Q g
  let T := covarianceT μ g Q
  have hν : 0 ≤ ν := Real.sqrt_nonneg _
  have hT : 0 ≤ √T := Real.sqrt_nonneg _
  have h2ν : 0 ≤ √2 * ν := mul_nonneg (Real.sqrt_nonneg _) hν
  let E₀ := (∫ p, kappa (c p) ∂μ.prod μ) - 2 * (∫ x, kappa (d x) ∂μ) + kappa r
  let Ec := kappa r * ((∫ x, a x ∂μ) - 1) ^ 2
  let Ep := ∫ p : Ω × Ω, (a p.1 * a p.2 - 1) * (kappa (c p) - kappa r) ∂μ.prod μ
  let Es := -2 * (∫ x, (a x - 1) * (kappa (d x) - kappa r) ∂μ)
  have ha : BM a := radialWeight_bm Q g hg
  have hc : BM c := pairCorr_bm Q g hg hm hQ
  have hH := original_mean_energy_le μ Q g hg hQeq
  have hd : BM d := singleCorr_bm μ Q g hg hm hQ
  have hcr : ∀ p, |c p| ≤ 1 := pairCorr_abs Q g hm hQ
  have hdr : ∀ x, |d x| ≤ 1 := singleCorr_abs μ Q g hm hQ hH
  have hkc := bm_kappa hc hcr
  have hkd := bm_kappa hd hdr
  have hKc : L2le (μ.prod μ) (fun p => kappa (c p) - kappa r) (√T + √2 * ν) := by
    refine L2le.of_abs_le (hkc.sub (BM.const _)).1.aestronglyMeasurable
      (normalized_pair_L2 μ Q g hg hm hQ hQeq) ?_
    exact fun p => kappa_abs_difference (hcr p) (by linarith) (by linarith)
  have hKd : L2le μ (fun x => kappa (d x) - kappa r) (√T + ν) := by
    refine L2le.of_abs_le (hkd.sub (BM.const _)).1.aestronglyMeasurable
      (normalized_single_L2 μ Q g hg hm hQ hH) ?_
    exact fun x => kappa_abs_difference (hdr x) (by linarith) (by linarith)
  have hPa : L2le (μ.prod μ) (fun p : Ω × Ω => a p.1 * a p.2 - 1) (√2 * ν) :=
    (radial_pair_L2 μ Q g hg hQ hQeq).neg.congr_fun fun p => by ring
  have hSa : L2le μ (fun x => a x - 1) ν :=
    (radial_L2 μ Q g hg hQ).neg.congr_fun fun x => by ring
  have hEp : Ep ≤ √2 * ν * (√T + √2 * ν) := by
    have h := L2_integral_product (μ := μ.prod μ) ((ha.fst.mul ha.snd).sub (BM.const 1))
      (hkc.sub (BM.const (kappa r))) hPa hKc h2ν (add_nonneg hT h2ν)
    exact (le_abs_self _).trans h
  have hEs : Es ≤ 2 * ν * (√T + ν) := by
    have h := L2_integral_product (μ := μ) (ha.sub (BM.const 1))
      (hkd.sub (BM.const (kappa r))) hSa hKd hν (add_nonneg hT hν)
    have hlow := (abs_le.mp h).1
    dsimp [Es]
    nlinarith
  have hEc : Ec ≤ kappa r * ν ^ 2 := by
    have h := (sq_integral_le hSa.int_sq).trans hSa.le
    rw [integral_sub (ha.integrable μ) (integrable_const 1)] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact mul_le_mul_of_nonneg_left h (kappa_mem (by linarith) (by linarith)).1
  have hE₀ : E₀ ≤ endpointK r * (√T + √2 * ν) ^ 2 + slopeK r * ν ^ 2 :=
    normalized_unweighted_mean μ Q g hg hm hQ hQeq hr0 hr1
  have hΔ : weightedDelta μ Q g ≤ E₀ + Ec + Ep + Es := by
    have hp := integral_restore (μ := μ.prod μ) (ha.fst.mul ha.snd) hkc (kappa r)
    have hs := integral_restore (μ := μ) ha hkd (kappa r)
    rw [integral_prod_mul a a] at hp
    unfold weightedDelta
    change (∫ p : Ω × Ω, (a p.1 * a p.2) * kappa (c p) ∂μ.prod μ) -
      2 * (∫ x, a x * kappa (d x) ∂μ) + kappa r ≤ _
    rw [hp, hs]
    dsimp [E₀, Ec, Ep, Es]
    nlinarith
  exact mean_bound_of_error_bounds hΔ hE₀ hEc hEp hEs

end
end BstLean.Part205

#print axioms BstLean.Part205.weighted_mean_bound
