import BstLean.Part214Ordered
import BstLean.Part148Tools

/-! Marginals of distinct whole rows retain their product distributions. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory

section
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {m : ℕ}

lemma iid_rows : iIndepFun (fun i : Fin m => fun x : Fin m → X => x i)
    (Measure.pi fun _ : Fin m => μ) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem iid_pair {i j : Fin m} (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin m → X => (x i, x j))
      (Measure.pi fun _ : Fin m => μ) (μ.prod μ) := by
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  have h := ((iid_rows μ).indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [(measurePreserving_eval (fun _ : Fin m => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin m => μ) j).map_eq] using h

theorem iid_triple {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving (fun x : Fin m → X => (x i, (x j, x k)))
      (Measure.pi fun _ : Fin m => μ) (μ.prod (μ.prod μ)) := by
  have hI := ((iid_rows μ).indepFun_prodMk (fun i => measurable_pi_apply i)
    j k i hij.symm hik.symm).symm
  refine ⟨(measurable_pi_apply i).prodMk
    ((measurable_pi_apply j).prodMk (measurable_pi_apply k)), ?_⟩
  have h := hI.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    ((measurable_pi_apply j).prodMk (measurable_pi_apply k)).aemeasurable
  simpa only [(measurePreserving_eval (fun _ : Fin m => μ) i).map_eq,
    (iid_pair μ hjk).map_eq] using h

variable {φ : X × X → ℝ} (hφ : Measurable φ) (iφ : MemLp φ 2 (μ.prod μ))

include iφ in
lemma pair_memLp {i j : Fin m} (hij : i ≠ j) :
    MemLp (fun x : Fin m → X => φ (x i, x j)) 2 (Measure.pi fun _ : Fin m => μ) :=
  iφ.comp_measurePreserving (iid_pair μ hij)

include hφ in
lemma pair_mean {i j : Fin m} (hij : i ≠ j) :
    (∫ x : Fin m → X, φ (x i, x j) ∂Measure.pi fun _ : Fin m => μ) =
      ∫ p, φ p ∂μ.prod μ := by
  rw [← integral_map (iid_pair μ hij).measurable.aemeasurable hφ.aestronglyMeasurable,
    (iid_pair μ hij).map_eq]

include hφ iφ in
theorem pair_cov_same {i j : Fin m} (hij : i ≠ j) :
    covariance (fun x : Fin m → X => φ (x i, x j)) (fun x => φ (x i, x j))
      (Measure.pi fun _ : Fin m => μ) =
      (∫ p, φ p ^ 2 ∂μ.prod μ) - (∫ p, φ p ∂μ.prod μ) ^ 2 := by
  rw [covariance_eq_sub (pair_memLp μ iφ hij) (pair_memLp μ iφ hij),
    pair_mean μ hφ hij]
  have he : (∫ x : Fin m → X, φ (x i, x j) * φ (x i, x j)
      ∂Measure.pi fun _ : Fin m => μ) = ∫ p, φ p ^ 2 ∂μ.prod μ := by
    simp only [← pow_two]
    exact pair_mean μ (hφ.pow_const 2) hij
  simp only [Pi.mul_apply]
  rw [he, pow_two]

include hφ iφ in
theorem pair_cov_shared {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    covariance (fun x : Fin m → X => φ (x i, x j)) (fun x => φ (x i, x k))
      (Measure.pi fun _ : Fin m => μ) =
      (∫ p : X × (X × X), φ (p.1, p.2.1) * φ (p.1, p.2.2) ∂μ.prod (μ.prod μ)) -
        (∫ p, φ p ∂μ.prod μ) ^ 2 := by
  rw [covariance_eq_sub (pair_memLp μ iφ hij) (pair_memLp μ iφ hik),
    pair_mean μ hφ hij, pair_mean μ hφ hik]
  have hm : Measurable (fun p : X × (X × X) => φ (p.1, p.2.1) * φ (p.1, p.2.2)) :=
    (hφ.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hφ.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have he := integral_map (μ := Measure.pi fun _ : Fin m => μ) (iid_triple μ hij hik hjk).measurable.aemeasurable hm.aestronglyMeasurable
  rw [(iid_triple μ hij hik hjk).map_eq] at he
  simp only [Pi.mul_apply]
  rw [← he, pow_two]

include hφ iφ in
theorem pair_cov_disjoint {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    covariance (fun x : Fin m → X => φ (x i, x j)) (fun x => φ (x k, x l))
      (Measure.pi fun _ : Fin m => μ) = 0 := by
  have hi := (iid_rows μ).indepFun_prodMk_prodMk (fun i => measurable_pi_apply i)
    i j k l hik hil hjk hjl
  exact (hi.comp hφ hφ).covariance_eq_zero (pair_memLp μ iφ hij) (pair_memLp μ iφ hkl)

include hφ iφ in
theorem pair_scalar_cov {ψ : X → ℝ} (hψ : Measurable ψ) (iψ : MemLp ψ 2 μ)
    {i j : Fin m} (hij : i ≠ j) :
    covariance (fun x : Fin m → X => φ (x i, x j)) (fun x => ψ (x i))
      (Measure.pi fun _ : Fin m => μ) =
      (∫ p : X × X, φ p * ψ p.1 ∂μ.prod μ) -
        (∫ p, φ p ∂μ.prod μ) * (∫ x, ψ x ∂μ) := by
  have mp := measurePreserving_eval (fun _ : Fin m => μ) i
  have ip : MemLp (fun x : Fin m → X => ψ (x i)) 2 (Measure.pi fun _ : Fin m => μ) := iψ.comp_measurePreserving mp
  rw [covariance_eq_sub (pair_memLp μ iφ hij) ip,
    pair_mean μ hφ hij]
  have hx : (∫ x : Fin m → X, ψ (x i) ∂Measure.pi fun _ : Fin m => μ) = ∫ x, ψ x ∂μ := by
    rw [← integral_map mp.measurable.aemeasurable hψ.aestronglyMeasurable, mp.map_eq]
  rw [hx]
  have hp := iid_pair μ hij
  have hh := integral_map (μ := Measure.pi fun _ : Fin m => μ) hp.measurable.aemeasurable
    (hφ.mul (hψ.comp measurable_fst)).aestronglyMeasurable
  rw [hp.map_eq] at hh
  simp only [Pi.mul_apply, Function.comp_apply] at hh
  simp only [Pi.mul_apply]
  rw [← hh]

include hφ iφ in
theorem pair_scalar_disjoint {ψ : X → ℝ} (hψ : Measurable ψ) (iψ : MemLp ψ 2 μ)
    {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    covariance (fun x : Fin m → X => φ (x i, x j)) (fun x => ψ (x k))
      (Measure.pi fun _ : Fin m => μ) = 0 := by
  have hi := (iid_rows μ).indepFun_prodMk (fun i => measurable_pi_apply i) i j k hik hjk
  exact (hi.comp hφ hψ).covariance_eq_zero (pair_memLp μ iφ hij)
    (iψ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => μ) k))

end

/-- Under variance one the Gaussian matrix distribution is exactly the product of its rows. -/
theorem gaussMat_one_pi (m N : ℕ) : BstLean.Part130.gaussMat m N 1 =
    Measure.pi (fun _ : Fin m => BstLean.Part29.stdGauss (Fin N)) := by
  have h := BstLean.Part148.gaussMat_rows_map m N 1
  change Measure.map (id : (Fin m → Fin N → ℝ) → (Fin m → Fin N → ℝ))
    (BstLean.Part130.gaussMat m N 1) = _ at h
  simp only [Real.sqrt_one, one_smul] at h
  change Measure.map id (Part130.gaussMat m N 1) = Measure.pi (fun _ : Fin m => Measure.map id (Part29.stdGauss (Fin N))) at h
  simpa only [Measure.map_id] using h

end BstLean.Part218
#print axioms BstLean.Part218.pair_cov_shared
#print axioms BstLean.Part218.gaussMat_one_pi
