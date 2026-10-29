import BstLean.Part59Defs
import BstLean.Part53T2_Comparison
import BstLean.Part53T2_Integrability
import BstLean.Part53Laws

/-! # Part 59: the radial binomial expansion and its variance bound -/

namespace BstLean.Part59

open MeasureTheory
open BstLean.Part36 (CoefIdxD mapMD)
open BstLean.Part41 (Tens contr uJ varU sdU)
open BstLean.Part40 (SphLaw)
open BstLean.Part53 (fvA TF)
open BstLean.Part53.T2Aux

variable {n d : ℕ}

lemma upLaw_sphere59x {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : UpLaw n μ K) :
    SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := hμ
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (BstLean.Part29.uniformSphere_ae_sphere n)

private lemma binomial_shift59x (k j : ℕ) (hj : j ≤ k) (l : ℝ) :
    l ^ j - 1 = ∑ r ∈ Finset.Icc 1 k, (l - 1) ^ r * (j.choose r : ℝ) := by
  classical
  have hb : l ^ j = ∑ r ∈ Finset.range (j + 1), (l - 1) ^ r * (j.choose r : ℝ) := by
    simpa using add_pow (l - 1) (1 : ℝ) j
  have hs : (∑ r ∈ Finset.range (j + 1), (l - 1) ^ r * (j.choose r : ℝ)) =
      ∑ r ∈ Finset.range (k + 1), (l - 1) ^ r * (j.choose r : ℝ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r hr hrj
    have hlt : j < r := by simp only [Finset.mem_range] at hr hrj; omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  rw [hb, hs]
  change _ = ∑ r ∈ Finset.Ico 1 (k + 1), _
  rw [Finset.sum_Ico_eq_sub _ (by omega)]
  simp

lemma fvA_bin59x (k r : ℕ) (A : Tens n) (W : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    fvA k (binA r A) (mapMD W x) =
      ∑ j ∈ Finset.range (k + 1), (j.choose r : ℝ) * uJ A j W x := by
  classical
  unfold fvA contr uJ binA
  apply Finset.sum_congr rfl
  intro j _
  unfold contr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- The binomial expansion retains cancellations between homogeneous terms. -/
lemma radial_binomial59x (k : ℕ) (f0 : ℝ) (T : Tens n)
    (W : CoefIdxD n d → ℝ) (l : ℝ) (x : Fin n → ℝ) :
    BstLean.Part41.fval k f0 T (mapMD (l • W) x) -
        BstLean.Part41.fval k f0 T (mapMD W x) =
      ∑ r ∈ Finset.Icc 1 k, (l - 1) ^ r * fvA k (binA r (TF k f0 T)) (mapMD W x) := by
  classical
  simp_rw [← BstLean.Part53.fvA_TF, fvA_bin59x, Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ j ∈ Finset.range (k + 1), uJ (TF k f0 T) j (l • W) x) -
      (∑ j ∈ Finset.range (k + 1), uJ (TF k f0 T) j W x) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [uJ_smul]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [← binomial_shift59x k j (by simpa using hj)]
  ring

lemma continuous_fvA_map59x (k : ℕ) (A : Tens n) (W : CoefIdxD n d → ℝ) :
    Continuous (fun x => fvA k A (mapMD W x)) := by
  classical
  exact continuous_finsetSum _ (fun j _ => continuous_u A j W)

lemma joint_fvA_map59x (k : ℕ) (A : Tens n) :
    Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => fvA k A (mapMD p.1 p.2)) := by
  classical
  exact continuous_finsetSum _ (fun j _ => joint_uJ_cont A j)

lemma variance_fvA_measurable59x (μ : Measure (Fin n → ℝ)) [SFinite μ] (k : ℕ) (A : Tens n) :
    Measurable (fun W : CoefIdxD n d → ℝ => varU μ (fun x => fvA k A (mapMD W x))) := by
  have hh := (joint_fvA_map59x (d := d) k A).measurable
  have hm : Measurable (fun W : CoefIdxD n d → ℝ => ∫ x, fvA k A (mapMD W x) ∂μ) :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  exact ((hh.sub (hm.comp measurable_fst)).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

/-- Cauchy--Schwarz bounds the radial defect by the binomial Euler variances. -/
lemma radial_square_le59x (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (W : CoefIdxD n d → ℝ) (l : ℝ) :
    radDef59 μ k f0 T W l ^ 2 ≤ (k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
      (l - 1) ^ (2 * r) * varU μ (fun x => fvA k (binA r (TF k f0 T)) (mapMD W x)) := by
  classical
  let := hμ.prob
  let H := fun r x => fvA k (binA r (TF k f0 T)) (mapMD W x)
  have hi (r : ℕ) : MemLp (H r) 2 μ := sphere_memLp hμ (continuous_fvA_map59x _ _ _)
  have he : radDef59 μ k f0 T W l ≤
      ∑ r ∈ Finset.Icc 1 k, |(l - 1) ^ r| * sdU μ (H r) := by
    unfold radDef59
    simp_rw [radial_binomial59x]
    exact (sd_sum_le _ _ (fun r _ => (hi r).const_mul _)).trans
      (Finset.sum_le_sum fun r _ => (sd_mul _ _ (hi r)).le)
  have hnn : 0 ≤ radDef59 μ k f0 T W l := Real.sqrt_nonneg _
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 k)
    (f := fun r => |(l - 1) ^ r| * sdU μ (H r))
  calc
    _ ≤ (∑ r ∈ Finset.Icc 1 k, |(l - 1) ^ r| * sdU μ (H r)) ^ 2 :=
      (sq_le_sq₀ hnn (hnn.trans he)).mpr he
    _ ≤ _ := by
      have hc : (Finset.Icc 1 k).card = k := by simp
      rw [hc] at hs
      apply hs.trans_eq
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [mul_pow, sq_abs, ← pow_mul, Nat.mul_comm r 2, sdU,
        Real.sq_sqrt (show 0 ≤ varU μ (H r) from integral_nonneg fun _ => sq_nonneg _)]

end BstLean.Part59
