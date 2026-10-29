import BstLean.Part56PropD_Expansion
import BstLean.Part56PropD_Bingham

/-! Measurability and boundedness for the mixed perpendicular features. -/
namespace BstLean.Part56

open MeasureTheory
open BstLean.Part41 (Mono)
open BstLean.Part53 (unitF53 radF53)

variable {n : ℕ}

theorem coord_abs_le_one (x : Fin n → ℝ) (hx : (∑ i, x i ^ 2) ≤ 1) (i : Fin n) :
    |x i| ≤ 1 := by
  apply (sq_le_one_iff_abs_le_one _).mp
  exact (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (x j))
    (Finset.mem_univ i)).trans hx

theorem unitF53_sumsq_le_one (x : Fin n → ℝ) :
    (∑ i, unitF53 x i ^ 2) ≤ 1 := by
  let S : ℝ := ∑ i, x i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hz : Real.sqrt S = 0
  · simp [unitF53, S, hz]
  · have he : (1 / Real.sqrt S) ^ 2 * S = 1 := by
      field_simp
      exact (Real.sq_sqrt hS).symm
    simp only [unitF53, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    change (1 / Real.sqrt S) ^ 2 * S ≤ 1
    exact he.le

theorem perpDir_sumsq_le_one (v g : Fin n → ℝ) :
    (∑ i, perpDir v g i ^ 2) ≤ 1 :=
  unitF53_sumsq_le_one (fun i => g i - (∑ l, v l * g l) * v i)

theorem perpDir_orthogonal (v g : Fin n → ℝ) (hv : UnitV v) :
    (∑ i, v i * perpDir v g i) = 0 := by
  let c : ℝ := 1 / Real.sqrt (∑ i, (g i - (∑ l, v l * g l) * v i) ^ 2)
  have he (i : Fin n) : v i * perpDir v g i =
      c * (v i * g i - (∑ l, v l * g l) * v i ^ 2) := by
    simp only [perpDir, Pi.smul_apply, smul_eq_mul, c]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change c * ((∑ i, v i * g i) - (∑ i, v i * g i) * (∑ i, v i ^ 2)) = 0
  rw [hv]
  ring

@[fun_prop] theorem continuous_PhiJI (d j i : ℕ) (p : Mono n d) :
    Continuous (fun q : (Fin n → ℝ) × (Fin n → ℝ) => PhiJI d j i q.1 q.2 p) := by
  classical
  unfold PhiJI
  split_ifs
  · exact continuous_linearProduct_coeff p.2.1 i
  · exact continuous_const

theorem PhiJI_bound (d j i : ℕ) (a w : Fin n → ℝ)
    (ha : ∀ l, |a l| ≤ 1) (hw : ∀ l, |w l| ≤ 1) (p : Mono n d) :
    |PhiJI d j i a w p| ≤ (2 : ℝ) ^ j := by
  classical
  by_cases hp : (p.1 : ℕ) = j
  · unfold PhiJI
    rw [if_pos hp]
    exact (linearProduct_coeff_bound a w ha hw p.2.1 i).trans_eq
      (congrArg (fun q : ℕ => (2 : ℝ) ^ q) (p.2.2.trans hp))
  · simp only [PhiJI, hp, ite_false, abs_zero]
    positivity

theorem psiHat_bound (d j : ℕ) (s r : ℝ) (v w : Fin n → ℝ)
    (hs : |s| ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hv : UnitV v) (hw : (∑ l, w l ^ 2) ≤ 1) (p : Mono n d) :
    |psiHat d j s r v w p| ≤ (j : ℝ) * 2 ^ j := by
  classical
  have ha : ∀ l, |(s • v) l| ≤ 1 := by
    intro l
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact (mul_le_mul hs (coord_abs_le_one v (le_of_eq hv) l)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hwb : ∀ l, |w l| ≤ 1 := coord_abs_le_one w hw
  simp only [psiHat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ i ∈ Finset.range j, |r ^ i * PhiJI d j (i + 1) (s • v) w p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j, (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (pow_nonneg hr0 _)]
      exact (mul_le_mul (pow_le_one₀ hr0 hr1) (PhiJI_bound d j (i + 1) (s • v) w ha hwb p)
        (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
    _ = _ := by simp

theorem PhiJI_perp_memLp (d j i : ℕ) (v : Fin n → ℝ) (hv : UnitV v)
    (s : ℝ) (hs : |s| ≤ 1) (p : Mono n d) :
    MemLp (fun g => PhiJI d j i (s • v) (perpDir v g) p) 2 (BstLean.Part29.stdGauss (Fin n)) := by
  have hw : Measurable (perpDir v) := by
    unfold perpDir
    fun_prop
  let f : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun q => PhiJI d j i q.1 q.2 p
  let q : (Fin n → ℝ) → ((Fin n → ℝ) × (Fin n → ℝ)) := fun g => (s • v, perpDir v g)
  have hf : Measurable f := (continuous_PhiJI d j i p).measurable
  have hq : Measurable q := measurable_const.prodMk hw
  have hm : Measurable (fun g => PhiJI d j i (s • v) (perpDir v g) p) := by
    change Measurable (f ∘ q)
    exact hf.comp hq
  have ha : ∀ l, |(s • v) l| ≤ 1 := by
    intro l
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact (mul_le_mul hs (coord_abs_le_one v (le_of_eq hv) l)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  apply MemLp.of_bound hm.aestronglyMeasurable ((2 : ℝ) ^ j)
  exact Filter.Eventually.of_forall fun g => by
    simpa only [Real.norm_eq_abs] using
      PhiJI_bound d j i (s • v) (perpDir v g) ha
        (coord_abs_le_one _ (perpDir_sumsq_le_one _ _)) p

theorem psiHat_perp_memLp (d j : ℕ) (v : Fin n → ℝ) (hv : UnitV v)
    (s r : ℝ) (hs : |s| ≤ 1) (p : Mono n d) :
    MemLp (fun g => psiHat d j s r v (perpDir v g) p) 2 (BstLean.Part29.stdGauss (Fin n)) := by
  have h := memLp_finsetSum (Finset.range j) (fun i _ =>
    (PhiJI_perp_memLp d j (i + 1) v hv s hs p).const_mul (r ^ i))
  convert h using 1
  ext g
  simp only [psiHat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

section Mixed
variable {k : ℕ}

noncomputable def mixedPsi (d j : ℕ) (v : Fin (k + 1) → ℝ)
    (x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) : Mono (k + 1) d → ℝ :=
  psiHat d j (axialS x.1.1 (radF53 x.1.2)) (axialR x.1.1 (radF53 x.1.2)) v (perpDir v x.2)

theorem measurable_mixedPsi_coord (d j : ℕ) (v : Fin (k + 1) → ℝ) (p : Mono (k + 1) d) :
    Measurable (fun x => mixedPsi d j v x p) := by
  have hS0 : Measurable (fun x : ℝ × (Fin k → ℝ) => axialS x.1 (radF53 x.2)) := by
    unfold axialS radF53
    fun_prop
  have hA : Measurable (fun x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ) =>
      axialS x.1.1 (radF53 x.1.2) • v) :=
    (hS0.comp measurable_fst).smul measurable_const
  have hW0 : Measurable (perpDir v) := by
    unfold perpDir
    fun_prop
  have hW : Measurable (fun x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ) => perpDir v x.2) :=
    hW0.comp measurable_snd
  have hR0 : Measurable (fun x : ℝ × (Fin k → ℝ) => axialR x.1 (radF53 x.2)) := by
    unfold axialR radF53
    fun_prop
  have hR : Measurable (fun x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ) =>
      axialR x.1.1 (radF53 x.1.2)) := hR0.comp measurable_fst
  have he : (fun x => mixedPsi d j v x p) =
      (fun x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ) =>
        ∑ i ∈ Finset.range j, axialR x.1.1 (radF53 x.1.2) ^ i *
          PhiJI d j (i + 1) (axialS x.1.1 (radF53 x.1.2) • v) (perpDir v x.2) p) := by
    ext x
    simp only [mixedPsi, psiHat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  have hPhi (i : ℕ) : Measurable (fun x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ) =>
      PhiJI d j (i + 1) (axialS x.1.1 (radF53 x.1.2) • v) (perpDir v x.2) p) := by
    let f : ((Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ)) → ℝ :=
      fun q => PhiJI d j (i + 1) q.1 q.2 p
    let q : ((ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) →
        ((Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ)) :=
      fun x => (axialS x.1.1 (radF53 x.1.2) • v, perpDir v x.2)
    have hf : Measurable f := (continuous_PhiJI d j (i + 1) p).measurable
    have hq : Measurable q := hA.prodMk hW
    change Measurable (f ∘ q)
    exact hf.comp hq
  apply Finset.measurable_sum
  intro i _
  exact (hR.pow_const i).mul (hPhi i)

theorem mixedPsi_bound (d j : ℕ) (v : Fin (k + 1) → ℝ) (hv : UnitV v)
    (x : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) (p : Mono (k + 1) d) :
    |mixedPsi d j v x p| ≤ (j : ℝ) * 2 ^ j :=
  psiHat_bound d j _ _ v _ (axialS_abs_le_one _ _)
    (axialR_nonneg _ _ (Real.sqrt_nonneg _))
    (axialR_le_one _ _ (Real.sqrt_nonneg _)) hv (perpDir_sumsq_le_one _ _) p

theorem mixedPsi_memLp (d j : ℕ) (v : Fin (k + 1) → ℝ) (hv : UnitV v)
    (μ : Measure ((ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ))) [IsFiniteMeasure μ]
    (p : Mono (k + 1) d) : MemLp (fun x => mixedPsi d j v x p) 2 μ := by
  apply MemLp.of_bound (measurable_mixedPsi_coord d j v p).aestronglyMeasurable ((j : ℝ) * 2 ^ j)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using mixedPsi_bound d j v hv x p

end Mixed

end BstLean.Part56
