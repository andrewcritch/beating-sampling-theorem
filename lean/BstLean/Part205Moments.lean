import BstLean.Part205Normalize
import BstLean.Part205Covariance

/-! Radial and normalized-correlation moment supplies from the actual field moments. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part139

lemma bm_div_const {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ} (hf : BM f) (Q : ℝ) :
    BM (fun x => f x / Q) := by
  convert hf.mul (BM.const (1 / Q)) using 1
  ext x
  simp [div_eq_mul_inv]

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : ℕ} (Q : ℝ) (g : Ω → Fin m → ℝ)

noncomputable def radialNu : ℝ := √(∫ x, (normSq (g x) / Q - 1) ^ 2 ∂μ)

noncomputable def pairCorr (p : Ω × Ω) : ℝ :=
  dotp (normalizeInput Q g p.1) (normalizeInput Q g p.2) / Q

noncomputable def singleCorr (x : Ω) : ℝ :=
  dotp (normalizeInput Q g x) (meanV μ g) / Q

lemma radialNu_sq : radialNu μ Q g ^ 2 = ∫ x, (normSq (g x) / Q - 1) ^ 2 ∂μ :=
  Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

lemma radial_L2 (hg : ∀ j, BM (fun x => g x j)) (hQ : 0 < Q) :
    L2le μ (fun x => 1 - radialWeight Q g x) (radialNu μ Q g) := by
  have ha := radialWeight_bm Q g hg
  have hb : BM (fun x => 1 - radialWeight Q g x) := (BM.const 1).sub ha
  refine ⟨hb.1.aestronglyMeasurable, hb.sq.integrable _, ?_⟩
  rw [radialNu_sq]
  have h := radial_second_le (μ := μ)
    (Filter.Eventually.of_forall (radialWeight_nonneg Q g hQ))
    ((ha.sub (BM.const 1)).sq.integrable μ)
    ((ha.sq.sub (BM.const 1)).sq.integrable μ)
  simp_rw [radialWeight_sq Q g hQ] at h
  have he : (fun x => (1 - radialWeight Q g x) ^ 2) =
      fun x => (radialWeight Q g x - 1) ^ 2 := by funext x; ring
  rw [he]
  exact h

lemma radial_pair_L2 (hg : ∀ j, BM (fun x => g x j)) (hQ : 0 < Q)
    (hQeq : ∫ x, normSq (g x) ∂μ = Q) :
    L2le (μ.prod μ) (fun p => 1 - radialWeight Q g p.1 * radialWeight Q g p.2)
      (√2 * radialNu μ Q g) := by
  have ha := radialWeight_bm Q g hg
  have hb : BM (fun p : Ω × Ω => 1 - radialWeight Q g p.1 * radialWeight Q g p.2) :=
    (BM.const 1).sub (ha.fst.mul ha.snd)
  refine ⟨hb.1.aestronglyMeasurable, hb.sq.integrable _, ?_⟩
  have h := radial_pair_second_le (μ := μ) (ha.integrable μ) (ha.sq.integrable μ)
    (radialWeight_second Q g hg μ hQ hQeq)
  have hs := (radial_L2 μ Q g hg hQ).le
  have he : (fun x => (1 - radialWeight Q g x) ^ 2) =
      fun x => (radialWeight Q g x - 1) ^ 2 := by funext x; ring
  rw [he] at hs
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact h.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

lemma pairCorr_bm (hg : ∀ j, BM (fun x => g x j)) (hm : 1 ≤ m) (hQ : 0 < Q) :
    BM (pairCorr Q g) := by
  have hz := normalizeInput_bm Q g hg hm hQ
  exact bm_div_const (BM.sum _ (fun j _ => (hz j).fst.mul (hz j).snd)) Q

lemma singleCorr_bm (hg : ∀ j, BM (fun x => g x j)) (hm : 1 ≤ m) (hQ : 0 < Q) :
    BM (singleCorr μ Q g) := by
  have hz := normalizeInput_bm Q g hg hm hQ
  exact bm_div_const (BM.sum _ (fun j _ => (hz j).mul (BM.const (meanV μ g j)))) Q

lemma pairCorr_abs (hm : 1 ≤ m) (hQ : 0 < Q) (p : Ω × Ω) : |pairCorr Q g p| ≤ 1 := by
  have hn : ∀ x, nrm (normalizeInput Q g x) = √Q := by
    intro x
    unfold nrm
    rw [normalizeInput_normSq Q g hm hQ]
  have h := abs_dotp_le_nrm (normalizeInput Q g p.1) (normalizeInput Q g p.2)
  rw [hn, hn, Real.mul_self_sqrt hQ.le] at h
  unfold pairCorr
  rw [abs_div, abs_of_pos hQ]
  exact (div_le_div_of_nonneg_right h hQ.le).trans_eq (div_self hQ.ne')

lemma singleCorr_abs (hm : 1 ≤ m) (hQ : 0 < Q)
    (hH : normSq (meanV μ g) ≤ Q) (x : Ω) : |singleCorr μ Q g x| ≤ 1 := by
  have hn : nrm (normalizeInput Q g x) = √Q := by
    unfold nrm
    rw [normalizeInput_normSq Q g hm hQ]
  have h := abs_dotp_le_nrm (normalizeInput Q g x) (meanV μ g)
  rw [hn] at h
  have h' : nrm (meanV μ g) ≤ √Q := Real.sqrt_le_sqrt hH
  have hb : |dotp (normalizeInput Q g x) (meanV μ g)| ≤ Q :=
    h.trans ((mul_le_mul_of_nonneg_left h' (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt hQ.le))
  unfold singleCorr
  rw [abs_div, abs_of_pos hQ]
  exact (div_le_div_of_nonneg_right hb hQ.le).trans_eq (div_self hQ.ne')

lemma dotp_smul_pair (a b : ℝ) (x y : Fin m → ℝ) :
    dotp (a • x) (b • y) = a * b * dotp x y := by
  unfold dotp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma pairCorr_raw (hQ : 0 < Q) (p : Ω × Ω) :
    radialWeight Q g p.1 * radialWeight Q g p.2 * pairCorr Q g p =
      dotp (g p.1) (g p.2) / Q := by
  conv_rhs => rw [normalizeInput_factor Q g hQ p.1, normalizeInput_factor Q g hQ p.2]
  rw [dotp_smul_pair]
  unfold pairCorr
  ring

lemma singleCorr_raw (hQ : 0 < Q) (x : Ω) :
    radialWeight Q g x * singleCorr μ Q g x = dotp (g x) (meanV μ g) / Q := by
  conv_rhs => rw [normalizeInput_factor Q g hQ x,
    show meanV μ g = (1 : ℝ) • meanV μ g by simp]
  rw [dotp_smul_pair]
  unfold singleCorr
  ring

theorem normalized_pair_L2 (hg : ∀ j, BM (fun x => g x j)) (hm : 1 ≤ m) (hQ : 0 < Q)
    (hQeq : ∫ x, normSq (g x) ∂μ = Q) :
    L2le (μ.prod μ) (fun p => pairCorr Q g p - normSq (meanV μ g) / Q)
      (√(covarianceT μ g Q) + √2 * radialNu μ Q g) := by
  have hr : L2le (μ.prod μ) (fun p =>
      radialWeight Q g p.1 * radialWeight Q g p.2 * pairCorr Q g p - normSq (meanV μ g) / Q)
      (√(covarianceT μ g Q)) :=
    (covariance_pair_L2 μ g hg hQ).congr_fun fun p => by rw [pairCorr_raw Q g hQ]
  exact correlation_normalization (pairCorr_bm Q g hg hm hQ).1
    (pairCorr_abs Q g hm hQ) hr (radial_pair_L2 μ Q g hg hQ hQeq)
    (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem normalized_single_L2 (hg : ∀ j, BM (fun x => g x j)) (hm : 1 ≤ m) (hQ : 0 < Q)
    (hH : normSq (meanV μ g) ≤ Q) :
    L2le μ (fun x => singleCorr μ Q g x - normSq (meanV μ g) / Q)
      (√(covarianceT μ g Q) + radialNu μ Q g) := by
  have hr : L2le μ (fun x => radialWeight Q g x * singleCorr μ Q g x - normSq (meanV μ g) / Q)
      (√(covarianceT μ g Q)) :=
    (covariance_single_L2 μ g hg hQ).congr_fun fun x => by rw [singleCorr_raw μ Q g hQ]
  exact correlation_normalization (singleCorr_bm μ Q g hg hm hQ).1
    (singleCorr_abs μ Q g hm hQ hH) hr (radial_L2 μ Q g hg hQ)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end BstLean.Part205

#print axioms BstLean.Part205.normalized_pair_L2
#print axioms BstLean.Part205.normalized_single_L2
