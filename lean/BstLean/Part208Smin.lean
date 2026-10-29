import BstLean.Part152Op
import BstLean.Part153Op

/-! Part 208: smallest singular value and its Gaussian concentration.
The sharp lower bound on its mean remains a separate obligation. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 (normSq normSq_nonneg e0 normSq_e0 gaussMat)
open BstLean.Part152 (opN mulVec_le_opN opN_le_frob gaussConc_mat_lower_sharp)
open BstLean.Part153 (nrm nrm_nonneg abs_nrm_sub_le)

def minStretchSet {N d : ℕ} (G : Matrix (Fin N) (Fin d) ℝ) : Set ℝ :=
  {r | ∃ x : Fin d → ℝ, normSq x = 1 ∧ r = nrm (G *ᵥ x)}

noncomputable def minStretch {N d : ℕ} (G : Matrix (Fin N) (Fin d) ℝ) : ℝ :=
  sInf (minStretchSet G)

lemma minStretchSet_nonempty {N d : ℕ} (hd : 1 ≤ d) (G : Matrix (Fin N) (Fin d) ℝ) :
    (minStretchSet G).Nonempty :=
  ⟨nrm (G *ᵥ e0 d), e0 d, normSq_e0 hd, rfl⟩

lemma minStretchSet_bddBelow {N d : ℕ} (G : Matrix (Fin N) (Fin d) ℝ) :
    BddBelow (minStretchSet G) := by
  refine ⟨0, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  exact nrm_nonneg _

lemma minStretch_nonneg {N d : ℕ} (hd : 1 ≤ d) (G : Matrix (Fin N) (Fin d) ℝ) :
    0 ≤ minStretch G := by
  apply le_csInf (minStretchSet_nonempty hd G)
  rintro r ⟨x, hx, rfl⟩
  exact nrm_nonneg _

lemma minStretch_le {N d : ℕ} (G : Matrix (Fin N) (Fin d) ℝ)
    {x : Fin d → ℝ} (hx : normSq x = 1) : minStretch G ≤ nrm (G *ᵥ x) :=
  csInf_le (minStretchSet_bddBelow G) ⟨x, hx, rfl⟩

lemma minStretch_le_add {N d : ℕ} (hd : 1 ≤ d) (G H : Matrix (Fin N) (Fin d) ℝ) :
    minStretch G ≤ minStretch H + √(∑ i, ∑ j, (G i j - H i j) ^ 2) := by
  have h : minStretch G - √(∑ i, ∑ j, (G i j - H i j) ^ 2) ≤ minStretch H := by
    apply le_csInf (minStretchSet_nonempty hd H)
    rintro r ⟨x, hx, rfl⟩
    have hx1 : nrm x = 1 := by unfold nrm; rw [hx, sqrt_one]
    have hdiff : |nrm (G *ᵥ x) - nrm (H *ᵥ x)| ≤
        √(∑ i, ∑ j, (G i j - H i j) ^ 2) := by
      refine (abs_nrm_sub_le _ _).trans ?_
      rw [← sub_mulVec]
      have hb := mulVec_le_opN (G - H) x
      change nrm ((G - H) *ᵥ x) ≤ opN (G - H) * nrm x at hb
      rw [hx1, mul_one] at hb
      exact hb.trans (opN_le_frob (G - H))
    have hmin := minStretch_le G hx
    have hb := (abs_le.mp hdiff).2
    linarith
  linarith

/-- The smallest singular value is one-Lipschitz for the Frobenius distance. -/
theorem minStretch_lip {N d : ℕ} (hd : 1 ≤ d) (G H : Matrix (Fin N) (Fin d) ℝ) :
    |minStretch G - minStretch H| ≤ 1 * √(∑ i, ∑ j, (G i j - H i j) ^ 2) := by
  have h1 := minStretch_le_add hd G H
  have h2 := minStretch_le_add hd H G
  have he : (∑ i, ∑ j, (H i j - G i j) ^ 2) = ∑ i, ∑ j, (G i j - H i j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he] at h2
  rw [one_mul, abs_le]
  constructor <;> linarith

theorem minStretch_continuous {N d : ℕ} (hd : 1 ≤ d) :
    Continuous (minStretch (N := N) (d := d)) :=
  BstLean.Part148.matLip_continuous (minStretch_lip hd)

theorem minStretch_lt_iff {N d : ℕ} (hd : 1 ≤ d) (G : Matrix (Fin N) (Fin d) ℝ) (s : ℝ) :
    minStretch G < s ↔ ∃ x : Fin d → ℝ, normSq x = 1 ∧ nrm (G *ᵥ x) < s := by
  constructor
  · intro h
    by_contra hbad
    push_neg at hbad
    have hlow : s ≤ minStretch G := by
      apply le_csInf (minStretchSet_nonempty hd G)
      rintro r ⟨x, hx, rfl⟩
      exact hbad x hx
    linarith
  · rintro ⟨x, hx, hbad⟩
    exact (minStretch_le G hx).trans_lt hbad

theorem measurableSet_minStretch_failure {N d : ℕ} (hd : 1 ≤ d) (s : ℝ) :
    MeasurableSet {G : Matrix (Fin N) (Fin d) ℝ |
      ∃ x : Fin d → ℝ, normSq x = 1 ∧ nrm (G *ᵥ x) < s} := by
  have he : {G : Matrix (Fin N) (Fin d) ℝ |
      ∃ x : Fin d → ℝ, normSq x = 1 ∧ nrm (G *ᵥ x) < s} = {G | minStretch G < s} := by
    ext G
    exact (minStretch_lt_iff hd G s).symm
  rw [he]
  exact measurableSet_lt (minStretch_continuous hd).measurable measurable_const

/-- The actual Gaussian lower deviation has one exponential tail.
The centre of this estimate is the actual Gaussian mean. -/
theorem gaussian_minStretch_deviation {N d : ℕ} (hd : 1 ≤ d) {v τ : ℝ}
    (hv : 0 < v) (hτ : 0 ≤ τ) :
    (gaussMat N d v).real {G | ∃ x : Fin d → ℝ, normSq x = 1 ∧
      nrm (G *ᵥ x) < (∫ M, minStretch M ∂gaussMat N d v) - √v * √(2 * τ)} ≤ exp (-τ) := by
  haveI : IsProbabilityMeasure (gaussMat N d v) := by unfold gaussMat; infer_instance
  have h := gaussConc_mat_lower_sharp (g := minStretch (N := N) (d := d))
    (L := 1) zero_le_one (minStretch_lip hd) hv.le
    (t := √v * √(2 * τ)) (by positivity)
  have he : -(√v * √(2 * τ)) ^ 2 / (2 * (v * (1 : ℝ) ^ 2)) = -τ := by
    rw [mul_pow, sq_sqrt hv.le, sq_sqrt (by positivity)]
    field_simp [hv.ne']
    <;> ring
  rw [he] at h
  refine (measureReal_mono (s₂ := {G | minStretch G ≤
    (∫ M, minStretch M ∂gaussMat N d v) - √v * √(2 * τ)}) ?_ (measure_ne_top _ _)).trans h
  rintro G ⟨x, hx, hbad⟩
  exact ((minStretch_le G hx).trans_lt hbad).le

/-- A sharp mean comparison would close the remaining smallest-singular-value tail.
This theorem keeps that unproved comparison as an explicit premise. -/
theorem gaussian_minStretch_of_mean {N d : ℕ} (hd : 1 ≤ d) {v τ : ℝ}
    (hv : 0 < v) (hτ : 0 ≤ τ)
    (hmean : √v * (√(N : ℝ) - √(d : ℝ)) ≤ ∫ M, minStretch M ∂gaussMat N d v) :
    (gaussMat N d v).real {G | ∃ x : Fin d → ℝ, normSq x = 1 ∧
      nrm (G *ᵥ x) < √v * (√(N : ℝ) - √(d : ℝ) - √(2 * τ))} ≤ exp (-τ) := by
  haveI : IsProbabilityMeasure (gaussMat N d v) := by unfold gaussMat; infer_instance
  refine (measureReal_mono (s₂ := {G | ∃ x : Fin d → ℝ, normSq x = 1 ∧
    nrm (G *ᵥ x) < (∫ M, minStretch M ∂gaussMat N d v) - √v * √(2 * τ)})
      ?_ (measure_ne_top _ _)).trans (gaussian_minStretch_deviation hd hv hτ)
  rintro G ⟨x, hx, hbad⟩
  exact ⟨x, hx, hbad.trans_le (by nlinarith only [hmean])⟩

end BstLean.Part208
