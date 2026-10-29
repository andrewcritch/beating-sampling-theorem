import BstLean.Part207Moments
import BstLean.Part162Pq

/-! A cubic bound for the radial quadratic plus a Gaussian linear term. -/
namespace BstLean.Part207
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)

lemma eval_preserving {n : ℕ} (i : Fin n) :
    MeasurePreserving (Function.eval i : (Fin n → ℝ) → ℝ) (stdGauss (Fin n))
      (gaussianReal 0 1) :=
  measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i

lemma linear_four {n : ℕ} (u : Fin n → ℝ) :
    MemLp (fun z : Fin n → ℝ => ∑ i, u i * z i) 4 (stdGauss (Fin n)) ∧
    ∫ z : Fin n → ℝ, (∑ i, u i * z i) ^ 4 ∂stdGauss (Fin n) =
      3 * (∑ i, u i ^ 2) ^ 2 := by
  classical
  have hm : MemLp (fun z : Fin n → ℝ => ∑ i, u i * z i) 4 (stdGauss (Fin n)) := by
    have h := memLp_finsetSum' Finset.univ (fun i _ =>
      ((memLp_id_gaussianReal (μ := 0) (v := 1) 4).comp_measurePreserving
        (eval_preserving i)).const_mul (u i))
    have he : (∑ i : Fin n, fun z : Fin n → ℝ => u i * (id ∘ Function.eval i) z) =
        (fun z : Fin n → ℝ => ∑ i, u i * z i) := by
      funext z
      simp
    rw [he] at h
    exact h
  refine ⟨hm, ?_⟩
  have h := BstLean.Part162.gauss_dot_mom u 4
  have hg : BstLean.Part162.gmom 4 = 3 := by
    unfold BstLean.Part162.gmom
    simp only [abs_four]
    exact BstLean.Part151.gm4
  have hu : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [dotProduct, mul_comm, abs_four] at h
  rw [hg] at h
  convert h using 1
  simp only [dotProduct, ← sq, show ∀ x : ℝ, √x ^ 4 = (√x ^ 2) ^ 2 from fun x => by ring]
  rw [Real.sq_sqrt hu]

/-- The triangle second-moment bound is sufficient for a cubic coefficient four.
No division by the linear coefficient or the centre norm occurs. -/
theorem quadratic_cube {n : ℕ} (K b : ℝ) (u : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => |K + b * (normSq z - n) + ∑ i, u i * z i| ^ 3)
      (stdGauss (Fin n)) ∧
    ∫ z : Fin n → ℝ, |K + b * (normSq z - n) + ∑ i, u i * z i| ^ 3
      ∂stdGauss (Fin n) ≤
      4 * (|K| + |b| * √(2 * (n : ℝ)) + √(∑ i, u i ^ 2)) ^ 3 := by
  classical
  let γ := stdGauss (Fin n)
  let W : (Fin n → ℝ) → ℝ := fun z => normSq z - n
  let D : (Fin n → ℝ) → ℝ := fun z => ∑ i, u i * z i
  let F : (Fin n → ℝ) → ℝ := fun z => K + b * W z + D z
  have mW : Measurable W := BstLean.Part130.measurable_normSq.sub_const _
  have mD : Measurable D := by dsimp [D]; fun_prop
  have mF : Measurable F := by dsimp [F]; fun_prop
  obtain ⟨iW4, _, hW2, hW4⟩ := BstLean.Part151.chi_centred n
  have w4 : MemLp W 4 γ := mem_four mW iW4
  have d4 : MemLp D 4 γ := (linear_four u).1
  have f4 : MemLp F 4 γ := ((memLp_const K).add (w4.const_mul b)).add d4
  have f2 : MemLp F 2 γ := f4.mono_exponent (by norm_num)
  have iF4 : Integrable (fun z => F z ^ 4) γ := by
    simpa [Real.norm_eq_abs, abs_four] using f4.integrable_norm_pow'
  have hW4' : lpNorm W 4 γ ≤ 2 * √(2 * (n : ℝ)) := by
    apply norm_four_le mW (by positivity)
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * n by positivity)
    calc ∫ z, W z ^ 4 ∂γ ≤ 16 * (2 * (n : ℝ)) ^ 2 := radial_four_le n
      _ = (2 * √(2 * (n : ℝ))) ^ 4 := by
        have he : √(2 * (n : ℝ)) ^ 4 = (2 * (n : ℝ)) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
        rw [mul_pow (2 : ℝ) (√(2 * (n : ℝ))) 4, he]
        norm_num
  have hW2' : lpNorm W 2 γ ≤ √(2 * (n : ℝ)) := by
    apply norm_two_le mW (by positivity)
    rw [hW2, Real.sq_sqrt (by positivity)]
  have hu : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hD4' : lpNorm D 4 γ ≤ 2 * √(∑ i, u i ^ 2) := by
    apply norm_four_le mD (by positivity)
    rw [(linear_four u).2]
    have he : √(∑ i, u i ^ 2) ^ 4 = (∑ i, u i ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hu]
    rw [mul_pow, he]
    norm_num
    nlinarith [sq_nonneg (∑ i, u i ^ 2)]
  have hD2' : lpNorm D 2 γ ≤ √(∑ i, u i ^ 2) := by
    apply norm_two_le mD (by positivity)
    have h := BstLean.Part162.gauss_dot_mom u 2
    have hg : BstLean.Part162.gmom 2 = 1 := by
      unfold BstLean.Part162.gmom
      simp only [sq_abs]
      exact BstLean.Part151.gm2
    simp only [dotProduct, mul_comm, sq_abs] at h
    rw [hg] at h
    simpa [dotProduct, ← sq, Real.sq_sqrt hu] using h.le
  have normF (p : ℝ≥0∞) (hp : 1 ≤ p) (hw : MemLp W p γ) (hD : MemLp D p γ) :
      lpNorm F p γ ≤ |K| + |b| * lpNorm W p γ + lpNorm D p γ := by
    have h1 := lpNorm_add_le ((memLp_const K).add (hw.const_mul b)) hp (g := D)
    have h2 := lpNorm_add_le (memLp_const K : MemLp (fun _ : Fin n → ℝ => K) p γ)
      hp (g := b • W)
    have hconst : lpNorm (fun _ : Fin n → ℝ => K) p γ = |K| := by
      rw [lpNorm_const (by exact ne_of_gt (lt_of_lt_of_le (by norm_num) hp))
        (by exact MeasureTheory.IsProbabilityMeasure.ne_zero γ), probReal_univ]
      simp [Real.norm_eq_abs]
    rw [hconst, lpNorm_const_smul] at h2
    simp only [coe_nnnorm, Real.norm_eq_abs] at h2
    calc lpNorm F p γ ≤ lpNorm ((fun _ => K) + b • W) p γ + lpNorm D p γ := h1
      _ ≤ |K| + |b| * lpNorm W p γ + lpNorm D p γ := by gcongr
  let L := |K| + |b| * √(2 * (n : ℝ)) + √(∑ i, u i ^ 2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have nf2 : lpNorm F 2 γ ≤ L := by
    calc _ ≤ _ :=
        normF 2 (by norm_num) (w4.mono_exponent (by norm_num))
          (d4.mono_exponent (by norm_num))
      _ ≤ L := by dsimp [L]; gcongr
  have nf4 : lpNorm F 4 γ ≤ 2 * L := by
    calc _ ≤ _ := normF 4 (by norm_num) w4 d4
      _ ≤ |K| + |b| * (2 * √(2 * (n : ℝ))) + 2 * √(∑ i, u i ^ 2) := by gcongr
      _ ≤ 2 * L := by dsimp [L]; nlinarith [abs_nonneg K]
  apply cube_of_two_four mF iF4 hL
  · rw [← norm_two_sq mF]
    exact pow_le_pow_left₀ lpNorm_nonneg nf2 2
  · rw [← norm_four_pow mF]
    have h := pow_le_pow_left₀ lpNorm_nonneg nf4 4
    simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 from by norm_num] using h

end BstLean.Part207
