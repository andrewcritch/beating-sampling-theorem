import Mathlib

/-!
# Part 29, layer L4 (F1): a Bessel inequality for the variance

The parity floor of part 20 (Lemma F) and part 29 bounds `Var_x f(m(x))` below by its projection onto the
orthogonal multilinear monomials `x_S`. This file states the abstract step: for a finite family `φ_s` with
mean zero, pairwise orthogonal, and `E φ_s² = w > 0`, `Var h ≥ Σ_s (E[h φ_s])² / w`.
-/

namespace BstLean.Part29

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private theorem energy_bound (P : Measure Ω) (φ : ι → Ω → ℝ) (w : ℝ)
    (hw : 0 < w)
    (hφ2 : ∀ s t, Integrable (fun ω => φ s ω * φ t ω) P)
    (horth : ∀ s t, s ≠ t → ∫ ω, φ s ω * φ t ω ∂P = 0)
    (hnorm : ∀ s, ∫ ω, φ s ω ^ 2 ∂P = w)
    (S : Finset ι) :
    ∀ h : Ω → ℝ, Integrable (fun ω => h ω ^ 2) P →
    (∀ s, Integrable (fun ω => h ω * φ s ω) P) →
    ∑ s ∈ S, (∫ ω, h ω * φ s ω ∂P) ^ 2 / w ≤ ∫ ω, h ω ^ 2 ∂P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro h hh2 hhφ
      simpa using integral_nonneg (fun ω => sq_nonneg (h ω))
  | @insert a S ha ih =>
      intro h hh2 hhφ
      let c := (∫ ω, h ω * φ a ω ∂P) / w
      let r := fun ω => h ω - c * φ a ω
      have hpa : Integrable (fun ω => φ a ω ^ 2) P := by
        simpa only [pow_two] using hφ2 a a
      have hr2 : Integrable (fun ω => r ω ^ 2) P := by
        have := (hh2.sub ((hhφ a).const_mul (2*c))).add (hpa.const_mul (c^2))
        convert this using 1
        ext ω
        dsimp [r]
        ring
      have hrφ : ∀ s, Integrable (fun ω => r ω * φ s ω) P := by
        intro s
        convert (hhφ s).sub ((hφ2 a s).const_mul c) using 1
        ext ω
        dsimp [r]
        ring
      have hcov (s : ι) (hs : s ∈ S) :
          (∫ ω, r ω * φ s ω ∂P) = ∫ ω, h ω * φ s ω ∂P := by
        have has : a ≠ s := by intro e; exact ha (e ▸ hs)
        simp only [r, sub_mul, mul_assoc]
        rw [integral_sub (hhφ s) ((hφ2 a s).const_mul c), integral_const_mul,
          horth a s has]
        simp
      have he : (∫ ω, r ω ^ 2 ∂P) =
          (∫ ω, h ω ^ 2 ∂P) - (∫ ω, h ω * φ a ω ∂P)^2 / w := by
        have heq : (fun ω => r ω ^ 2) =
            (fun ω => (h ω ^ 2 - (2*c) * (h ω * φ a ω)) + c^2 * φ a ω ^ 2) := by
          funext ω
          dsimp [r]
          ring
        have hsub : Integrable (fun ω => h ω ^ 2 - (2*c) * (h ω * φ a ω)) P :=
          hh2.sub ((hhφ a).const_mul (2*c))
        rw [heq, integral_add hsub (hpa.const_mul (c^2)),
          integral_sub hh2 ((hhφ a).const_mul (2*c))]
        simp only [integral_const_mul, hnorm]
        dsimp [c]
        field_simp [ne_of_gt hw]
        ring
      have hb := ih r hr2 hrφ
      rw [he] at hb
      have hsum : (∑ s ∈ S, (∫ ω, r ω * φ s ω ∂P)^2 / w) =
          ∑ s ∈ S, (∫ ω, h ω * φ s ω ∂P)^2 / w := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hcov s hs]
      rw [hsum] at hb
      rw [Finset.sum_insert ha]
      linarith

/-- **Bessel's inequality for the variance.** -/
theorem var_ge_bessel (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → ℝ) (φ : ι → Ω → ℝ) (w : ℝ)
    (hw : 0 < w)
    (hh2 : Integrable (fun ω => h ω ^ 2) P) (hh : Integrable h P)
    (hφ2 : ∀ s t, Integrable (fun ω => φ s ω * φ t ω) P)
    (hhφ : ∀ s, Integrable (fun ω => h ω * φ s ω) P) (hφ : ∀ s, Integrable (φ s) P)
    (hmean : ∀ s, ∫ ω, φ s ω ∂P = 0)
    (horth : ∀ s t, s ≠ t → ∫ ω, φ s ω * φ t ω ∂P = 0)
    (hnorm : ∀ s, ∫ ω, φ s ω ^ 2 ∂P = w) :
    ∑ s, (∫ ω, h ω * φ s ω ∂P) ^ 2 / w ≤ ∫ ω, (h ω - ∫ ω', h ω' ∂P) ^ 2 ∂P := by
  let μ := ∫ ω, h ω ∂P
  let H := fun ω => h ω - μ
  have hH2 : Integrable (fun ω => H ω ^ 2) P := by
    have := (hh2.sub (hh.const_mul (2*μ))).add (integrable_const (μ^2))
    convert this using 1
    ext ω
    dsimp [H]
    ring
  have hHφ : ∀ s, Integrable (fun ω => H ω * φ s ω) P := by
    intro s
    convert (hhφ s).sub ((hφ s).const_mul μ) using 1
    ext ω
    dsimp [H]
    ring
  have hcov (s : ι) : (∫ ω, H ω * φ s ω ∂P) = ∫ ω, h ω * φ s ω ∂P := by
    simp only [H, sub_mul]
    rw [integral_sub (hhφ s) ((hφ s).const_mul μ), integral_const_mul, hmean s]
    simp
  have hb := energy_bound P φ w hw hφ2 horth hnorm Finset.univ H hH2 hHφ
  simpa only [hcov, H, μ] using hb

end BstLean.Part29
