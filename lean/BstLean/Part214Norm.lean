import BstLean.Part109DiagA
import BstLean.Part141Centre

/-! Exact logarithmic Chernoff bounds for the first-layer norm. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 BstLean.Part130 BstLean.Part141

section
variable {ι : Type} [Fintype ι]

/-- A single signed tilt covers both chi-square tails. -/
theorem norm_tilt_charge {η : ℝ} (hη : -1 < η) :
    (stdGauss ι).real {ξ | 0 ≤ (η / (2 * (1 + η))) *
      ((∑ i, ξ i ^ 2) - (1 + η) * (Fintype.card ι : ℝ))} ≤
      exp (-(Fintype.card ι : ℝ) / 2 * (η - log (1 + η))) := by
  let d : ℝ := Fintype.card ι
  let s : ℝ := η / (2 * (1 + η))
  have h1 : 0 < 1 + η := by linarith
  have he : 1 + 2 * (-s) = (1 + η)⁻¹ := by dsimp [s]; field_simp; ring
  obtain ⟨hi, hv⟩ := BstLean.Part109.mgfPi (ι := ι) (fun _ => -s) (fun _ => by
    have h : 0 < 1 + 2 * (-s) := by rw [he]; positivity
    linarith)
  let C := exp (-s * ((1 + η) * d))
  have hb := BstLean.Part109.chern (ι := ι)
    (S := {ξ | 0 ≤ s * ((∑ i, ξ i ^ 2) - (1 + η) * d)})
    (h := fun ξ => C * exp (-∑ i, -s * ξ i ^ 2))
    (fun ξ => by dsimp [C]; positivity) (hi.const_mul C) (by
      intro ξ hξ
      dsimp only [C]
      rw [← exp_add]
      apply one_le_exp
      have hs : (∑ i, -s * ξ i ^ 2) = -s * ∑ i, ξ i ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      rw [hs]
      change 0 ≤ s * ((∑ i, ξ i ^ 2) - (1 + η) * d) at hξ
      nlinarith)
  refine hb.trans_eq ?_
  rw [integral_const_mul, hv]
  simp only [he, Finset.prod_const, Finset.card_univ]
  have hroot : (√((1 + η)⁻¹))⁻¹ = exp (log (1 + η) / 2) := by
    rw [sqrt_inv, inv_inv, BstLean.Part109.sqrt_eq_exp h1]
  rw [hroot, ← exp_nat_mul, ← exp_add]
  have hmul : s * (1 + η) = η / 2 := by dsimp [s]; field_simp
  dsimp [C, d]
  congr 1
  have hh := congrArg (fun x : ℝ => x * (Fintype.card ι : ℝ)) hmul
  nlinarith [hh]

theorem norm_upper_charge {ε : ℝ} (hε : 0 < ε) :
    (stdGauss ι).real {ξ | (1 + ε) * (Fintype.card ι : ℝ) < ∑ i, ξ i ^ 2} ≤
      exp (-(Fintype.card ι : ℝ) / 2 * (ε - log (1 + ε))) := by
  apply (measureReal_mono (fun ξ hξ => ?_)).trans (norm_tilt_charge (by linarith : -1 < ε))
  change 0 ≤ (ε / (2 * (1 + ε))) * ((∑ i, ξ i ^ 2) - (1 + ε) * (Fintype.card ι : ℝ))
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hξ.le)

theorem norm_lower_charge {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (stdGauss ι).real {ξ | (∑ i, ξ i ^ 2) < (1 - ε) * (Fintype.card ι : ℝ)} ≤
      exp (-(Fintype.card ι : ℝ) / 2 * (-ε - log (1 - ε))) := by
  have h := norm_tilt_charge (ι := ι) (η := -ε) (by linarith)
  rw [show 1 + -ε = 1 - ε by ring] at h
  apply (measureReal_mono (fun ξ hξ => ?_)).trans h
  change 0 ≤ (-ε / (2 * (1 - ε))) * ((∑ i, ξ i ^ 2) - (1 - ε) * (Fintype.card ι : ℝ))
  exact mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    (sub_nonpos.mpr hξ.le)

end

noncomputable def firstOmega {N m : ℕ} (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  rowS M₁ / (2 * (m : ℝ))

lemma measurable_firstOmega {N m : ℕ} :
    Measurable (firstOmega : Matrix (Fin m) (Fin N) ℝ → ℝ) := measurable_rowS.div_const _

/-- The He-scaled norm has exactly the paper's two logarithmic payments. -/
theorem firstOmega_charge {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (gaussMat m N (2 / (N : ℝ))).real {M | ε < |firstOmega M - 1|} ≤
      exp (-((m : ℝ) * N) / 2 * (ε - log (1 + ε))) +
      exp (-((m : ℝ) * N) / 2 * (-ε - log (1 - ε))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let T : (Fin m × Fin N → ℝ) → Matrix (Fin m) (Fin N) ℝ :=
    fun ξ => Matrix.of fun i j => √(2 / (N : ℝ)) * ξ (i, j)
  have mT : Measurable T := by dsimp [T]; fun_prop
  have mS : MeasurableSet {M : Matrix (Fin m) (Fin N) ℝ | ε < |firstOmega M - 1|} :=
    measurableSet_lt measurable_const ((measurable_firstOmega.sub measurable_const).abs)
  have hT : ∀ ξ, firstOmega (T ξ) = (∑ i, ξ i ^ 2) / ((m : ℝ) * N) := by
    intro ξ
    unfold firstOmega rowS normSq rowOf
    dsimp [T]
    simp_rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / (N : ℝ))]
    simp_rw [← Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    field_simp
    <;> ring
  change ((stdGauss (Fin m × Fin N)).map T).real _ ≤ _
  rw [map_measureReal_apply mT mS]
  have hs : T ⁻¹' {M | ε < |firstOmega M - 1|} ⊆
      {ξ | (1 + ε) * (Fintype.card (Fin m × Fin N) : ℝ) < ∑ i, ξ i ^ 2} ∪
        {ξ | (∑ i, ξ i ^ 2) < (1 - ε) * (Fintype.card (Fin m × Fin N) : ℝ)} := by
    intro ξ hξ
    change ε < |firstOmega (T ξ) - 1| at hξ
    rw [hT] at hξ
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, mem_union, mem_setOf_eq]
    rcases lt_abs.mp hξ with h | h
    · left
      have hh : 1 + ε < (∑ i, ξ i ^ 2) / ((m : ℝ) * N) := by linarith
      exact (lt_div_iff₀ (by positivity)).mp hh
    · right
      have hh : (∑ i, ξ i ^ 2) / ((m : ℝ) * N) < 1 - ε := by linarith
      exact (div_lt_iff₀ (by positivity)).mp hh
  have hb := (measureReal_mono (μ := stdGauss (Fin m × Fin N)) hs).trans
    (measureReal_union_le _ _)
  have hu := norm_upper_charge (ι := Fin m × Fin N) hε
  have hl := norm_lower_charge (ι := Fin m × Fin N) hε hε1
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
    hb.trans (add_le_add hu hl)

end BstLean.Part214
#print axioms BstLean.Part214.norm_tilt_charge
#print axioms BstLean.Part214.firstOmega_charge
