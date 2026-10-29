import BstLean.Part292Chi

/-! Count and transverse energy are paid once, without a union over table nodes. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153
open BstLean.Part151 (mask measurable_mask)

noncomputable def activeEnergy {m d : ℕ} (z : Fin m → ℝ)
    (G : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  ∑ i, if 0 < z i then normSq (G i) else 0

theorem activeEnergy_measurable (m d : ℕ) :
    Measurable (fun p : (Fin m → ℝ) × Matrix (Fin m) (Fin d) ℝ =>
      activeEnergy p.1 p.2) := by
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · exact measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst)
  · exact BstLean.Part130.measurable_normSq.comp ((measurable_pi_apply i).comp measurable_snd)
  · exact measurable_const

theorem active_count_card {m : ℕ} (z : Fin m → ℝ) :
    (∑ i, mask (z i)) = ((Finset.univ.filter fun i => 0 < z i).card : ℝ) := by
  classical
  simp only [mask]
  simp

theorem gated_chi_on_count {m d : ℕ} (hd : 0 < d) {η x : ℝ}
    (hx : 0 ≤ x)
    (hD0 : 0 < (d : ℝ)*((1/2-η)*m))
    (hD : x ≤ (d : ℝ)*((1/2-η)*m)) :
    ((stdGauss (Fin m)).prod (gaussMat m d 1)).real
      {p | (1/2-η)*m ≤ ∑ i, mask (p.1 i) ∧ activeEnergy p.1 p.2 <
        (d : ℝ)*((1/2-η)*m)-2*sqrt ((d : ℝ)*((1/2-η)*m)*x)} ≤
      exp (-x) := by
  let K : ℝ := (1/2-η)*m
  let D : ℝ := (d : ℝ)*K
  let E : Set ((Fin m → ℝ) × Matrix (Fin m) (Fin d) ℝ) :=
    {p | K ≤ ∑ i, mask (p.1 i) ∧ activeEnergy p.1 p.2 < D-2*sqrt (D*x)}
  have hEm : MeasurableSet E :=
    (measurableSet_le measurable_const
      (Finset.measurable_sum _ fun i _ => measurable_mask.comp
        ((measurable_pi_apply i).comp measurable_fst))).inter
      (measurableSet_lt (activeEnergy_measurable m d) measurable_const)
  have hE : ((stdGauss (Fin m)).prod (gaussMat m d 1)).real E ≤ exp (-x) := by
    apply prod_real_le_of_fibre hEm (exp_pos _).le
    intro z
    by_cases hz : K ≤ ∑ i, mask (z i)
    · let S := Finset.univ.filter fun i => 0 < z i
      have hcard : D ≤ (S.card : ℝ)*d := by
        have hc := active_count_card z
        change ∑ i, mask (z i) = (S.card : ℝ) at hc
        rw [hc] at hz
        dsimp [D]
        nlinarith [mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg d)]
      have hsel := selected_chi_lower hd S hx hD hD0 hcard
      apply le_trans (measureReal_mono ?_) hsel
      intro G hG
      change ∑ i ∈ S, normSq (G i) < D-2*sqrt (D*x)
      have he : ∑ i ∈ S, normSq (G i) = activeEnergy z G := by
        simp [S, activeEnergy, Finset.sum_filter]
      rw [he]
      exact hG.2
    · have he : {G | (z,G) ∈ E} = ∅ := by
        ext G
        simp [E, hz]
      rw [he]
      simp only [measureReal_empty]
      exact (exp_pos _).le
  exact hE

theorem product_count_lower {m d : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    ((stdGauss (Fin m)).prod (gaussMat m d 1)).real
      {p | ∑ i, mask (p.1 i) < (1/2-η)*m} ≤ exp (-2*η^2*m) := by
  have hf := prod_real_fst (μ₁ := stdGauss (Fin m)) (μ₂ := gaussMat m d 1)
    {z : Fin m → ℝ | ∑ i, mask (z i) < (1/2-η)*m}
  exact hf.le.trans (cnt_tail_lower hη)

theorem gated_chi_lower {m d : ℕ} (hd : 0 < d) {η x : ℝ}
    (hη : 0 ≤ η) (hx : 0 ≤ x)
    (hD0 : 0 < (d : ℝ)*((1/2-η)*m))
    (hD : x ≤ (d : ℝ)*((1/2-η)*m)) :
    ((stdGauss (Fin m)).prod (gaussMat m d 1)).real
      {p | activeEnergy p.1 p.2 <
        (d : ℝ)*((1/2-η)*m)-2*sqrt ((d : ℝ)*((1/2-η)*m)*x)} ≤
      exp (-2*η^2*m)+exp (-x) := by
  let K : ℝ := (1/2-η)*m
  let D : ℝ := (d : ℝ)*K
  let E : Set ((Fin m → ℝ) × Matrix (Fin m) (Fin d) ℝ) :=
    {p | K ≤ ∑ i, mask (p.1 i) ∧ activeEnergy p.1 p.2 < D-2*sqrt (D*x)}
  have hE : ((stdGauss (Fin m)).prod (gaussMat m d 1)).real E ≤ exp (-x) :=
    gated_chi_on_count hd hx hD0 hD
  have hcprod : ((stdGauss (Fin m)).prod (gaussMat m d 1)).real
      {p | ∑ i, mask (p.1 i) < K} ≤ exp (-2*η^2*m) := by
    exact product_count_lower hη
  let μ := (stdGauss (Fin m)).prod (gaussMat m d 1)
  let C : Set ((Fin m → ℝ) × Matrix (Fin m) (Fin d) ℝ) :=
    {p | ∑ i, mask (p.1 i) < K}
  let T : Set ((Fin m → ℝ) × Matrix (Fin m) (Fin d) ℝ) :=
    {p | activeEnergy p.1 p.2 < D-2*sqrt (D*x)}
  have hsub : T ⊆ C ∪ E := by
    intro p hp
    by_cases hk : ∑ i, mask (p.1 i) < K
    · exact Or.inl hk
    · exact Or.inr ⟨le_of_not_gt hk, hp⟩
  have hm : μ.real T ≤ μ.real C + μ.real E :=
    (measureReal_mono hsub).trans (measureReal_union_le C E)
  exact hm.trans (add_le_add hcprod hE)

end BstLean.Part292
