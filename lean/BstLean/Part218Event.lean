import BstLean.Part218ConcreteKernels
import BstLean.Part218DirectionCharge
import BstLean.Part218Positive

/-! The complete concrete first-layer event and its P10e complement charge. -/
namespace BstLean.Part218
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part214

noncomputable def e1Statistics (N m : ℕ) : Fin 4 → Matrix (Fin m) (Fin N) ℝ → ℝ :=
  ![paperTrace N m, BstLean.Part214.paperDiagonal N m,
    offStatistic (remainderKernel N) m, fun M => offStatistic (normKernel N) m M + inputVarianceMean N m]
noncomputable def e1MeanBounds (N m : ℕ) : Fin 4 → ℝ :=
  ![(m : ℝ) * N * (m + N + 1), (m : ℝ) * N * (N + 2),
    covarianceMeanBound N m, inputVarianceMean N m]
noncomputable def e1Centers (N m : ℕ) : Fin 4 → ℝ :=
  ![(m : ℝ) * N * (m + N + 1), (m : ℝ) * N * (N + 2),
    covarianceMean N m, inputVarianceMean N m]
noncomputable def e1Variances (N m : ℕ) : Fin 4 → ℝ :=
  ![traceVariance N m, 8 * (m : ℝ) * N * (N + 2) * (N + 3),
    covarianceVarianceBound N m, normVarianceBound N m]

noncomputable def concreteFirstLayerEvent (N m : ℕ) (εω ph : ℝ) (ε : Fin 4 → ℝ) :
    Set (Matrix (Fin m) (Fin N) ℝ) :=
  firstLayerEvent firstOmega worldDirection (e1Statistics N m) εω (directionMean N m) ph
    (e1MeanBounds N m) ε

theorem concreteFirstLayerEvent_iff {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ)
    (εω ph : ℝ) (ε : Fin 4 → ℝ) :
    M ∈ concreteFirstLayerEvent N m εω ph ε ↔
      |firstOmega M - 1| ≤ εω ∧
      paperTrace N m M ≤ (1 + ε 0) * ((m : ℝ) * N * (m + N + 1)) ∧
      BstLean.Part214.paperDiagonal N m M ≤ (1 + ε 1) * ((m : ℝ) * N * (N + 2)) ∧
      offStatistic (remainderKernel N) m M ≤ (1 + ε 2) * covarianceMeanBound N m ∧
      worldDirection M ≤ directionMean N m / ph ∧
      offStatistic (normKernel N) m M ≤ ε 3 * inputVarianceMean N m := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1 0, h.2.1 1, h.2.1 2, h.2.2, ?_⟩
    have h3 := h.2.1 3
    change offStatistic (normKernel N) m M + inputVarianceMean N m ≤
      (1 + ε 3) * inputVarianceMean N m at h3
    linarith
  · rintro ⟨hω, hS, hB, hC, hH, hV⟩
    refine ⟨hω, ?_, hH⟩
    intro i
    fin_cases i
    · exact hS
    · exact hB
    · exact hC
    · change offStatistic (normKernel N) m M + inputVarianceMean N m ≤
        (1 + ε 3) * inputVarianceMean N m
      linarith

lemma e1Statistics_measurable {N m : ℕ} (hN : 1 ≤ N) (i : Fin 4) :
    Measurable (e1Statistics N m i) := by
  fin_cases i
  · exact (measurable_wishartTrace N m).const_mul _
  · exact BstLean.Part214.measurable_paperDiagonal N m
  · exact offStatistic_measurable (remainderKernel_measurable N)
  · exact (offStatistic_measurable (normKernel_measurable hN)).add_const _

lemma e1MeanBounds_pos {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m) (i : Fin 4) :
    0 < e1MeanBounds N m i := by
  have hn' : (0 : ℝ) < N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : 0 < (m : ℝ) - 1 := by linarith
  fin_cases i
  · change 0 < (m : ℝ) * N * (m + N + 1)
    positivity
  · change 0 < (m : ℝ) * N * (N + 2)
    positivity
  · change 0 < covarianceMeanBound N m
    unfold covarianceMeanBound
    have hj := angularJ2_pos hN (angularOffset N)
    positivity
  · exact inputVarianceMean_pos (by omega) (by omega)

lemma e1Centers_le {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m) (i : Fin 4) :
    e1Centers N m i ≤ e1MeanBounds N m i := by
  fin_cases i
  · exact le_rfl
  · exact le_rfl
  · exact (covarianceOff_supply hN hm).2.1
  · exact le_rfl

lemma e1Centered_integrable {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m) (i : Fin 4) :
    Integrable (fun M => (e1Statistics N m i M - e1Centers N m i) ^ 2)
      (gaussMat m N (2 / (N : ℝ))) := by
  fin_cases i
  · exact (paperTrace_moments (m := m) (by omega : 1 ≤ N)).2.2.1
  · exact (BstLean.Part214.paperDiagonal_moments (m := m) (by omega : 1 ≤ N)).2.2.1
  · exact (covarianceOff_supply hN hm).1
  · simpa [e1Statistics, e1Centers] using (normOff_supply (by omega : 1 ≤ N) (by omega : 1 ≤ m)).1

lemma e1Centered_bound {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m) (i : Fin 4) :
    (∫ M, (e1Statistics N m i M - e1Centers N m i) ^ 2 ∂gaussMat m N (2 / (N : ℝ))) ≤
      e1Variances N m i := by
  fin_cases i
  · exact (paperTrace_moments (m := m) (by omega : 1 ≤ N)).2.2.2.le
  · exact (BstLean.Part214.paperDiagonal_moments (m := m) (by omega : 1 ≤ N)).2.2.2.le
  · exact (covarianceOff_supply hN hm).2.2
  · simpa [e1Statistics, e1Centers, e1Variances] using
      (normOff_supply (by omega : 1 ≤ N) (by omega : 1 ≤ m)).2

/-- All moment supplies concern the actual matrix statistics. No moment hypothesis remains. -/
theorem concreteFirstLayerEvent_charge {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m)
    {εω ph : ℝ} {ε : Fin 4 → ℝ} (hεω : 0 < εω) (hεω1 : εω < 1)
    (hph : 0 < ph) (hε : ∀ i, 0 < ε i) :
    MeasurableSet (concreteFirstLayerEvent N m εω ph ε) ∧
    (gaussMat m N (2 / (N : ℝ))).real (concreteFirstLayerEvent N m εω ph ε)ᶜ ≤
      (exp (-((m : ℝ) * N) / 2 * (εω - log (1 + εω))) +
        exp (-((m : ℝ) * N) / 2 * (-εω - log (1 - εω)))) +
        (∑ i, e1Variances N m i / (ε i * e1MeanBounds N m i) ^ 2) + ph := by
  have hn : 1 ≤ N := by omega
  have hm1 : 1 ≤ m := by omega
  exact firstLayerEvent_world_charge hn hm1 (worldDirection_measurable hn)
    (e1Statistics_measurable hn) hεω hεω1 (e1MeanBounds_pos hN hm) hε
    (directionMean_pos hN hm1) hph (fun M => centeredGram_nonneg M (BstLean.Part137.h1bar M))
    (worldDirection_mean hn hm1).1 (worldDirection_mean hn hm1).2.le
    (e1Centered_integrable hN hm) (e1Centers_le hN hm) (e1Centered_bound hN hm)

end BstLean.Part218
#print BstLean.Part218.concreteFirstLayerEvent_charge
#print axioms BstLean.Part218.concreteFirstLayerEvent_charge
