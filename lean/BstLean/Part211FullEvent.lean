import BstLean.Part211Deviation
import BstLean.Part160MFD

/-! The complete full-error source intersection and its probability charge. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (sO2 gO rhoC)
open BstLean.Part153
open BstLean.Part154 (BadH csC)

lemma measurable_sharp_MA {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    MeasurableSet {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ | p.2 ∉ SharpMA n c τ p.1} := by
  have hd : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => BstLean.Part154.dC p.1 p.2 c τ) :=
    BstLean.Part160.measurable_dC_gen measurable_const measurable_const measurable_fst measurable_snd
  have hm := (hd.stronglyMeasurable.integral_prod_right'
    (ν := gaussMat (mA n) (mA n) (2 / (mA n : ℝ)))).measurable
  have hb : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ =>
      BstLean.Part154.GamBarF (stdGauss (Fin n)) (BstLean.Part154.fA A c τ)) := by
    have he : (fun A : Matrix (Fin (mA n)) (Fin n) ℝ =>
        BstLean.Part154.GamBarF (stdGauss (Fin n)) (BstLean.Part154.fA A c τ)) =
        fun A => gO A c τ - sO2 A c τ := by
      funext A
      rw [BstLean.Part154.GamBarF_fA]
      unfold sO2 normSq
      ring
    rw [he]
    exact (measurable_gO_A1 (BstLean.Part130.one_le_mA hn) c τ).sub (measurable_sO2 c τ)
  simp only [SharpMA, mem_setOf_eq, not_le]
  exact measurableSet_lt ((hm.comp measurable_fst).add
    ((((hb.comp measurable_fst).sqrt).add measurable_const).const_mul _)) hd

/-- This restriction permits conditional concentration without an independence assumption. -/
theorem restricted_sharp_MA_charge {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hr : BstLean.Part154.rhoBar n csC < 1 / 4) :
    (nuA n).real {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      p.1 ∈ Eop n ∧ csC * τ ^ 2 ≤ sO2 p.1 c τ ∧ p.2 ∉ SharpMA n c τ p.1} ≤ exp (-12) := by
  have hm : MeasurableSet {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      p.1 ∈ Eop n ∧ csC * τ ^ 2 ≤ sO2 p.1 c τ ∧ p.2 ∉ SharpMA n c τ p.1} :=
    ((measurableSet_Eop n).preimage measurable_fst).inter
      ((measurableSet_le measurable_const ((measurable_sO2 c τ).comp measurable_fst)).inter
        (measurable_sharp_MA hn c τ))
  apply prod_real_le_of_fibre hm (by positivity)
  intro A
  by_cases h : A ∈ Eop n ∧ csC * τ ^ 2 ≤ sO2 A c τ
  · exact (measureReal_mono (by intro M hM; exact hM.2.2)).trans
      (sharp_MA_source_charge hn A c hτ csC_positive hr h.1 h.2)
  · have he : {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        A ∈ Eop n ∧ csC * τ ^ 2 ≤ sO2 A c τ ∧ M ∉ SharpMA n c τ A} = ∅ := by
      ext M
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun hM => h ⟨hM.1, hM.2.1⟩
    change (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))).real
      {M | A ∈ Eop n ∧ csC * τ ^ 2 ≤ sO2 A c τ ∧ M ∉ SharpMA n c τ A} ≤ _
    rw [he, measureReal_empty]
    positivity

def FullSource (n J : ℕ) (c : Fin n → ℝ) (τ MP : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {p | p ∈ EnergySource n J c τ ∧ p.1 ∉ BadH n c τ 12 ∧
    N1 2 p.1 c τ ≤ N12bar n 12 ∧ p.2 ∈ SharpMA n c τ p.1 ∧
    p.2 ∉ BadN22 n c τ p.1 ∧ XiS p.1 p.2 c τ ≤ MP * (2 / (n : ℝ)) / n}

/-- The energy, sharp MA, HS and radius sources cost eleven tails and the PP allowance. -/
theorem full_source_charge {n J P : ℕ} (hn : 4096 ≤ n) (hP : 1 ≤ P)
    (hnP : 2 * P + 1 < n) (c : Fin n → ℝ) {τ MP η : ℝ} (hτ : 0 < τ)
    (hMP : 0 < MP) (hη : 0 ≤ η) (hr : BstLean.Part154.rhoBar n csC < 1 / 4) :
    (nuA n).real (FullSource n J c τ MP)ᶜ ≤
      exp (-(n : ℝ) / 2) + 3445 / (n : ℝ) ^ 2 + 11 * exp (-12) +
        (jS n P η ^ 2 * n / (((n : ℝ) - 1 - 2 * P) * MP)) ^ P := by
  have hn0 : 1 ≤ n := by omega
  let B0 := (EnergySource n J c τ)ᶜ
  let B1 := {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ | p.1 ∈ BadH n c τ 12}
  let B2 := {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ | N12bar n 12 < N1 2 p.1 c τ}
  let B3 := {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
    p.1 ∈ Eop n ∧ csC * τ ^ 2 ≤ sO2 p.1 c τ ∧ p.2 ∉ SharpMA n c τ p.1}
  let B4 := {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ | p.2 ∈ BadN22 n c τ p.1}
  let B5 := {p : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ | MP * (2 / (n : ℝ)) / n < XiS p.1 p.2 c τ}
  have hsub : (FullSource n J c τ MP)ᶜ ⊆ ((((B0 ∪ B1) ∪ B2) ∪ B3) ∪ B4) ∪ B5 := by
    intro p hp
    by_contra h
    simp only [mem_union, not_or] at h
    have he : p ∈ EnergySource n J c τ := not_not.mp h.1.1.1.1.1
    have hA : p.1 ∈ Eop n ∧ csC * τ ^ 2 ≤ sO2 p.1 c τ := by
      have ha := he.1
      simp only [FirstEnergyBad, mem_union, mem_compl_iff, mem_setOf_eq, not_or, not_not,
        not_lt] at ha
      exact ha.1.1
    apply hp
    exact ⟨he, h.1.1.1.1.2, not_lt.mp h.1.1.1.2,
      by by_contra hM; exact h.1.1.2 ⟨hA.1, hA.2, hM⟩, h.1.2, not_lt.mp h.2⟩
  have h0 := energy_source_charge hn J c hτ
  have h1 : (nuA n).real B1 ≤ exp (-12) := by
    rw [prod_real_fst]
    exact BstLean.Part154.EH_prob hn0 c τ (by norm_num)
  have h2 : (nuA n).real B2 ≤ exp (-12) := by
    change (nuA n).real {p | p.1 ∈ {A | N12bar n 12 < N1 2 A c τ}} ≤ _
    rw [prod_real_fst]
    exact N12_event hn0 c τ (by norm_num)
  have h3 := restricted_sharp_MA_charge hn0 c hτ hr
  have hm4 : MeasurableSet B4 := measurableSet_lt
    (((measurable_int_N2 hn0 (by norm_num : 1 ≤ 2) c τ).comp measurable_fst).add
      (((((measurable_N1 hn0 (by norm_num : 1 ≤ 2) c τ).comp measurable_fst).const_add 1).const_mul
        _).div_const _)) (measurable_N2_joint hn0 (by norm_num) c τ)
  have h4 : (nuA n).real B4 ≤ exp (-12) := prod_real_le_of_fibre hm4 (by positivity)
    (fun A => N22_event hn0 A c τ (by norm_num))
  have h5 := lemmaPP_XiS_sharp hP hnP c hτ hMP hη
  have u1 := measureReal_union_le (μ := nuA n) B0 B1
  have u2 := measureReal_union_le (μ := nuA n) (B0 ∪ B1) B2
  have u3 := measureReal_union_le (μ := nuA n) ((B0 ∪ B1) ∪ B2) B3
  have u4 := measureReal_union_le (μ := nuA n) (((B0 ∪ B1) ∪ B2) ∪ B3) B4
  have u5 := measureReal_union_le (μ := nuA n) ((((B0 ∪ B1) ∪ B2) ∪ B3) ∪ B4) B5
  have h6 := measureReal_mono (μ := nuA n) hsub
  change (nuA n).real B0 ≤ _ at h0
  change (nuA n).real B3 ≤ _ at h3
  change (nuA n).real B5 ≤ _ at h5
  linarith

#print axioms restricted_sharp_MA_charge
#print axioms full_source_charge
end BstLean.Part211
