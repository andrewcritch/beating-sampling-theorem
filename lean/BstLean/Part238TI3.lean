import BstLean.Part238Charge

/-! Part 238: a proved three-mode TI supply from the inherited TI-lite route of Part 182.
The constants and the charge `51 e^{-τ} + 12 e^{-2η²m}` are those of the inherited route.
They are not the paper-sharp constants or the paper charge `50 e^{-τ}` of Lemma `t7:p04:ti`. -/
namespace BstLean.Part238
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part182
open BstLean.Part151 (jac)
open BstLean.Part153 (projT nrm jacT)

variable {n : ℕ}

/-- **Inherited three-mode pair tail.** Under the block side conditions of `ta_pair`, the three
mode bounds and the overlap cap fail with probability at most `51e^{-τ} + 12e^{-2η²m}`. -/
theorem ta_pair3 (hn : 2 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) {cp τ η kE ko ks : ℝ} (hcp0 : 0 ≤ x ⬝ᵥ x') (hcp : x ⬝ᵥ x' ≤ cp)
    (hcp1 : cp ≤ 1) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (ham : 0 < s3am n τ) (hdm : 0 ≤ s3dm n τ (x ⬝ᵥ x'))
    (h6 : s3dm n τ (x ⬝ᵥ x') ^ 2 ≤ 2 * s3ap n τ ^ 2) (hc1 : s3c1 n τ (x ⬝ᵥ x') < 1)
    (hr1 : 0 ≤ s3Cpa n (x ⬝ᵥ x') - s3r1 n τ)
    (hpos : s3e0 n τ ≤ (s3Cpa n (x ⬝ᵥ x') - s3r1 n τ) / s3ap n τ)
    (hkE : e3_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) ≤ n * kE)
    (hko : o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) ≤ n * ko)
    (hks : s3nks n τ η (x ⬝ᵥ x') ≤ n * ks) :
    (BstLean.Part153.nuA n).real
      {θ | ¬ ModeBounds (jac θ.1 θ.2 x) (jac θ.1 θ.2 x') kE ko ks cp x x'} ≤
      51 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  have hn1 : 1 ≤ n := by omega
  have hc' : (x' ⬝ᵥ x) ^ 2 < 1 := by rwa [dotProduct_comm]
  set μ := BstLean.Part153.nuA n with hμ
  have hP : IsProbabilityMeasure μ := by
    rw [hμ]; unfold BstLean.Part153.nuA gaussMat; infer_instance
  set SE := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      e3_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) <
      opN (PEm x x' * ((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') * PEm x x')} with hSE
  set SO1 := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) <
      nrm (PEm x x' *ᵥ (((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') *ᵥ eTan x' x))} with hSO1
  set SO2 := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) <
      nrm (PEm x' x *ᵥ (((jac θ.1 θ.2 x')ᵀ * jac θ.1 θ.2 x) *ᵥ eTan x x'))} with hSO2
  set SS := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      s3nks n τ η (x ⬝ᵥ x') <
      |(jac θ.1 θ.2 x *ᵥ eTan x x') ⬝ᵥ (jac θ.1 θ.2 x' *ᵥ eTan x' x)|} with hSS
  have hE := e4_Eblock hx hx' hc hn1 hcp hcp1 hη hτ ham hdm h6 hc1.le
  have hO1 := o3_Oblock hn hx hx' hc hτ hη hη
  have hO2 := o3_Oblock hn hx' hx hc' hτ hη hη
  have hS := s3_Sblock hn1 hx hx' hc hτ hη ham hdm h6 hc1 hr1 hpos
  have hcc : (x ⬝ᵥ x') ^ 2 ≤ cp ^ 2 := pow_le_pow_left₀ hcp0 hcp 2
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ¬ ModeBounds (jac θ.1 θ.2 x) (jac θ.1 θ.2 x') kE ko ks cp x x'} ⊆
      ((SE ∪ SO1) ∪ SO2) ∪ SS := by
    intro θ hθ
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hno
    simp only [hSE, hSO1, hSO2, hSS, Set.mem_setOf_eq, not_lt] at h1 h2 h3 h4
    apply hθ
    refine ⟨hcc, h1.trans hkE, h2.trans hko, ?_, h4.trans hks⟩
    rw [ta_PEm_symm hx hx' hc]
    exact h3.trans hko
  calc μ.real {θ | ¬ ModeBounds (jac θ.1 θ.2 x) (jac θ.1 θ.2 x') kE ko ks cp x x'}
      ≤ μ.real (((SE ∪ SO1) ∪ SO2) ∪ SS) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real SE + μ.real SO1 + μ.real SO2 + μ.real SS := by
        refine (measureReal_union_le _ _).trans ?_
        refine add_le_add ((measureReal_union_le _ _).trans ?_) le_rfl
        exact add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ (12 * exp (-τ) + 4 * exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (8 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) + exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (8 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) + exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (23 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ))) := by
        gcongr
    _ = 51 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by ring

/-- **Inherited three-mode TI supply** from the numeric hypotheses `ta_num` of Part 182. -/
theorem ta_TI3 (hn : 2 ≤ n) {cm cp kE ko ks η τ : ℝ} (hcm : 0 ≤ cm) (hcp : cp < 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hnum : ta_num n cm cp kE ko ks η τ) :
    TI3_hyp n cm cp kE ko ks (51 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))) := by
  intro x x' hx hx' h1 h2
  obtain ⟨hko, ham, hall⟩ := hnum
  obtain ⟨hdm, h6, hc1, hr1, hpos, hkE, hks⟩ := hall _ h1 h2
  have hc : (x ⬝ᵥ x') ^ 2 < 1 := by nlinarith
  exact ta_pair3 hn hx hx' hc (hcm.trans h1) h2 hcp.le hη hτ ham hdm h6 hc1 hr1 hpos hkE hko hks

end BstLean.Part238
