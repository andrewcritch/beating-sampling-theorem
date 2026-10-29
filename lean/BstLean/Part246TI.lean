import BstLean.Part246EBlock
import BstLean.Part244TI

/-! Part 244: **the sharp two-input Jacobian bound (Lemma `t7:p04:ti`) as a three-mode TI
hypothesis**, with the paper's E-block constant (sharp, via Gordon/Davidson–Szarek), and the
paper's O-block and S-block constants (Part 182). The charge is
`53 e^{-τ} + 12 e^{-2η²m}` from the separate block accounting. -/
namespace BstLean.Part246
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part151 (jac)
open BstLean.Part153 (projT nrm jacT)
open BstLean.Part238 (ModeBounds TI3_hyp TI3_of_cover SharpCovEvent SharpCovEvent_ret_charge_M12)

variable {n : ℕ}

/-- **The sharp pair tail.** -/
theorem ta_pair3_sharp (hn : 2 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) {cp τ η kE ko ks : ℝ} (hcp0 : 0 ≤ x ⬝ᵥ x') (hcp : x ⬝ᵥ x' ≤ cp)
    (hcp1 : cp ≤ 1) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (ham : 0 < s3am n τ) (hdm : 0 ≤ s3dm n τ (x ⬝ᵥ x'))
    (h6 : s3dm n τ (x ⬝ᵥ x') ^ 2 ≤ 2 * s3ap n τ ^ 2) (hc1 : s3c1 n τ (x ⬝ᵥ x') < 1)
    (hr1 : 0 ≤ s3Cpa n (x ⬝ᵥ x') - s3r1 n τ)
    (hpos : s3e0 n τ ≤ (s3Cpa n (x ⬝ᵥ x') - s3r1 n τ) / s3ap n τ)
    (hkE : e3s_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) ≤ n * kE)
    (hko : o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) ≤ n * ko)
    (hks : s3nks n τ η (x ⬝ᵥ x') ≤ n * ks) :
    (BstLean.Part153.nuA n).real
      {θ | ¬ ModeBounds (jac θ.1 θ.2 x) (jac θ.1 θ.2 x') kE ko ks cp x x'} ≤
      53 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  have hn1 : 1 ≤ n := by omega
  have hc' : (x' ⬝ᵥ x) ^ 2 < 1 := by rwa [dotProduct_comm]
  set μ := BstLean.Part153.nuA n with hμ
  have hP : IsProbabilityMeasure μ := by
    rw [hμ]; unfold BstLean.Part153.nuA gaussMat; infer_instance
  set SE := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      e3s_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (√(2 * τ))
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
  have hE := e4_Eblock_sharp hx hx' hc hn1 hcp hcp1 hη hτ ham hdm h6 hc1.le
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
    _ ≤ (14 * exp (-τ) + 4 * exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (8 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) + exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (8 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) + exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (23 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ))) := by
        gcongr
    _ = 53 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by ring

/-- The numeric premises of the sharp Lemma TI on the overlap class `[cm, cp]`. -/
def ta_num_sharp (n : ℕ) (cm cp kE ko ks η τ : ℝ) : Prop :=
  o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) ≤ n * ko ∧
  0 < s3am n τ ∧
  ∀ c, cm ≤ c → c ≤ cp →
    0 ≤ s3dm n τ c ∧ s3dm n τ c ^ 2 ≤ 2 * s3ap n τ ^ 2 ∧ s3c1 n τ c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n τ ∧ s3e0 n τ ≤ (s3Cpa n c - s3r1 n τ) / s3ap n τ ∧
    e3s_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ c) / 2 + η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) ≤ n * kE ∧
    s3nks n τ η c ≤ n * ks

/-- **Sharp Lemma TI as a three-mode hypothesis.** -/
theorem ta_TI3_sharp (hn : 2 ≤ n) {cm cp kE ko ks η τ : ℝ} (hcm : 0 ≤ cm) (hcp : cp < 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hnum : ta_num_sharp n cm cp kE ko ks η τ) :
    TI3_hyp n cm cp kE ko ks (53 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))) := by
  intro x x' hx hx' h1 h2
  obtain ⟨hko, ham, hall⟩ := hnum
  obtain ⟨hdm, h6, hc1, hr1, hpos, hkE, hks⟩ := hall _ h1 h2
  have hc : (x ⬝ᵥ x') ^ 2 < 1 := by nlinarith
  exact ta_pair3_sharp hn hx hx' hc (hcm.trans h1) h2 hcp.le hη hτ ham hdm h6 hc1 hr1 hpos hkE hko
    hks

/-- **The M1/M2 sharp covariance event charge from the sharp Lemma TI.** Given the wide operator
hypothesis and the sharp numeric premises on the core overlap class `[.40, .63]`, the joint event
costs `ε` once. -/
theorem SharpCovEvent_ret_charge_M12_TI {n : ℕ} (hn : 11883 ≤ n) (D : Design n)
    (hτW : TauWorld D) {lam₀ kE ko ks η τ ε : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hlam : ta_lam kE ko ks ≤ lam₀) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hTI₀ : TI_hyp n (34 / 100) (73 / 100) lam₀
      (53 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))))
    (hnum : ta_num_sharp n (40 / 100) (63 / 100) kE ko ks η τ) :
    (retDist D.toCentres).real
      (agentEv D (SharpCovEvent n BstLean.Part199.exampleWide BstLean.Part199.exampleCore
        (46 / 100) (528 / 1000) lam₀ kE ko ks (63 / 100)
        ((53 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))) / ε)))ᶜ ≤ ε :=
  SharpCovEvent_ret_charge_M12 hn D hτW hkE hko hks hlam (by positivity) hε hTI₀
    (ta_TI3_sharp (by omega) (by norm_num) (by norm_num) hη hτ hnum)

end BstLean.Part246

namespace BstLean.Part246
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part151 (jac)
open BstLean.Part238 (ModeBounds TI3_hyp SharpCovEvent SharpCovEvent_ret_charge_M12)

/-- **M1/M2 sharp covariance event charge from the sharp Lemma TI at both levels.** The only
remaining premises are the sharp numeric conditions on the wide overlap class `[.34, .73]`
(constants `kE₀, ko₀, ks₀`, `λ₀ = λ(kE₀, ko₀, ks₀)`) and on the core class `[.40, .63]`. -/
theorem SharpCovEvent_ret_charge_M12_num {n : ℕ} (hn : 11883 ≤ n) (D : Design n)
    (hτW : TauWorld D) {kE₀ ko₀ ks₀ kE ko ks η τ ε : ℝ}
    (hkE₀ : 0 ≤ kE₀) (hko₀ : 0 ≤ ko₀) (hks₀ : 0 ≤ ks₀)
    (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hlam : ta_lam kE ko ks ≤ ta_lam kE₀ ko₀ ks₀) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hnum₀ : ta_num_sharp n (34 / 100) (73 / 100) kE₀ ko₀ ks₀ η τ)
    (hnum : ta_num_sharp n (40 / 100) (63 / 100) kE ko ks η τ) :
    (retDist D.toCentres).real
      (agentEv D (SharpCovEvent n BstLean.Part199.exampleWide BstLean.Part199.exampleCore
        (46 / 100) (528 / 1000) (ta_lam kE₀ ko₀ ks₀) kE ko ks (63 / 100)
        ((53 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))) / ε)))ᶜ ≤ ε :=
  SharpCovEvent_ret_charge_M12 hn D hτW hkE hko hks hlam (by positivity) hε
    (BstLean.Part244.TI_hyp_of_TI3 (by omega) hkE₀ hko₀ hks₀ (by norm_num)
      (ta_TI3_sharp (by omega) (by norm_num) (by norm_num) hη hτ hnum₀))
    (ta_TI3_sharp (by omega) (by norm_num) (by norm_num) hη hτ hnum)

end BstLean.Part246
