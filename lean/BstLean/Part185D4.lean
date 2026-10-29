import BstLean.Part185D2
import BstLean.Part185D3
import BstLean.Part182TIA

/-!
# Part 185 (file `D4`): the two-sided E block of Lemma TI under `nuA`, and Lemma TI with it

No proof is left open; no `native_decide` or `axiom` is used.

* **`d4_Eblock`**: `Pr_{nuA}(‖P_E Jᵀ J' P_E‖ > e3_bound2 …) ≤ 18e^{−τ} + 5e^{−2η²m} + net`, with
  `K₂ = m(κ̇(c₁⁺)/2 + η)` (upper count), `K₂⁻ = m(κ̇(c₁⁻)/2 − η)` (lower count, `d3_c1lo`), and
  `net = (2⌈√(2n)/ε⌉ + 1)^{2n} e^{−K₂⁻δ²/4}`.
* **`d4_pair`**, **`d4_TI`**, **`d4_TI46`**: Lemma TI (the pair tail, `ms_opN`) with the
  two-sided E block: charge `57e^{−τ} + 13e^{−2η²m} + N_b` (`N_b` bounds `net` on the window);
  at `τ = 46`, `2η²m ≥ 46`, `N_b ≤ 2·10⁻¹⁹`: `TI_hyp n cm cp λ 10⁻¹⁸`.
-/

namespace BstLean.Part185

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask jac)
open BstLean.Part153 (projT nrm nrm_mulVec_le opN_mul_le opN_le_of_bound gaussMat_decomp jacT)
open BstLean.Part151 (jac)
open BstLean.Part182
open BstLean.Part184 (gridN)

variable {n : ℕ}

section pair3
variable {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
  (hc : (x ⬝ᵥ x') ^ 2 < 1)
include hx hx' hc

theorem d4_Eblock (hn : 1 ≤ n) {cp η τ δ ε : ℝ} (hcp : x ⬝ᵥ x' ≤ cp) (hcp1 : cp ≤ 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (ham : 0 < s3am n τ) (hdm : 0 ≤ s3dm n τ (x ⬝ᵥ x'))
    (h6 : s3dm n τ (x ⬝ᵥ x') ^ 2 ≤ 2 * s3ap n τ ^ 2) (hc1 : s3c1 n τ (x ⬝ᵥ x') ≤ 1)
    (h6lo : (√(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2)
    (hKlo0 : 0 ≤ ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η))
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbl : 0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)) (√(2 * τ)) δ ε) :
    (BstLean.Part153.nuA n).real {θ |
      e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η))
        (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) δ ε <
      opN (PEm x x' * ((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') * PEm x x')} ≤
      18 * exp (-τ) + 5 * exp (-2 * η ^ 2 * (mA n : ℕ)) +
        (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) *
          exp (-(((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η) * δ ^ 2 / 4)) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set K₁ := ((mA n : ℕ) : ℝ) * (1 / 2 + η)
  set K₁₁ := ((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)
  set K₂ := ((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)
  set K₂l := ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)
  set G₁ := e4_G1 (m := mA n) x x' K₁ K₁₁ τ
  have hG₁m : MeasurableSet G₁ := e4_measurableSet_G1 x x' K₁ K₁₁ τ
  have hm : 0 < mA n := by unfold mA; positivity
  set bd := e3_bound2 n K₂ K₂l (√(2 * τ)) (e4_b n K₁ τ) (e4_b n K₁₁ τ ^ 2) (e4_b n 2 τ) δ ε
  have hPE : ∀ J J' : Matrix (Fin (mA n)) (Fin n) ℝ,
      PEm x x' * (Jᵀ * J') * PEm x x' = (J * PEm x x')ᵀ * (J' * PEm x x') := by
    intro J J'
    rw [Matrix.transpose_mul, e4_PEm_symm]; simp only [Matrix.mul_assoc]
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      bd < opN (PEm x x' * ((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') * PEm x x')} ⊆
      (((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ}) ∪ {θ | cnt2 x x' θ < K₂l}) ∪
        {θ | θ.1 ∈ G₁ ∧ K₂l ≤ cnt2 x x' θ ∧ cnt2 x x' θ ≤ K₂ ∧
          bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))} := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq, hPE] at hθ
    by_cases h1 : θ.1 ∈ G₁
    · by_cases h2 : cnt2 x x' θ ≤ K₂
      · by_cases h3 : K₂l ≤ cnt2 x x' θ
        · right; exact ⟨h1, h3, h2, hθ⟩
        · left; right; exact not_le.mp h3
      · left; left; right; exact not_le.mp h2
    · left; left; left; exact ⟨h1, Set.mem_univ _⟩
  have hprod : (BstLean.Part153.nuA n).real (G₁ᶜ ×ˢ Set.univ) =
      (gaussMat (mA n) n (2 / (n : ℝ))).real G₁ᶜ := by
    unfold BstLean.Part153.nuA
    rw [Measure.real, Measure.prod_prod, measure_univ, mul_one]
    rfl
  have tG := e4_G1_charge hx hx' hc hn hcp hcp1 hη hτ
  have tM : (BstLean.Part153.nuA n).real {θ | K₂ < cnt2 x x' θ} ≤
      5 * exp (-τ) + exp (-2 * η ^ 2 * (mA n : ℕ)) :=
    mask_second_tail hn hx hx' hτ hη ham hdm h6 hc1
  have tL : (BstLean.Part153.nuA n).real {θ | cnt2 x x' θ < K₂l} ≤
      5 * exp (-τ) + exp (-2 * η ^ 2 * (mA n : ℕ)) :=
    d3_mask_second_tail_lo hn hx hx' hτ hη ham h6lo
  have tJ := d2_joint x x' (PEm x x') (ℓ := e4_b n K₁ τ) (L11 := e4_b n K₁₁ τ ^ 2)
    (π₁ := e4_b n 2 τ) (K := K₂) (Klo := K₂l) (υ := √(2 * τ)) (δ := δ) (ε := ε)
    (by unfold e4_b; positivity)
    (by unfold e4_b; positivity) (Real.sqrt_nonneg _) hm hKlo0 hδ0 hδ1 hε0 hε1 hbl G₁ hG₁m
    (fun A hA => e4_good_of_G1 x x' K₁ K₁₁ τ hA)
  have e2 : -(√(2 * τ)) ^ 2 / 2 = -τ := by rw [Real.sq_sqrt (by linarith)]; ring
  rw [e2] at tJ
  set W4 := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      θ.1 ∈ G₁ ∧ K₂l ≤ cnt2 x x' θ ∧ cnt2 x x' θ ≤ K₂ ∧
        bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))} with hW4
  have u1 := measureReal_union_le (μ := BstLean.Part153.nuA n)
    (((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ}) ∪ {θ | cnt2 x x' θ < K₂l}) W4
  have u2 := measureReal_union_le (μ := BstLean.Part153.nuA n)
    ((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ}) {θ | cnt2 x x' θ < K₂l}
  have u3 := measureReal_union_le (μ := BstLean.Part153.nuA n)
    (G₁ᶜ ×ˢ Set.univ) {θ | K₂ < cnt2 x x' θ}
  have hm0 := measureReal_mono (μ := BstLean.Part153.nuA n) hsub
  rw [hprod] at u3
  linarith
end pair3


/-- **The pair tail of Lemma TI with the two-sided E block**. -/
theorem d4_pair (hn : 2 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) {cp τ η kE ko ks : ℝ} (hcp : x ⬝ᵥ x' ≤ cp) (hcp1 : cp ≤ 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) {δ ε Nb : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ham : 0 < s3am n τ) (hdm : 0 ≤ s3dm n τ (x ⬝ᵥ x'))
    (h6 : s3dm n τ (x ⬝ᵥ x') ^ 2 ≤ 2 * s3ap n τ ^ 2) (hc1 : s3c1 n τ (x ⬝ᵥ x') < 1)
    (hr1 : 0 ≤ s3Cpa n (x ⬝ᵥ x') - s3r1 n τ)
    (hpos : s3e0 n τ ≤ (s3Cpa n (x ⬝ᵥ x') - s3r1 n τ) / s3ap n τ)
    (h6lo : (√(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2)
    (hKlo0 : 0 ≤ (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)))
    (hbl : 0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)) (√(2 * τ)) δ ε)
    (hnet : (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-((((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)) * δ ^ 2 / 4)) ≤ Nb)
    (hkE0 : 0 ≤ kE) (hko0 : 0 ≤ ko) (hks0 : 0 ≤ ks)
    (hkE : e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) δ ε ≤ n * kE)
    (hko : o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) ≤ n * ko)
    (hks : s3nks n τ η (x ⬝ᵥ x') ≤ n * ks) :
    (BstLean.Part153.nuA n).real {θ | pairBad θ.1 θ.2 (ta_lam kE ko ks) x x'} ≤
      57 * exp (-τ) + 13 * exp (-2 * η ^ 2 * (mA n : ℕ)) + Nb := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc' : (x' ⬝ᵥ x) ^ 2 < 1 := by rwa [dotProduct_comm]
  set μ := BstLean.Part153.nuA n with hμ
  have hP : IsProbabilityMeasure μ := by
    rw [hμ]; unfold BstLean.Part153.nuA gaussMat; infer_instance
  set SE := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) δ ε <
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
  have hE := d4_Eblock hx hx' hc hn1 hcp hcp1 hη hτ ham hdm h6 hc1.le h6lo hKlo0 hδ0 hδ1 hε0 hε1 hbl
  have hO1 := o3_Oblock hn hx hx' hc hτ hη hη
  have hO2 := o3_Oblock hn hx' hx hc' hτ hη hη
  have hS := s3_Sblock hn1 hx hx' hc hτ hη ham hdm h6 hc1 hr1 hpos
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      pairBad θ.1 θ.2 (ta_lam kE ko ks) x x'} ⊆ ((SE ∪ SO1) ∪ SO2) ∪ SS := by
    intro θ hθ
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hno
    simp only [hSE, hSO1, hSO2, hSS, Set.mem_setOf_eq, not_lt] at h1 h2 h3 h4
    have h3' : nrm (PEm x x' *ᵥ (((jac θ.1 θ.2 x')ᵀ * jac θ.1 θ.2 x) *ᵥ eTan x x')) ≤ n * ko := by
      rw [ta_PEm_symm hx hx' hc]; exact h3.trans hko
    have hms := ms_opN hx hx' hc (jac θ.1 θ.2 x) (jac θ.1 θ.2 x')
      (mul_nonneg hnR hkE0) (mul_nonneg hnR hko0) (mul_nonneg hnR hks0)
      (h1.trans hkE) (h2.trans hko) h3' (h4.trans hks)
    rw [ta_lam_scale hnR] at hms
    have hbad : (n : ℝ) * ta_lam kE ko ks <
        opN ((jacT θ.1 θ.2 x)ᵀ * jacT θ.1 θ.2 x') := hθ
    have e : jacT θ.1 θ.2 x = jac θ.1 θ.2 x * projT x := rfl
    have e' : jacT θ.1 θ.2 x' = jac θ.1 θ.2 x' * projT x' := rfl
    rw [e, e'] at hbad
    linarith
  calc μ.real {θ | pairBad θ.1 θ.2 (ta_lam kE ko ks) x x'}
      ≤ μ.real (((SE ∪ SO1) ∪ SO2) ∪ SS) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real SE + μ.real SO1 + μ.real SO2 + μ.real SS := by
        refine (measureReal_union_le _ _).trans ?_
        refine add_le_add ((measureReal_union_le _ _).trans ?_) le_rfl
        exact add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ (18 * exp (-τ) + 5 * exp (-2 * η ^ 2 * (mA n : ℕ)) + Nb) +
        (8 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) + exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (8 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) + exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (23 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ))) := by
        gcongr
        exact hE.trans (by linarith)
    _ = 57 * exp (-τ) + 13 * exp (-2 * η ^ 2 * (mA n : ℕ)) + Nb := by ring

/-- **The numeric hypotheses of Lemma TI (two-sided E block) on the class `[cm, cp]`.** -/
def d4_num (n : ℕ) (cm cp kE ko ks η τ δ ε Nb : ℝ) : Prop :=
  o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) ≤ n * ko ∧
  0 < s3am n τ ∧
  ∀ c, cm ≤ c → c ≤ cp →
    0 ≤ s3dm n τ c ∧ s3dm n τ c ^ 2 ≤ 2 * s3ap n τ ^ 2 ∧ s3c1 n τ c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n τ ∧ s3e0 n τ ≤ (s3Cpa n c - s3r1 n τ) / s3ap n τ ∧
    (√(2 * n * (1 - kappa c)) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2 ∧
    0 ≤ (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ c) / 2 - η)) ∧
    0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ c) / 2 + η)) (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ c) / 2 - η)) (√(2 * τ)) δ ε ∧
    (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-((((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ c) / 2 - η)) * δ ^ 2 / 4)) ≤ Nb ∧
    e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ c) / 2 + η)) (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ c) / 2 - η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) δ ε ≤ n * kE ∧
    s3nks n τ η c ≤ n * ks

/-- **Lemma TI (TI-lite) from the numeric hypotheses.** -/
theorem d4_TI (hn : 2 ≤ n) {cm cp kE ko ks η τ δ ε Nb : ℝ} (hcm : 0 ≤ cm) (hcp : cp < 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hkE0 : 0 ≤ kE) (hko0 : 0 ≤ ko) (hks0 : 0 ≤ ks)
    (hnum : d4_num n cm cp kE ko ks η τ δ ε Nb) :
    TI_hyp n cm cp (ta_lam kE ko ks) (57 * exp (-τ) + 13 * exp (-2 * η ^ 2 * (mA n : ℕ)) + Nb) := by
  intro x x' hx hx' h1 h2
  obtain ⟨hko, ham, hall⟩ := hnum
  obtain ⟨hdm, h6, hc1, hr1, hpos, h6lo, hKl, hbl, hnet, hkE, hks⟩ := hall _ h1 h2
  have hc : (x ⬝ᵥ x') ^ 2 < 1 := by nlinarith
  exact d4_pair hn hx hx' hc h2 hcp.le hη hτ hδ0 hδ1 hε0 hε1 ham hdm h6 hc1 hr1 hpos h6lo hKl hbl
    hnet hkE0 hko0 hks0 hkE hko hks

/-- **Lemma TI (TI-lite) at `τ = 46`**: if `2η²m ≥ 46`, the charge is at most `10⁻¹⁸`. -/
theorem d4_TI46 (hn : 2 ≤ n) {cm cp kE ko ks η δ ε : ℝ} (hcm : 0 ≤ cm) (hcp : cp < 1)
    (hη : 0 ≤ η) (hηm : 46 ≤ 2 * η ^ 2 * (mA n : ℕ)) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hkE0 : 0 ≤ kE) (hko0 : 0 ≤ ko) (hks0 : 0 ≤ ks)
    (hnum : d4_num n cm cp kE ko ks η 46 δ ε (2 / 10 ^ 19)) :
    TI_hyp n cm cp (ta_lam kE ko ks) (1 / 10 ^ 18) := by
  have h := d4_TI hn hcm hcp hη (by norm_num) hδ0 hδ1 hε0 hε1 hkE0 hko0 hks0 hnum
  intro x x' hx hx' h1 h2
  refine (h x x' hx hx' h1 h2).trans ?_
  have he : exp (-(46 : ℝ)) ≤ (3678794412 / 10 ^ 10 : ℝ) ^ 46 := by
    have e : exp (-(46 : ℝ)) = exp (-1) ^ 46 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have h1 : exp (-1) ≤ (3678794412 / 10 ^ 10 : ℝ) := by
      have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
    exact pow_le_pow_left₀ (exp_pos _).le h1 46
  have h2' : exp (-2 * η ^ 2 * (mA n : ℕ)) ≤ exp (-(46 : ℝ)) := by
    apply Real.exp_le_exp.mpr; linarith
  have : (70 : ℝ) * (3678794412 / 10 ^ 10) ^ 46 + 2 / 10 ^ 19 ≤ 1 / 10 ^ 18 := by norm_num
  linarith

end BstLean.Part185

open BstLean.Part185 in
#print axioms d4_Eblock
open BstLean.Part185 in
#print axioms d4_TI46
