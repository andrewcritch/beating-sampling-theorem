import BstLean.Part182EBlk4
import BstLean.Part182OBlk3
import BstLean.Part182SBlk3
import BstLean.Part182Def

/-!
# Part 182 (file `TIA`): the assembly of Lemma TI (TI-lite) from the E, O and S blocks

No proof is left open; no `native_decide` or `axiom` is used.

* **`ta_pair`**: for unit `x`, `x'` with `c = x·x'`, `c² < 1`, if the three block bounds
  `e3_bound … ≤ n·k_E`, `o3_kO … ≤ n·k_o`, `s3nks … ≤ n·k_s` and the side conditions of the blocks
  hold, then `Pr_{A₁,A₂}(pairBad λ x x') ≤ 51e^{−τ} + 12e^{−2η²m}` with
  `λ = (k_E + k_s)/2 + √(((k_E − k_s)/2)² + k_o²)` (Lemma MS: `ms_opN`). The charge: E block
  `12e^{−τ} + 4e^{−2η²m}`, O block twice (both orientations) `2·(8e^{−τ} + 3e^{−2η²m})`, S block
  `23e^{−τ} + 2e^{−2η²m}`.
* `ta_num`: the numeric hypotheses, for every `c ∈ [cm, cp]`.
* **`ta_TI`**: `TI_hyp n cm cp λ (51e^{−τ} + 12e^{−2η²m})` from `ta_num` (`0 ≤ cm`, `cp < 1`).
* **`ta_TI46`**: at `τ = 46` with `2η²m ≥ 46`: `TI_hyp n cm cp λ 10⁻¹⁸` (`63e^{−46} ≤ 10⁻¹⁸`).
The numeric hypotheses themselves (`ta_num`) are NOT proved here.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (jac)
open BstLean.Part153 (projT nrm jacT)

variable {n : ℕ}

/-- `λ(k_E, k_o, k_s)`, the MS eigenvalue. -/
noncomputable def ta_lam (kE ko ks : ℝ) : ℝ := (kE + ks) / 2 + √(((kE - ks) / 2) ^ 2 + ko ^ 2)

lemma ta_lam_scale {s : ℝ} (hs : 0 ≤ s) (kE ko ks : ℝ) :
    (s * kE + s * ks) / 2 + √(((s * kE - s * ks) / 2) ^ 2 + (s * ko) ^ 2) = s * ta_lam kE ko ks := by
  unfold ta_lam
  have e : ((s * kE - s * ks) / 2) ^ 2 + (s * ko) ^ 2 = s ^ 2 * (((kE - ks) / 2) ^ 2 + ko ^ 2) := by
    ring
  rw [e, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]
  ring

lemma ta_PEm_symm {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (w : Fin n → ℝ) : PEm x x' *ᵥ w = PEm x' x *ᵥ w := by
  rw [PEm_alt hx hx' hc]
  unfold PEm
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp [Pi.sub_apply, Pi.smul_apply, dotProduct_comm, smul_eq_mul, mul_comm]

/-- **The pair tail of Lemma TI (TI-lite)**. -/
theorem ta_pair (hn : 2 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) {cp τ η kE ko ks : ℝ} (hcp : x ⬝ᵥ x' ≤ cp) (hcp1 : cp ≤ 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (ham : 0 < s3am n τ) (hdm : 0 ≤ s3dm n τ (x ⬝ᵥ x'))
    (h6 : s3dm n τ (x ⬝ᵥ x') ^ 2 ≤ 2 * s3ap n τ ^ 2) (hc1 : s3c1 n τ (x ⬝ᵥ x') < 1)
    (hr1 : 0 ≤ s3Cpa n (x ⬝ᵥ x') - s3r1 n τ)
    (hpos : s3e0 n τ ≤ (s3Cpa n (x ⬝ᵥ x') - s3r1 n τ) / s3ap n τ)
    (hkE0 : 0 ≤ kE) (hko0 : 0 ≤ ko) (hks0 : 0 ≤ ks)
    (hkE : e3_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) ≤ n * kE)
    (hko : o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) ≤ n * ko)
    (hks : s3nks n τ η (x ⬝ᵥ x') ≤ n * ks) :
    (BstLean.Part153.nuA n).real {θ | pairBad θ.1 θ.2 (ta_lam kE ko ks) x x'} ≤
      51 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
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
    _ ≤ (12 * exp (-τ) + 4 * exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (8 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) + exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (8 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ)) + exp (-2 * η ^ 2 * (mA n : ℕ))) +
        (23 * exp (-τ) + 2 * exp (-2 * η ^ 2 * (mA n : ℕ))) := by
        gcongr
    _ = 51 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by ring

/-- **The numeric hypotheses of Lemma TI on the class `[cm, cp]`** (not proved in this file). -/
def ta_num (n : ℕ) (cm cp kE ko ks η τ : ℝ) : Prop :=
  o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η)) (((mA n : ℕ) : ℝ) * (1 / 2 + η)) ≤ n * ko ∧
  0 < s3am n τ ∧
  ∀ c, cm ≤ c → c ≤ cp →
    0 ≤ s3dm n τ c ∧ s3dm n τ c ^ 2 ≤ 2 * s3ap n τ ^ 2 ∧ s3c1 n τ c < 1 ∧
    0 ≤ s3Cpa n c - s3r1 n τ ∧ s3e0 n τ ≤ (s3Cpa n c - s3r1 n τ) / s3ap n τ ∧
    e3_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ c) / 2 + η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) ≤ n * kE ∧
    s3nks n τ η c ≤ n * ks

/-- **Lemma TI (TI-lite) from the numeric hypotheses.** -/
theorem ta_TI (hn : 2 ≤ n) {cm cp kE ko ks η τ : ℝ} (hcm : 0 ≤ cm) (hcp : cp < 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hkE0 : 0 ≤ kE) (hko0 : 0 ≤ ko) (hks0 : 0 ≤ ks)
    (hnum : ta_num n cm cp kE ko ks η τ) :
    TI_hyp n cm cp (ta_lam kE ko ks) (51 * exp (-τ) + 12 * exp (-2 * η ^ 2 * (mA n : ℕ))) := by
  intro x x' hx hx' h1 h2
  obtain ⟨hko, ham, hall⟩ := hnum
  obtain ⟨hdm, h6, hc1, hr1, hpos, hkE, hks⟩ := hall _ h1 h2
  have hc : (x ⬝ᵥ x') ^ 2 < 1 := by nlinarith
  exact ta_pair hn hx hx' hc h2 hcp.le hη hτ ham hdm h6 hc1 hr1 hpos hkE0 hko0 hks0 hkE hko hks

/-- **Lemma TI (TI-lite) at `τ = 46`**: if `2η²m ≥ 46`, the charge is at most `10⁻¹⁸`. -/
theorem ta_TI46 (hn : 2 ≤ n) {cm cp kE ko ks η : ℝ} (hcm : 0 ≤ cm) (hcp : cp < 1)
    (hη : 0 ≤ η) (hηm : 46 ≤ 2 * η ^ 2 * (mA n : ℕ))
    (hkE0 : 0 ≤ kE) (hko0 : 0 ≤ ko) (hks0 : 0 ≤ ks)
    (hnum : ta_num n cm cp kE ko ks η 46) :
    TI_hyp n cm cp (ta_lam kE ko ks) (1 / 10 ^ 18) := by
  have h := ta_TI hn hcm hcp hη (by norm_num) hkE0 hko0 hks0 hnum
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
  have : (63 : ℝ) * (3678794412 / 10 ^ 10) ^ 46 ≤ 1 / 10 ^ 18 := by norm_num
  linarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms ta_pair
open BstLean.Part182 in
#print axioms ta_TI
open BstLean.Part182 in
#print axioms ta_TI46
