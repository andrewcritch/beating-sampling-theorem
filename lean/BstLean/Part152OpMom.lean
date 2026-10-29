import BstLean.Part152Op
import BstLean.Part152LM
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Part 152 (file `OpMom`): the moment forms for a Gaussian matrix

Role: `delegations/statements/p152-spec.md`; the moment forms of the standard facts (G1), (G2) of
the paper proof of Theorem 5. `gaussMomConst P = (2^P·P!)^{1/(2P)}` is the Gaussian moment constant
`𝔪_P` of the paper.

* `gaussConc_mat_moment`: for `g` Lipschitz with constant `L` for the Frobenius norm and a matrix
  with independent `N(0, v)` entries: `E (g − E g)_+^{2P} ≤ (√v·L)^{2P}·2^P·P!`.
* `moment_shift`: Minkowski's inequality in the form `X ≤ c + Y`, `E Y^{2P} ≤ B^{2P}` gives
  `E X^{2P} ≤ (c + B)^{2P}`.
* **`opN_moment`**: `E (opN M)^{2P} ≤ (√v·(√p + √q + 𝔪_P))^{2P}` for `P ≥ 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part152

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130

/-- The Gaussian moment constant `𝔪_P = (2^P·P!)^{1/(2P)}`. -/
noncomputable def gaussMomConst (P : ℕ) : ℝ :=
  ((2 : ℝ) ^ P * (P.factorial : ℝ)) ^ (1 / ((2 * P : ℕ) : ℝ))

lemma gaussMomConst_nonneg (P : ℕ) : 0 ≤ gaussMomConst P := Real.rpow_nonneg (by positivity) _

lemma gaussMomConst_pow {P : ℕ} (hP : 1 ≤ P) :
    gaussMomConst P ^ (2 * P) = (2 : ℝ) ^ P * (P.factorial : ℝ) := by
  unfold gaussMomConst
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have : (1 / ((2 * P : ℕ) : ℝ)) * ((2 * P : ℕ) : ℝ) = 1 := by
    have : ((2 * P : ℕ) : ℝ) ≠ 0 := by
      have : 0 < 2 * P := by omega
      exact_mod_cast this.ne'
    field_simp
  rw [this, Real.rpow_one]

section mat

variable {m k : ℕ} {g : Matrix (Fin m) (Fin k) ℝ → ℝ} {L : ℝ}

/-- **The moment form of sharp Gaussian concentration for a function of a Gaussian matrix.** -/
theorem gaussConc_mat_moment (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) (P : ℕ) :
    Integrable (fun M => (max (g M - ∫ M, g M ∂gaussMat m k v) 0) ^ (2 * P)) (gaussMat m k v) ∧
    ∫ M, (max (g M - ∫ M, g M ∂gaussMat m k v) 0) ^ (2 * P) ∂gaussMat m k v ≤
      (√v * L) ^ (2 * P) * (2 ^ P * (P.factorial : ℝ)) := by
  have hgc := BstLean.Part148.matLip_continuous hL
  set T : (Fin m × Fin k → ℝ) → Matrix (Fin m) (Fin k) ℝ :=
    fun ξ => Matrix.of fun i j => Real.sqrt v * ξ (i, j) with hT
  have mT : Measurable T := measurable_ofFlat _
  have hf : EuLip (fun ξ => g (T ξ)) (√v * L) := flat_euLip hL hv
  obtain ⟨hi, hb⟩ := gaussConc_moment (mul_nonneg (Real.sqrt_nonneg v) hL0) hf P
  have eI : ∫ M, g M ∂gaussMat m k v = ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k) := by
    unfold gaussMat
    exact integral_map mT.aemeasurable hgc.measurable.aestronglyMeasurable
  have msq : Measurable fun M => (max (g M - ∫ M, g M ∂gaussMat m k v) 0) ^ (2 * P) :=
    ((hgc.measurable.sub measurable_const).max measurable_const).pow_const _
  rw [← eI] at hi hb
  constructor
  · exact (integrable_map_measure (μ := stdGauss (Fin m × Fin k)) (f := T)
      msq.aestronglyMeasurable mT.aemeasurable).mpr hi
  · have e2 : ∫ M, (max (g M - ∫ M, g M ∂gaussMat m k v) 0) ^ (2 * P) ∂gaussMat m k v =
        ∫ ξ, (max (g (T ξ) - ∫ M, g M ∂gaussMat m k v) 0) ^ (2 * P)
          ∂stdGauss (Fin m × Fin k) := by
      conv_lhs => unfold gaussMat
      exact integral_map mT.aemeasurable msq.aestronglyMeasurable
    rw [e2]
    exact hb

end mat

lemma enn_pow_root (a : ℝ≥0∞) {n : ℕ} (hn : 0 < n) : (a ^ n) ^ (1 / (n : ℝ)) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [this, ENNReal.rpow_one]

lemma enn_root_pow (a : ℝ≥0∞) {n : ℕ} (hn : 0 < n) : (a ^ (1 / (n : ℝ))) ^ n = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have : (1 / (n : ℝ)) * (n : ℝ) = 1 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [this, ENNReal.rpow_one]

/-- **Minkowski's inequality for a shift**: if `0 ≤ X ≤ c + Y`, `Y ≥ 0` and
`E Y^{2P} ≤ B^{2P}`, then `E X^{2P} ≤ (c + B)^{2P}`. -/
theorem moment_shift {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXm : Measurable X) (hYm : Measurable Y) (hX0 : ∀ ω, 0 ≤ X ω)
    (hY0 : ∀ ω, 0 ≤ Y ω) {c : ℝ} (hc : 0 ≤ c) (hle : ∀ ω, X ω ≤ c + Y ω) {P : ℕ} (hP : 1 ≤ P)
    {B : ℝ} (hB0 : 0 ≤ B) (hYi : Integrable (fun ω => Y ω ^ (2 * P)) μ)
    (hYb : ∫ ω, Y ω ^ (2 * P) ∂μ ≤ B ^ (2 * P)) :
    Integrable (fun ω => X ω ^ (2 * P)) μ ∧ ∫ ω, X ω ^ (2 * P) ∂μ ≤ (c + B) ^ (2 * P) := by
  have hn : 0 < 2 * P := by omega
  have hn1 : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast hn
  have Mk := ENNReal.lintegral_Lp_add_le (μ := μ) (p := ((2 * P : ℕ) : ℝ))
    (f := fun _ => ENNReal.ofReal c) (g := fun ω => ENNReal.ofReal (Y ω)) aemeasurable_const
    hYm.ennreal_ofReal.aemeasurable hn1
  simp only [Pi.add_apply, ENNReal.rpow_natCast] at Mk
  have t1 : (∫⁻ _ : Ω, ENNReal.ofReal c ^ (2 * P) ∂μ) ^ (1 / ((2 * P : ℕ) : ℝ)) =
      ENNReal.ofReal c := by
    rw [lintegral_const, measure_univ, mul_one, enn_pow_root _ hn]
  have t2 : (∫⁻ ω, ENNReal.ofReal (Y ω) ^ (2 * P) ∂μ) ^ (1 / ((2 * P : ℕ) : ℝ)) ≤
      ENNReal.ofReal B := by
    have e : ∫⁻ ω, ENNReal.ofReal (Y ω) ^ (2 * P) ∂μ = ENNReal.ofReal (∫ ω, Y ω ^ (2 * P) ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hYi (ae_of_all _ fun ω => pow_nonneg (hY0 ω) _)]
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_pow (hY0 ω)]
    rw [e]
    calc ENNReal.ofReal (∫ ω, Y ω ^ (2 * P) ∂μ) ^ (1 / ((2 * P : ℕ) : ℝ))
        ≤ ENNReal.ofReal (B ^ (2 * P)) ^ (1 / ((2 * P : ℕ) : ℝ)) :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hYb) (by positivity)
      _ = ENNReal.ofReal B := by rw [ENNReal.ofReal_pow hB0, enn_pow_root _ hn]
  have hL : ∫⁻ ω, ENNReal.ofReal (X ω) ^ (2 * P) ∂μ ≤
      ∫⁻ ω, (ENNReal.ofReal c + ENNReal.ofReal (Y ω)) ^ (2 * P) ∂μ := by
    refine lintegral_mono fun ω => pow_le_pow_left' ?_ _
    rw [← ENNReal.ofReal_add hc (hY0 ω)]
    exact ENNReal.ofReal_le_ofReal (hle ω)
  have h3 : (∫⁻ ω, ENNReal.ofReal (X ω) ^ (2 * P) ∂μ) ^ (1 / ((2 * P : ℕ) : ℝ)) ≤
      ENNReal.ofReal c + ENNReal.ofReal B :=
    (ENNReal.rpow_le_rpow hL (by positivity)).trans (Mk.trans (by rw [t1]; gcongr))
  have h4 : ∫⁻ ω, ENNReal.ofReal (X ω) ^ (2 * P) ∂μ ≤ ENNReal.ofReal ((c + B) ^ (2 * P)) := by
    have := pow_le_pow_left' h3 (2 * P)
    rw [enn_root_pow _ hn, ← ENNReal.ofReal_add hc hB0, ← ENNReal.ofReal_pow (by positivity)] at this
    exact this
  have h5 : ∫⁻ ω, ENNReal.ofReal (X ω ^ (2 * P)) ∂μ ≤ ENNReal.ofReal ((c + B) ^ (2 * P)) := by
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) h4
    rw [ENNReal.ofReal_pow (hX0 ω)]
  have hnn : ∀ ω, 0 ≤ X ω ^ (2 * P) := fun ω => pow_nonneg (hX0 ω) _
  have hsm : AEStronglyMeasurable (fun ω => X ω ^ (2 * P)) μ :=
    (hXm.pow_const _).aestronglyMeasurable
  refine ⟨⟨hsm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).2
    (lt_of_le_of_lt h5 ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hsm]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h5

/-- **The moment form of the bound of the operator norm of a Gaussian matrix**:
`E (opN M)^{2P} ≤ (√v·(√p + √q + 𝔪_P))^{2P}` for `P ≥ 1`. -/
theorem opN_moment {p q : ℕ} {v : ℝ} (hv : 0 ≤ v) {P : ℕ} (hP : 1 ≤ P) :
    Integrable (fun M : Matrix (Fin p) (Fin q) ℝ => opN M ^ (2 * P)) (gaussMat p q v) ∧
    ∫ M : Matrix (Fin p) (Fin q) ℝ, opN M ^ (2 * P) ∂gaussMat p q v ≤
      (√v * (√p + √q + gaussMomConst P)) ^ (2 * P) := by
  obtain ⟨hYi, hYb⟩ := gaussConc_mat_moment (g := (opN : Matrix (Fin p) (Fin q) ℝ → ℝ))
    zero_le_one opN_lip hv P
  have hmean := (opN_mean_le (p := p) (q := q) hv).2
  have hcm : Measurable (opN : Matrix (Fin p) (Fin q) ℝ → ℝ) := opN_continuous.measurable
  have h := moment_shift (μ := gaussMat p q v) (X := opN)
    (Y := fun M => max (opN M - ∫ M, opN M ∂gaussMat p q v) 0) hcm
    ((hcm.sub measurable_const).max measurable_const) opN_nonneg (fun M => le_max_right _ _)
    (c := √v * (√p + √q)) (by positivity)
    (fun M => by
      have := le_max_left (opN M - ∫ M, opN M ∂gaussMat p q v) 0
      linarith)
    hP (B := √v * gaussMomConst P) (mul_nonneg (Real.sqrt_nonneg v) (gaussMomConst_nonneg P)) hYi
    (by
      refine hYb.trans (le_of_eq ?_)
      rw [mul_one, mul_pow, gaussMomConst_pow hP])
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  congr 1
  ring

end BstLean.Part152

open BstLean.Part152 in
#print axioms gaussConc_mat_moment
open BstLean.Part152 in
#print axioms moment_shift
open BstLean.Part152 in
#print axioms opN_moment
