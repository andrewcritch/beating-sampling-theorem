import BstLean.Part198Row
import BstLean.Part160MFB2

/-! The sharpened row bound supplies both factors in the first pair moment. -/
namespace BstLean.Part198
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part154
open BstLean.Part153 (rowLaw nrm)
open BstLean.Part160.MFB

noncomputable def rowJ {n : ℕ} (c : Fin n → ℝ) (τ S0 : ℝ) : ℝ :=
  (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹

/-- The integrated radial cutoff charge. -/
noncomputable def rowEps : ℝ := rexp (-12)

/-- The first pair mean in units `1/n`. -/
noncomputable def rowPair (n : ℕ) (c : Fin n → ℝ) (τ S0 : ℝ) : ℝ :=
  (1 - rowJ c τ S0 / 2 + rowEps / 2) * (1 - rowJ c τ S0 * (((n : ℝ) - 1) / (2 * n)) + rowEps / 2) +
    rowJ c τ S0 / (2 * n)

lemma rowEps_pos : 0 < rowEps := by unfold rowEps; positivity

lemma rowJ_bounds {n : ℕ} (c : Fin n → ℝ) {τ S0 : ℝ} (hτ : 0 < τ) (hS0 : 0 < S0) :
    0 < rowJ c τ S0 ∧ rowJ c τ S0 ≤ 1 := by
  have h0 : 0 ≤ (2 / π) * normSq c / (τ ^ 2 * S0) :=
    div_nonneg (mul_nonneg (by positivity) (normSq_nonneg c)) (by positivity)
  have h1 : (1 : ℝ) ≤ √(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))) :=
    Real.one_le_sqrt.mpr (by linarith)
  unfold rowJ
  exact ⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ h1⟩

lemma rowPair_pos {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (_hc : 0 < normSq c) {τ S0 : ℝ} (hτ : 0 < τ)
    (hS0 : 0 < S0) : 0 < rowPair n c τ S0 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hJ0, hJ1⟩ := rowJ_bounds c hτ hS0
  have he := rowEps_pos
  have h1 : 0 ≤ 1 - rowJ c τ S0 / 2 + rowEps / 2 := by linarith
  have hq : ((n : ℝ) - 1) / (2 * n) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hq0 : 0 ≤ ((n : ℝ) - 1) / (2 * n) := div_nonneg (by linarith) (by positivity)
  have h2 : 0 ≤ 1 - rowJ c τ S0 * (((n : ℝ) - 1) / (2 * n)) + rowEps / 2 := by
    have : rowJ c τ S0 * (((n : ℝ) - 1) / (2 * n)) ≤ 1 * (1 / 2) := mul_le_mul hJ1 hq hq0 (by norm_num)
    linarith
  have h3 : 0 < rowJ c τ S0 / (2 * n) := by positivity
  unfold rowPair
  have := mul_nonneg h1 h2
  linarith

/-- The optimisation over the Young parameter, with a first constant `M`. -/
lemma row_inner {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) (a : Fin n → ℝ) :
    ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a' ^ 2 ∂rowLaw n ≤
      1 / (n : ℝ) * ((1 - rowJ c τ S0 / 2 + rowEps / 2) * normSq a +
        rowJ c τ S0 / 2 * ((a ⬝ᵥ c) ^ 2 / normSq c)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨iD, eD⟩ := rl_dot2 hn a
  obtain ⟨-, -, hR⟩ := refl_eq c τ ((meas_dot'_L1c a).pow_const 2) (fun a' => sq_nonneg _)
    (fun a' => by rw [dotProduct_neg, neg_sq]) iD
  obtain ⟨-, hK⟩ := sharp_row_variance hn c hc hτ a hS0 hS
  rw [hR, eD]
  unfold rowJ rowEps
  have e : 1 / 4 * (2 / (n : ℝ)) * ((normSq a - (a ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹ - rexp (-12) * normSq a) =
      1 / (n : ℝ) * (1 / 2 * ((normSq a - (a ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹ - rexp (-12) * normSq a)) := by ring
  rw [e] at hK
  have e2 : 1 / 2 * (2 / (n : ℝ) * normSq a) = 1 / (n : ℝ) * normSq a := by ring
  rw [e2]
  have e3 : 1 / (n : ℝ) * ((1 - (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹ / 2 +
        rexp (-12) / 2) * normSq a +
        (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹ / 2 * ((a ⬝ᵥ c) ^ 2 / normSq c)) =
      1 / (n : ℝ) * normSq a - 1 / (n : ℝ) * (1 / 2 * ((normSq a - (a ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹ - rexp (-12) * normSq a)) := by ring
  rw [e3]
  linarith

/-- `E[|a|² p²] ≤ 1 − J(n − 1)/(2n) + ε/2`. -/
lemma row_norm {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) :
    Integrable (fun a => normSq a * pR c τ a ^ 2) (rowLaw n) ∧
    ∫ a, normSq a * pR c τ a ^ 2 ∂rowLaw n ≤
      1 - rowJ c τ S0 * (((n : ℝ) - 1) / (2 * n)) + rowEps / 2 := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨iN, eN⟩ := rl_normSq hn
  obtain ⟨i1, i3, hR⟩ := refl_eq c τ (continuous_normSq.measurable) normSq_nonneg
    BstLean.Part135.normSq_neg iN
  refine ⟨i1, ?_⟩
  rw [hR, eN]
  -- `|a|² = Σ_k ⟨e_k, a⟩²`
  have hcoord : ∀ a : Fin n → ℝ, normSq a * (pR c τ a * (1 - pR c τ a)) =
      ∑ k : Fin n, ((Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ a) ^ 2 *
        (pR c τ a * (1 - pR c τ a)) := by
    intro a
    rw [← Finset.sum_mul]
    congr 1
    unfold normSq
    exact Finset.sum_congr rfl fun k _ => by rw [single_dotProduct, one_mul]
  have hk : ∀ k : Fin n, Integrable (fun a => ((Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ a) ^ 2 *
      (pR c τ a * (1 - pR c τ a))) (rowLaw n) ∧
      1 / 4 * (2 / (n : ℝ)) * ((1 - c k ^ 2 / normSq c) * rowJ c τ S0 - rowEps) ≤
        ∫ a, ((Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ a) ^ 2 *
          (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    intro k
    obtain ⟨hi, hb⟩ := sharp_row_variance hn c hc hτ (Pi.single k (1 : ℝ)) hS0 hS
    refine ⟨hi, ?_⟩
    have e1 : normSq (Pi.single k (1 : ℝ) : Fin n → ℝ) = 1 := by
      unfold normSq
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun h => absurd (Finset.mem_univ k) h)]
      simp
    have e2 : (Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ c = c k := by
      rw [single_dotProduct, one_mul]
    rw [e1, e2] at hb
    unfold rowJ rowEps
    linarith
  have hsumI : ∫ a, normSq a * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n =
      ∑ k : Fin n, ∫ a, ((Pi.single k (1 : ℝ) : Fin n → ℝ) ⬝ᵥ a) ^ 2 *
        (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    simp_rw [hcoord]
    exact integral_finsetSum _ fun k _ => (hk k).1
  have hlow : 1 / 4 * (2 / (n : ℝ)) * (((n : ℝ) - 1) * rowJ c τ S0 - n * rowEps) ≤
      ∫ a, normSq a * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    rw [hsumI]
    have h1 := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => (hk k).2)
    refine le_trans (le_of_eq ?_) h1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
      ← Finset.sum_div]
    have hcs : ∑ k : Fin n, c k ^ 2 = normSq c := rfl
    rw [hcs, div_self hc.ne']
    simp
  have e : 1 / 4 * (2 / (n : ℝ)) * (((n : ℝ) - 1) * rowJ c τ S0 - n * rowEps) =
      rowJ c τ S0 * (((n : ℝ) - 1) / (2 * n)) - rowEps / 2 := by
    field_simp; ring
  rw [e] at hlow
  linarith

/-- **The first pair mean with the reflection gain on both rows**:
`E[⟨a, a′⟩² p² p′²] ≤ rowPair/n`. -/
lemma row_pair_moment {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) :
    Integrable (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2) ((rowLaw n).prod (rowLaw n)) ∧
    ∫ q : (Fin n → ℝ) × (Fin n → ℝ), (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2
      ∂((rowLaw n).prod (rowLaw n)) ≤ 1 / (n : ℝ) * rowPair n c τ S0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hI, -⟩ := mean1 hn c τ
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  obtain ⟨hJ0, hJ1⟩ := rowJ_bounds c hτ hS0
  have he := rowEps_pos
  obtain ⟨iR, hR⟩ := row_norm hn c hc hτ hS0 hS
  obtain ⟨iC, eC⟩ := rl_dot2 hn c
  obtain ⟨iA, hA⟩ := refl_le c τ ((meas_dot'_L1c c).pow_const 2) (fun a => sq_nonneg _)
    (fun a => by rw [dotProduct_neg, neg_sq]) iC
  rw [eC] at hA
  have h0 : ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
      0 ≤ (q.1 ⬝ᵥ q.2) ^ 2 * pR c τ q.1 ^ 2 * pR c τ q.2 ^ 2 := fun q => by positivity
  have inner : ∀ a : Fin n → ℝ,
      ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 ∂rowLaw n ≤
        1 / (n : ℝ) * ((1 - rowJ c τ S0 / 2 + rowEps / 2) * (normSq a * pR c τ a ^ 2) +
          rowJ c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2)) := by
    intro a
    have hin := row_inner hn c hc hτ hS0 hS a
    have e : ∀ a' : Fin n → ℝ, (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 =
        pR c τ a ^ 2 * ((a ⬝ᵥ a') ^ 2 * pR c τ a' ^ 2) := fun a' => by ring
    simp_rw [e]
    rw [integral_const_mul]
    have := mul_le_mul_of_nonneg_left hin (sq_nonneg (pR c τ a))
    refine this.trans (le_of_eq ?_)
    rw [dotProduct_comm c a]
    field_simp
  have iB : Integrable (fun a : Fin n → ℝ =>
      1 / (n : ℝ) * ((1 - rowJ c τ S0 / 2 + rowEps / 2) * (normSq a * pR c τ a ^ 2) +
        rowJ c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2))) (rowLaw n) :=
    ((iR.const_mul _).add (iA.const_mul _)).const_mul _
  have hmain := integral_mono_of_nonneg
    (f := fun a : Fin n → ℝ => ∫ a', (a ⬝ᵥ a') ^ 2 * pR c τ a ^ 2 * pR c τ a' ^ 2 ∂rowLaw n)
    (ae_of_all _ fun a => integral_nonneg fun a' => h0 (a, a')) iB (ae_of_all _ inner)
  refine hmain.trans ?_
  have hsplit : ∫ a : Fin n → ℝ,
      1 / (n : ℝ) * ((1 - rowJ c τ S0 / 2 + rowEps / 2) * (normSq a * pR c τ a ^ 2) +
        rowJ c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2)) ∂rowLaw n =
      1 / (n : ℝ) * ((1 - rowJ c τ S0 / 2 + rowEps / 2) * ∫ a, normSq a * pR c τ a ^ 2 ∂rowLaw n +
        rowJ c τ S0 / 2 / normSq c * ∫ a, (c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2 ∂rowLaw n) := by
    rw [integral_const_mul]
    congr 1
    have hA2 : ∫ a : Fin n → ℝ, ((1 - rowJ c τ S0 / 2 + rowEps / 2) * (normSq a * pR c τ a ^ 2) +
        rowJ c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2)) ∂rowLaw n =
        ∫ a : Fin n → ℝ, (1 - rowJ c τ S0 / 2 + rowEps / 2) * (normSq a * pR c τ a ^ 2) ∂rowLaw n +
        ∫ a : Fin n → ℝ, rowJ c τ S0 / 2 / normSq c * ((c ⬝ᵥ a) ^ 2 * pR c τ a ^ 2) ∂rowLaw n :=
      integral_add (iR.const_mul _) (iA.const_mul _)
    rw [hA2, integral_const_mul, integral_const_mul]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hc1 : 0 ≤ 1 - rowJ c τ S0 / 2 + rowEps / 2 := by linarith
  have t1 := mul_le_mul_of_nonneg_left hR hc1
  have hc2 : 0 ≤ rowJ c τ S0 / 2 / normSq c := by positivity
  have t2 := mul_le_mul_of_nonneg_left hA hc2
  have e2 : rowJ c τ S0 / 2 / normSq c * (1 / 2 * (2 / (n : ℝ) * normSq c)) =
      rowJ c τ S0 / (2 * n) := by field_simp
  rw [e2] at t2
  unfold rowPair
  linarith


#print axioms row_pair_moment
end BstLean.Part198
