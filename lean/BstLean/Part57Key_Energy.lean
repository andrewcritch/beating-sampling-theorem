import BstLean.Part57Key_Linear

/-! Ordered tensor covariance bounds and restriction to monomial coordinates. -/

namespace BstLean.Part57.KeyProof
open MeasureTheory BstLean.Part29 BstLean.Part56
open BstLean.Part41 (Mono)
variable {n d r : ℕ}

lemma dir_dot_sq (V : Fin r → Fin n → ℝ) (g h : Fin n → ℝ) :
    dot56 (perpDirR V g) (perpDirR V h) ^ 2 ≤ 1 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (perpDirR V g) (perpDirR V h)
  have hn : 0 ≤ ∑ i, perpDirR V h i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact hc.trans (by simpa using mul_le_mul (dir_sq V g) (dir_sq V h) hn zero_le_one)

lemma tensor_inner_bound (d j i : ℕ) (hj : j ≤ d) (hi : 1 ≤ i)
    (V : Fin r → Fin n → ℝ) (hV : OrthoF V) (y : Fin r → ℝ)
    (hy : ∑ a, y a ^ 2 ≤ 1) (g h : Fin n → ℝ) :
    (∑ τ : Fin j → Fin n,
      tensorCoeff56 j i (spanV V y) (perpDirR V g) τ *
        tensorCoeff56 j i (spanV V y) (perpDirR V h) τ) ^ 2 ≤
      ((2 : ℝ) ^ d) ^ 2 * dot56 (perpDirR V g) (perpDirR V h) ^ 2 := by
  rw [tensorCoeff_inner56 j i _ _ _ (dir_orth V hV y g) (dir_orth V hV y h)]
  have hs2 : dot56 (spanV V y) (spanV V y) ≤ 1 := by
    simpa only [dot56, ← pow_two, span_sq V hV] using hy
  have hs0 : 0 ≤ dot56 (spanV V y) (spanV V y) := by
    unfold dot56
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hp : dot56 (spanV V y) (spanV V y) ^ (j - i) ≤ 1 := pow_le_one₀ hs0 hs2
  have hp2 : (dot56 (spanV V y) (spanV V y) ^ (j - i)) ^ 2 ≤ 1 := by
    have hpn := pow_nonneg hs0 (j - i)
    nlinarith
  have hD := dir_dot_sq V g h
  have hDi : (dot56 (perpDirR V g) (perpDirR V h) ^ i) ^ 2 ≤
      dot56 (perpDirR V g) (perpDirR V h) ^ 2 := by
    have ht := pow_le_pow_of_le_one (sq_nonneg (dot56 (perpDirR V g) (perpDirR V h))) hD hi
    simpa only [pow_one, ← pow_mul, Nat.mul_comm] using ht
  have hchoose : (j.choose i : ℝ) ≤ (2 : ℝ) ^ d := by
    calc
      _ ≤ (2 : ℝ) ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hj
  have hchoose2 := pow_le_pow_left₀ (Nat.cast_nonneg (j.choose i) : (0 : ℝ) ≤ _) hchoose 2
  calc
    _ = (j.choose i : ℝ) ^ 2 * (dot56 (spanV V y) (spanV V y) ^ (j - i)) ^ 2 *
      (dot56 (perpDirR V g) (perpDirR V h) ^ i) ^ 2 := by ring
    _ ≤ ((2 : ℝ) ^ d) ^ 2 * 1 * dot56 (perpDirR V g) (perpDirR V h) ^ 2 := by
      apply mul_le_mul
      · exact mul_le_mul hchoose2 hp2 (sq_nonneg _) (sq_nonneg _)
      · exact hDi
      · exact sq_nonneg _
      · positivity
    _ = _ := by ring

lemma int_tensor_product (V : Fin r → Fin n → ℝ) (a : Fin n → ℝ) (j i : ℕ)
    (τ υ : Fin j → Fin n) : Integrable (fun g =>
      tensorCoeff56 j i a (perpDirR V g) τ * tensorCoeff56 j i a (perpDirR V g) υ)
      (stdGauss (Fin n)) :=
  integrable_cont_dir V _ ((continuous_tensorCoeff56 j i a τ).mul (continuous_tensorCoeff56 j i a υ))

lemma tensor_energy (hr : 1 ≤ r) (hn : 2 * r ≤ n) (V : Fin r → Fin n → ℝ) (hV : OrthoF V)
    (d j i : ℕ) (hj : j ≤ d) (hi : 1 ≤ i) (y : Fin r → ℝ) (hy : ∑ a, y a ^ 2 ≤ 1) :
    covEnergy56 (stdGauss (Fin n))
      (fun τ g => tensorCoeff56 j i (spanV V y) (perpDirR V g) τ) ≤
        (((2 : ℝ) ^ d) ^ 2 * 18) / ((n : ℝ) - r) := by
  have hN : 0 < (n : ℝ) - r := by
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hn' : 2 * (r : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let A : ℝ := ((2 : ℝ) ^ d) ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hinner (g : Fin n → ℝ) :
      (∫ h, (∑ τ : Fin j → Fin n, tensorCoeff56 j i (spanV V y) (perpDirR V g) τ *
        tensorCoeff56 j i (spanV V y) (perpDirR V h) τ) ^ 2 ∂stdGauss (Fin n)) ≤
          A * (18 / ((n : ℝ) - r)) := by
    have hid := integrable_cont_dir V (fun w => dot56 (perpDirR V g) w ^ 2)
      (by unfold dot56; fun_prop)
    have hb := integral_mono_of_nonneg (Filter.Eventually.of_forall fun h => sq_nonneg _)
      (hid.const_mul A) (Filter.Eventually.of_forall fun h => tensor_inner_bound d j i hj hi V hV y hy g h)
    rw [integral_const_mul] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ((linear_moment hr hn V hV (perpDirR V g)).trans ?_) hA)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (dir_sq V g)
      (show 0 ≤ 18 / ((n : ℝ) - r) by positivity)
  rw [← same_integral_cov56 _ _ (fun τ υ => int_tensor_product V (spanV V y) j i τ υ)]
  calc
    _ ≤ ∫ _g, A * (18 / ((n : ℝ) - r)) ∂stdGauss (Fin n) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall hinner)
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]; dsimp [A]; ring

lemma raw_energy (hr : 1 ≤ r) (hn : 2 * r ≤ n) (V : Fin r → Fin n → ℝ) (hV : OrthoF V)
    (d j i : ℕ) (hj : j ≤ d) (hi : 1 ≤ i) (y : Fin r → ℝ) (hy : ∑ a, y a ^ 2 ≤ 1) :
    covEnergy56 (stdGauss (Fin n))
      (fun β : Sym (Fin n) j => fun g => tensorCoeff56 j i (spanV V y) (perpDirR V g) (enum56 β)) ≤
        (((2 : ℝ) ^ d) ^ 2 * 18) / ((n : ℝ) - r) := by
  exact (covEnergy_restrict_le56 (ι := Sym (Fin n) j) (κ := Fin j → Fin n)
    (stdGauss (Fin n)) (fun τ g => tensorCoeff56 j i (spanV V y) (perpDirR V g) τ)
    (enum56 : Sym (Fin n) j → Fin j → Fin n) enum_injective56).trans
    (tensor_energy hr hn V hV d j i hj hi y hy)

lemma key_from_linear (d r : ℕ) (hr : 1 ≤ r) : KeyLemma57 d r (((2 : ℝ) ^ d) ^ 2 * 18) := by
  intro n hn V hV y y' hy hy' j i i' hj hi hij hi' hij'
  simp_rw [PhiJI_inner_block56 d j i i' hj]
  let F : Sym (Fin n) j → (Fin n → ℝ) → ℝ :=
    fun β g => tensorCoeff56 j i (spanV V y) (perpDirR V g) (enum56 β)
  let G : Sym (Fin n) j → (Fin n → ℝ) → ℝ :=
    fun β g => tensorCoeff56 j i' (spanV V y') (perpDirR V g) (enum56 β)
  let B : ℝ := (((2 : ℝ) ^ d) ^ 2 * 18) / ((n : ℝ) - r)
  have hB : 0 ≤ B := by
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hn' : 2 * (r : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [B]
    exact div_nonneg (by positivity) (by linarith)
  have hF : ∀ p q, Integrable (fun g => F p g * F q g) (stdGauss (Fin n)) :=
    fun p q => int_tensor_product V (spanV V y) j i (enum56 p) (enum56 q)
  have hG : ∀ p q, Integrable (fun g => G p g * G q g) (stdGauss (Fin n)) :=
    fun p q => int_tensor_product V (spanV V y') j i' (enum56 p) (enum56 q)
  have hEF : covEnergy56 (stdGauss (Fin n)) F ≤ B := raw_energy hr hn V hV d j i hj hi y hy
  have hEG : covEnergy56 (stdGauss (Fin n)) G ≤ B := raw_energy hr hn V hV d j i' hj hi' y' hy'
  have hEG0 : 0 ≤ covEnergy56 (stdGauss (Fin n)) G :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcross := cross_integral_sq_le56 (stdGauss (Fin n)) F G hF hG
  have hprod := mul_le_mul hEF hEG hEG0 hB
  change (∫ g, ∫ h, (∑ p, F p g * G p h) ^ 2 ∂stdGauss (Fin n) ∂stdGauss (Fin n)) ≤ B
  have hnonneg : 0 ≤ ∫ g, ∫ h, (∑ p, F p g * G p h) ^ 2
      ∂stdGauss (Fin n) ∂stdGauss (Fin n) :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  nlinarith

end BstLean.Part57.KeyProof
