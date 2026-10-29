import BstLean.Part56Key_Covariance

namespace BstLean.Part56

open MeasureTheory BstLean.Part29
open BstLean.Part41 (Mono)

private lemma orth_smul56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) (s : ℝ) (g : Fin n → ℝ) :
    dot56 (s • v) (perpDir v g) = 0 := by
  unfold dot56
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  rw [perpDir_orth56 v g hv, mul_zero]

private lemma dot_smul_self56 {n : ℕ} (v : Fin n → ℝ) (hv : UnitV v) (s : ℝ) :
    dot56 (s • v) (s • v) = s ^ 2 := by
  unfold dot56
  change (∑ i, (s * v i) * (s * v i)) = _
  have he : (∑ i, (s * v i) * (s * v i)) = s ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, hv, mul_one]

private lemma perp_dot_sq_le_one56 {n : ℕ} (v g h : Fin n → ℝ) :
    dot56 (perpDir v g) (perpDir v h) ^ 2 ≤ 1 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (perpDir v g) (perpDir v h)
  have hn : 0 ≤ ∑ i, perpDir v h i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact hc.trans (by
    calc
      _ ≤ 1 * 1 := mul_le_mul (perpDir_sq_le_one56 v g) (perpDir_sq_le_one56 v h) hn zero_le_one
      _ = 1 := by ring)

private lemma tensor_inner_sq_bound56 {n : ℕ} (d j i : ℕ) (hj : j ≤ d) (hi : 1 ≤ i)
    (v : Fin n → ℝ) (hv : UnitV v) (s : ℝ) (hs : |s| ≤ 1) (g h : Fin n → ℝ) :
    (∑ τ : Fin j → Fin n,
      tensorCoeff56 j i (s • v) (perpDir v g) τ *
        tensorCoeff56 j i (s • v) (perpDir v h) τ) ^ 2 ≤
      ((2 : ℝ) ^ d) ^ 2 * dot56 (perpDir v g) (perpDir v h) ^ 2 := by
  rw [tensorCoeff_inner56 j i _ _ _ (orth_smul56 v hv s g) (orth_smul56 v hv s h),
    dot_smul_self56 v hv]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
  have hp : (s ^ 2) ^ (j - i) ≤ 1 := pow_le_one₀ (sq_nonneg s) hs2
  have hp2 : ((s ^ 2) ^ (j - i)) ^ 2 ≤ 1 := by
    have hpn : 0 ≤ (s ^ 2) ^ (j - i) := pow_nonneg (sq_nonneg s) _
    nlinarith
  have hD : dot56 (perpDir v g) (perpDir v h) ^ 2 ≤ 1 := perp_dot_sq_le_one56 v g h
  have hDi : (dot56 (perpDir v g) (perpDir v h) ^ i) ^ 2 ≤
      dot56 (perpDir v g) (perpDir v h) ^ 2 := by
    have ht := pow_le_pow_of_le_one (sq_nonneg (dot56 (perpDir v g) (perpDir v h))) hD hi
    simpa only [pow_one, ← pow_mul, Nat.mul_comm] using ht
  have hchoose : (j.choose i : ℝ) ≤ (2 : ℝ) ^ d := by
    calc
      _ ≤ (2 : ℝ) ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hj
  have hchoose2 : (j.choose i : ℝ) ^ 2 ≤ ((2 : ℝ) ^ d) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hchoose 2
  calc
    _ = (j.choose i : ℝ) ^ 2 * ((s ^ 2) ^ (j - i)) ^ 2 *
      (dot56 (perpDir v g) (perpDir v h) ^ i) ^ 2 := by ring
    _ ≤ ((2 : ℝ) ^ d) ^ 2 * 1 * dot56 (perpDir v g) (perpDir v h) ^ 2 := by
      apply mul_le_mul
      · exact mul_le_mul hchoose2 hp2 (sq_nonneg _) (sq_nonneg _)
      · exact hDi
      · exact sq_nonneg _
      · positivity
    _ = _ := by ring

theorem tensor_covEnergy_bound56 {n : ℕ} (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : UnitV v)
    (C : ℝ) (hC : 0 ≤ C)
    (hlin : ∀ a : Fin n → ℝ, (∫ g, dot56 a (perpDir v g) ^ 2 ∂stdGauss (Fin n)) ≤
      C / ((n : ℝ) - 1) * ∑ i, a i ^ 2)
    (d j i : ℕ) (hj : j ≤ d) (hi : 1 ≤ i) (s : ℝ) (hs : |s| ≤ 1) :
    covEnergy56 (stdGauss (Fin n))
      (fun τ g => tensorCoeff56 j i (s • v) (perpDir v g) τ) ≤
        (((2 : ℝ) ^ d) ^ 2 * C) / ((n : ℝ) - 1) := by
  have hN : 0 < (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let A : ℝ := ((2 : ℝ) ^ d) ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hinner (g : Fin n → ℝ) :
      (∫ h, (∑ τ : Fin j → Fin n, tensorCoeff56 j i (s • v) (perpDir v g) τ *
        tensorCoeff56 j i (s • v) (perpDir v h) τ) ^ 2 ∂stdGauss (Fin n)) ≤
          A * (C / ((n : ℝ) - 1)) := by
    have hid := integrable_cont_perpDir56 v
      (fun w => dot56 (perpDir v g) w ^ 2) (by unfold dot56; fun_prop)
    have hb := integral_mono_of_nonneg (Filter.Eventually.of_forall fun h => sq_nonneg _)
      (hid.const_mul A) (Filter.Eventually.of_forall fun h =>
        tensor_inner_sq_bound56 d j i hj hi v hv s hs g h)
    rw [integral_const_mul] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ((hlin (perpDir v g)).trans ?_) hA)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (perpDir_sq_le_one56 v g)
      (show 0 ≤ C / ((n : ℝ) - 1) from div_nonneg hC hN.le)
  rw [← same_integral_cov56 _ _ (fun τ υ => integrable_tensorCoeff_product56 v (s • v) j i τ υ)]
  calc
    _ ≤ ∫ _g, A * (C / ((n : ℝ) - 1)) ∂stdGauss (Fin n) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall hinner)
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]; dsimp [A]; ring

theorem raw_covEnergy_bound56 {n : ℕ} (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : UnitV v)
    (C : ℝ) (hC : 0 ≤ C)
    (hlin : ∀ a : Fin n → ℝ, (∫ g, dot56 a (perpDir v g) ^ 2 ∂stdGauss (Fin n)) ≤
      C / ((n : ℝ) - 1) * ∑ i, a i ^ 2)
    (d j i : ℕ) (hj : j ≤ d) (hi : 1 ≤ i) (s : ℝ) (hs : |s| ≤ 1) :
    covEnergy56 (stdGauss (Fin n))
      (fun β : Sym (Fin n) j => fun g => tensorCoeff56 j i (s • v) (perpDir v g) (enum56 β)) ≤
        (((2 : ℝ) ^ d) ^ 2 * C) / ((n : ℝ) - 1) := by
  exact (covEnergy_restrict_le56 (ι := Sym (Fin n) j) (κ := Fin j → Fin n)
    (stdGauss (Fin n)) (fun τ g => tensorCoeff56 j i (s • v) (perpDir v g) τ)
    (enum56 : Sym (Fin n) j → Fin j → Fin n) enum_injective56).trans
    (tensor_covEnergy_bound56 hn v hv C hC hlin d j i hj hi s hs)

theorem PhiJI_inner_block56 {n : ℕ} (d j i i' : ℕ) (hj : j ≤ d)
    (a a' w w' : Fin n → ℝ) :
    (∑ p : Mono n d, PhiJI d j i a w p * PhiJI d j i' a' w' p) =
      ∑ β : Sym (Fin n) j, tensorCoeff56 j i a w (enum56 β) * tensorCoeff56 j i' a' w' (enum56 β) := by
  classical
  let b : Fin (d + 1) := ⟨j, by omega⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single b]
  · simp only [PhiJI, b, ite_true]
    apply Finset.sum_congr rfl
    intro β hβ
    simp only [tensorCoeff56, tensorPoly_enum56]
    rfl
  · intro c hc hcb
    have hcj : (c : ℕ) ≠ j := by intro he; apply hcb; apply Fin.ext; exact he
    simp only [PhiJI, hcj, ite_false, zero_mul, Finset.sum_const_zero]
  · simp

theorem keyLemma56_from_linear (d : ℕ) (C : ℝ) (hC : 0 < C)
    (hlin : ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ a : Fin n → ℝ,
      (∫ g, dot56 a (perpDir v g) ^ 2 ∂stdGauss (Fin n)) ≤
        C / ((n : ℝ) - 1) * ∑ i, a i ^ 2) :
    KeyLemma56 d (((2 : ℝ) ^ d) ^ 2 * C) := by
  intro n hn v hv s s' hs hs' j i i' hj hi hij hi' hij'
  simp_rw [PhiJI_inner_block56 d j i i' hj]
  let F : Sym (Fin n) j → (Fin n → ℝ) → ℝ :=
    fun β g => tensorCoeff56 j i (s • v) (perpDir v g) (enum56 β)
  let G : Sym (Fin n) j → (Fin n → ℝ) → ℝ :=
    fun β g => tensorCoeff56 j i' (s' • v) (perpDir v g) (enum56 β)
  let B : ℝ := (((2 : ℝ) ^ d) ^ 2 * C) / ((n : ℝ) - 1)
  have hB : 0 ≤ B := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [B]
    apply div_nonneg (by positivity)
    linarith
  have hF : ∀ p q, Integrable (fun g => F p g * F q g) (stdGauss (Fin n)) :=
    fun p q => integrable_tensorCoeff_product56 v (s • v) j i (enum56 p) (enum56 q)
  have hG : ∀ p q, Integrable (fun g => G p g * G q g) (stdGauss (Fin n)) :=
    fun p q => integrable_tensorCoeff_product56 v (s' • v) j i' (enum56 p) (enum56 q)
  have hEF : covEnergy56 (stdGauss (Fin n)) F ≤ B :=
    raw_covEnergy_bound56 hn v hv C hC.le (hlin n hn v hv) d j i hj hi s hs
  have hEG : covEnergy56 (stdGauss (Fin n)) G ≤ B :=
    raw_covEnergy_bound56 hn v hv C hC.le (hlin n hn v hv) d j i' hj hi' s' hs'
  have hEF0 : 0 ≤ covEnergy56 (stdGauss (Fin n)) F :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEG0 : 0 ≤ covEnergy56 (stdGauss (Fin n)) G :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcross := cross_integral_sq_le56 (stdGauss (Fin n)) F G hF hG
  have hprod := mul_le_mul hEF hEG hEG0 hB
  change (∫ g, ∫ h, (∑ p, F p g * G p h) ^ 2 ∂stdGauss (Fin n) ∂stdGauss (Fin n)) ≤ B
  have hnonneg : 0 ≤ ∫ g, ∫ h, (∑ p, F p g * G p h) ^ 2
      ∂stdGauss (Fin n) ∂stdGauss (Fin n) :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  nlinarith

end BstLean.Part56
