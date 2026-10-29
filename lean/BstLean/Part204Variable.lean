import BstLean.Part204Reserve

/-! S06: variable hidden thresholds and centre transfer. -/

namespace BstLean.Part204

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN sS)
open BstLean.Part141 (aOf)
open BstLean.Part150 (c1F kappa4 c1F_kappa4_le c1F_nonneg kappa4_nonneg)
open BstLean.Part157

open BstLean.Part159

variable {n : ℕ}

theorem bWp_dist_variable (hn : 4096 ≤ n) (hC : ConstC n) {θ : WHid n}
    {ε T η : ℝ} (hε : ε ≤ 1 / 1000) (hη : 0 < η)
    (hS : |SWp θ / 2 - 1| ≤ ε)
    (hA : 2 / (mW n : ℝ) * normSq (aOf 1 θ) ≤ T) :
    2 / (mW n : ℝ) * normSq (bWp θ - bhat θ) ≤
      (2 * (1 + η) * (3212 / 100000) * (1001 / 1000) +
      (1 + 1 / η) * (2 * T + 36) / 10 ^ 17) /
        ((n : ℝ) * (mW n : ℝ)) := by
  have hn4 : 4096 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
  have hmpos : (0 : ℝ) < mW n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨hJ1, hJ2⟩ := JW_ge hn4
  have hJpos : (0 : ℝ) < (JW n : ℝ) := by
    have : (1000 : ℝ) ≤ (JW n : ℝ) := by exact_mod_cast hJ2
    linarith
  set X : ℝ := 1 / ((n : ℝ) * (mW n : ℝ)) with hX
  have hXpos : 0 < X := by positivity
  set d := cNt n - cN (2 * n) with hd
  -- the constant
  have hC' : d ^ 2 * (n : ℝ) * (mW n : ℝ) ≤ 1 / 10 ^ 17 := hC
  have hdX : d ^ 2 ≤ 1 / 10 ^ 17 * X := by
    rw [hX]
    have e : 1 / 10 ^ 17 * (1 / ((n : ℝ) * (mW n : ℝ))) =
        1 / 10 ^ 17 / ((n : ℝ) * (mW n : ℝ)) := by ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨hcw, -⟩ := BstLean.Part201.cN_even_window hn
  have hc0 : 0 ≤ cN (2 * n) := BstLean.Part141.cN_nonneg _
  have hd1 : |d| ≤ cN (2 * n) / 100 := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    have h1 : 1 / 10 ^ 17 * X ≤ (1 / (13 * (n : ℝ))) / 10 ^ 4 := by
      rw [hX]
      rw [div_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : (cN (2 * n) / 100) ^ 2 = cN (2 * n) ^ 2 / 10 ^ 4 := by ring
    rw [h2]
    have h3 : (1 / (13 * (n : ℝ))) / 10 ^ 4 ≤ cN (2 * n) ^ 2 / 10 ^ 4 :=
      div_le_div_of_nonneg_right hcw (by norm_num)
    linarith
  -- `S_W`
  have hS' : |SWp θ / 2 - 1| ≤ 1 / 1000 := hS.trans hε
  obtain ⟨hSa, hSb⟩ := abs_le.mp hS'
  have hS1 : 1998 / 1000 ≤ SWp θ := by linarith
  have hS2 : SWp θ ≤ 2002 / 1000 := by linarith
  -- the three pieces
  set c1 := c1F kappa4 (JW n) with hc1
  have hc1le : c1 ≤ 1792 / 10000 := c1F_kappa4_le hJ2
  have hc10 : 0 ≤ c1 := c1F_nonneg kappa4_nonneg _
  set A := c1 * sWp θ / (JW n) with hAdef
  have hst := sWp_sq_le hn1 θ
  have hJm : (mW n : ℝ) ≤ (JW n : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hJ1 2
    rwa [Real.sq_sqrt hmpos.le] at this
  have hA2 : A ^ 2 ≤ 3212 / 100000 * (1001 / 1000) * X := by
    rw [hAdef, div_pow, mul_pow, div_le_iff₀ (by positivity)]
    have h1 : c1 ^ 2 ≤ 3212 / 100000 := by nlinarith
    have h2 : sWp θ ^ 2 ≤ 1001 / 1000 / (n : ℝ) := by
      refine hst.trans ?_
      rw [div_le_div_iff₀ (by positivity) hnpos]
      nlinarith
    have h3 : c1 ^ 2 * sWp θ ^ 2 ≤ 3212 / 100000 * (1001 / 1000 / (n : ℝ)) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by norm_num)
    have h4 : 3212 / 100000 * (1001 / 1000 / (n : ℝ)) =
        3212 / 100000 * (1001 / 1000) * X * (mW n : ℝ) := by
      rw [hX]; field_simp
    have h5 : 3212 / 100000 * (1001 / 1000) * X * (mW n : ℝ) ≤
        3212 / 100000 * (1001 / 1000) * X * (JW n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hJm (by positivity)
    linarith
  have hCs := BstLean.Part204.sWp_sub_sq hn hm θ hS1 hS2 hd1
  set Cs := |sWp θ - sS θ.1| with hCsdef
  have hCs2 : Cs ^ 2 ≤ 9 * d ^ 2 := by
    rw [hCsdef, sq_abs]
    exact hCs
  have hTa : 2 / (mW n : ℝ) * normSq (aOf 1 θ) ≤ T := hA
  -- coordinates
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (mW n) → ℝ, δ = bWp θ - bhat θ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; exact div_nonneg (mul_nonneg hc10 (sWp_nonneg θ)) hJpos.le
  have hcoord : ∀ i : Fin (mW n), δ i ^ 2 ≤
      (1 + η) * A ^ 2 +
        (1 + 1 / η) * (2 * (d ^ 2 * aOf 1 θ i ^ 2) + 2 * Cs ^ 2) := by
    intro i
    have h1 := bWp_coord hn1 (by omega : 1 ≤ JW n) θ i
    have h2 : |δ i| ≤ A + (|d| * |aOf 1 θ i| + Cs) := by
      rw [hδ]
      simp only [Pi.sub_apply]
      linarith
    have hB0 : 0 ≤ |d| * |aOf 1 θ i| + Cs := by positivity
    have h3 : δ i ^ 2 ≤ (A + (|d| * |aOf 1 θ i| + Cs)) ^ 2 := by
      rw [← sq_abs (δ i)]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h4 := sq_add_eta (η := η) hη A (|d| * |aOf 1 θ i| + Cs)
    have h5 : (|d| * |aOf 1 θ i| + Cs) ^ 2 ≤ 2 * (d ^ 2 * aOf 1 θ i ^ 2) + 2 * Cs ^ 2 := by
      have e : d ^ 2 * aOf 1 θ i ^ 2 = (|d| * |aOf 1 θ i|) ^ 2 := by
        rw [mul_pow, sq_abs, sq_abs]
      rw [e]
      exact sq_add_two _ _
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 1 + 1 / η)
    exact h3.trans (h4.trans (add_le_add le_rfl h6))
  have h7 := dist_assembly hm δ (aOf 1 θ) hcoord
  rw [← hδ]
  have h9 : d ^ 2 * (2 / (mW n : ℝ) * normSq (aOf 1 θ)) ≤ d ^ 2 * T :=
    mul_le_mul_of_nonneg_left hTa (sq_nonneg _)
  have hT0 : 0 ≤ T :=
    (mul_nonneg (by positivity) (normSq_nonneg _)).trans hTa
  have h11 : d ^ 2 * T ≤ 1 / 10 ^ 17 * X * T :=
    mul_le_mul_of_nonneg_right hdX hT0
  have h12 : Cs ^ 2 ≤ 9 * (1 / 10 ^ 17 * X) :=
    hCs2.trans (mul_le_mul_of_nonneg_left hdX (by norm_num))
  have h13 := mul_le_mul_of_nonneg_left hA2 (by positivity : 0 ≤ 2 * (1 + η))
  have h14 := mul_le_mul_of_nonneg_left (by linarith [h9, h11, h12] :
      2 * (d ^ 2 * (2 / (mW n : ℝ) * normSq (aOf 1 θ))) + 4 * Cs ^ 2 ≤
        2 * (1 / 10 ^ 17 * X * T) + 36 * (1 / 10 ^ 17 * X))
      (by positivity : 0 ≤ 1 + 1 / η)
  have e : (2 * (1 + η) * (3212 / 100000) * (1001 / 1000) +
      (1 + 1 / η) * (2 * T + 36) / 10 ^ 17) /
        ((n : ℝ) * (mW n : ℝ)) =
      2 * (1 + η) * (3212 / 100000) * (1001 / 1000) * X +
        (1 + 1 / η) * (2 * (1 / 10 ^ 17 * X * T) + 36 * (1 / 10 ^ 17 * X)) := by
    rw [hX]
    ring
  rw [e]
  linarith

/-- A variable narrow hidden window supplies the standard scalar bound. -/
theorem pap_q_variable (hn : 4096 ≤ n) {θ : WHid n} {ε : ℝ}
    (hε : ε ≤ 1 / 1000) (hS : |SWp θ / 2 - 1| ≤ ε) :
    0 ≤ qOf n (ccP n) θ ∧ qOf n (ccP n) θ ≤ 1001 / 1000 ∧
      |qOf n (ccP n) θ - 1| ≤
        1002 / 1000 * ε + 407 / 100 * |kapT n - BstLean.Part140.kap1 (2 * n)| := by
  obtain ⟨hq, he⟩ := BstLean.Part204.pap_q hn (BstLean.Part201.constK hn)
    (hS.trans hε)
  refine ⟨Real.sqrt_nonneg _, hq, he.trans ?_⟩
  linarith

/-- Scaled squared lengths satisfy the Euclidean triangle bound. -/
theorem normSq_triangle_scaled {m : ℕ} (a b : Fin m → ℝ) {t X Y : ℝ}
    (ht : 0 ≤ t) (ha : t * normSq a ≤ X) (hb : t * normSq b ≤ Y) :
    t * normSq (a + b) ≤ (√X + √Y) ^ 2 := by
  have hA : 0 ≤ t * normSq a := mul_nonneg ht (normSq_nonneg _)
  have hB : 0 ≤ t * normSq b := mul_nonneg ht (normSq_nonneg _)
  have hX : 0 ≤ X := hA.trans ha
  have hY : 0 ≤ Y := hB.trans hb
  have hdot := BstLean.Part130.abs_dot_le a b
  have hcross : t * (∑ i, a i * b i) ≤ √X * √Y := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hdot) ht
    have e : t * (√(normSq a) * √(normSq b)) =
        √(t * normSq a) * √(t * normSq b) := by
      rw [Real.sqrt_mul ht, Real.sqrt_mul ht]
      calc
        t * (√(normSq a) * √(normSq b)) =
            (√t) ^ 2 * (√(normSq a) * √(normSq b)) := by rw [Real.sq_sqrt ht]
        _ = (√t * √(normSq a)) * (√t * √(normSq b)) := by ring
    rw [e] at h1
    exact h1.trans (mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [BstLean.Part133.normSq_add_eq]
  change t * (normSq a + normSq b + 2 * (∑ i, a i * b i)) ≤ (√X + √Y) ^ 2
  have hsX := Real.sq_sqrt hX
  have hsY := Real.sq_sqrt hY
  nlinarith

/-- Transfer a hidden distance bound to the actual computed binomial centre. -/
theorem centre_transfer {θ : WHid n} (b : Fin (mW n) → ℝ) {X Y : ℝ}
    (hX : 2 / (mW n : ℝ) * normSq (bhat θ - b) ≤ X)
    (hY : 2 / (mW n : ℝ) * normSq (bWp θ - bhat θ) ≤ Y) :
    2 / (mW n : ℝ) * normSq (bWp θ - b) ≤ (√X + √Y) ^ 2 := by
  have e : bWp θ - b = (bhat θ - b) + (bWp θ - bhat θ) := by abel
  rw [e]
  exact normSq_triangle_scaled _ _ (by positivity) hX hY

/-- Transfer a hidden distance threshold in units of the World variance. -/
theorem centre_transfer_4096 (hn : 4096 ≤ n) {θ : WHid n}
    (hS : θ ∈ goodS n) (hA : θ ∈ goodAo n)
    (b : Fin (mW n) → ℝ) {X : ℝ}
    (hX : (n : ℝ) * (2 / (mW n : ℝ)) * normSq (bhat θ - b) ≤ X) :
    (n : ℝ) * (2 / (mW n : ℝ)) * normSq (bWp θ - b) ≤
      (√X + √(645 / 10 ^ 4 / (mW n : ℝ))) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hd := BstLean.Part204.bWp_dist hn (BstLean.Part201.constC hn) hS hA
  have hY : (n : ℝ) * (2 / (mW n : ℝ)) * normSq (bWp θ - bhat θ) ≤
      645 / 10 ^ 4 / (mW n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hd hnpos.le
    have e : (n : ℝ) * (2 / ((2 * n : ℕ) : ℝ) *
        (645 / 10 ^ 4 / (mW n : ℝ))) = 645 / 10 ^ 4 / (mW n : ℝ) := by
      push_cast
      field_simp
    rw [e] at h
    simpa only [mul_assoc] using h
  have e : bWp θ - b = (bhat θ - b) + (bWp θ - bhat θ) := by abel
  rw [e]
  exact normSq_triangle_scaled _ _ (by positivity) hX hY

end BstLean.Part204

#print axioms BstLean.Part204.bWp_dist_variable
#print axioms BstLean.Part204.pap_q_variable
#print axioms BstLean.Part204.normSq_triangle_scaled
#print axioms BstLean.Part204.centre_transfer
#print axioms BstLean.Part204.centre_transfer_4096
