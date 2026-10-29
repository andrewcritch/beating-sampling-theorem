import BstLean.Part149Stage2
import BstLean.Part149CDefs

/-!
# Part 149, item 5: two outputs with different centres and scalars (Lemma C)

Do not use `sorry`, `native_decide` or `axiom`.

`gO b τ (A₃, F) = E_γ F(A₃ b + τ·γ)` is the output of the last stage for a centre `b` and a
scalar `τ` (`Part149Stage`).

* `outCompare`: `E_{A₃, F} (gO b τ − gO b' τ')² ≤ 2·(v·|b − b'|² + (τ − τ')²)` (the coupling
  through the same Gaussian vector and the same `A₃`).
* `tauOutOf_sub_sq`: `(tauOutOf n b − tauOutOf n b')² ≤ (2/m)·|b − b'|²·Yhi/(m/n − Yhi)` if
  `|b|², |b'|² ≤ Yhi < m/n`.
* `outCompare_tau`: `E (gO b (tauOutOf n b) − gO b' (tauOutOf n b'))² ≤
  2·(2/m)·|b − b'|²·(m/n)/(m/n − Yhi)`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part134

variable {n m mF : ℕ}

/-- **Two outputs with different centres and scalars.** -/
theorem outCompare {v : ℝ} (hv : 0 ≤ v) (hn : 1 ≤ n) (hmF : 1 ≤ mF) (b b' : Fin m → ℝ)
    (τ τ' : ℝ) :
    ∫⁻ p, ENNReal.ofReal ((gO b τ p - gO b' τ' p) ^ 2)
        ∂((gaussMat n m v).prod (mlpGauss n mF 1)) ≤
      ENNReal.ofReal (2 * (v * normSq (b - b') + (τ - τ') ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have mD : Measurable (fun p : Matrix (Fin n) (Fin m) ℝ × MlpParam n mF 1 =>
      ENNReal.ofReal ((gO b τ p - gO b' τ' p) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_gO b τ).sub (measurable_gO b' τ')).pow_const 2)
  rw [lintegral_prod _ mD.aemeasurable]
  have key : ∀ M : Matrix (Fin n) (Fin m) ℝ,
      ∫⁻ F, ENNReal.ofReal ((gO b τ (M, F) - gO b' τ' (M, F)) ^ 2) ∂mlpGauss n mF 1 ≤
        ENNReal.ofReal (2 / (n : ℝ) * (normSq (M.mulVec (b - b')) + (τ - τ') ^ 2 * n)) := by
    intro M
    set X : (Fin n → ℝ) → Fin n → ℝ := fun γ => M.mulVec b + τ • γ with hX
    set Y : (Fin n → ℝ) → Fin n → ℝ := fun γ => M.mulVec b' + τ' • γ with hY
    have mX : Measurable X := measurable_const.add (measurable_id.const_smul τ)
    have mY : Measurable Y := measurable_const.add (measurable_id.const_smul τ')
    have eXY : ∀ γ, X γ - Y γ = M.mulVec (b - b') + (τ - τ') • γ := by
      intro γ
      simp only [hX, hY]
      rw [Matrix.mulVec_sub]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hg := gauss_shift_normSq (M.mulVec (b - b')) (τ - τ')
    have iXY : Integrable (fun γ => normSq (X γ - Y γ)) (stdGauss (Fin n)) := by
      simp_rw [eXY]; exact hg.1
    obtain ⟨hint, hle⟩ := lemmaC149 (stdGauss (Fin n)) (m := mF) hn hmF mX mY iXY
    simp_rw [eXY] at hle
    rw [hg.2] at hle
    have ediff : ∀ F : MlpParam n mF 1,
        ∫ γ, (mlpEval F (X γ) 0 - mlpEval F (Y γ) 0) ∂stdGauss (Fin n) =
          gO b τ (M, F) - gO b' τ' (M, F) := by
      intro F
      obtain ⟨C, hC0, hC⟩ := evF_growth F
      have iF : ∀ (c : Fin n → ℝ) (t : ℝ),
          Integrable (fun γ : Fin n → ℝ => evF F (c + t • γ)) (stdGauss (Fin n)) := by
        intro c t
        have iG : Integrable (fun γ : Fin n → ℝ =>
            (1 + C * (1 + 2 * normSq c)) + (C * (2 * t ^ 2)) * normSq γ) (stdGauss (Fin n)) :=
          (integrable_const _).add ((stdGauss_normSq n).1.const_mul _)
        refine Integrable.mono' iG ((measurable_evF F).comp
          (measurable_const.add (measurable_id.const_smul t))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun γ => ?_)
        rw [Real.norm_eq_abs]
        refine (evF_abs_le F hC _).trans ?_
        have h2 := normSq_add_le c (t • γ)
        rw [normSq_smul] at h2
        have h6 : C * (1 + normSq (c + t • γ)) ≤
            C * (1 + (2 * normSq c + 2 * (t ^ 2 * normSq γ))) :=
          mul_le_mul_of_nonneg_left (by linarith) hC0
        linarith
      exact integral_sub (iF _ _) (iF _ _)
    simp_rw [← ediff]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hle
  have iM := (layer_lin_sq (m := n) (k := m) hv (b - b')).1
  have eM := (layer_lin_sq (m := n) (k := m) hv (b - b')).2
  have iR : Integrable (fun M : Matrix (Fin n) (Fin m) ℝ =>
      2 / (n : ℝ) * (normSq (M.mulVec (b - b')) + (τ - τ') ^ 2 * n)) (gaussMat n m v) :=
    (iM.add (integrable_const _)).const_mul _
  calc ∫⁻ M, ∫⁻ F, ENNReal.ofReal ((gO b τ (M, F) - gO b' τ' (M, F)) ^ 2) ∂mlpGauss n mF 1
        ∂gaussMat n m v
      ≤ ∫⁻ M, ENNReal.ofReal (2 / (n : ℝ) * (normSq (M.mulVec (b - b')) + (τ - τ') ^ 2 * n))
          ∂gaussMat n m v := lintegral_mono key
    _ = ENNReal.ofReal (∫ M, 2 / (n : ℝ) * (normSq (M.mulVec (b - b')) + (τ - τ') ^ 2 * n)
          ∂gaussMat n m v) :=
        (ofReal_integral_eq_lintegral_ofReal iR (Filter.Eventually.of_forall fun M => by
          have := normSq_nonneg (M.mulVec (b - b'))
          positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [integral_const_mul, integral_add iM (integrable_const _), eM]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        field_simp

/-- The scalars of two centres. -/
lemma tauOutOf_sub_sq (hn : 1 ≤ n) (hm : 1 ≤ m) {b b' : Fin m → ℝ} {Yhi : ℝ}
    (hb : normSq b ≤ Yhi) (hb' : normSq b' ≤ Yhi) (hY : Yhi < (m : ℝ) / n) :
    (tauOutOf n b - tauOutOf n b') ^ 2 ≤
      2 / (m : ℝ) * normSq (b - b') * (Yhi / ((m : ℝ) / n - Yhi)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set v : ℝ := 2 / (m : ℝ) with hv
  have hv0 : 0 < v := by rw [hv]; positivity
  set d : ℝ := (m : ℝ) / n with hd
  have evd : 2 / (n : ℝ) = v * d := by rw [hv, hd]; field_simp
  have hYhi0 : 0 ≤ Yhi := (normSq_nonneg b).trans hb
  set y₀ : ℝ := v * (d - Yhi) with hy₀
  have hy₀0 : 0 < y₀ := by rw [hy₀]; exact mul_pos hv0 (by linarith)
  have hx : ∀ {c : Fin m → ℝ}, normSq c ≤ Yhi →
      max 0 (2 / (n : ℝ) - v * normSq c) = v * (d - normSq c) ∧ y₀ ≤ v * (d - normSq c) := by
    intro c hc
    have h1 : y₀ ≤ v * (d - normSq c) := by
      rw [hy₀]; exact mul_le_mul_of_nonneg_left (by linarith) hv0.le
    refine ⟨?_, h1⟩
    rw [evd, ← mul_sub]
    exact max_eq_right (by linarith)
  obtain ⟨e1, g1⟩ := hx hb
  obtain ⟨e2, g2⟩ := hx hb'
  unfold tauOutOf
  rw [← hv, e1, e2]
  set x : ℝ := v * (d - normSq b) with hxd
  set y : ℝ := v * (d - normSq b') with hyd
  have hx0 : 0 < x := lt_of_lt_of_le hy₀0 g1
  have hy0 : 0 < y := lt_of_lt_of_le hy₀0 g2
  -- `(√x − √y)² ≤ (x − y)²/(4 y₀)`
  have hsx : √y₀ ≤ √x := Real.sqrt_le_sqrt g1
  have hsy : √y₀ ≤ √y := Real.sqrt_le_sqrt g2
  have hs0 : 0 < √y₀ := Real.sqrt_pos.mpr hy₀0
  have e3 : (√x - √y) * (√x + √y) = x - y := by
    have a1 := Real.sq_sqrt hx0.le
    have a2 := Real.sq_sqrt hy0.le
    nlinarith
  have h4 : (√x - √y) ^ 2 * (4 * y₀) ≤ (x - y) ^ 2 := by
    have a3 := Real.sq_sqrt hy₀0.le
    have h5 : (2 * √y₀) ^ 2 ≤ (√x + √y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h6 : (x - y) ^ 2 = (√x - √y) ^ 2 * (√x + √y) ^ 2 := by rw [← e3]; ring
    rw [h6]
    have : (2 * √y₀) ^ 2 = 4 * y₀ := by rw [mul_pow, a3]; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
  -- `(x − y)² = v²(|b'|² − |b|²)² ≤ v²·|b − b'|²·4·Yhi`
  have h7 : (normSq b' - normSq b) ^ 2 ≤ normSq (b - b') * (4 * Yhi) := by
    have t1 := BstLean.Part140.nrm_add_le' (b - b') b'
    have t2 := BstLean.Part140.nrm_add_le' (b' - b) b
    have eb : b - b' + b' = b := by abel
    have eb' : b' - b + b = b' := by abel
    rw [eb] at t1
    rw [eb'] at t2
    have en : nrm (b' - b) = nrm (b - b') := by
      unfold nrm
      congr 1
      simp only [normSq, Pi.sub_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [en] at t2
    have n1 := nrm_sq b
    have n2 := nrm_sq b'
    have n3 := nrm_sq (b - b')
    have p1 := nrm_nonneg b
    have p2 := nrm_nonneg b'
    have p3 := nrm_nonneg (b - b')
    have habs : |nrm b - nrm b'| ≤ nrm (b - b') := by
      rw [abs_le]; constructor <;> linarith
    have hsum : (nrm b + nrm b') ^ 2 ≤ 4 * Yhi := by
      have q1 : nrm b ^ 2 ≤ Yhi := by rw [n1]; exact hb
      have q2 : nrm b' ^ 2 ≤ Yhi := by rw [n2]; exact hb'
      nlinarith [sq_nonneg (nrm b - nrm b')]
    have e5 : normSq b' - normSq b = (nrm b' - nrm b) * (nrm b' + nrm b) := by
      rw [← n1, ← n2]; ring
    rw [e5, mul_pow, ← n3]
    have h8 : (nrm b' - nrm b) ^ 2 ≤ nrm (b - b') ^ 2 := by
      rw [← sq_abs (nrm b' - nrm b), abs_sub_comm]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have h9 : (nrm b' + nrm b) ^ 2 ≤ 4 * Yhi := by rw [add_comm]; exact hsum
    exact mul_le_mul h8 h9 (sq_nonneg _) (sq_nonneg _)
  have e6 : x - y = v * (normSq b' - normSq b) := by rw [hxd, hyd]; ring
  have h10 : (√x - √y) ^ 2 ≤ (x - y) ^ 2 / (4 * y₀) := by
    rw [le_div_iff₀ (by positivity)]; exact h4
  refine h10.trans ?_
  rw [e6, mul_pow, hy₀, div_le_iff₀ (by positivity)]
  have hdY : 0 < d - Yhi := by linarith
  have e7 : v * normSq (b - b') * (Yhi / (d - Yhi)) * (4 * (v * (d - Yhi))) =
      v ^ 2 * (normSq (b - b') * (4 * Yhi)) := by
    field_simp
  rw [e7]
  exact mul_le_mul_of_nonneg_left h7 (sq_nonneg _)

/-- **Two outputs, each with the scalar of its own centre.** -/
theorem outCompare_tau (hn : 1 ≤ n) (hm : 1 ≤ m) (hmF : 1 ≤ mF) {b b' : Fin m → ℝ} {Yhi : ℝ}
    (hb : normSq b ≤ Yhi) (hb' : normSq b' ≤ Yhi) (hY : Yhi < (m : ℝ) / n) :
    ∫⁻ p, ENNReal.ofReal ((gO b (tauOutOf n b) p - gO b' (tauOutOf n b') p) ^ 2)
        ∂((gaussMat n m (2 / (m : ℝ))).prod (mlpGauss n mF 1)) ≤
      ENNReal.ofReal (2 * (2 / (m : ℝ)) * normSq (b - b') *
        ((m : ℝ) / n / ((m : ℝ) / n - Yhi))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine (outCompare (v := 2 / (m : ℝ)) (by positivity) hn hmF b b' _ _).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := tauOutOf_sub_sq hn hm hb hb' hY
  have hdY : 0 < (m : ℝ) / n - Yhi := by linarith
  have e : 2 * (2 / (m : ℝ)) * normSq (b - b') * ((m : ℝ) / n / ((m : ℝ) / n - Yhi)) =
      2 * (2 / (m : ℝ) * normSq (b - b') +
        2 / (m : ℝ) * normSq (b - b') * (Yhi / ((m : ℝ) / n - Yhi))) := by
    have e0 : (m : ℝ) / n / ((m : ℝ) / n - Yhi) = 1 + Yhi / ((m : ℝ) / n - Yhi) := by
      rw [eq_comm, one_add_div hdY.ne']
      ring
    rw [e0]
    ring
  rw [e]
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms outCompare
open BstLean.Part149 in
#print axioms outCompare_tau
