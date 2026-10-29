import BstLean.Part160ScTab

/-!
# Part 160 (file `ScLoMean`): an upper bound of the mean of the first-layer variance

Do not use `sorry`, `native_decide` or `axiom`.

* `kappa_lower_all`: `κ(r) ≥ 1/π + r/2 + r²/(2π)` on `[−1, 1]`.
* `pair_lower`: `a b κ(d/(ab)) ≥ ab/π + d/2 + d²/(2π·ab)` for `|d| ≤ ab`.
* `int_Kn_ge`: `E_{ξ,ξ′}[|y||y′| κ] ≥ (ρ² − τ²)/π + |c|²/2 + |c|⁴/(2πρ²)`.
* `sO2_mean_eq`: `E s_h² = (2/n)·(ρ² − E Kn)`.
* `scUp n c τ`, **`sO2_mean_upper`**: `E s_h² ≤ scUp = (2/n)((1 − 1/π)ρ² + τ²/π − |c|²/2 −
  |c|⁴/(2πρ²))`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (hO gO sO2)
open BstLean.Part153 (nrm)

variable {n m : ℕ}

/-- `κ(r) ≥ 1/π + r/2 + r²/(2π)` on `[−1, 1]`. -/
theorem kappa_lower_all {r : ℝ} (h0 : -1 ≤ r) (h1 : r ≤ 1) :
    1 / π + r / 2 + r ^ 2 / (2 * π) ≤ kappa r := by
  have hπ := Real.pi_pos
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 1 / π + t / 2 + t ^ 2 / (2 * π) ≤ kappa t := by
    intro t ht0 ht1
    have h := BstLean.Part132.kappa_ge_poly ht0 ht1
    have e : t ^ 2 / (2 * π) ≤ (t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 80) / π := by
      rw [div_le_div_iff₀ (by positivity) hπ]
      have : 0 ≤ t ^ 4 / 24 + t ^ 6 / 80 := by positivity
      nlinarith [sq_nonneg t]
    linarith
  rcases le_total 0 r with hr | hr
  · exact key r hr h1
  · have h := key (-r) (by linarith) (by linarith)
    rw [kappa_neg_eq, neg_sq] at h
    linarith

/-- **The pair lower bound**: `a b κ(d/(ab)) ≥ ab/π + d/2 + d²/(ab)/(2π)` for `|d| ≤ ab`. -/
theorem pair_lower {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : |d| ≤ a * b) :
    a * b / π + d / 2 + d ^ 2 / (a * b) / (2 * π) ≤ a * b * kappa (d / (a * b)) := by
  have hπ := Real.pi_pos
  rcases eq_or_lt_of_le (mul_nonneg ha hb) with hab | hab
  · have hd0 : d = 0 := by
      rw [← hab] at hd
      exact abs_eq_zero.mp (le_antisymm hd (abs_nonneg d))
    rw [← hab, hd0]
    simp
  · obtain ⟨q, hq'⟩ : ∃ q : ℝ, q = a * b := ⟨_, rfl⟩
    rw [← hq'] at hab hd ⊢
    have hr : -1 ≤ d / q ∧ d / q ≤ 1 := by
      obtain ⟨h1, h2⟩ := abs_le.mp hd
      constructor
      · rw [le_div_iff₀ hab]; linarith
      · rw [div_le_one hab]; exact h2
    have hq := kappa_lower_all hr.1 hr.2
    have h1 := mul_le_mul_of_nonneg_left hq hab.le
    have e1 : q * (1 / π + d / q / 2 + (d / q) ^ 2 / (2 * π)) =
        q / π + d / 2 + d ^ 2 / q / (2 * π) := by
      field_simp
    rw [e1] at h1
    exact h1

/-- `|d| ≤ (λ/2)·d²/q + q/(2λ)` for `q ≥ |d|`, `λ > 0` (also `q = 0`). -/
lemma amgm_div {d q l : ℝ} (hq : |d| ≤ q) (hl : 0 < l) :
    d ≤ l / 2 * (d ^ 2 / q) + q / (2 * l) := by
  have hq0 : 0 ≤ q := (abs_nonneg d).trans hq
  rcases eq_or_lt_of_le hq0 with h | h
  · have hd0 : d = 0 := by
      rw [← h] at hq
      exact abs_eq_zero.mp (le_antisymm hq (abs_nonneg d))
    rw [← h, hd0]; simp
  · have e : l / 2 * (d ^ 2 / q) + q / (2 * l) = (l ^ 2 * d ^ 2 + q ^ 2) / (2 * l * q) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (l * d - q)]

/-- **A lower bound of the mean of the pair kernel**:
`E Kn ≥ (ρ² − τ²)/π + |c|²/2 + |c|⁴/ρ²/(2π)`. -/
theorem int_Kn_ge (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2) / π + normSq c / 2 +
        normSq c ^ 2 / (normSq c + (n : ℝ) * τ ^ 2) / (2 * π) ≤
      ∫ z, Kn c τ z ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 < normSq c + (n : ℝ) * τ ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg c) (by positivity)
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ₂ : Measure ((Fin n → ℝ) × (Fin n → ℝ)),
      γ₂ = (stdGauss (Fin n)).prod (stdGauss (Fin n)) := ⟨_, rfl⟩
  have hprob2 : IsProbabilityMeasure γ₂ := by rw [hγ₂]; infer_instance
  obtain ⟨fa, hfa⟩ : ∃ fa : (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
      fa = fun z => nrm (c + τ • z.1) * nrm (c + τ • z.2) := ⟨_, rfl⟩
  obtain ⟨fd, hfd⟩ : ∃ fd : (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
      fd = fun z => ∑ j, (c + τ • z.1) j * (c + τ • z.2) j := ⟨_, rfl⟩
  have ia : Integrable fa γ₂ := by rw [hfa, hγ₂]; exact integrable_nrm_prod c τ
  have icoord : ∀ j : Fin n, Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      (c + τ • z.1) j * (c + τ • z.2) j) γ₂ := fun j => by
    rw [hγ₂]; exact (int_shift_coord c τ j).1.mul_prod (int_shift_coord c τ j).1
  have id' : Integrable fd γ₂ := by
    rw [hfd]; exact integrable_finsetSum _ fun j _ => icoord j
  have ma : Measurable fa := by rw [hfa]; exact (measurable_nrm1 c τ).mul (measurable_nrm2 c τ)
  have md : Measurable fd := by rw [hfd]; exact measurable_dotz c τ
  have hda : ∀ z, |fd z| ≤ fa z := fun z => by
    rw [hfd, hfa]; exact dot_abs_le _ _
  have fa0 : ∀ z, 0 ≤ fa z := fun z => (abs_nonneg _).trans (hda z)
  have hD2le : ∀ z, fd z ^ 2 / fa z ≤ fa z := by
    intro z
    rcases eq_or_lt_of_le (fa0 z) with h | h
    · rw [← h, div_zero]
    · rw [div_le_iff₀ h, ← sq]
      exact sq_le_sq' (by linarith [(abs_le.mp (hda z)).1]) (abs_le.mp (hda z)).2
  have iD : Integrable (fun z => fd z ^ 2 / fa z) γ₂ := by
    refine Integrable.mono' ia ((md.pow_const 2).div ma).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (fa0 z))]
    exact hD2le z
  -- the three integrals
  have h1 : normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 ≤ ∫ z, fa z ∂γ₂ := by
    have hp := integral_prod_mul (μ := stdGauss (Fin n)) (ν := stdGauss (Fin n))
      (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) (fun ξ : Fin n → ℝ => nrm (c + τ • ξ))
    have e : ∫ z, fa z ∂γ₂ = (∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n)) ^ 2 := by
      rw [hfa, hγ₂, sq]; exact hp
    rw [e]
    exact mean_nrm_sq_ge c hτ.le
  have h1' : ∫ z, fa z ∂γ₂ ≤ normSq c + (n : ℝ) * τ ^ 2 := by
    have hp := integral_prod_mul (μ := stdGauss (Fin n)) (ν := stdGauss (Fin n))
      (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) (fun ξ : Fin n → ℝ => nrm (c + τ • ξ))
    have e : ∫ z, fa z ∂γ₂ = (∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n)) ^ 2 := by
      rw [hfa, hγ₂, sq]; exact hp
    rw [e]
    exact mean_nrm_sq_le c τ
  have h2 : ∫ z, fd z ∂γ₂ = normSq c := by
    rw [hfd, integral_finsetSum _ fun j _ => icoord j]
    unfold normSq
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hγ₂]
    have hp := integral_prod_mul (μ := stdGauss (Fin n)) (ν := stdGauss (Fin n))
      (fun ξ : Fin n → ℝ => (c + τ • ξ) j) (fun ξ : Fin n → ℝ => (c + τ • ξ) j)
    rw [(int_shift_coord c τ j).2] at hp
    rw [sq]; exact hp
  -- Cauchy–Schwarz: `∫ d²/(ab) ≥ |c|⁴/ρ²`
  have h3 : normSq c ^ 2 / (normSq c + (n : ℝ) * τ ^ 2) ≤ ∫ z, fd z ^ 2 / fa z ∂γ₂ := by
    have hI0 : 0 ≤ ∫ z, fd z ^ 2 / fa z ∂γ₂ :=
      integral_nonneg fun z => div_nonneg (sq_nonneg _) (fa0 z)
    rcases eq_or_lt_of_le (normSq_nonneg c) with hN | hN
    · rw [← hN]; simpa using hI0
    · obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (normSq c + (n : ℝ) * τ ^ 2) / normSq c := ⟨_, rfl⟩
      have hl0 : 0 < l := by rw [hl]; positivity
      have hpt : ∀ z, fd z ≤ l / 2 * (fd z ^ 2 / fa z) + fa z / (2 * l) :=
        fun z => amgm_div (hda z) hl0
      have hA : ∫ z, (l / 2 * (fd z ^ 2 / fa z) + fa z / (2 * l)) ∂γ₂ =
          ∫ z, l / 2 * (fd z ^ 2 / fa z) ∂γ₂ + ∫ z, fa z / (2 * l) ∂γ₂ :=
        integral_add (iD.const_mul _) (ia.div_const _)
      have hm : ∫ z, fd z ∂γ₂ ≤ ∫ z, (l / 2 * (fd z ^ 2 / fa z) + fa z / (2 * l)) ∂γ₂ :=
        integral_mono id' ((iD.const_mul _).add (ia.div_const _)) hpt
      rw [hA, h2, integral_const_mul, integral_div] at hm
      have h4 : (∫ z, fa z ∂γ₂) / (2 * l) ≤ (normSq c + (n : ℝ) * τ ^ 2) / (2 * l) :=
        div_le_div_of_nonneg_right h1' (by positivity)
      have e4 : (normSq c + (n : ℝ) * τ ^ 2) / (2 * l) = normSq c / 2 := by
        rw [hl]; field_simp
      rw [e4] at h4
      have h5 : normSq c / 2 ≤ l / 2 * ∫ z, fd z ^ 2 / fa z ∂γ₂ := by linarith
      rw [div_le_iff₀ hR]
      have e5 : l / 2 * (∫ z, fd z ^ 2 / fa z ∂γ₂) * (2 * normSq c) =
          (∫ z, fd z ^ 2 / fa z ∂γ₂) * (normSq c + (n : ℝ) * τ ^ 2) := by
        rw [hl]; field_simp
      nlinarith
  -- pointwise
  have hpt : ∀ z, fa z / π + fd z / 2 + fd z ^ 2 / fa z / (2 * π) ≤ Kn c τ z := by
    intro z
    have h := pair_lower (BstLean.Part153.nrm_nonneg (c + τ • z.1))
      (BstLean.Part153.nrm_nonneg (c + τ • z.2)) (dot_abs_le (c + τ • z.1) (c + τ • z.2))
    rw [hfa, hfd]
    exact h
  have j1 := ia.div_const π
  have j2 := id'.div_const 2
  have j3 := iD.div_const (2 * π)
  have hint : ∫ z, (fa z / π + fd z / 2 + fd z ^ 2 / fa z / (2 * π)) ∂γ₂ ≤ ∫ z, Kn c τ z ∂γ₂ :=
    integral_mono ((j1.add j2).add j3) (by rw [hγ₂]; exact integrable_Kn c τ) hpt
  have hA : ∫ z, (fa z / π + fd z / 2 + fd z ^ 2 / fa z / (2 * π)) ∂γ₂ =
      ∫ z, (fa z / π + fd z / 2) ∂γ₂ + ∫ z, fd z ^ 2 / fa z / (2 * π) ∂γ₂ :=
    integral_add (j1.add j2) j3
  have hB : ∫ z, (fa z / π + fd z / 2) ∂γ₂ = ∫ z, fa z / π ∂γ₂ + ∫ z, fd z / 2 ∂γ₂ :=
    integral_add j1 j2
  rw [hA, hB, integral_div, integral_div, integral_div, h2] at hint
  rw [← hγ₂]
  refine le_trans ?_ hint
  have a1 : (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2) / π ≤ (∫ z, fa z ∂γ₂) / π :=
    div_le_div_of_nonneg_right h1 hπ.le
  have a3 : normSq c ^ 2 / (normSq c + (n : ℝ) * τ ^ 2) / (2 * π) ≤
      (∫ z, fd z ^ 2 / fa z ∂γ₂) / (2 * π) := div_le_div_of_nonneg_right h3 (by positivity)
  linarith

/-- `E_{A₁} s_h² = (2/n)·(ρ² − E Kn)`. -/
theorem sO2_mean_eq (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat m n (2 / (n : ℝ)) =
      2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) -
        2 / (n : ℝ) * ∫ z, Kn c τ z ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hGi, hGe⟩ := BstLean.Part153.GamS_mean (m := m) hm c τ (v := 2 / (n : ℝ))
    (by positivity)
  have eG : (fun A : Matrix (Fin m) (Fin n) ℝ => BstLean.Part153.GamS A c τ) =
      fun A => gO A c τ := funext fun A => BstLean.Part153.GamS_eq_gO hm A c τ
  rw [eG] at hGi hGe
  have hH : ∀ i : Fin m, Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => hO A c τ i ^ 2)
      (gaussMat m n (2 / (n : ℝ))) := fun i => (hO_sq_mean hn c τ i).1
  have hS : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => 2 / (m : ℝ) * ∑ i, hO A c τ i ^ 2)
      (gaussMat m n (2 / (n : ℝ))) :=
    (integrable_finsetSum _ fun i _ => hH i).const_mul _
  unfold sO2
  rw [integral_sub hGi hS, hGe, integral_const_mul, integral_finsetSum _ fun i _ => hH i]
  simp_rw [fun i : Fin m => (hO_sq_mean (m := m) hn c τ i).2]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The upper bound of `E_{A₁} s_h²`. -/
noncomputable def scUp (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  2 / (n : ℝ) * ((1 - 1 / π) * (normSq c + (n : ℝ) * τ ^ 2) + τ ^ 2 / π - normSq c / 2 -
    normSq c ^ 2 / (normSq c + (n : ℝ) * τ ^ 2) / (2 * π))

/-- **An upper bound of the mean of the first-layer variance**: `E s_h² ≤ scUp`. -/
theorem sO2_mean_upper (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat m n (2 / (n : ℝ)) ≤ scUp n c τ := by
  rw [sO2_mean_eq hn hm]
  have h := int_Kn_ge hn c hτ
  have h2 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left h h2
  unfold scUp
  have e : 2 / (n : ℝ) * ((1 - 1 / π) * (normSq c + (n : ℝ) * τ ^ 2) + τ ^ 2 / π - normSq c / 2 -
      normSq c ^ 2 / (normSq c + (n : ℝ) * τ ^ 2) / (2 * π)) =
      2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) - 2 / (n : ℝ) *
      ((normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2) / π + normSq c / 2 +
        normSq c ^ 2 / (normSq c + (n : ℝ) * τ ^ 2) / (2 * π)) := by ring
  rw [e]
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms int_Kn_ge
open BstLean.Part160 in
#print axioms sO2_mean_upper
