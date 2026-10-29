import BstLean.Part160Split2

/-!
# Part 160 (file `Split3`): the split of second order with a lower bound of the centre energy

Do not use `sorry`, `native_decide` or `axiom`.

`gap_sq` of `Part160Split2` uses `(E σ)² ≤ γ_A(1 + N22)²`. With a lower bound `e_lo` of the centre
energy `e_b`: `E σ² = γ_A E ω₂ − t_A E⟨h, b/|b|⟩² ≤ γ_A((1 + N22)² − (√e_lo − √(ξ/n))²)`.

* `Esig2_upper`: `t_A·E|r|² ≤ γ_A·E ω₂ − t_A(|b| − |μ − b|)²` when `|μ − b| ≤ |b|`.
* `gap_sq'`, `frameA_point3`: the versions of `gap_sq`, `frameA_point2` with the factor `μ` in the
  place of `1 + N22`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part134 (lam res sig eDir eDir_unit_or_zero measurable_eDir measurable_res)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm XiS Xi4 N2 sq2 hid2Mean_cr)

variable {n : ℕ}

/-- **An upper bound of the mean residual energy**: if `|μ − b| ≤ |b|` then
`t_A·E|r|² ≤ γ_A·E ω₂ − t_A·(|b| − |μ − b|)²`. -/
theorem Esig2_upper (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ}
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b)
    (hbd : nrm (hid2Mean_cr A₁ A₂ c τ - b) ≤ nrm b) :
    ∫ ξ, 2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ∂stdGauss (Fin n) ≤
      2 / (n : ℝ) * ∫ ξ, sq2 A₁ A₂ c τ ξ ^ 2 ∂stdGauss (Fin n) -
        2 / (mA n : ℝ) * (nrm b - nrm (hid2Mean_cr A₁ A₂ c τ - b)) ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  obtain ⟨t, htd⟩ : ∃ t : ℝ, t = 2 / (mA n : ℝ) := ⟨_, rfl⟩
  rw [← htd] at ht0 ⊢
  obtain ⟨mu, hmu⟩ : ∃ mu : Fin (mA n) → ℝ, mu = hid2Mean_cr A₁ A₂ c τ := ⟨_, rfl⟩
  rw [← hmu] at hbd ⊢
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → ℝ,
      f = fun ξ => b ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) := ⟨_, rfl⟩
  obtain ⟨hfm, hfb⟩ := BstLean.Part153.dot_hid2_bdd_cr hn1 A₁ A₂ c τ b
  rw [← hf] at hfm
  have hfb' : ∀ ξ, |f ξ| ≤ nrm b * (opN A₂ * opN A₁) := fun ξ => by rw [hf]; exact hfb ξ
  have hfi : Integrable f (stdGauss (Fin n)) := by
    rw [hf]; exact BstLean.Part153.integrable_dot_hid2_cr hn1 A₁ A₂ c τ b
  have hf2 : Integrable (fun ξ => f ξ ^ 2) (stdGauss (Fin n)) :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable
      ((nrm b * (opN A₂ * opN A₁)) ^ 2) (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(abs_le.mp (hfb' ξ)).1]) (abs_le.mp (hfb' ξ)).2)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ ξ, f ξ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  -- `M² ≤ ∫ f²`
  have hJ : M ^ 2 ≤ ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n) := by
    have i2 := hfi.const_mul (2 * M)
    have hA : ∫ x, (f x ^ 2 - 2 * M * f x + M ^ 2) ∂stdGauss (Fin n) =
        ∫ x, (f x ^ 2 - 2 * M * f x) ∂stdGauss (Fin n) + ∫ _x, M ^ 2 ∂stdGauss (Fin n) :=
      integral_add (hf2.sub i2) (integrable_const _)
    have hB : ∫ x, (f x ^ 2 - 2 * M * f x) ∂stdGauss (Fin n) =
        ∫ x, f x ^ 2 ∂stdGauss (Fin n) - ∫ x, 2 * M * f x ∂stdGauss (Fin n) :=
      integral_sub hf2 i2
    have e : (fun x => (f x - M) ^ 2) = fun x => f x ^ 2 - 2 * M * f x + M ^ 2 :=
      funext fun x => by ring
    have h0 : 0 ≤ ∫ x, (f x - M) ^ 2 ∂stdGauss (Fin n) := integral_nonneg fun x => sq_nonneg _
    rw [e, hA, hB, integral_const_mul, ← hM, integral_const, probReal_univ, one_smul] at h0
    nlinarith
  have hMe : M = b ⬝ᵥ mu := by
    rw [hM, hf, hmu, BstLean.Part153.integral_dot_hid2_cr hn1]
  -- `M ≥ |b|·(|b| − |μ − b|) ≥ 0`
  have hnb := BstLean.Part153.nrm_nonneg b
  have hnd := BstLean.Part153.nrm_nonneg (mu - b)
  have hb2 : normSq b = nrm b ^ 2 := (BstLean.Part153.nrm_sq b).symm
  have hMlo : nrm b * (nrm b - nrm (mu - b)) ≤ M := by
    have e : M = normSq b + b ⬝ᵥ (mu - b) := by
      rw [hMe, dotProduct_sub, BstLean.Part153.dot_self_cr]; ring
    have h1 := BstLean.Part153.abs_dot_le_nrm b (mu - b)
    rw [e, hb2]
    have := (abs_le.mp h1).1
    nlinarith
  have hM2 : normSq b * (nrm b - nrm (mu - b)) ^ 2 ≤ M ^ 2 := by
    have h0 : 0 ≤ nrm b * (nrm b - nrm (mu - b)) := mul_nonneg hnb (by linarith)
    have := pow_le_pow_left₀ h0 hMlo 2
    rw [mul_pow, ← hb2] at this
    exact this
  have hpt : ∀ ξ, t * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) =
      2 / (n : ℝ) * sq2 A₁ A₂ c τ ξ ^ 2 - t / normSq b * f ξ ^ 2 := by
    intro ξ
    rw [BstLean.Part136.normSq_res hb.ne', mul_sub, htd, t_normSq_hid2 hn1, hf]
    have e : ∑ j, hid2 A₁ A₂ (sphPt (c + τ • ξ)) j * b j =
        b ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) := by
      unfold dotProduct
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]; ring
  have hsq2m := BstLean.Part153.measurable_sq2 A₁ A₂ c τ
  have hsq2b : ∀ ξ, |sq2 A₁ A₂ c τ ξ| ≤ opN A₂ * opN A₁ / √(n : ℝ) := by
    intro ξ
    rw [BstLean.Part153.sq2_eq_hid2,
      abs_of_nonneg (div_nonneg (BstLean.Part153.nrm_nonneg _) (Real.sqrt_nonneg _))]
    exact div_le_div_of_nonneg_right (BstLean.Part153.nrm_hid2_sph_le_cr hn1 A₁ A₂ _)
      (Real.sqrt_nonneg _)
  have hs2i : Integrable (fun ξ => sq2 A₁ A₂ c τ ξ ^ 2) (stdGauss (Fin n)) :=
    Integrable.of_bound (hsq2m.pow_const 2).aestronglyMeasurable
      ((opN A₂ * opN A₁ / √(n : ℝ)) ^ 2) (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(abs_le.mp (hsq2b ξ)).1]) (abs_le.mp (hsq2b ξ)).2)
  simp_rw [hpt]
  rw [integral_sub (hs2i.const_mul _) (hf2.const_mul _), integral_const_mul, integral_const_mul]
  have h2 : t * (nrm b - nrm (mu - b)) ^ 2 ≤ t / normSq b * ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    have := mul_le_mul_of_nonneg_left (hM2.trans hJ) ht0
    nlinarith
  linarith

/-- **An upper bound of `(E σ)²` from a lower bound of the centre energy**:
`(E σ)² ≤ γ_A·μ²` when `μ² ≥ (1 + N22)² − (l₁ − e₂)²`, `l₁² ≤ e_lo ≤ e_b`, `ξ/n ≤ e₂²`, `e₂ ≤ l₁`. -/
theorem sigD_mean_sq_le (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ}
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) {xi N22 e2 elo l1 mu : ℝ}
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤ xi * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 A₁ A₂ c τ ≤ N22) (he2 : 0 ≤ e2) (he2' : xi / n ≤ e2 ^ 2)
    (hlo : 2 / (n : ℝ) * elo ≤ 2 / (mA n : ℝ) * normSq b) (hl1 : l1 ^ 2 ≤ elo) (hl12 : e2 ≤ l1)
    (hmu : (1 + N22) ^ 2 - (l1 - e2) ^ 2 ≤ mu ^ 2)
    (hi1 : Integrable (sigD A₁ A₂ c τ b) (stdGauss (Fin n)))
    (hi2 : Integrable (fun ξ => sigD A₁ A₂ c τ b ξ ^ 2) (stdGauss (Fin n))) :
    (∫ ξ, sigD A₁ A₂ c τ b ξ ∂stdGauss (Fin n)) ^ 2 ≤ 2 / (n : ℝ) * mu ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 / (mA n : ℝ) := ⟨_, rfl⟩
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = 2 / (n : ℝ) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have hγ : 0 < γ := by rw [hγd]; positivity
  have hN2nn := BstLean.Part153.N2_nonneg 2 A₁ A₂ c τ
  have hN22nn : 0 ≤ N22 := hN2nn.trans hN22
  obtain ⟨st, hst⟩ : ∃ st : ℝ, st = √t := ⟨_, rfl⟩
  have hst0 : 0 ≤ st := by rw [hst]; exact Real.sqrt_nonneg _
  have hst2 : st ^ 2 = t := by rw [hst]; exact Real.sq_sqrt ht0.le
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ, g0 = √γ := ⟨_, rfl⟩
  have hg0p : 0 < g0 := by rw [hg0]; exact Real.sqrt_pos.mpr hγ
  have hg02 : g0 ^ 2 = γ := by rw [hg0]; exact Real.sq_sqrt hγ.le
  obtain ⟨nb, hnbd⟩ : ∃ nb : ℝ, nb = nrm b := ⟨_, rfl⟩
  obtain ⟨nd, hndd⟩ : ∃ nd : ℝ, nd = nrm (hid2Mean_cr A₁ A₂ c τ - b) := ⟨_, rfl⟩
  have hnb : 0 ≤ nb := by rw [hnbd]; exact BstLean.Part153.nrm_nonneg b
  have hnd : 0 ≤ nd := by rw [hndd]; exact BstLean.Part153.nrm_nonneg _
  have hl10 : 0 ≤ l1 := le_trans he2 hl12
  have hbl : g0 * l1 ≤ st * nb := by
    refine abs_le_of_sq_le_sq' ?_ (mul_nonneg hst0 hnb) |>.2
    rw [mul_pow, mul_pow, hst2, hg02, hnbd, BstLean.Part153.nrm_sq, ht, hγd]
    exact (mul_le_mul_of_nonneg_left hl1 (by positivity)).trans hlo
  have hbu : st * nd ≤ g0 * e2 := by
    refine abs_le_of_sq_le_sq' ?_ (mul_nonneg hg0p.le he2) |>.2
    rw [mul_pow, mul_pow, hst2, hg02, hndd, BstLean.Part153.nrm_sq, ht, hγd]
    refine hxi.trans ?_
    have : xi * (2 / (n : ℝ)) / n = 2 / (n : ℝ) * (xi / n) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left he2' (by positivity)
  have hstp : 0 < st := by rw [hst]; exact Real.sqrt_pos.mpr ht0
  have hbd : nd ≤ nb := by
    have h1 : st * nd ≤ st * nb :=
      hbu.trans ((mul_le_mul_of_nonneg_left hl12 hg0p.le).trans hbl)
    exact le_of_mul_le_mul_left h1 hstp
  have hup := Esig2_upper (τ := τ) hn A₁ A₂ c hb (by rw [← hnbd, ← hndd]; exact hbd)
  rw [← ht, ← hγd, ← hnbd, ← hndd] at hup
  have hσsq : ∀ ξ, sigD A₁ A₂ c τ b ξ ^ 2 =
      t * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) := by
    intro ξ; rw [ht]; exact sigD_sq A₁ A₂ c τ b ξ
  simp_rw [← hσsq] at hup
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ y, sigD A₁ A₂ c τ b y ∂stdGauss (Fin n) := ⟨_, rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I2 : ℝ, I2 = ∫ ξ, sigD A₁ A₂ c τ b ξ ^ 2 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hM, ← hγd]
  rw [← hI2] at hup
  -- Jensen
  have hJ : M ^ 2 ≤ I2 := by
    have i2 := hi1.const_mul (2 * M)
    have hA : ∫ x, (sigD A₁ A₂ c τ b x ^ 2 - 2 * M * sigD A₁ A₂ c τ b x + M ^ 2)
        ∂stdGauss (Fin n) =
        ∫ x, (sigD A₁ A₂ c τ b x ^ 2 - 2 * M * sigD A₁ A₂ c τ b x) ∂stdGauss (Fin n) +
          ∫ _x, M ^ 2 ∂stdGauss (Fin n) :=
      integral_add (hi2.sub i2) (integrable_const _)
    have hB : ∫ x, (sigD A₁ A₂ c τ b x ^ 2 - 2 * M * sigD A₁ A₂ c τ b x) ∂stdGauss (Fin n) =
        ∫ x, sigD A₁ A₂ c τ b x ^ 2 ∂stdGauss (Fin n) -
          ∫ x, 2 * M * sigD A₁ A₂ c τ b x ∂stdGauss (Fin n) :=
      integral_sub hi2 i2
    have e : (fun x => (sigD A₁ A₂ c τ b x - M) ^ 2) =
        fun x => sigD A₁ A₂ c τ b x ^ 2 - 2 * M * sigD A₁ A₂ c τ b x + M ^ 2 :=
      funext fun x => by ring
    have h0 : 0 ≤ ∫ x, (sigD A₁ A₂ c τ b x - M) ^ 2 ∂stdGauss (Fin n) :=
      integral_nonneg fun x => sq_nonneg _
    rw [e, hA, hB, integral_const_mul, ← hM, ← hI2, integral_const, probReal_univ, one_smul] at h0
    nlinarith
  obtain ⟨J, hJd⟩ : ∃ J : ℝ, J = ∫ ξ, sq2 A₁ A₂ c τ ξ ^ 2 ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hJd] at hup
  have h2 : J ≤ (1 + N22) ^ 2 := by
    rw [hJd]
    exact (BstLean.Part153.int_sq2_sq_le hn1 A₁ A₂ c τ).trans
      (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have h4 := mul_le_mul_of_nonneg_left h2 hγ.le
  have h5 : γ * (l1 - e2) ^ 2 ≤ t * (nb - nd) ^ 2 := by
    have e : t * (nb - nd) ^ 2 = (st * nb - st * nd) ^ 2 := by rw [← hst2]; ring
    have e' : γ * (l1 - e2) ^ 2 = (g0 * l1 - g0 * e2) ^ 2 := by rw [← hg02]; ring
    rw [e, e']
    exact pow_le_pow_left₀ (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hl12 hg0p.le))
      (by linarith) 2
  have h6 := mul_le_mul_of_nonneg_left hmu hγ.le
  rw [mul_sub] at h6
  linarith

/-- **The second moment of the positive part of the energy gap**:
`∫ (A − |r|²)₊² ≤ (2 γ_A μ ρ/t_A)²` with `A = γ_A s²/t_A`, `ρ² ≥ N/n`, and
`μ² ≥ (1 + N22)² − (l₁ − e₂)²`, `l₁² ≤ e_lo ≤ e_b` (a LOWER bound of the centre energy; it gives
`(E σ)² ≤ γ_A μ²`). -/
theorem gap_sq' (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) {N eb xi N22 e1 e2 s ρ elo l1 mu : ℝ}
    (hXi : XiS A₁ A₂ c τ ≤ N * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq b ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤ xi * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 A₁ A₂ c τ ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / n ≤ e2 ^ 2)
    (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n)
    (hρ : N / n ≤ ρ ^ 2)
    (hlo : 2 / (n : ℝ) * elo ≤ 2 / (mA n : ℝ) * normSq b) (hl1 : l1 ^ 2 ≤ elo) (hl12 : e2 ≤ l1)
    (_hmu0 : 0 ≤ mu) (hmu : (1 + N22) ^ 2 - (l1 - e2) ^ 2 ≤ mu ^ 2) :
    ∫ ξ, (max 0 (2 / (n : ℝ) * s ^ 2 / (2 / (mA n : ℝ)) -
        normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))))) ^ 2 ∂stdGauss (Fin n) ≤
      (2 * (2 / (n : ℝ)) * mu * ρ / (2 / (mA n : ℝ))) ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) < 2 / (mA n : ℝ) := by positivity
  obtain ⟨hi1, hi2, hV, L, hL, hs'⟩ := sigD_moments hn A₁ A₂ c hτ hb hXi heb hxi hN22 he1 he1'
    he2 he2' hs2
  have hN2nn := BstLean.Part153.N2_nonneg 2 A₁ A₂ c τ
  have hN22nn : 0 ≤ N22 := hN2nn.trans hN22
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 / (mA n : ℝ) := ⟨_, rfl⟩
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = 2 / (n : ℝ) := ⟨_, rfl⟩
  rw [← ht] at ht0 ⊢
  rw [← hγd] at hγ hV hs' ⊢
  have hγs : (√γ * s) ^ 2 = γ * s ^ 2 := by rw [mul_pow, Real.sq_sqrt hγ.le]
  rw [hγs] at hs'
  obtain ⟨σ, hσ⟩ : ∃ σ : (Fin n → ℝ) → ℝ, σ = sigD A₁ A₂ c τ b := ⟨_, rfl⟩
  have hi1' := hi1
  rw [← hσ] at hi1 hV
  have hi2' : Integrable (fun ξ => σ ξ ^ 2) (stdGauss (Fin n)) := by rw [hσ]; exact hi2
  have hL' : L ≤ ∫ ξ, σ ξ ^ 2 ∂stdGauss (Fin n) := by rw [hσ]; exact hL
  have hσ0 : ∀ ξ, 0 ≤ σ ξ := fun ξ => by rw [hσ]; exact sigD_nonneg A₁ A₂ c τ b ξ
  have hσsq : ∀ ξ, σ ξ ^ 2 = t * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) := by
    intro ξ; rw [hσ, ht]; exact sigD_sq A₁ A₂ c τ b ξ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ y, σ y ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hM] at hV
  have hM0 : 0 ≤ M := by rw [hM]; exact integral_nonneg hσ0
  have i2 := hi1.const_mul (2 * M)
  have hcen : Integrable (fun x => (σ x - M) ^ 2) (stdGauss (Fin n)) := by
    have e : (fun x => (σ x - M) ^ 2) = fun x => σ x ^ 2 - 2 * M * σ x + M ^ 2 :=
      funext fun x => by ring
    rw [e]
    exact (hi2'.sub i2).add (integrable_const _)
  have hvar : ∫ x, (σ x - M) ^ 2 ∂stdGauss (Fin n) = ∫ x, σ x ^ 2 ∂stdGauss (Fin n) - M ^ 2 := by
    have hA : ∫ x, (σ x ^ 2 - 2 * M * σ x + M ^ 2) ∂stdGauss (Fin n) =
        ∫ x, (σ x ^ 2 - 2 * M * σ x) ∂stdGauss (Fin n) + ∫ _x, M ^ 2 ∂stdGauss (Fin n) :=
      integral_add (hi2'.sub i2) (integrable_const _)
    have hB : ∫ x, (σ x ^ 2 - 2 * M * σ x) ∂stdGauss (Fin n) =
        ∫ x, σ x ^ 2 ∂stdGauss (Fin n) - ∫ x, 2 * M * σ x ∂stdGauss (Fin n) :=
      integral_sub hi2' i2
    have e : (fun x => (σ x - M) ^ 2) = fun x => σ x ^ 2 - 2 * M * σ x + M ^ 2 :=
      funext fun x => by ring
    rw [e, hA, hB, integral_const_mul, ← hM, integral_const, probReal_univ, one_smul]
    ring
  have hvar0 : 0 ≤ ∫ x, (σ x - M) ^ 2 ∂stdGauss (Fin n) := integral_nonneg fun x => sq_nonneg _
  -- `γ s² ≤ M²`
  have hMlo : γ * s ^ 2 ≤ M ^ 2 := by linarith
  -- `M² ≤ γ (1 + N22)²`
  have hsq2m := BstLean.Part153.measurable_sq2 A₁ A₂ c τ
  have hsq2b : ∀ ξ, |sq2 A₁ A₂ c τ ξ| ≤ opN A₂ * opN A₁ / √(n : ℝ) := by
    intro ξ
    rw [BstLean.Part153.sq2_eq_hid2,
      abs_of_nonneg (div_nonneg (BstLean.Part153.nrm_nonneg _) (Real.sqrt_nonneg _))]
    exact div_le_div_of_nonneg_right (BstLean.Part153.nrm_hid2_sph_le_cr hn1 A₁ A₂ _)
      (Real.sqrt_nonneg _)
  have hs2i : Integrable (fun ξ => sq2 A₁ A₂ c τ ξ ^ 2) (stdGauss (Fin n)) :=
    Integrable.of_bound (hsq2m.pow_const 2).aestronglyMeasurable
      ((opN A₂ * opN A₁ / √(n : ℝ)) ^ 2) (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(abs_le.mp (hsq2b ξ)).1]) (abs_le.mp (hsq2b ξ)).2)
  have hMhi : M ^ 2 ≤ γ * mu ^ 2 := by
    rw [hM, hσ, hγd]
    exact sigD_mean_sq_le hn A₁ A₂ c hb hxi hN22 he2 he2' hlo hl1 hl12 hmu hi1' hi2
  -- the pointwise bound
  have hpt : ∀ ξ, (max 0 (γ * s ^ 2 / t - normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))))) ^ 2 ≤
      4 * M ^ 2 / t ^ 2 * (σ ξ - M) ^ 2 := by
    intro ξ
    have hR : normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) = σ ξ ^ 2 / t := by
      rw [hσsq]; field_simp
    rw [hR]
    have e : γ * s ^ 2 / t - σ ξ ^ 2 / t = (γ * s ^ 2 - σ ξ ^ 2) / t := by ring
    rw [e]
    have hrhs : 0 ≤ 4 * M ^ 2 / t ^ 2 * (σ ξ - M) ^ 2 := by positivity
    by_cases hD : γ * s ^ 2 - σ ξ ^ 2 ≤ 0
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hD ht0.le)]
      simpa using hrhs
    · have hD' : 0 < γ * s ^ 2 - σ ξ ^ 2 := not_le.mp hD
      rw [max_eq_right (div_nonneg hD'.le ht0.le)]
      have hlt : σ ξ < M := by
        by_contra hge
        have hge' : M ≤ σ ξ := not_lt.mp hge
        have : M ^ 2 ≤ σ ξ ^ 2 := pow_le_pow_left₀ hM0 hge' 2
        linarith
      have h1 : γ * s ^ 2 - σ ξ ^ 2 ≤ 2 * M * (M - σ ξ) := by
        nlinarith [hσ0 ξ]
      have h2 : (γ * s ^ 2 - σ ξ ^ 2) ^ 2 ≤ (2 * M * (M - σ ξ)) ^ 2 :=
        pow_le_pow_left₀ hD'.le h1 2
      rw [div_pow]
      calc (γ * s ^ 2 - σ ξ ^ 2) ^ 2 / t ^ 2 ≤ (2 * M * (M - σ ξ)) ^ 2 / t ^ 2 :=
            div_le_div_of_nonneg_right h2 (sq_nonneg t)
        _ = _ := by ring
  have hmono := integral_mono_of_nonneg (μ := stdGauss (Fin n))
    (Filter.Eventually.of_forall fun ξ => sq_nonneg
      (max 0 (γ * s ^ 2 / t - normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))))))
    (hcen.const_mul (4 * M ^ 2 / t ^ 2)) (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  refine hmono.trans ?_
  have hNn : N * γ / n = γ * (N / n) := by ring
  rw [hNn] at hV
  have h5 : 4 * M ^ 2 / t ^ 2 * ∫ x, (σ x - M) ^ 2 ∂stdGauss (Fin n) ≤
      4 * (γ * mu ^ 2) / t ^ 2 * (γ * ρ ^ 2) := by
    have h6 : ∫ x, (σ x - M) ^ 2 ∂stdGauss (Fin n) ≤ γ * ρ ^ 2 :=
      hV.trans (mul_le_mul_of_nonneg_left hρ hγ.le)
    have h7 : 4 * M ^ 2 / t ^ 2 ≤ 4 * (γ * mu ^ 2) / t ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)
    exact mul_le_mul h7 h6 hvar0 (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The frame bound at one retained value by the split of second order, with a lower bound of
the centre energy, every number free.**
`n·L_A ≤ (N + ξ)/s² + 2κμρ/(sd²·s²) + (16.09·a)⁴/(n³(s − sd)⁸)`, `μ² ≥ (1 + N22)² − (l₁ − e₂)²`. -/
theorem frameA_point3 (hn : 10 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) {N a eb xi e1 e2 N22 q sd s r η κ ρ elo l1 mu cf : ℝ} (hN0 : 0 ≤ N)
    (hb : 0 < normSq ((1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N * (2 / (n : ℝ)) / n)
    (hXi4 : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (hXi8 : Xi8 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq ((1 / rhoC c.1.2 (D.tau0 c)) •
      bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤
        xi * (2 / (n : ℝ)) / n)
    (hN2 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / (n : ℝ) ≤ e2 ^ 2)
    (hq : 2 * N / n ≤ q)
    (hsd : 0 < sd) (hs : sd < s) (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - q)
    (ha0 : 0 ≤ a) (hr : 0 ≤ r) (hr2 : 4 * a ^ 2 + N ^ 2 ≤ r ^ 2) (hη : 0 < η) (hκ0 : 0 < κ)
    (hκ : (1 + η) ^ 3 * (2 * a + r) ^ 2 + (1 + 1 / η) ^ 3 * xi ^ 2 ≤ κ ^ 2)
    (hρ0 : 0 < ρ) (hρ : N / n ≤ ρ ^ 2)
    (hlo : 2 / (n : ℝ) * elo ≤ 2 / (mA n : ℝ) * normSq ((1 / rhoC c.1.2 (D.tau0 c)) •
      bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c))) (hl1 : l1 ^ 2 ≤ elo) (hl12 : e2 ≤ l1)
    (hmu0 : 0 < mu) (hmu : (1 + N22) ^ 2 - (l1 - e2) ^ 2 ≤ mu ^ 2)
    (hsum : (N + xi) / s ^ 2 + 2 * κ * mu * ρ / (sd ^ 2 * s ^ 2) +
      (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) ≤ cf)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      cf / n * ∑ j, w j ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) < 2 / (mA n : ℝ) := by positivity
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs0 : 0 < s := lt_trans hsd hs
  have hgap : 0 < s - sd := by linarith
  have hN2nn := BstLean.Part153.N2_nonneg 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)
  have hN22nn : 0 ≤ N22 := hN2nn.trans hN2
  have hs2' : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n := by linarith
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j, w j ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← hS]
  by_cases hSz : S = 0
  · have hw : w = 0 := BstLean.Part134.eq_zero_of_normSq (by rw [← hSz, hS]; rfl)
    simp [hw, hSz]
  have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSz)
  have hcov := cov_at_of_XiS hn6 D c hτ hXi
  have hcen : CENTRE_at D c xi := by
    unfold CENTRE_at
    rw [hD c, muStand_eq]
    exact hxi
  have hT1 := Cr_at hn1 D c hN0 hcov hcen w
  rw [← hS] at hT1
  rw [← hD c] at hb heb hxi hlo
  obtain ⟨b, hbd⟩ : ∃ b : Fin (mA n) → ℝ, b = D.bA c.1 c.2.1.1 := ⟨_, rfl⟩
  rw [← hbd] at hb heb hxi hlo hT1 ⊢
  have hint : Integrable (fun ξ => (∑ j, res b (hStand D c ξ) j * w j) ^ 2) (stdGauss (Fin n)) := by
    simp_rw [res_symm b _ w]
    exact hStand_int2 hn1 D c (res b w)
  obtain ⟨hint4, hP4⟩ := resid_fourth hn6 c.2.1.1.1 c.2.1.1.2 c.1.2 hτ b w hXi hXi4 hxi ha0 hr
    hr2 hη hκ0.le hκ
  rw [← hS] at hP4
  have hQ2 := gap_sq' hn6 c.2.1.1.1 c.2.1.1.2 c.1.2 hτ hb hXi heb hxi hN2 he1 he1' he2 he2' hs2'
    hρ hlo hl1 hl12 hmu0.le hmu
  have hm8 := mass_bound8 hn c.2.1.1.1 c.2.1.1.2 c.1.2 hτ hb hXi hXi4 hXi8 heb hxi hN2 he1 he1'
    he2 he2' hsd.le hs hs2'
  -- the cutoffs
  obtain ⟨ac, hac⟩ : ∃ ac : ℝ, ac = 2 / (n : ℝ) * sd ^ 2 / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Ac, hAc⟩ : ∃ Ac : ℝ, Ac = 2 / (n : ℝ) * s ^ 2 / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have hac0 : 0 < ac := by rw [hac]; positivity
  have hAc0 : 0 < Ac := by rw [hAc]; positivity
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = κ * (2 / (n : ℝ) / n) * S / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : ℝ, Q = 2 * (2 / (n : ℝ)) * mu * ρ / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hPd]; positivity
  have hQ0 : 0 < Q := by rw [hQd]; positivity
  rw [← hPd] at hP4
  rw [← hAc, ← hQd] at hQ2
  have h1 := frame_split2 (stdGauss (Fin n)) (measurable_hStand D c) b w hac0 hAc0 hP0 hQ0 hint
    hint4 hP4 hQ2
  rw [← hS] at h1
  have hset : {ξ : Fin n → ℝ | normSq (res b (hStand D c ξ)) < ac} =
      {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 c.2.1.1.1 c.2.1.1.2
        (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    change normSq (res b (hStand D c ξ)) < ac ↔
      2 / (mA n : ℝ) * normSq (res b (hStand D c ξ)) < 2 / (n : ℝ) * sd ^ 2
    rw [hac, lt_div_iff₀ (by positivity), mul_comm]
  rw [hset] at h1
  obtain ⟨Pm, hPm⟩ : ∃ Pm : ℝ, Pm = (stdGauss (Fin n)).real
      {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 c.2.1.1.1 c.2.1.1.2
        (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := ⟨_, rfl⟩
  rw [← hPm] at h1 hm8
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ ξ, (∑ j, res b (hStand D c ξ) j * w j) ^ 2
      ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hI] at h1 hT1
  obtain ⟨M8, hM8⟩ : ∃ M8 : ℝ, M8 = (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) :=
    ⟨_, rfl⟩
  rw [← hM8] at hm8 hsum
  -- the three terms
  have t1 : 1 / Ac * I ≤ (N + xi) / s ^ 2 / n * S := by
    have e : 1 / Ac * I = (2 / (mA n : ℝ) * I) / (2 / (n : ℝ) * s ^ 2) := by
      rw [hAc]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : (N + xi) / s ^ 2 / n * S * (2 / (n : ℝ) * s ^ 2) =
        (N + xi) * (2 / (n : ℝ)) / n * S := by field_simp
    rw [e2]; exact hT1
  have t2 : P * Q / (ac * Ac) = 2 * κ * mu * ρ / (sd ^ 2 * s ^ 2) / n * S := by
    rw [hPd, hQd, hac, hAc]
    field_simp
  have t3 : Pm * S ≤ M8 / n * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS0
    rw [le_div_iff₀ hnR]; linarith
  have t4 : ((N + xi) / s ^ 2 / n + 2 * κ * mu * ρ / (sd ^ 2 * s ^ 2) / n + M8 / n) * S ≤
      cf / n * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS0
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right hsum hnR.le
  rw [t2] at h1
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms Esig2_upper
open BstLean.Part160 in
#print axioms gap_sq'
open BstLean.Part160 in
#print axioms frameA_point3
open BstLean.Part160 in
#print axioms sigD_mean_sq_le
