import BstLean.Part150NormA

/-!
# Part 150, item 5: `bO/ρ` against `bMF`, the mean over `A₂` for a fixed good `A₁`

* `bO_sub_bMF_pt`: for every `A₂`:
  `|bO/ρ − bMF|² ≤ (m/π)·Δ²/s2 + 2|A₂ e₁|²`, with `s2 = (2/m)(N2 − |b1|²) > 0`,
  `Δ = s2 − sO2/ρ²`, `e₁ = b1 − hO/ρ` (`e1N`).
* `bO_sub_bMF_A2`: the mean over `A₂`: `≤ (m/π)·Δ²/s2 + 4|e₁|²`.
* **`normII_fixed`**: for a first matrix `A₁` with `errD1 ≤ (dεD)²` and `Qk k ≤ (dεQ)²`:
  `E_{A₂}|bO/ρ − bMF|² ≤ CQn·Qk/d + CEn·errD1/d + d·C0n` (`d = m/n`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part137 BstLean.Part141
open BstLean.Part149 (a1 b1 N2 sMF bMF errD1 Qk)

variable {n m : ℕ}

/-- The comparison for every `A₂`. -/
theorem bO_sub_bMF_pt (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < 2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁))) :
    normSq ((1 / rhoC c τ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)) ≤
      (m : ℝ) / π * ((sO2 A₁ c τ / rhoC c τ ^ 2 -
          2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁))) ^ 2 /
        (2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)))) +
      2 * normSq (A₂.mulVec (e1N c τ A₁)) := by
  have hρ := rhoC_pos hn c hτ
  set ρ := rhoC c τ with hρdef
  set s2 : ℝ := 2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)) with hs2
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set δ : ℝ := √(sO2 A₁ c τ / ρ ^ 2) - √s2 with hδ
  have hδ2 : δ ^ 2 ≤ (sO2 A₁ c τ / ρ ^ 2 - s2) ^ 2 / s2 := sqrt_sub_sq_le_div _ hs
  have esO : 1 / ρ * sO A₁ c τ = √(sO2 A₁ c τ / ρ ^ 2) := by
    unfold sO
    rw [Real.sqrt_div' _ (sq_nonneg ρ), Real.sqrt_sq hρ.le]; ring
  have esMF : sMF c τ A₁ = √s2 := rfl
  have eA : A₂.mulVec (e1N c τ A₁) =
      A₂.mulVec (b1 c τ A₁) - (1 / ρ) • A₂.mulVec (hO A₁ c τ) := by
    unfold e1N
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hcoord : ∀ j, ((1 / ρ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)) j ^ 2 ≤
      2 * (1 / (2 * π)) * δ ^ 2 + 2 * (A₂.mulVec (e1N c τ A₁)) j ^ 2 := by
    intro j
    have e1 : ((1 / ρ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)) j =
        psiS (1 / ρ * sO A₁ c τ) (1 / ρ * (A₂.mulVec (hO A₁ c τ)) j) -
          psiS (sMF c τ A₁) ((A₂.mulVec (b1 c τ A₁)) j) := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [psiS_smul (by positivity)]
      rfl
    have t1 := psiS_lip_s_phi (1 / ρ * sO A₁ c τ) (sMF c τ A₁)
      (1 / ρ * (A₂.mulVec (hO A₁ c τ)) j)
    have t2 := psiS_lip_x (sMF c τ A₁) (1 / ρ * (A₂.mulVec (hO A₁ c τ)) j)
      ((A₂.mulVec (b1 c τ A₁)) j)
    rw [esO, esMF] at t1
    have e2 : 1 / ρ * (A₂.mulVec (hO A₁ c τ)) j - (A₂.mulVec (b1 c τ A₁)) j =
        -(A₂.mulVec (e1N c τ A₁)) j := by
      rw [eA]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e2, abs_neg] at t2
    have hx : |((1 / ρ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)) j| ≤
        1 / √(2 * π) * |δ| + |(A₂.mulVec (e1N c τ A₁)) j| := by
      rw [e1, esO, esMF] at *
      refine (abs_sub_le _ (psiS (√s2) (1 / ρ * (A₂.mulVec (hO A₁ c τ)) j)) _).trans ?_
      rw [esMF] at t2
      exact add_le_add t1 t2
    have hphi : (1 / √(2 * π)) ^ 2 = 1 / (2 * π) := by
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
    have hsq := abs_le_of_sq_le_sq' (le_refl _) (by positivity :
      (0 : ℝ) ≤ 1 / √(2 * π) * |δ| + |(A₂.mulVec (e1N c τ A₁)) j|)
    have h2 : ((1 / ρ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)) j ^ 2 ≤
        (1 / √(2 * π) * |δ| + |(A₂.mulVec (e1N c τ A₁)) j|) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    refine h2.trans ?_
    have h3 : (1 / √(2 * π) * |δ| + |(A₂.mulVec (e1N c τ A₁)) j|) ^ 2 ≤
        2 * (1 / √(2 * π) * |δ|) ^ 2 + 2 * |(A₂.mulVec (e1N c τ A₁)) j| ^ 2 := by
      nlinarith only [sq_nonneg (1 / √(2 * π) * |δ| - |(A₂.mulVec (e1N c τ A₁)) j|)]
    rw [mul_pow, hphi, sq_abs, sq_abs] at h3
    linarith only [h3]
  have hsum : normSq ((1 / ρ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)) ≤
      (m : ℝ) * (2 * (1 / (2 * π)) * δ ^ 2) + 2 * normSq (A₂.mulVec (e1N c τ A₁)) := by
    unfold normSq
    refine (Finset.sum_le_sum fun j _ => hcoord j).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
  refine hsum.trans ?_
  have : (m : ℝ) * (2 * (1 / (2 * π)) * δ ^ 2) ≤
      (m : ℝ) / π * ((sO2 A₁ c τ / ρ ^ 2 - s2) ^ 2 / s2) := by
    have e : (m : ℝ) * (2 * (1 / (2 * π)) * δ ^ 2) = (m : ℝ) / π * δ ^ 2 := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hδ2 (by positivity)
  linarith only [this]

/-- The comparison in mean over `A₂`. -/
theorem bO_sub_bMF_A2 (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (hs : 0 < 2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁))) :
    ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)))
        ∂gaussMat m m (2 / (m : ℝ)) ≤
      ENNReal.ofReal ((m : ℝ) / π * ((sO2 A₁ c τ / rhoC c τ ^ 2 -
          2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁))) ^ 2 /
        (2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)))) + 4 * normSq (e1N c τ A₁)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hint, hval⟩ := layer_lin_sq (m := m) (k := m) (v := 2 / (m : ℝ)) (by positivity)
    (e1N c τ A₁)
  set C : ℝ := (m : ℝ) / π * ((sO2 A₁ c τ / rhoC c τ ^ 2 -
      2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁))) ^ 2 /
    (2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)))) with hC
  have hC0 : 0 ≤ C := by rw [hC]; have := Real.pi_pos; positivity
  have hI : Integrable (fun A₂ : Matrix (Fin m) (Fin m) ℝ =>
      C + 2 * normSq (A₂.mulVec (e1N c τ A₁))) (gaussMat m m (2 / (m : ℝ))) :=
    (integrable_const C).add (hint.const_mul 2)
  have hv : ∫ A₂ : Matrix (Fin m) (Fin m) ℝ, C + 2 * normSq (A₂.mulVec (e1N c τ A₁))
      ∂gaussMat m m (2 / (m : ℝ)) = C + 4 * normSq (e1N c τ A₁) := by
    rw [integral_add (integrable_const C) (hint.const_mul 2)]
    have e1 : ∫ _A₂ : Matrix (Fin m) (Fin m) ℝ, C ∂gaussMat m m (2 / (m : ℝ)) = C := by
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have e2 : ∫ A₂ : Matrix (Fin m) (Fin m) ℝ, 2 * normSq (A₂.mulVec (e1N c τ A₁))
        ∂gaussMat m m (2 / (m : ℝ)) = 2 * ((m : ℝ) * (2 / (m : ℝ) * normSq (e1N c τ A₁))) := by
      rw [integral_const_mul, hval]
    rw [e1, e2]
    field_simp
    ring
  calc ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)))
        ∂gaussMat m m (2 / (m : ℝ))
      ≤ ∫⁻ A₂ : Matrix (Fin m) (Fin m) ℝ, ENNReal.ofReal (C + 2 * normSq (A₂.mulVec (e1N c τ A₁)))
          ∂gaussMat m m (2 / (m : ℝ)) :=
        lintegral_mono fun A₂ => ENNReal.ofReal_le_ofReal (bO_sub_bMF_pt hn c hτ A₁ A₂ hs)
    _ = ENNReal.ofReal (C + 4 * normSq (e1N c τ A₁)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hI
          (Filter.Eventually.of_forall fun A₂ =>
            add_nonneg hC0 (mul_nonneg (by norm_num) (normSq_nonneg _))), hv]

/-- The constant of `Qk` in the comparison. -/
noncomputable def CQn (n : ℕ) (εD εQ lam : ℝ) : ℝ :=
  192 * (6 / (n : ℝ)) / (π * (1 - εD)) +
    (4 + 24 * (6 / (n : ℝ)) * (εQ + 2 * εD ^ 2 + 6 / (n : ℝ) / 2) / (π * (1 - εD))) / (2 * lam)

/-- The constant of `errD1` in the comparison. -/
noncomputable def CEn (n : ℕ) (εD εQ : ℝ) : ℝ :=
  24 * (6 / (n : ℝ)) * (17 + 16 * εD) / (π * (1 - εD)) +
    2 * (6 / (n : ℝ)) *
      (4 + 24 * (6 / (n : ℝ)) * (εQ + 2 * εD ^ 2 + 6 / (n : ℝ) / 2) / (π * (1 - εD)))

/-- The constant term of the comparison. -/
noncomputable def C0n (n : ℕ) (εD εQ lam : ℝ) : ℝ :=
  96 * (1 + εD) * (6 / (n : ℝ)) ^ 2 / (π * (1 - εD)) +
    (4 + 24 * (6 / (n : ℝ)) * (εQ + 2 * εD ^ 2 + 6 / (n : ℝ) / 2) / (π * (1 - εD))) *
      (6 / (n : ℝ)) ^ 2 * (lam + 1) / 2

/-- **The comparison for a fixed good `A₁`, in mean over `A₂`.** -/
theorem normII_fixed (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) {k εD εQ lam : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hεD0 : 0 ≤ εD) (hεD1 : εD < 1) (hεQ0 : 0 ≤ εQ)
    (hcond : k * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD)) (hlam : 0 < lam)
    (hD1 : errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2)
    (hQ : Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2) :
    ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂)))
        ∂gaussMat m m (2 / (m : ℝ)) ≤
      ENNReal.ofReal (CQn n εD εQ lam * (Qk k c τ A₁ / ((m : ℝ) / n)) +
        CEn n εD εQ * (errD1 c τ A₁ / ((m : ℝ) / n)) + (m : ℝ) / n * C0n n εD εQ lam) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set d : ℝ := (m : ℝ) / n with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have h1ε : 0 < 1 - εD := by linarith
  obtain ⟨hN2pos, hY, _⟩ := BstLean.Part149.centre_det hn hm c τ A₁ (π₀ := 1 / 2) (ζ := 1)
    (K := 0) hk0 hk1 hεD0 hεD1 hεQ0 hcond (by norm_num) (by norm_num) (by norm_num) le_rfl hD1 hQ
  have hNabs := BstLean.Part149.abs_N2_sub_le (stdGauss (Fin n))
    (BstLean.Part149.bm_a1 hn c τ A₁) (d := d) (δ := d * εD) (by positivity) hD1
  have hNabs' : |N2 c τ A₁ - d| ≤ d * εD := hNabs
  have hNlo : d * (1 - εD) ≤ N2 c τ A₁ := by linarith [(abs_le.mp hNabs').1]
  have hNhi : N2 c τ A₁ ≤ d * (1 + εD) := by linarith [(abs_le.mp hNabs').2]
  set s2 : ℝ := 2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)) with hs2
  have hs2lo : (1 - εD) / (2 * n) ≤ s2 := by
    have h1 : d * (1 - εD) / 4 ≤ N2 c τ A₁ - normSq (b1 c τ A₁) := by linarith
    have h2 : 2 / (m : ℝ) * (d * (1 - εD) / 4) ≤ s2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : 2 / (m : ℝ) * (d * (1 - εD) / 4) = (1 - εD) / (2 * n) := by
      rw [hd]; field_simp; ring
    linarith
  have hs2pos : 0 < s2 := lt_of_lt_of_le (by positivity) hs2lo
  refine (bO_sub_bMF_A2 hn hm c hτ A₁ hs2pos).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the quantities
  set V := VN c τ with hV
  have hV0 : 0 ≤ V := VN_nonneg c τ
  have hV6 : V ≤ 6 / (n : ℝ) := VN_le hn c hτ
  set E := errD1 c τ A₁ with hE
  have hE0 : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  set Q := Qk k c τ A₁ with hQdef
  have hQ0 : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  set I := ∫ γ, wN c τ γ * nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n) with hI
  have hI2 : |I| ^ 2 ≤ 2 * V * E / d + d * V ^ 2 / 2 := by
    rw [sq_abs]; exact wnrm_sq_le hn hm c hτ A₁
  have he := e1N_normSq_le hn c hτ A₁ k
  rw [← hI, ← sq_abs I] at he
  have hp := dotp_b1_e1N_le hn c hτ A₁ hk0
  have hΔ := sMF_sq_sub_sO2 hn hm c hτ A₁
  set e := normSq (e1N c τ A₁) with hedef
  have he0 : 0 ≤ e := normSq_nonneg _
  set p := |dotp (b1 c τ A₁) (e1N c τ A₁)| with hpdef
  have hp0 : 0 ≤ p := abs_nonneg _
  have hX0 : 0 ≤ √E * √V + 2 * p + e := by positivity
  have hmain := arith_II (lam := lam) (Pc := π * (1 - εD))
    (ce := εQ + 2 * εD ^ 2 + 6 / (n : ℝ) / 2)
    (ke := 4 + 24 * (6 / (n : ℝ)) * (εQ + 2 * εD ^ 2 + 6 / (n : ℝ) / 2) / (π * (1 - εD)))
    hd0 hεD0 hεQ0 hk1 hV0 hV6 hE0 hD1 hQ0 hQ hN2pos.le hNhi (abs_nonneg I) hI2 he0 he hp0 hp hlam
    (by positivity) rfl rfl
  -- the scale term
  have hΔ2 : (sO2 A₁ c τ / rhoC c τ ^ 2 - s2) ^ 2 ≤
      (2 / (m : ℝ) * (√E * √V + 2 * p + e)) ^ 2 := by
    have : |sO2 A₁ c τ / rhoC c τ ^ 2 - s2| ≤ 2 / (m : ℝ) * (√E * √V + 2 * p + e) := by
      rw [abs_sub_comm]; exact hΔ
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hterm : (m : ℝ) / π * ((sO2 A₁ c τ / rhoC c τ ^ 2 - s2) ^ 2 / s2) ≤
      8 / (π * (1 - εD) * d) * (√E * √V + 2 * p + e) ^ 2 := by
    have h1 : (sO2 A₁ c τ / rhoC c τ ^ 2 - s2) ^ 2 / s2 ≤
        (2 / (m : ℝ) * (√E * √V + 2 * p + e)) ^ 2 / ((1 - εD) / (2 * n)) := by
      apply div_le_div₀ (by positivity) hΔ2 (by positivity) hs2lo
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (m : ℝ) / π)
    refine h2.trans (le_of_eq ?_)
    rw [hd]; field_simp; ring
  unfold CQn CEn C0n
  linarith only [hmain, hterm]

end BstLean.Part150
