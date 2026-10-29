import BstLean.Part136Det
import BstLean.Part140Dist

/-!
# Part 149: the frame bound and the scalars from an `L²` bound of the Gram kernel

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md`, item 3 (deterministic part). Every probability space
`(U, μ)` and every hidden map `h` with bounded measurable coordinates. Hypotheses: the Gram kernel
`G(u, u') = ⟨h(u), h(u')⟩` is within `Δ` of a constant `a` in `L²(μ ⊗ μ)`, and `|h(u)|²` is within
`δ` of a constant `d` in `L²(μ)`. With `b = h̄ = E_u h(u)` (the exact centre):

* `frameA`: `b ≠ 0` and the unit residual directions have the frame bound
  `Δ/s + Δ²/ε₂² + δ²/ε₁²` (`det_frame` of Part 136 with no feature family: the Hilbert–Schmidt
  rate).
* `scalarsA`: `||b|² − a| ≤ Δ`; `E_u |b|²(λ(u) − 1)² ≤ Δ²/(a − Δ)`;
  `E_u |r(u)|² ≤ d + δ − |b|²`;
  `E_u (|r(u)| − √(d − |b|²))² ≤ (Δ/√(a − Δ) + (δ + 2Δ)/√(d − a − Δ))²`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM bm_cauchy_schwarz)
open BstLean.Part130 BstLean.Part134
open BstLean.Part132 (nrm nrm_nonneg nrm_sq)
open BstLean.Part136 (hbar det_frame bm_fst bm_snd normSq_res)

variable {m : ℕ} {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]

/-- Minkowski's inequality in `L²` for bounded measurable functions. -/
lemma bm_minkowski {f g : U → ℝ} (hf : BM f) (hg : BM g) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : ∫ u, f u ^ 2 ∂μ ≤ a ^ 2) (h2 : ∫ u, g u ^ 2 ∂μ ≤ b ^ 2) :
    ∫ u, (f u + g u) ^ 2 ∂μ ≤ (a + b) ^ 2 := by
  have cs := bm_cauchy_schwarz μ hf hg
  have i1 : 0 ≤ ∫ u, f u ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have h3 : ∫ u, f u * g u ∂μ ≤ a * b := by
    have h4 : (∫ u, f u * g u ∂μ) ^ 2 ≤ (a * b) ^ 2 := by
      calc (∫ u, f u * g u ∂μ) ^ 2 ≤ (∫ u, f u ^ 2 ∂μ) * ∫ u, g u ^ 2 ∂μ := cs
        _ ≤ a ^ 2 * b ^ 2 := mul_le_mul h1 h2 (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg a)
        _ = (a * b) ^ 2 := by ring
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h4 (mul_nonneg ha hb))
  have e : (fun u => (f u + g u) ^ 2) = fun u => (f u ^ 2 + 2 * (f u * g u)) + g u ^ 2 := by
    funext u; ring
  rw [e, integral_add (f := fun u => f u ^ 2 + 2 * (f u * g u)) (g := fun u => g u ^ 2)
      ((hf.sq.integrable μ).add (((hf.mul hg).integrable μ).const_mul _)) (hg.sq.integrable μ),
    integral_add (f := fun u => f u ^ 2) (g := fun u => 2 * (f u * g u)) (hf.sq.integrable μ)
      (((hf.mul hg).integrable μ).const_mul _), integral_const_mul]
  nlinarith

/-- **The frame bound of the unit residual directions for the exact centre, from an `L²` bound of
the Gram kernel against a constant.** -/
theorem frameA {h : U → Fin m → ℝ} (hh : ∀ j, BM (fun u => h u j))
    {a Δ d δ ε₁ ε₂ s : ℝ} (hΔ : 0 ≤ Δ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (haΔ : Δ < a)
    (hD : ∫ p, (∑ k, h p.1 k * h p.2 k - a) ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂μ ≤ δ ^ 2)
    (hs : 0 < s) (hsle : s ≤ d - ε₁ - (a + ε₂) ^ 2 / (a - Δ)) :
    hbar μ h ≠ 0 ∧ ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, eDir (hbar μ h) (h u) j * w j) ^ 2 ∂μ ≤
        (Δ / s + Δ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
  have h0 := det_frame μ hh (κ := Fin 0) (κ₂ := Fin 0) (ℓ := fun _ _ => 0) (ℓ₂ := fun _ _ => 0)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (τ := 0) (τ₂ := 0) le_rfl le_rfl (fun v => by simp) (fun v => by simp)
    (a := a) (c := 0) (c₂ := 0) (Δ := Δ) (d := d) (δ := δ) (ε₁ := ε₁) (ε₂ := ε₂) (s := s)
    le_rfl le_rfl hΔ hε₁ hε₂ haΔ (by simpa using hD) hd hs hsle
  refine ⟨h0.1, fun w => ?_⟩
  have := h0.2 w
  simpa using this

/-- **The scalars of the stand-in for the exact centre.** -/
theorem scalarsA {h : U → Fin m → ℝ} (hh : ∀ j, BM (fun u => h u j))
    {a Δ d δ : ℝ} (hΔ : 0 ≤ Δ) (hδ : 0 ≤ δ) (haΔ : Δ < a) (hda : a + Δ < d)
    (hD : ∫ p, (∑ k, h p.1 k * h p.2 k - a) ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂μ ≤ δ ^ 2) :
    |normSq (hbar μ h) - a| ≤ Δ ∧
    ∫ u, normSq (hbar μ h) * (lam (hbar μ h) (h u) - 1) ^ 2 ∂μ ≤ Δ ^ 2 / (a - Δ) ∧
    ∫ u, normSq (res (hbar μ h) (h u)) ∂μ ≤ d + δ - normSq (hbar μ h) ∧
    ∫ u, (√(normSq (res (hbar μ h) (h u))) - √(d - normSq (hbar μ h))) ^ 2 ∂μ ≤
      (Δ / √(a - Δ) + (δ + 2 * Δ) / √(d - a - Δ)) ^ 2 := by
  set b := hbar μ h with hb
  have hbj : ∀ j, b j = ∫ u, h u j ∂μ := fun j => rfl
  have hmeas : Measurable h := measurable_pi_iff.mpr fun j => (hh j).meas
  set D : U × U → ℝ := fun p => ∑ k, h p.1 k * h p.2 k - a with hDdef
  have bG : BM (fun p : U × U => ∑ k, h p.1 k * h p.2 k) :=
    bm_sum Finset.univ fun k _ => (bm_fst (hh k)).mul (bm_snd (hh k))
  have bD : BM D := bG.sub (BM.const a)
  set X : U → ℝ := fun u => ∑ j, h u j * b j with hX
  have bX : BM X := bm_sum Finset.univ fun j _ => (hh j).mul (BM.const _)
  have eX : ∀ u, X u - a = ∫ u', D (u, u') ∂μ := by
    intro u
    have i1 : Integrable (fun u' => ∑ k, h u k * h u' k) μ :=
      integrable_finsetSum _ fun k _ => ((hh k).integrable μ).const_mul _
    have v1 : ∫ u', ∑ k, h u k * h u' k ∂μ = X u := by
      rw [integral_finsetSum _ fun k _ => ((hh k).integrable μ).const_mul _]
      simp only [integral_const_mul, hX, hbj]
    simp only [hDdef]
    rw [integral_sub i1 (integrable_const a), v1]
    simp
  have hXa : ∫ u, (X u - a) ^ 2 ∂μ ≤ Δ ^ 2 := by
    have pt : ∀ u, (∫ u', D (u, u') ∂μ) ^ 2 ≤ ∫ u', D (u, u') ^ 2 ∂μ := by
      intro u
      have bDu : BM (fun u' => D (u, u')) := bD.comp (measurable_const.prodMk measurable_id)
      have := bm_cauchy_schwarz μ bDu (BM.const 1)
      simpa using this
    calc ∫ u, (X u - a) ^ 2 ∂μ = ∫ u, (∫ u', D (u, u') ∂μ) ^ 2 ∂μ := by simp_rw [eX]
      _ ≤ ∫ u, ∫ u', D (u, u') ^ 2 ∂μ ∂μ :=
          integral_mono ((bD.integral_right μ).sq.integrable μ)
            ((bD.sq.integral_right μ).integrable μ) pt
      _ = ∫ p, D p ^ 2 ∂(μ.prod μ) := (integral_prod _ (bD.sq.integrable _)).symm
      _ ≤ Δ ^ 2 := hD
  set Y := normSq b with hY
  have hXint : ∫ u, X u ∂μ = Y := by
    simp only [hX]
    rw [integral_finsetSum _ fun j _ => ((hh j).integrable μ).mul_const _]
    simp only [integral_mul_const, ← hbj, hY, normSq]
    exact Finset.sum_congr rfl fun j _ => by rw [sq]
  have eY : Y - a = ∫ u, (X u - a) ∂μ := by
    rw [integral_sub (bX.integrable μ) (integrable_const a), hXint]
    simp
  have hYsq : (Y - a) ^ 2 ≤ ∫ u, (X u - a) ^ 2 ∂μ := by
    rw [eY]
    have := bm_cauchy_schwarz μ (bX.sub (BM.const a)) (BM.const 1)
    simpa using this
  have hYa : |Y - a| ≤ Δ := abs_le_of_sq_le_sq (hYsq.trans hXa) hΔ
  have haΔ' : 0 < a - Δ := by linarith
  have hYge : a - Δ ≤ Y := by linarith [(abs_le.mp hYa).1]
  have hYle : Y ≤ a + Δ := by linarith [(abs_le.mp hYa).2]
  have hYpos : 0 < Y := lt_of_lt_of_le haΔ' hYge
  have hY0 : normSq b ≠ 0 := hYpos.ne'
  -- `E (X − Y)² ≤ Δ²`
  have hXY : ∫ u, (X u - Y) ^ 2 ∂μ ≤ Δ ^ 2 := by
    have e : (fun u => (X u - Y) ^ 2) =
        fun u => ((X u - a) ^ 2 - 2 * (Y - a) * (X u - a)) + (Y - a) ^ 2 := by
      funext u; ring
    have bXa : BM (fun u => X u - a) := bX.sub (BM.const a)
    rw [e, integral_add (f := fun u => (X u - a) ^ 2 - 2 * (Y - a) * (X u - a))
        (g := fun _ => (Y - a) ^ 2) ((bXa.sq.integrable μ).sub ((bXa.integrable μ).const_mul _))
        (integrable_const _),
      integral_sub (f := fun u => (X u - a) ^ 2) (g := fun u => 2 * (Y - a) * (X u - a))
        (bXa.sq.integrable μ) ((bXa.integrable μ).const_mul _), integral_const_mul, ← eY]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith [sq_nonneg (Y - a)]
  have elam : ∀ u, lam b (h u) = X u / Y := fun u => rfl
  have blam : BM (fun u => lam b (h u)) := by
    simp_rw [elam]
    have := bX.mul (BM.const (Y⁻¹))
    simpa [div_eq_mul_inv] using this
  -- (S3)
  have hS3 : ∫ u, Y * (lam b (h u) - 1) ^ 2 ∂μ ≤ Δ ^ 2 / (a - Δ) := by
    have pt : ∀ u, Y * (lam b (h u) - 1) ^ 2 ≤ (a - Δ)⁻¹ * (X u - Y) ^ 2 := by
      intro u
      rw [elam]
      have e : Y * (X u / Y - 1) ^ 2 = Y⁻¹ * (X u - Y) ^ 2 := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ haΔ' hYge) (sq_nonneg _)
    have bXY : BM (fun u => X u - Y) := bX.sub (BM.const Y)
    calc ∫ u, Y * (lam b (h u) - 1) ^ 2 ∂μ ≤ ∫ u, (a - Δ)⁻¹ * (X u - Y) ^ 2 ∂μ :=
          integral_mono (((BM.const Y).mul ((blam.sub (BM.const 1)).sq)).integrable μ)
            ((bXY.sq.integrable μ).const_mul _) pt
      _ = (a - Δ)⁻¹ * ∫ u, (X u - Y) ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ (a - Δ)⁻¹ * Δ ^ 2 := mul_le_mul_of_nonneg_left hXY (inv_nonneg.mpr haΔ'.le)
      _ = Δ ^ 2 / (a - Δ) := by rw [div_eq_inv_mul]
  -- the norm of `h`
  have bN : BM (fun u => normSq (h u)) := bm_sum Finset.univ fun j _ => (hh j).sq
  have hNint : ∫ u, normSq (h u) ∂μ ≤ d + δ := by
    have bNd : BM (fun u => normSq (h u) - d) := bN.sub (BM.const d)
    have h1 : (∫ u, (normSq (h u) - d) ∂μ) ^ 2 ≤ ∫ u, (normSq (h u) - d) ^ 2 ∂μ := by
      have := bm_cauchy_schwarz μ bNd (BM.const 1)
      simpa using this
    have h2 : |∫ u, (normSq (h u) - d) ∂μ| ≤ δ := abs_le_of_sq_le_sq (h1.trans hd) hδ
    rw [integral_sub (bN.integrable μ) (integrable_const d)] at h2
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h2
    linarith [(abs_le.mp h2).2]
  have hX2 : Y ^ 2 ≤ ∫ u, X u ^ 2 ∂μ := by
    have := bm_cauchy_schwarz μ bX (BM.const 1)
    rw [← hXint]
    simpa using this
  -- (S2)
  have eres : ∀ u, normSq (res b (h u)) = normSq (h u) - Y⁻¹ * X u ^ 2 := by
    intro u
    rw [normSq_res hY0, div_eq_inv_mul]
  have hS2 : ∫ u, normSq (res b (h u)) ∂μ ≤ d + δ - Y := by
    simp_rw [eres]
    rw [integral_sub (bN.integrable μ) ((bX.sq.integrable μ).const_mul _), integral_const_mul]
    have h1 : Y ≤ Y⁻¹ * ∫ u, X u ^ 2 ∂μ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hYpos]
      nlinarith
    linarith
  refine ⟨hYa, hS3, hS2, ?_⟩
  -- (S4)
  have hτ0 : 0 < d - a - Δ := by linarith
  set τ₀ := √(d - a - Δ) with hτ₀
  have hτ₀pos : 0 < τ₀ := Real.sqrt_pos.mpr hτ0
  have hdY : d - a - Δ ≤ d - Y := by linarith
  set τ' := √(d - Y) with hτ'
  have hττ : τ₀ ≤ τ' := Real.sqrt_le_sqrt hdY
  have hτ'pos : 0 < τ' := lt_of_lt_of_le hτ₀pos hττ
  have hτ'sq : τ' ^ 2 = d - Y := Real.sq_sqrt (by linarith)
  set f1 : U → ℝ := fun u => √Y * |lam b (h u) - 1| with hf1
  set f2 : U → ℝ := fun u => τ₀⁻¹ * |normSq (h u) - d| with hf2
  set f3 : U → ℝ := fun u => τ₀⁻¹ * (2 * |X u - Y|) with hf3
  have babs : ∀ {F : U → ℝ}, BM F → BM (fun u => |F u|) := by
    intro F hF
    obtain ⟨M, hM⟩ := hF.bdd
    exact ⟨hF.meas.abs, M, fun u => by rw [abs_abs]; exact hM u⟩
  have b1 : BM f1 := (BM.const _).mul (babs (blam.sub (BM.const 1)))
  have b2 : BM f2 := (BM.const _).mul (babs (bN.sub (BM.const d)))
  have b3 : BM f3 := (BM.const _).mul ((BM.const 2).mul (babs (bX.sub (BM.const Y))))
  have n1 : ∫ u, f1 u ^ 2 ∂μ ≤ (Δ / √(a - Δ)) ^ 2 := by
    have e : ∀ u, f1 u ^ 2 = Y * (lam b (h u) - 1) ^ 2 := by
      intro u
      simp only [hf1]
      rw [mul_pow, Real.sq_sqrt hYpos.le, sq_abs]
    simp_rw [e]
    rw [div_pow, Real.sq_sqrt haΔ'.le]
    exact hS3
  have n2 : ∫ u, f2 u ^ 2 ∂μ ≤ (δ / τ₀) ^ 2 := by
    have e : ∀ u, f2 u ^ 2 = (τ₀⁻¹) ^ 2 * (normSq (h u) - d) ^ 2 := by
      intro u
      simp only [hf2]
      rw [mul_pow, sq_abs]
    simp_rw [e]
    rw [integral_const_mul, div_pow, div_eq_inv_mul, inv_pow]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  have n3 : ∫ u, f3 u ^ 2 ∂μ ≤ (2 * Δ / τ₀) ^ 2 := by
    have e : ∀ u, f3 u ^ 2 = ((τ₀⁻¹) ^ 2 * 4) * (X u - Y) ^ 2 := by
      intro u
      simp only [hf3]
      rw [mul_pow, mul_pow, sq_abs]
      ring
    simp_rw [e]
    rw [integral_const_mul]
    have : (2 * Δ / τ₀) ^ 2 = ((τ₀⁻¹) ^ 2 * 4) * Δ ^ 2 := by
      rw [div_pow, div_eq_inv_mul, inv_pow]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hXY (by positivity)
  have n23 := bm_minkowski μ b2 b3 (div_nonneg hδ hτ₀pos.le)
    (div_nonneg (by positivity) hτ₀pos.le) n2 n3
  have n123 := bm_minkowski μ b1 (b2.add b3) (div_nonneg hΔ (Real.sqrt_nonneg _))
    (add_nonneg (div_nonneg hδ hτ₀pos.le) (div_nonneg (by positivity) hτ₀pos.le)) n1 n23
  have ebound : Δ / √(a - Δ) + (δ / τ₀ + 2 * Δ / τ₀) =
      Δ / √(a - Δ) + (δ + 2 * Δ) / τ₀ := by ring
  rw [ebound] at n123
  refine le_trans ?_ n123
  have pt : ∀ u, (√(normSq (res b (h u))) - τ') ^ 2 ≤ (f1 u + (f2 u + f3 u)) ^ 2 := by
    intro u
    have hf0 : 0 ≤ f1 u + (f2 u + f3 u) := by
      simp only [hf1, hf2, hf3]
      positivity
    rw [← sq_abs (√(normSq (res b (h u))) - τ')]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    -- triangle inequality
    have er : res b (h u) = (h u - b) + (1 - lam b (h u)) • b := by
      unfold res
      ext j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have er' : h u - b = res b (h u) + (lam b (h u) - 1) • b := by
      unfold res
      ext j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have nsm : ∀ c : ℝ, nrm (c • b) = √Y * |c| := by
      intro c
      unfold nrm
      rw [normSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, mul_comm]
    have t1 : nrm (res b (h u)) ≤ nrm (h u - b) + √Y * |lam b (h u) - 1| := by
      have := BstLean.Part140.nrm_add_le' (h u - b) ((1 - lam b (h u)) • b)
      rw [← er, nsm, abs_sub_comm] at this
      exact this
    have t2 : nrm (h u - b) ≤ nrm (res b (h u)) + √Y * |lam b (h u) - 1| := by
      have := BstLean.Part140.nrm_add_le' (res b (h u)) ((lam b (h u) - 1) • b)
      rw [← er', nsm] at this
      exact this
    -- the norm of `h − b` against `τ'`
    have eN : normSq (h u - b) = normSq (h u) - 2 * X u + Y := by
      simp only [normSq, Pi.sub_apply, hX, hY]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hρ := nrm_nonneg (h u - b)
    have t3 : |nrm (h u - b) - τ'| ≤ f2 u + f3 u := by
      have e1 : (nrm (h u - b) - τ') * (nrm (h u - b) + τ') =
          (normSq (h u) - d) - 2 * (X u - Y) := by
        have h2 : nrm (h u - b) ^ 2 = normSq (h u) - 2 * X u + Y := by rw [nrm_sq, eN]
        calc (nrm (h u - b) - τ') * (nrm (h u - b) + τ') = nrm (h u - b) ^ 2 - τ' ^ 2 := by ring
          _ = normSq (h u) - d - 2 * (X u - Y) := by rw [h2, hτ'sq]; ring
      have h1 : |nrm (h u - b) - τ'| * τ₀ ≤ |normSq (h u) - d| + 2 * |X u - Y| := by
        calc |nrm (h u - b) - τ'| * τ₀ ≤ |nrm (h u - b) - τ'| * (nrm (h u - b) + τ') :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ = |(nrm (h u - b) - τ') * (nrm (h u - b) + τ')| := by
              rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ nrm (h u - b) + τ')]
          _ = |(normSq (h u) - d) - 2 * (X u - Y)| := by rw [e1]
          _ ≤ |normSq (h u) - d| + |2 * (X u - Y)| := abs_sub _ _
          _ = |normSq (h u) - d| + 2 * |X u - Y| := by rw [abs_mul]; norm_num
      have h3 : f2 u + f3 u = (|normSq (h u) - d| + 2 * |X u - Y|) / τ₀ := by
        rw [hf2, hf3]; ring
      rw [h3, le_div_iff₀ hτ₀pos]
      exact h1
    have e2 : √(normSq (res b (h u))) = nrm (res b (h u)) := rfl
    rw [e2, abs_le]
    have t3' := abs_le.mp t3
    have h4 : f1 u = √Y * |lam b (h u) - 1| := by rw [hf1]
    rw [h4]
    constructor <;> linarith [t3'.1, t3'.2]
  have mres : Measurable (fun u => (√(normSq (res b (h u))) - τ') ^ 2) :=
    (((measurable_normSq.comp ((measurable_res b).comp hmeas)).sqrt).sub measurable_const).pow_const 2
  have bsum : BM (fun u => (f1 u + (f2 u + f3 u)) ^ 2) := (b1.add (b2.add b3)).sq
  have ires : Integrable (fun u => (√(normSq (res b (h u))) - τ') ^ 2) μ :=
    Integrable.mono' (bsum.integrable μ) mres.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pt u)
  exact integral_mono ires (bsum.integrable μ) pt

end BstLean.Part149

open BstLean.Part149 in
#print axioms frameA
open BstLean.Part149 in
#print axioms scalarsA
