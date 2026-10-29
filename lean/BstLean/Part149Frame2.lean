import BstLean.Part149Frame

/-!
# Part 149: the scalars and the two-point quantity of the unit residual directions (second route)

Do not use `sorry`, `native_decide` or `axiom`.

Every probability space `(U, μ)`, hidden map `h` with bounded measurable coordinates, exact centre
`b = h̄`. Hypotheses: `‖G − a‖_{L²(μ⊗μ)} ≤ Δ` (Gram kernel against a constant),
`‖|h|² − d‖₂ ≤ δ`, and a SEPARATE bound `‖X − |b|²‖₂ ≤ ΔX` of `X(u) = ⟨h(u), b⟩`.

* `scalarsB`: `scalarsA` of `Part149Frame` with `ΔX` in the place of `Δ` where the proof uses the
  fluctuation of `X`.
* `dirB`: with `e(u)` the unit residual direction (`eDir`), `σ₀ = √(d − |b|²)`:
  `σ₀²·|E_u e(u)|² ≤ E_u(|r(u)| − σ₀)²`; for `0 < s`:
  `E_{u,u'}⟨e(u), e(u')⟩² ≤ (Δ + ΔX²/(a − Δ))²/s² + 2·μ{|r|² < s}`;
  `μ{e = 0} ≤ μ{|r|² < s}`; `(σ₀ − √s)²·μ{|r|² < s} ≤ E_u(|r(u)| − σ₀)²`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM bm_cauchy_schwarz)
open BstLean.Part130 BstLean.Part134
open BstLean.Part132 (nrm nrm_nonneg nrm_sq)
open BstLean.Part136 (hbar det_frame bm_fst bm_snd normSq_res)

variable {m : ℕ} {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]

/-- **The scalars of the stand-in for the exact centre, with a separate bound `ΔX` of the
fluctuation of `X(u) = ⟨h(u), h̄⟩`.** -/
theorem scalarsB {h : U → Fin m → ℝ} (hh : ∀ j, BM (fun u => h u j))
    {a Δ d δ ΔX : ℝ} (hΔ : 0 ≤ Δ) (hδ : 0 ≤ δ) (hΔX : 0 ≤ ΔX) (haΔ : Δ < a) (hda : a + Δ < d)
    (hD : ∫ p, (∑ k, h p.1 k * h p.2 k - a) ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂μ ≤ δ ^ 2)
    (hXv : ∫ u, (∑ j, h u j * hbar μ h j - normSq (hbar μ h)) ^ 2 ∂μ ≤ ΔX ^ 2) :
    |normSq (hbar μ h) - a| ≤ Δ ∧
    ∫ u, normSq (hbar μ h) * (lam (hbar μ h) (h u) - 1) ^ 2 ∂μ ≤ ΔX ^ 2 / (a - Δ) ∧
    ∫ u, normSq (res (hbar μ h) (h u)) ∂μ ≤ d + δ - normSq (hbar μ h) ∧
    ∫ u, (√(normSq (res (hbar μ h) (h u))) - √(d - normSq (hbar μ h))) ^ 2 ∂μ ≤
      (ΔX / √(a - Δ) + (δ + 2 * ΔX) / √(d - a - Δ)) ^ 2 := by
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
  have hXY : ∫ u, (X u - Y) ^ 2 ∂μ ≤ ΔX ^ 2 := hXv
  have elam : ∀ u, lam b (h u) = X u / Y := fun u => rfl
  have blam : BM (fun u => lam b (h u)) := by
    simp_rw [elam]
    have := bX.mul (BM.const (Y⁻¹))
    simpa [div_eq_mul_inv] using this
  -- (S3)
  have hS3 : ∫ u, Y * (lam b (h u) - 1) ^ 2 ∂μ ≤ ΔX ^ 2 / (a - Δ) := by
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
      _ ≤ (a - Δ)⁻¹ * ΔX ^ 2 := mul_le_mul_of_nonneg_left hXY (inv_nonneg.mpr haΔ'.le)
      _ = ΔX ^ 2 / (a - Δ) := by rw [div_eq_inv_mul]
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
  have n1 : ∫ u, f1 u ^ 2 ∂μ ≤ (ΔX / √(a - Δ)) ^ 2 := by
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
  have n3 : ∫ u, f3 u ^ 2 ∂μ ≤ (2 * ΔX / τ₀) ^ 2 := by
    have e : ∀ u, f3 u ^ 2 = ((τ₀⁻¹) ^ 2 * 4) * (X u - Y) ^ 2 := by
      intro u
      simp only [hf3]
      rw [mul_pow, mul_pow, sq_abs]
      ring
    simp_rw [e]
    rw [integral_const_mul]
    have : (2 * ΔX / τ₀) ^ 2 = ((τ₀⁻¹) ^ 2 * 4) * ΔX ^ 2 := by
      rw [div_pow, div_eq_inv_mul, inv_pow]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hXY (by positivity)
  have n23 := bm_minkowski μ b2 b3 (div_nonneg hδ hτ₀pos.le)
    (div_nonneg (by positivity) hτ₀pos.le) n2 n3
  have n123 := bm_minkowski μ b1 (b2.add b3) (div_nonneg hΔX (Real.sqrt_nonneg _))
    (add_nonneg (div_nonneg hδ hτ₀pos.le) (div_nonneg (by positivity) hτ₀pos.le)) n1 n23
  have ebound : ΔX / √(a - Δ) + (δ / τ₀ + 2 * ΔX / τ₀) =
      ΔX / √(a - Δ) + (δ + 2 * ΔX) / τ₀ := by ring
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


/-- **The unit residual directions for the exact centre: their mean and the set where the
residual is small.** -/
theorem dirB {h : U → Fin m → ℝ} (hh : ∀ j, BM (fun u => h u j))
    {a Δ d δ ΔX : ℝ} (hΔ : 0 ≤ Δ) (hδ : 0 ≤ δ) (hΔX : 0 ≤ ΔX) (haΔ : Δ < a) (hda : a + Δ < d)
    (hD : ∫ p, (∑ k, h p.1 k * h p.2 k - a) ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂μ ≤ δ ^ 2)
    (hXv : ∫ u, (∑ j, h u j * hbar μ h j - normSq (hbar μ h)) ^ 2 ∂μ ≤ ΔX ^ 2)
    {s : ℝ} (hs : 0 < s) (hs' : s < d - a - Δ) :
    (d - normSq (hbar μ h)) * ∑ j, (∫ u, eDir (hbar μ h) (h u) j ∂μ) ^ 2 ≤
      ∫ u, (√(normSq (res (hbar μ h) (h u))) - √(d - normSq (hbar μ h))) ^ 2 ∂μ ∧
    μ.real {u | eDir (hbar μ h) (h u) = 0} ≤
      μ.real {u | normSq (res (hbar μ h) (h u)) < s} ∧
    (√(d - a - Δ) - √s) ^ 2 * μ.real {u | normSq (res (hbar μ h) (h u)) < s} ≤
      ∫ u, (√(normSq (res (hbar μ h) (h u))) - √(d - normSq (hbar μ h))) ^ 2 ∂μ := by
  obtain ⟨hYa, -, -, -⟩ := scalarsB μ hh hΔ hδ hΔX haΔ hda hD hd hXv
  set b := hbar μ h with hb
  have hbj : ∀ j, b j = ∫ u, h u j ∂μ := fun j => rfl
  have hmeas : Measurable h := measurable_pi_iff.mpr fun j => (hh j).meas
  set X : U → ℝ := fun u => ∑ j, h u j * b j with hX
  have bX : BM X := bm_sum Finset.univ fun j _ => (hh j).mul (BM.const _)
  set Y := normSq b with hY
  have hXint : ∫ u, X u ∂μ = Y := by
    simp only [hX]
    rw [integral_finsetSum _ fun j _ => ((hh j).integrable μ).mul_const _]
    simp only [integral_mul_const, ← hbj, hY, normSq]
    exact Finset.sum_congr rfl fun j _ => by rw [sq]
  have haΔ' : 0 < a - Δ := by linarith
  have hYge : a - Δ ≤ Y := by linarith [(abs_le.mp hYa).1]
  have hYle : Y ≤ a + Δ := by linarith [(abs_le.mp hYa).2]
  have hYpos : 0 < Y := lt_of_lt_of_le haΔ' hYge
  have hY0 : normSq b ≠ 0 := hYpos.ne'
  have hτ0 : 0 < d - a - Δ := by linarith
  have hdY : d - a - Δ ≤ d - Y := by linarith
  set σ₀ := √(d - Y) with hσ₀
  have hσsq : σ₀ ^ 2 = d - Y := Real.sq_sqrt (by linarith)
  have hτσ : √(d - a - Δ) ≤ σ₀ := Real.sqrt_le_sqrt hdY
  have hsτ : √s < √(d - a - Δ) := Real.sqrt_lt_sqrt hs.le hs'
  have elam : ∀ u, lam b (h u) = X u / Y := fun u => rfl
  have blam : BM (fun u => lam b (h u)) := by
    simp_rw [elam]
    have := bX.mul (BM.const (Y⁻¹))
    simpa [div_eq_mul_inv] using this
  -- the residual and its direction
  have bres : ∀ j, BM (fun u => res b (h u) j) := by
    intro j
    have : (fun u => res b (h u) j) = fun u => h u j - lam b (h u) * b j := by
      funext u; simp [res]
    rw [this]
    exact (hh j).sub (blam.mul (BM.const _))
  have mN : Measurable (fun u => √(normSq (res b (h u)))) :=
    (measurable_normSq.comp ((measurable_res b).comp hmeas)).sqrt
  have bN : BM (fun u => normSq (res b (h u))) := bm_sum Finset.univ fun j _ => (bres j).sq
  have bNs : BM (fun u => √(normSq (res b (h u)))) := by
    obtain ⟨C, hC⟩ := bN.bdd
    refine ⟨mN, 1 + C, fun u => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : normSq (res b (h u)) ≤ C := (le_abs_self _).trans (hC u)
    have h2 : √(normSq (res b (h u))) ≤ 1 + normSq (res b (h u)) := by
      have h3 := Real.sq_sqrt (normSq_nonneg (res b (h u)))
      nlinarith [sq_nonneg (√(normSq (res b (h u))) - 1), Real.sqrt_nonneg (normSq (res b (h u)))]
    linarith
  have ee : ∀ u, res b (h u) = √(normSq (res b (h u))) • eDir b (h u) :=
    fun u => res_eq_smul_eDir b (h u)
  have ebd : ∀ u, normSq (eDir b (h u)) ≤ 1 := by
    intro u
    rcases eDir_unit_or_zero b (h u) with h1 | h1
    · exact h1.le
    · rw [h1]; simp [normSq]
  have be : ∀ j, BM (fun u => eDir b (h u) j) := by
    intro j
    refine ⟨(measurable_pi_apply j).comp ((measurable_eDir b).comp hmeas), 1, fun u => ?_⟩
    have h1 : eDir b (h u) j ^ 2 ≤ normSq (eDir b (h u)) :=
      Finset.single_le_sum (f := fun i => eDir b (h u) i ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2 := ebd u
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
  have hres0 : ∀ j, ∫ u, res b (h u) j ∂μ = 0 := by
    intro j
    have e1 : (fun u => res b (h u) j) = fun u => h u j - Y⁻¹ * b j * X u := by
      funext u
      simp only [res, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, elam]
      ring
    rw [e1, integral_sub ((hh j).integrable μ) ((bX.integrable μ).const_mul _), integral_const_mul,
      hXint, ← hbj]
    field_simp
    ring
  set φ : U → ℝ := fun u => σ₀ - √(normSq (res b (h u))) with hφ
  have bφ : BM φ := (BM.const σ₀).sub bNs
  set V : ℝ := ∫ u, (√(normSq (res b (h u))) - σ₀) ^ 2 ∂μ with hV
  have hVφ : ∫ u, φ u ^ 2 ∂μ = V := by
    rw [hV]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hφ]
    ring
  -- (P1)
  have hP1 : (d - Y) * ∑ j, (∫ u, eDir b (h u) j ∂μ) ^ 2 ≤ V := by
    set v : Fin m → ℝ := fun j => ∫ u, φ u * eDir b (h u) j ∂μ with hv
    have ev : ∀ j, v j = σ₀ * ∫ u, eDir b (h u) j ∂μ := by
      intro j
      have e1 : (fun u => φ u * eDir b (h u) j) =
          fun u => σ₀ * eDir b (h u) j - res b (h u) j := by
        funext u
        have := congrFun (ee u) j
        simp only [Pi.smul_apply, smul_eq_mul] at this
        simp only [hφ]
        rw [this]
        ring
      simp only [hv]
      rw [e1, integral_sub (((be j).integrable μ).const_mul _) ((bres j).integrable μ),
        integral_const_mul, hres0 j, sub_zero]
    set N : ℝ := ∑ j, v j ^ 2 with hN
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun j _ => sq_nonneg _
    set w : U → ℝ := fun u => ∑ j, v j * eDir b (h u) j with hw
    have bw : BM w := bm_sum Finset.univ fun j _ => (BM.const _).mul (be j)
    have eN : N = ∫ u, φ u * w u ∂μ := by
      have e1 : (fun u => φ u * w u) = fun u => ∑ j, v j * (φ u * eDir b (h u) j) := by
        funext u
        simp only [hw]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1, integral_finsetSum _ fun j _ => ((bφ.mul (be j)).integrable μ).const_mul _]
      simp only [integral_const_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [sq]
    have hw2 : ∀ u, w u ^ 2 ≤ N := by
      intro u
      have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (eDir b (h u))
      have h1 := ebd u
      have h2 : (∑ j, v j * eDir b (h u) j) ^ 2 ≤ N * normSq (eDir b (h u)) := cs
      simp only [hw]
      nlinarith [normSq_nonneg (eDir b (h u))]
    have hw2i : ∫ u, w u ^ 2 ∂μ ≤ N := by
      calc ∫ u, w u ^ 2 ∂μ ≤ ∫ _u, N ∂μ := integral_mono (bw.sq.integrable μ) (integrable_const _) hw2
        _ = N := by simp
    have cs := bm_cauchy_schwarz μ bφ bw
    rw [← eN, hVφ] at cs
    have hNV : N ≤ V := by
      have hV0 : 0 ≤ V := by rw [← hVφ]; exact integral_nonneg fun _ => sq_nonneg _
      by_cases hz : N = 0
      · rw [hz]; exact hV0
      · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hz)
        have h1 : N ^ 2 ≤ V * N := cs.trans (mul_le_mul_of_nonneg_left hw2i hV0)
        nlinarith
    have e2 : N = (d - Y) * ∑ j, (∫ u, eDir b (h u) j ∂μ) ^ 2 := by
      simp only [hN]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev, mul_pow, hσsq]
    rw [← e2]
    exact hNV
  -- the small-residual set
  set B : Set U := {u | normSq (res b (h u)) < s} with hB
  have mB : MeasurableSet B :=
    measurableSet_lt (measurable_normSq.comp ((measurable_res b).comp hmeas)) measurable_const
  -- (P4)
  have hP4 : (√(d - a - Δ) - √s) ^ 2 * μ.real B ≤ V := by
    have pt : ∀ u, B.indicator (fun _ => (√(d - a - Δ) - √s) ^ 2) u ≤
        (√(normSq (res b (h u))) - σ₀) ^ 2 := by
      intro u
      by_cases hu : u ∈ B
      · rw [Set.indicator_of_mem hu]
        have h1 : √(normSq (res b (h u))) < √s := Real.sqrt_lt_sqrt (normSq_nonneg _) hu
        have h2 : 0 ≤ √(d - a - Δ) - √s := by linarith
        have h3 : √(d - a - Δ) - √s ≤ σ₀ - √(normSq (res b (h u))) := by linarith
        nlinarith
      · rw [Set.indicator_of_notMem hu]
        positivity
    have hi : Integrable (B.indicator fun _ : U => (√(d - a - Δ) - √s) ^ 2) μ :=
      (integrable_const _).indicator mB
    have := integral_mono hi ((bNs.sub (BM.const σ₀)).sq.integrable μ) pt
    rw [integral_indicator_const _ mB, smul_eq_mul] at this
    rw [mul_comm]
    exact this
  -- (P3)
  have hP3 : μ.real {u | eDir b (h u) = 0} ≤ μ.real B := by
    refine measureReal_mono (fun u hu => ?_) (measure_ne_top _ _)
    have hu' : eDir b (h u) = 0 := hu
    have h1 := ee u
    rw [hu', smul_zero] at h1
    show normSq (res b (h u)) < s
    rw [h1]
    simpa [normSq] using hs
  exact ⟨hP1, hP3, hP4⟩

/-- **The two-point quantity of the unit residual directions for the exact centre.** -/
theorem dirB2 {h : U → Fin m → ℝ} (hh : ∀ j, BM (fun u => h u j))
    {a Δ d δ ΔX : ℝ} (hΔ : 0 ≤ Δ) (hδ : 0 ≤ δ) (hΔX : 0 ≤ ΔX) (haΔ : Δ < a) (hda : a + Δ < d)
    (hD : ∫ p, (∑ k, h p.1 k * h p.2 k - a) ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂μ ≤ δ ^ 2)
    (hXv : ∫ u, (∑ j, h u j * hbar μ h j - normSq (hbar μ h)) ^ 2 ∂μ ≤ ΔX ^ 2)
    {s : ℝ} (hs : 0 < s) (hs' : s < d - a - Δ) :
    ∫ p, (∑ j, eDir (hbar μ h) (h p.1) j * eDir (hbar μ h) (h p.2) j) ^ 2 ∂(μ.prod μ) ≤
      (Δ + ΔX ^ 2 / (a - Δ)) ^ 2 / s ^ 2 +
        2 * μ.real {u | normSq (res (hbar μ h) (h u)) < s} := by
  obtain ⟨hYa, -, -, -⟩ := scalarsB μ hh hΔ hδ hΔX haΔ hda hD hd hXv
  set b := hbar μ h with hb
  have hbj : ∀ j, b j = ∫ u, h u j ∂μ := fun j => rfl
  have hmeas : Measurable h := measurable_pi_iff.mpr fun j => (hh j).meas
  set X : U → ℝ := fun u => ∑ j, h u j * b j with hX
  have bX : BM X := bm_sum Finset.univ fun j _ => (hh j).mul (BM.const _)
  set Y := normSq b with hY
  have hXint : ∫ u, X u ∂μ = Y := by
    simp only [hX]
    rw [integral_finsetSum _ fun j _ => ((hh j).integrable μ).mul_const _]
    simp only [integral_mul_const, ← hbj, hY, normSq]
    exact Finset.sum_congr rfl fun j _ => by rw [sq]
  have haΔ' : 0 < a - Δ := by linarith
  have hYge : a - Δ ≤ Y := by linarith [(abs_le.mp hYa).1]
  have hYle : Y ≤ a + Δ := by linarith [(abs_le.mp hYa).2]
  have hYpos : 0 < Y := lt_of_lt_of_le haΔ' hYge
  have hY0 : normSq b ≠ 0 := hYpos.ne'
  have hτ0 : 0 < d - a - Δ := by linarith
  have hdY : d - a - Δ ≤ d - Y := by linarith
  set σ₀ := √(d - Y) with hσ₀
  have hσsq : σ₀ ^ 2 = d - Y := Real.sq_sqrt (by linarith)
  have hτσ : √(d - a - Δ) ≤ σ₀ := Real.sqrt_le_sqrt hdY
  have hsτ : √s < √(d - a - Δ) := Real.sqrt_lt_sqrt hs.le hs'
  have elam : ∀ u, lam b (h u) = X u / Y := fun u => rfl
  have blam : BM (fun u => lam b (h u)) := by
    simp_rw [elam]
    have := bX.mul (BM.const (Y⁻¹))
    simpa [div_eq_mul_inv] using this
  -- the residual and its direction
  have bres : ∀ j, BM (fun u => res b (h u) j) := by
    intro j
    have : (fun u => res b (h u) j) = fun u => h u j - lam b (h u) * b j := by
      funext u; simp [res]
    rw [this]
    exact (hh j).sub (blam.mul (BM.const _))
  have mN : Measurable (fun u => √(normSq (res b (h u)))) :=
    (measurable_normSq.comp ((measurable_res b).comp hmeas)).sqrt
  have bN : BM (fun u => normSq (res b (h u))) := bm_sum Finset.univ fun j _ => (bres j).sq
  have bNs : BM (fun u => √(normSq (res b (h u)))) := by
    obtain ⟨C, hC⟩ := bN.bdd
    refine ⟨mN, 1 + C, fun u => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : normSq (res b (h u)) ≤ C := (le_abs_self _).trans (hC u)
    have h2 : √(normSq (res b (h u))) ≤ 1 + normSq (res b (h u)) := by
      have h3 := Real.sq_sqrt (normSq_nonneg (res b (h u)))
      nlinarith [sq_nonneg (√(normSq (res b (h u))) - 1), Real.sqrt_nonneg (normSq (res b (h u)))]
    linarith
  have ee : ∀ u, res b (h u) = √(normSq (res b (h u))) • eDir b (h u) :=
    fun u => res_eq_smul_eDir b (h u)
  have ebd : ∀ u, normSq (eDir b (h u)) ≤ 1 := by
    intro u
    rcases eDir_unit_or_zero b (h u) with h1 | h1
    · exact h1.le
    · rw [h1]; simp [normSq]
  have be : ∀ j, BM (fun u => eDir b (h u) j) := by
    intro j
    refine ⟨(measurable_pi_apply j).comp ((measurable_eDir b).comp hmeas), 1, fun u => ?_⟩
    have h1 : eDir b (h u) j ^ 2 ≤ normSq (eDir b (h u)) :=
      Finset.single_le_sum (f := fun i => eDir b (h u) i ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2 := ebd u
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
  have hres0 : ∀ j, ∫ u, res b (h u) j ∂μ = 0 := by
    intro j
    have e1 : (fun u => res b (h u) j) = fun u => h u j - Y⁻¹ * b j * X u := by
      funext u
      simp only [res, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, elam]
      ring
    rw [e1, integral_sub ((hh j).integrable μ) ((bX.integrable μ).const_mul _), integral_const_mul,
      hXint, ← hbj]
    field_simp
    ring
  set B : Set U := {u | normSq (res b (h u)) < s} with hB
  have mB : MeasurableSet B :=
    measurableSet_lt (measurable_normSq.comp ((measurable_res b).comp hmeas)) measurable_const
  -- (P2)
  set Rk : U × U → ℝ := fun p => ∑ j, res b (h p.1) j * res b (h p.2) j with hRk
  have bRk : BM Rk := bm_sum Finset.univ fun j _ => (bm_fst (bres j)).mul (bm_snd (bres j))
  set Gk : U × U → ℝ := fun p => ∑ k, h p.1 k * h p.2 k with hGk
  have bG : BM Gk := bm_sum Finset.univ fun k _ => (bm_fst (hh k)).mul (bm_snd (hh k))
  set Dc : U × U → ℝ := fun p => Gk p - X p.1 - X p.2 + Y with hDc
  have bDc : BM Dc := ((bG.sub (bm_fst bX)).sub (bm_snd bX)).add (BM.const Y)
  set E2 : U × U → ℝ := fun p => Y⁻¹ * ((X p.1 - Y) * (X p.2 - Y)) with hE2
  have bXY : BM (fun u => X u - Y) := bX.sub (BM.const Y)
  have bE2 : BM E2 := (BM.const _).mul ((bm_fst bXY).mul (bm_snd bXY))
  have eRk : ∀ p, Rk p = Dc p + (-E2 p) := by
    intro p
    simp only [hRk, hDc, hE2, hGk, res, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, elam]
    have e1 : ∑ j, (h p.1 j - X p.1 / Y * b j) * (h p.2 j - X p.2 / Y * b j) =
        ∑ j, h p.1 j * h p.2 j - X p.2 / Y * ∑ j, h p.1 j * b j -
          X p.1 / Y * ∑ j, h p.2 j * b j + X p.1 / Y * (X p.2 / Y) * ∑ j, b j ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1]
    have e2 : ∑ j, b j ^ 2 = Y := rfl
    rw [e2]
    show ∑ j, h p.1 j * h p.2 j - X p.2 / Y * X p.1 - X p.1 / Y * X p.2 +
      X p.1 / Y * (X p.2 / Y) * Y = _
    field_simp
    ring
  -- `‖Dc‖ ≤ ‖G − a‖`
  have iDc1 : ∀ u, ∫ u', Dc (u, u') ∂μ = 0 := by
    intro u
    have i1 : Integrable (fun u' => ∑ k, h u k * h u' k) μ :=
      integrable_finsetSum _ fun k _ => ((hh k).integrable μ).const_mul _
    have v1 : ∫ u', ∑ k, h u k * h u' k ∂μ = X u := by
      rw [integral_finsetSum _ fun k _ => ((hh k).integrable μ).const_mul _]
      simp only [integral_const_mul, hX, hbj]
    have e0 : (fun u' => Dc (u, u')) =
        fun u' => ((∑ k, h u k * h u' k) + (Y - X u)) - X u' := by
      funext u'; simp only [hDc, hGk]; ring
    rw [e0, integral_sub (f := fun u' => (∑ k, h u k * h u' k) + (Y - X u)) (g := X)
        (i1.add (integrable_const _)) (bX.integrable μ),
      integral_add (f := fun u' => ∑ k, h u k * h u' k) (g := fun _ => Y - X u) i1
        (integrable_const _), v1, hXint]
    simp
  have iDc2 : ∀ u', ∫ u, Dc (u, u') ∂μ = 0 := by
    intro u'
    have i1 : Integrable (fun u => ∑ k, h u k * h u' k) μ :=
      integrable_finsetSum _ fun k _ => ((hh k).integrable μ).mul_const _
    have v1 : ∫ u, ∑ k, h u k * h u' k ∂μ = X u' := by
      rw [integral_finsetSum _ fun k _ => ((hh k).integrable μ).mul_const _]
      simp only [integral_mul_const, hX, hbj]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e0 : (fun u => Dc (u, u')) =
        fun u => ((∑ k, h u k * h u' k) + (Y - X u')) - X u := by
      funext u; simp only [hDc, hGk]; ring
    rw [e0, integral_sub (f := fun u => (∑ k, h u k * h u' k) + (Y - X u')) (g := X)
        (i1.add (integrable_const _)) (bX.integrable μ),
      integral_add (f := fun u => ∑ k, h u k * h u' k) (g := fun _ => Y - X u') i1
        (integrable_const _), v1, hXint]
    simp
  set ψ : U × U → ℝ := fun p => (X p.1 - Y) + (X p.2 - Y) + (Y - a) with hψ
  have bψ : BM ψ := ((bm_fst bXY).add (bm_snd bXY)).add (BM.const _)
  have hcross : ∫ p, Dc p * ψ p ∂(μ.prod μ) = 0 := by
    have e1 : (fun p : U × U => Dc p * ψ p) = fun p =>
        (Dc p * (X p.1 - Y) + Dc p * (X p.2 - Y)) + (Y - a) * Dc p := by
      funext p; simp only [hψ]; ring
    have b1 : BM (fun p : U × U => Dc p * (X p.1 - Y)) := bDc.mul (bm_fst bXY)
    have b2 : BM (fun p : U × U => Dc p * (X p.2 - Y)) := bDc.mul (bm_snd bXY)
    have z1 : ∫ p, Dc p * (X p.1 - Y) ∂(μ.prod μ) = 0 := by
      rw [integral_prod _ (b1.integrable _)]
      have : ∀ u, ∫ u', Dc (u, u') * (X u - Y) ∂μ = 0 := fun u => by
        rw [integral_mul_const, iDc1 u, zero_mul]
      simp only [this, integral_zero]
    have z2 : ∫ p, Dc p * (X p.2 - Y) ∂(μ.prod μ) = 0 := by
      rw [integral_prod_symm _ (b2.integrable _)]
      have : ∀ u', ∫ u, Dc (u, u') * (X u' - Y) ∂μ = 0 := fun u' => by
        rw [integral_mul_const, iDc2 u', zero_mul]
      simp only [this, integral_zero]
    have z3 : ∫ p, Dc p ∂(μ.prod μ) = 0 := by
      rw [integral_prod _ (bDc.integrable _)]
      simp only [iDc1, integral_zero]
    rw [e1, integral_add ((b1.add b2).integrable _) ((bDc.integrable _).const_mul _),
      integral_add (b1.integrable _) (b2.integrable _), integral_const_mul, z1, z2, z3]
    simp
  have hDcle : ∫ p, Dc p ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2 := by
    have e1 : (fun p : U × U => (Gk p - a) ^ 2) = fun p =>
        (Dc p ^ 2 + 2 * (Dc p * ψ p)) + ψ p ^ 2 := by
      funext p; simp only [hDc, hψ]; ring
    have h1 : ∫ p, (Gk p - a) ^ 2 ∂(μ.prod μ) = ∫ p, Dc p ^ 2 ∂(μ.prod μ) +
        ∫ p, ψ p ^ 2 ∂(μ.prod μ) := by
      rw [e1, integral_add (f := fun p : U × U => Dc p ^ 2 + 2 * (Dc p * ψ p))
        (g := fun p => ψ p ^ 2)
        ((bDc.sq.integrable _).add (((bDc.mul bψ).integrable _).const_mul _))
        (bψ.sq.integrable _), integral_add (f := fun p : U × U => Dc p ^ 2)
        (g := fun p => 2 * (Dc p * ψ p)) (bDc.sq.integrable _)
        (((bDc.mul bψ).integrable _).const_mul _), integral_const_mul, hcross]
      simp
    have h2 : 0 ≤ ∫ p, ψ p ^ 2 ∂(μ.prod μ) := integral_nonneg fun _ => sq_nonneg _
    have h3 : ∫ p, (Gk p - a) ^ 2 ∂(μ.prod μ) ≤ Δ ^ 2 := hD
    linarith
  have hE2le : ∫ p, (-E2 p) ^ 2 ∂(μ.prod μ) ≤ (ΔX ^ 2 / (a - Δ)) ^ 2 := by
    have e1 : (fun p : U × U => (-E2 p) ^ 2) = fun p =>
        (Y⁻¹) ^ 2 * ((X p.1 - Y) ^ 2 * (X p.2 - Y) ^ 2) := by
      funext p; simp only [hE2]; ring
    rw [e1, integral_const_mul, integral_prod_mul (fun u => (X u - Y) ^ 2)
      (fun u => (X u - Y) ^ 2)]
    have h0 : 0 ≤ ∫ u, (X u - Y) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have h1 : (∫ u, (X u - Y) ^ 2 ∂μ) * ∫ u, (X u - Y) ^ 2 ∂μ ≤ ΔX ^ 2 * ΔX ^ 2 :=
      mul_le_mul hXv hXv h0 (sq_nonneg _)
    have h2 : (Y⁻¹) ^ 2 ≤ ((a - Δ)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hYpos.le) (inv_anti₀ haΔ' hYge) 2
    calc (Y⁻¹) ^ 2 * ((∫ u, (X u - Y) ^ 2 ∂μ) * ∫ u, (X u - Y) ^ 2 ∂μ)
        ≤ ((a - Δ)⁻¹) ^ 2 * (ΔX ^ 2 * ΔX ^ 2) :=
          mul_le_mul h2 h1 (mul_nonneg h0 h0) (sq_nonneg _)
      _ = (ΔX ^ 2 / (a - Δ)) ^ 2 := by rw [div_eq_mul_inv]; ring
  have hRle : ∫ p, Rk p ^ 2 ∂(μ.prod μ) ≤ (Δ + ΔX ^ 2 / (a - Δ)) ^ 2 := by
    simp_rw [eRk]
    exact bm_minkowski (μ.prod μ) bDc bE2.neg hΔ (by positivity) hDcle hE2le
  -- the pointwise bound of `ρ²`
  have pt : ∀ p : U × U, (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ≤
      (s⁻¹) ^ 2 * Rk p ^ 2 + (B.indicator (fun _ => (1 : ℝ)) p.1 +
        B.indicator (fun _ => (1 : ℝ)) p.2) := by
    intro p
    have hρ1 : (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ≤ 1 := by
      have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (eDir b (h p.1)) (eDir b (h p.2))
      have h1 := ebd p.1
      have h2 := ebd p.2
      have h3 : (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ≤
          normSq (eDir b (h p.1)) * normSq (eDir b (h p.2)) := cs
      nlinarith [normSq_nonneg (eDir b (h p.1)), normSq_nonneg (eDir b (h p.2))]
    have hR0 : 0 ≤ (s⁻¹) ^ 2 * Rk p ^ 2 := by positivity
    by_cases h1 : p.1 ∈ B
    · rw [Set.indicator_of_mem h1]
      have : 0 ≤ B.indicator (fun _ => (1 : ℝ)) p.2 := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      linarith
    by_cases h2 : p.2 ∈ B
    · rw [Set.indicator_of_mem h2]
      have : 0 ≤ B.indicator (fun _ => (1 : ℝ)) p.1 := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      linarith
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero, add_zero]
    have g1 : s ≤ normSq (res b (h p.1)) := not_lt.mp h1
    have g2 : s ≤ normSq (res b (h p.2)) := not_lt.mp h2
    set n1 := √(normSq (res b (h p.1))) with hn1
    set n2 := √(normSq (res b (h p.2))) with hn2
    have hn1sq : n1 ^ 2 = normSq (res b (h p.1)) := Real.sq_sqrt (normSq_nonneg _)
    have hn2sq : n2 ^ 2 = normSq (res b (h p.2)) := Real.sq_sqrt (normSq_nonneg _)
    have eR : Rk p = n1 * n2 * ∑ j, eDir b (h p.1) j * eDir b (h p.2) j := by
      simp only [hRk]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have a1 := congrFun (ee p.1) j
      have a2 := congrFun (ee p.2) j
      simp only [Pi.smul_apply, smul_eq_mul] at a1 a2
      rw [a1, a2]
      ring
    have h3 : s ^ 2 ≤ (n1 * n2) ^ 2 := by
      rw [mul_pow, hn1sq, hn2sq, sq]
      exact mul_le_mul g1 g2 hs.le (hs.le.trans g1)
    have h4 : 1 ≤ (s ^ 2)⁻¹ * (n1 * n2) ^ 2 := by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    have e5 : (s⁻¹) ^ 2 * Rk p ^ 2 = ((s ^ 2)⁻¹ * (n1 * n2) ^ 2) *
        (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 := by
      rw [eR, inv_pow]; ring
    rw [e5]
    calc (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2
        = 1 * (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  have bρ : BM (fun p : U × U => (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2) :=
    (bm_sum Finset.univ fun j _ => (bm_fst (be j)).mul (bm_snd (be j))).sq
  have iB1 : Integrable (fun p : U × U => B.indicator (fun _ => (1 : ℝ)) p.1) (μ.prod μ) :=
    ((integrable_const (1 : ℝ)).indicator mB).comp_fst μ
  have iB2 : Integrable (fun p : U × U => B.indicator (fun _ => (1 : ℝ)) p.2) (μ.prod μ) :=
    ((integrable_const (1 : ℝ)).indicator mB).comp_snd μ
  have eB : ∫ u, B.indicator (fun _ => (1 : ℝ)) u ∂μ = μ.real B := by
    rw [integral_indicator_const _ mB, smul_eq_mul, mul_one]
  have eB1 : ∫ p : U × U, B.indicator (fun _ => (1 : ℝ)) p.1 ∂(μ.prod μ) = μ.real B := by
    rw [integral_prod _ iB1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact eB
  have eB2 : ∫ p : U × U, B.indicator (fun _ => (1 : ℝ)) p.2 ∂(μ.prod μ) = μ.real B := by
    rw [integral_prod _ iB2]
    simp only [eB, integral_const, probReal_univ, smul_eq_mul, one_mul]
  calc ∫ p, (∑ j, eDir b (h p.1) j * eDir b (h p.2) j) ^ 2 ∂(μ.prod μ)
      ≤ ∫ p, ((s⁻¹) ^ 2 * Rk p ^ 2 + (B.indicator (fun _ => (1 : ℝ)) p.1 +
          B.indicator (fun _ => (1 : ℝ)) p.2)) ∂(μ.prod μ) :=
        integral_mono (bρ.integrable _)
          (((bRk.sq.integrable _).const_mul _).add (iB1.add iB2)) pt
    _ = (s⁻¹) ^ 2 * ∫ p, Rk p ^ 2 ∂(μ.prod μ) + (μ.real B + μ.real B) := by
        rw [integral_add (f := fun p : U × U => (s⁻¹) ^ 2 * Rk p ^ 2)
          (g := fun p => B.indicator (fun _ => (1 : ℝ)) p.1 + B.indicator (fun _ => (1 : ℝ)) p.2)
          ((bRk.sq.integrable _).const_mul _) (iB1.add iB2),
          integral_add (f := fun p : U × U => B.indicator (fun _ => (1 : ℝ)) p.1)
          (g := fun p => B.indicator (fun _ => (1 : ℝ)) p.2) iB1 iB2, integral_const_mul, eB1, eB2]
    _ ≤ (Δ + ΔX ^ 2 / (a - Δ)) ^ 2 / s ^ 2 + 2 * μ.real B := by
        have := mul_le_mul_of_nonneg_left hRle (sq_nonneg (s⁻¹))
        have e3 : (s⁻¹) ^ 2 * (Δ + ΔX ^ 2 / (a - Δ)) ^ 2 =
            (Δ + ΔX ^ 2 / (a - Δ)) ^ 2 / s ^ 2 := by
          rw [inv_pow]; ring
        linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms scalarsB
open BstLean.Part149 in
#print axioms dirB
open BstLean.Part149 in
#print axioms dirB2
