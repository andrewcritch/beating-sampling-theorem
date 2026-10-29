import BstLean.Part182Schur

/-! Part 208: the Schur reduction accepts an integrated good-pair bound. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part182
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_dot_le_nrm)
variable {X : Type*} [MeasurableSpace X] {m k : ℕ}

/-- The good contribution is bounded after integration. The exceptional contribution
retains the same fourth-moment term as the pointwise-kernel Schur estimate. -/
theorem schur_integrated (μ : Measure X) [IsProbabilityMeasure μ]
    (B : X → Matrix (Fin m) (Fin k) ℝ) (hB : ∀ i j, Measurable (fun ξ => B ξ i j))
    (β : X → ℝ) (hβm : Measurable β) (hβ : ∀ ξ, opN (B ξ) ≤ β ξ) {CB : ℝ}
    (hCB : ∀ ξ, β ξ ≤ CB)
    (w : X → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ) (hwi : Integrable w μ)
    (hw2 : Integrable (fun ξ => w ξ ^ 2) μ) (S : Set X) (hS : MeasurableSet S)
    (hwS : ∀ ξ, ξ ∉ S → w ξ = 0)
    (G : Set (X × X)) (hG : MeasurableSet G) {R : ℝ} (hR0 : 0 ≤ R)
    (hgood : ∀ v : Fin m → ℝ,
      (∫ p in G, w p.1 * w p.2 *
        ((B p.1 *ᵥ vecMul v (B p.1)) ⬝ᵥ (B p.2 *ᵥ vecMul v (B p.2))) ∂μ.prod μ) ≤
        R * ∫ ξ, w ξ * normSq (vecMul v (B ξ)) ∂μ)
    (v : Fin m → ℝ) :
    ∫ ξ, w ξ * normSq (vecMul v (B ξ)) ∂μ ≤
      (R + √(√((μ.prod μ).real (Gᶜ ∩ S ×ˢ S)) *
        ∫ ξ, w ξ ^ 2 * β ξ ^ 4 ∂μ)) * normSq v := by
  classical
  set f : X → Fin k → ℝ := fun ξ => vecMul v (B ξ) with hfd
  set g : X → Fin m → ℝ := fun ξ => w ξ • (B ξ *ᵥ f ξ) with hgd
  set V := normSq v with hVd
  have hV0 : 0 ≤ V := normSq_nonneg v
  have hβ0 : ∀ ξ, 0 ≤ β ξ := fun ξ => (opN_nonneg _).trans (hβ ξ)
  -- measurability
  have hfm : ∀ j, Measurable (fun ξ => f ξ j) := by
    intro j
    show Measurable (fun ξ => ∑ i, v i * B ξ i j)
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (hB i j)
  have hBfm : ∀ i, Measurable (fun ξ => (B ξ *ᵥ f ξ) i) := by
    intro i
    show Measurable (fun ξ => ∑ j, B ξ i j * f ξ j)
    exact Finset.measurable_sum _ fun j _ => (hB i j).mul (hfm j)
  have hgm : ∀ i, Measurable (fun ξ => g ξ i) := fun i => hwm.mul (hBfm i)
  have hnfm : Measurable (fun ξ => normSq (f ξ)) := by
    show Measurable (fun ξ => ∑ j, f ξ j ^ 2)
    exact Finset.measurable_sum _ fun j _ => (hfm j).pow_const 2
  -- pointwise bounds
  have hfb : ∀ ξ, nrm (f ξ) ≤ β ξ * nrm v := fun ξ =>
    (nrm_vecMul_le _ _).trans (mul_le_mul_of_nonneg_right (hβ ξ) (nrm_nonneg _))
  have hBfb : ∀ ξ, nrm (B ξ *ᵥ f ξ) ≤ β ξ ^ 2 * nrm v := by
    intro ξ
    refine (nrm_mulVec_le _ _).trans ?_
    have := mul_le_mul (hβ ξ) (hfb ξ) (nrm_nonneg _) (hβ0 ξ)
    nlinarith [this]
  have hnf : ∀ ξ, normSq (f ξ) ≤ CB ^ 2 * V := by
    intro ξ
    rw [← nrm_sq, hVd, ← nrm_sq]
    have h1 := hfb ξ
    have h2 : β ξ * nrm v ≤ CB * nrm v := mul_le_mul_of_nonneg_right (hCB ξ) (nrm_nonneg _)
    have h3 : 0 ≤ nrm (f ξ) := nrm_nonneg _
    have h4 : 0 ≤ β ξ * nrm v := mul_nonneg (hβ0 ξ) (nrm_nonneg _)
    have h5 : nrm (f ξ) ^ 2 ≤ (CB * nrm v) ^ 2 := pow_le_pow_left₀ h3 (h1.trans h2) 2
    nlinarith
  have hgb : ∀ ξ, nrm (g ξ) ≤ w ξ * β ξ ^ 2 * nrm v := by
    intro ξ
    have e : nrm (g ξ) = w ξ * nrm (B ξ *ᵥ f ξ) := by
      show √(normSq (w ξ • (B ξ *ᵥ f ξ))) = _
      have : normSq (w ξ • (B ξ *ᵥ f ξ)) = w ξ ^ 2 * normSq (B ξ *ᵥ f ξ) := by
        simp [normSq, Finset.mul_sum, mul_pow]
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hw0 ξ)]
      rfl
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hBfb ξ) (hw0 ξ)
  have hgi : ∀ i, Integrable (fun ξ => g ξ i) μ := by
    intro i
    refine Integrable.mono' (hwi.mul_const (CB ^ 2 * nrm v)) (hgm i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_coord_le_nrm _ i).trans ((hgb ξ).trans ?_)
    have h1 : β ξ ^ 2 ≤ CB ^ 2 := pow_le_pow_left₀ (hβ0 ξ) (hCB ξ) 2
    have := mul_le_mul_of_nonneg_left h1 (hw0 ξ)
    have := mul_le_mul_of_nonneg_right this (nrm_nonneg v)
    linarith
  -- the identity `Q = v·a`, `a = ∫ g`
  set a : Fin m → ℝ := fun i => ∫ ξ, g ξ i ∂μ with had
  set Q := ∫ ξ, w ξ * normSq (vecMul v (B ξ)) ∂μ with hQd
  have hpt : ∀ ξ, w ξ * normSq (f ξ) = ∑ i, v i * g ξ i := by
    intro ξ
    have e1 : ∑ i, v i * g ξ i = w ξ * (v ⬝ᵥ (B ξ *ᵥ f ξ)) := by
      simp only [hgd, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, dotProduct_mulVec, normSq_eq_dot]
  have hQa : Q = v ⬝ᵥ a := by
    rw [hQd]
    have e : (fun ξ => w ξ * normSq (vecMul v (B ξ))) = fun ξ => ∑ i, v i * g ξ i :=
      funext hpt
    rw [e, integral_finsetSum _ fun i _ => (hgi i).const_mul (v i)]
    simp only [dotProduct, had]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hQ0 : 0 ≤ Q := integral_nonneg fun ξ => mul_nonneg (hw0 ξ) (normSq_nonneg _)
  have hQ2 : Q ^ 2 ≤ V * normSq a := by
    have h1 : Q ≤ nrm v * nrm a := hQa ▸ (le_abs_self _).trans (abs_dot_le_nrm v a)
    have h2 := pow_le_pow_left₀ hQ0 h1 2
    rw [mul_pow, nrm_sq, nrm_sq] at h2
    exact h2
  -- `|a|² = ∫∫ g·g'`
  have hpi : Integrable (fun p : X × X => g p.1 ⬝ᵥ g p.2) (μ.prod μ) := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (hgi i).mul_prod (hgi i)
  have haP : normSq a = ∫ p, g p.1 ⬝ᵥ g p.2 ∂(μ.prod μ) := by
    simp only [dotProduct]
    rw [integral_finsetSum _ fun i _ => (hgi i).mul_prod (hgi i)]
    simp only [normSq, had]
    exact Finset.sum_congr rfl fun i _ => by
      rw [integral_prod_mul (fun ξ => g ξ i) (fun ξ => g ξ i), sq]
  set F : X → ℝ := fun ξ => w ξ * β ξ ^ 2 with hFd
  have hF0 : ∀ ξ, 0 ≤ F ξ := fun ξ => mul_nonneg (hw0 ξ) (sq_nonneg _)
  set ind : X × X → ℝ := (Gᶜ ∩ S ×ˢ S).indicator 1 with hindd
  set Bd : X × X → ℝ := fun p => ind p * (F p.1 * F p.2) with hBdd
  set T : X × X → ℝ := G.indicator (fun p => g p.1 ⬝ᵥ g p.2) with hTd
  have hTi : Integrable T (μ.prod μ) := hpi.indicator hG
  have hww : Integrable (fun p : X × X => w p.1 * w p.2) (μ.prod μ) := hwi.mul_prod hwi
  have hFm : Measurable F := hwm.mul (hβm.pow_const 2)
  have hindm : Measurable ind := measurable_const.indicator (hG.compl.inter (hS.prod hS))
  have hind01 : ∀ p, ind p = 0 ∨ ind p = 1 := by
    intro p
    by_cases hp : p ∈ Gᶜ ∩ S ×ˢ S
    · right; simp only [hindd]; rw [Set.indicator_of_mem hp]; rfl
    · left; simp only [hindd]; rw [Set.indicator_of_notMem hp]
  have hBdi : Integrable Bd (μ.prod μ) := by
    refine Integrable.mono' (hww.const_mul (CB ^ 4)) (hindm.mul ((hFm.comp measurable_fst).mul
      (hFm.comp measurable_snd))).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    have hFF : 0 ≤ F p.1 * F p.2 := mul_nonneg (hF0 _) (hF0 _)
    have hb1 : β p.1 ^ 2 ≤ CB ^ 2 := pow_le_pow_left₀ (hβ0 _) (hCB _) 2
    have hb2 : β p.2 ^ 2 ≤ CB ^ 2 := pow_le_pow_left₀ (hβ0 _) (hCB _) 2
    have hF1 : F p.1 ≤ w p.1 * CB ^ 2 := mul_le_mul_of_nonneg_left hb1 (hw0 _)
    have hF2 : F p.2 ≤ w p.2 * CB ^ 2 := mul_le_mul_of_nonneg_left hb2 (hw0 _)
    have h3 : F p.1 * F p.2 ≤ (w p.1 * CB ^ 2) * (w p.2 * CB ^ 2) :=
      mul_le_mul hF1 hF2 (hF0 _) (mul_nonneg (hw0 _) (sq_nonneg _))
    have hval : ‖Bd p‖ ≤ F p.1 * F p.2 := by
      rcases hind01 p with h | h
      · simp only [hBdd, h, zero_mul, norm_zero]; exact hFF
      · simp only [hBdd, h, one_mul]; rw [Real.norm_eq_abs, abs_of_nonneg hFF]
    exact hval.trans (h3.trans (le_of_eq (by ring)))
  have hgdot : ∀ p : X × X, g p.1 ⬝ᵥ g p.2 =
      w p.1 * w p.2 * ((B p.1 *ᵥ f p.1) ⬝ᵥ (B p.2 *ᵥ f p.2)) := by
    intro p
    simp only [hgd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hptb : ∀ p : X × X, g p.1 ⬝ᵥ g p.2 ≤ T p + V * Bd p := by
    intro p
    by_cases hp : p ∈ G
    · have hBd0 : Bd p = 0 := by
        have hn : p ∉ Gᶜ ∩ S ×ˢ S := fun h => h.1 hp
        simp only [hBdd, hindd, Set.indicator_of_notMem hn, zero_mul]
      rw [hTd, Set.indicator_of_mem hp, hBd0, mul_zero, add_zero]
    · rw [hTd, Set.indicator_of_notMem hp, zero_add]
      by_cases hSS : p ∈ S ×ˢ S
      · have hind : ind p = 1 := by
          simp only [hindd]
          rw [Set.indicator_of_mem (show p ∈ Gᶜ ∩ S ×ˢ S from ⟨hp, hSS⟩)]
          rfl
        simp only [hBdd, hind, one_mul]
        refine (le_abs_self _).trans ((abs_dot_le_nrm _ _).trans ?_)
        have e : V * (F p.1 * F p.2) =
            (w p.1 * β p.1 ^ 2 * nrm v) * (w p.2 * β p.2 ^ 2 * nrm v) := by
          rw [hVd, ← nrm_sq, hFd]
          ring
        rw [e]
        exact mul_le_mul (hgb p.1) (hgb p.2) (nrm_nonneg _)
          (mul_nonneg (mul_nonneg (hw0 _) (sq_nonneg _)) (nrm_nonneg _))
      · have hz : w p.1 * w p.2 = 0 := by
          rcases not_and_or.1 (by simpa [Set.mem_prod] using hSS) with h | h
          · rw [hwS _ h, zero_mul]
          · rw [hwS _ h, mul_zero]
        rw [hgdot, hz, zero_mul]
        exact mul_nonneg hV0
          (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) p)
            (mul_nonneg (hF0 _) (hF0 _)))
  have hP : (∫ p, g p.1 ⬝ᵥ g p.2 ∂μ.prod μ) ≤
      (∫ p, T p ∂μ.prod μ) + V * ∫ p, Bd p ∂μ.prod μ := by
    have h := integral_mono hpi (hTi.add (hBdi.const_mul V)) hptb
    dsimp only [Pi.add_apply] at h
    rw [integral_add hTi (hBdi.const_mul V), integral_const_mul] at h
    exact h
  have hTG : (∫ p, T p ∂μ.prod μ) ≤ R * Q := by
    rw [hTd, integral_indicator hG]
    simp_rw [hgdot]
    exact hgood v
  -- the bad pairs
  set H := (μ.prod μ).real (Gᶜ ∩ S ×ˢ S) with hHd
  set A := ∫ ξ, w ξ ^ 2 * β ξ ^ 4 ∂μ with hAd
  have hH0 : 0 ≤ H := measureReal_nonneg
  have hF2 : ∀ ξ, F ξ ^ 2 = w ξ ^ 2 * β ξ ^ 4 := fun ξ => by simp only [hFd]; ring
  have hF2i : Integrable (fun ξ => F ξ ^ 2) μ := by
    refine Integrable.mono' (hw2.mul_const (CB ^ 4)) (hFm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hF2]
    have : β ξ ^ 4 ≤ CB ^ 4 := pow_le_pow_left₀ (hβ0 _) (hCB _) 4
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hA0 : 0 ≤ A := integral_nonneg fun ξ => by positivity
  have hFFi : ∫ p, F p.1 ^ 2 * F p.2 ^ 2 ∂(μ.prod μ) = A * A := by
    rw [integral_prod_mul (fun ξ => F ξ ^ 2) (fun ξ => F ξ ^ 2)]
    simp only [hF2, hAd]
  have hindi : ∫ p, ind p ∂(μ.prod μ) = H := integral_indicator_one (hG.compl.inter (hS.prod hS))
  have hJ : ∫ p, Bd p ∂(μ.prod μ) ≤ √H * A := by
    have h := le_sqrt_of_forall_pos (J := ∫ p, Bd p ∂(μ.prod μ)) hH0 (mul_nonneg hA0 hA0)
      (fun s hs => by
        have hint : Integrable (fun p : X × X => (s * ind p + F p.1 ^ 2 * F p.2 ^ 2 / s) / 2)
            (μ.prod μ) := by
          have hi1 : Integrable ind (μ.prod μ) :=
            (integrable_const (1 : ℝ)).indicator (hG.compl.inter (hS.prod hS))
          exact ((hi1.const_mul s).add ((hF2i.mul_prod hF2i).div_const s)).div_const 2
        have hle : ∫ p, Bd p ∂(μ.prod μ) ≤
            ∫ p, (s * ind p + F p.1 ^ 2 * F p.2 ^ 2 / s) / 2 ∂(μ.prod μ) := by
          refine integral_mono hBdi hint fun p => ?_
          have hFF : 0 ≤ F p.1 * F p.2 := mul_nonneg (hF0 _) (hF0 _)
          have hsq : 0 ≤ (s - F p.1 * F p.2) ^ 2 := sq_nonneg _
          show ind p * (F p.1 * F p.2) ≤ _
          rcases hind01 p with h | h
          · rw [h]; simp only [zero_mul, mul_zero, zero_add]; positivity
          · rw [h, one_mul, mul_one]
            rw [show F p.1 ^ 2 * F p.2 ^ 2 = (F p.1 * F p.2) ^ 2 by ring]
            rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
            have : (F p.1 * F p.2) ^ 2 / s = (F p.1 * F p.2) ^ 2 * s⁻¹ := div_eq_mul_inv _ _
            have hs' : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
            have : (F p.1 * F p.2) * 2 ≤ s + (F p.1 * F p.2) ^ 2 / s := by
              rw [← sub_nonneg]
              have e : s + (F p.1 * F p.2) ^ 2 / s - F p.1 * F p.2 * 2 =
                  (s - F p.1 * F p.2) ^ 2 / s := by field_simp; ring
              rw [e]; positivity
            linarith
        refine hle.trans (le_of_eq ?_)
        have hi1 : Integrable ind (μ.prod μ) :=
          (integrable_const (1 : ℝ)).indicator (hG.compl.inter (hS.prod hS))
        rw [integral_div, integral_add (f := fun p => s * ind p)
          (g := fun p => F p.1 ^ 2 * F p.2 ^ 2 / s) (hi1.const_mul s)
          ((hF2i.mul_prod hF2i).div_const s), integral_const_mul, integral_div, hFFi, hindi])
    refine h.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hH0, Real.sqrt_mul_self hA0]
  have hfin : Q ^ 2 ≤ V * (R * Q + V * (√H * A)) := by
    refine hQ2.trans ?_
    rw [haP]
    refine mul_le_mul_of_nonneg_left ?_ hV0
    have := mul_le_mul_of_nonneg_left hJ hV0
    linarith
  exact quad_step hQ0 hR0 (mul_nonneg (Real.sqrt_nonneg _) hA0) hV0 hfin

end BstLean.Part208
