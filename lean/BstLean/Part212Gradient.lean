import BstLean.Part167Grad

/-! The realized latitude densities have order-160 Jacobian bounds. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix xLat hhMat uHat consV)
open BstLean.Part151 (jac rowL rowL_apply gradSq)
open BstLean.Part162 (xLatH tanSq xLatH_eq dirW tanSq_eq_proj latitude_sq_le)
open BstLean.Part166 (bK bhat fK sK psiK repK latK FF SS fK_eq_FF sK_eq_SS)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part167
variable {n : ℕ}

lemma sqrt_sq_pow_le160 (T : ℝ) : (√T ^ 2) ^ 80 ≤ T ^ 80 := by
  by_cases h : 0 ≤ T
  · rw [Real.sq_sqrt h]
  · rw [Real.sqrt_eq_zero'.mpr (le_of_not_ge h)]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_pow (by norm_num : (80 : ℕ) ≠ 0)]
    exact Even.pow_nonneg (by decide : Even 80) T

variable (k : AgFam n) (a : Ix n) (v : Fin (n - 1) → ℝ)

theorem psiK_f_le160 (hn : 1 ≤ n) (hc : k.1.1 ≠ 0) (hv : v ≠ 0)
    (hK : NoKink k.2.1 k.2.2 (xLatH (repK k) (latK k a) v)) :
    psiK fK k a v ^ 80 ≤ ((1 - latK k a ^ 2) *
      latSq (gF k (xLatH (repK k) (latK k a) v)) (uHat (repK k))
        (dirW (repK k) (unitF53 v)) / n) ^ 80 := by
  set y := xLatH (repK k) (latK k a) v with hy
  set J := jac k.2.1 k.2.2 y
  set b := bhat (bK k)
  have hev := hid2_eventuallyEq_jac hK
  have hloc : fK k =ᶠ[𝓝 y] fun z => (√(n : ℝ))⁻¹ * ∑ j, (J *ᵥ z) j * b j := by
    rw [fK_eq_FF]
    filter_upwards [hev] with z hz
    unfold FF
    rw [hz]
  set Lc : (Fin n → ℝ) →L[ℝ] ℝ :=
    (√(n : ℝ))⁻¹ • ∑ l, gF k y l • (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ) with hLc
  have hLa : ∀ d, Lc d = (√(n : ℝ))⁻¹ * ∑ l, gF k y l * d l := by
    intro d; simp [hLc]
  have hfun : (fun z => (√(n : ℝ))⁻¹ * ∑ j, (J *ᵥ z) j * b j) = fun z => Lc z := by
    funext z; rw [hLa, sum_mulVec_mul]; rfl
  have hd : HasFDerivAt (fK k) Lc y := by
    have h0 : HasFDerivAt (fun z => (√(n : ℝ))⁻¹ * ∑ j, (J *ᵥ z) j * b j) Lc y := by
      rw [hfun]; exact Lc.hasFDerivAt
    exact h0.congr_of_eventuallyEq hloc
  have hT := tanSq_of_hasFDerivAt hn hc (s := latK k a) (latitude_sq_le _ _ _) (fK_hom k) hv hd hLa
  unfold psiK
  refine (sqrt_sq_pow_le160 _).trans (le_of_eq ?_)
  rw [hT]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_pow, Real.sq_sqrt hn0.le]
  congr 1
  field_simp

/-- **`Ψ_σ` through the Jacobian.** -/
theorem psiK_s_le160 (hn : 1 ≤ n) (hc : k.1.1 ≠ 0) (hv : v ≠ 0)
    (hK : NoKink k.2.1 k.2.2 (xLatH (repK k) (latK k a) v)) :
    psiK sK k a v ^ 80 ≤ ((1 - latK k a ^ 2) * (2 / (mA n : ℝ)) *
      latSq (gS k (xLatH (repK k) (latK k a) v)) (uHat (repK k))
        (dirW (repK k) (unitF53 v))) ^ 80 := by
  set y := xLatH (repK k) (latK k a) v with hy
  set J := jac k.2.1 k.2.2 y
  set b := bhat (bK k)
  have hev := hid2_eventuallyEq_jac hK
  -- the residual as a matrix map near `y`
  set R : Matrix (Fin (mA n)) (Fin n) ℝ := J - Matrix.vecMulVec b (vecMul b J) with hR
  have hRz : ∀ z, hid2 k.2.1 k.2.2 z = J *ᵥ z → rK k z = R *ᵥ z := by
    intro z hz
    unfold rK
    rw [hz, hR, Matrix.sub_mulVec]
    congr 1
    funext j
    rw [Pi.smul_apply, smul_eq_mul, sum_mulVec_mul J b z]
    simp only [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hry : rK k y = R *ᵥ y := hRz y (hev.self_of_nhds)
  have hloc : sK k =ᶠ[𝓝 y] fun z => √(2 / (mA n : ℝ)) * √(normSq (R *ᵥ z)) := by
    filter_upwards [hev] with z hz
    rw [sK_eq_rK, hRz z hz]
  unfold psiK
  by_cases hr : normSq (rK k y) = 0
  · -- `r(y) = 0`: `σ` has a minimum `0` on the latitude cone at `v`, so `Ψ_σ = 0`
    have hsy : sK k y = 0 := by rw [sK_eq_rK, hr]; simp
    have hmin : IsLocalMin (fun w => sK k (xLatH (repK k) (latK k a) w)) v := by
      refine Filter.Eventually.of_forall fun w => ?_
      show sK k y ≤ sK k (xLatH (repK k) (latK k a) w)
      rw [hsy, sK_eq_rK]; positivity
    have hT : tanSq (sK k) (repK k) (latK k a) v = 0 := by
      unfold tanSq gradSq
      rw [hmin.fderiv_eq_zero]
      have hvpos : 0 < radF53 v := BstLean.Part162.radF_pos hv
      have hx : sK k (xLat (repK k) (latK k a) (unitF53 v)) = 0 := by
        have h1 := sK_hom k (radF53 v) (xLat (repK k) (latK k a) (unitF53 v)) hvpos
        rw [← xLatH_eq, ← hy, hsy] at h1
        have := (mul_eq_zero.mp h1.symm).resolve_left hvpos.ne'
        exact this
      rw [hx]; simp
    rw [hT]; simp; positivity
  · have hRy : normSq (R *ᵥ y) ≠ 0 := by rw [← hry]; exact hr
    obtain ⟨L0, hL0, hL0a⟩ := hasFDerivAt_nrm_mulVec R hRy
    have hd : HasFDerivAt (sK k) (√(2 / (mA n : ℝ)) • L0) y :=
      (hL0.const_mul (√(2 / (mA n : ℝ)))).congr_of_eventuallyEq hloc
    have hg : vecMul (bhat (R *ᵥ y)) R = gS k y := by
      unfold gS
      rw [← hry, hR, Matrix.vecMul_sub]
      have e : vecMul (bhat (rK k y)) (Matrix.vecMulVec b (vecMul b J)) = 0 := by
        funext l
        simp only [vecMul, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Pi.zero_apply]
        have h0 := rK_orth k y
        have e2 : ∑ j, bhat (rK k y) j * (b j * ∑ i, b i * J i l) =
            (∑ j, rK k y j * b j) * ((√(normSq (rK k y)))⁻¹ * ∑ i, b i * J i l) := by
          unfold bhat
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e2, h0, zero_mul]
      rw [e, sub_zero]
    have hLa : ∀ d, (√(2 / (mA n : ℝ)) • L0) d = √(2 / (mA n : ℝ)) * ∑ l, gS k y l * d l := by
      intro d
      rw [_root_.smul_apply, hL0a, ← hg, smul_eq_mul]
    have hT := tanSq_of_hasFDerivAt hn hc (s := latK k a) (latitude_sq_le _ _ _) (sK_hom k) hv hd hLa
    refine (sqrt_sq_pow_le160 _).trans (le_of_eq ?_)
    rw [hT, Real.sq_sqrt (by positivity)]
    ring

end BstLean.Part212
