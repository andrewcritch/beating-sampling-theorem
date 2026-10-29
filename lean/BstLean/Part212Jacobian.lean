import BstLean.Part167Red
import BstLean.Part212Gradient

/-! The order-160 Jacobian moment supplies the realized latitude density moment. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix xLat hhMat uHat consV hh_normSq normSq_consV)
open BstLean.Part162 (xLatH tanSq xLatH_eq dirW latitude_sq_le radF_pos radF_sq)
open BstLean.Part166 (bK bhat fK sK psiK repK latK winC LJ_hyp)
open BstLean.Part151 (jac)
open BstLean.Part153 (nuA jac_smul)
open BstLean.Part53 (unitF53 radF53)

open BstLean.Part167
variable {n : ℕ}

def JacobianMoment160 (n : ℕ) (K2 : ℝ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), winC c τ → ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
    ∫⁻ θ, ENNReal.ofReal (latSq (gF ((c, τ), θ)
        (xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)))
        (uHat (rc c)) (dirW (rc c) (unitF53 v)) ^ 80) ∂nuA n ≤ ENNReal.ofReal (K2 ^ 80) ∧
    ∫⁻ θ, ENNReal.ofReal (latSq (gS ((c, τ), θ)
        (xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)))
        (uHat (rc c)) (dirW (rc c) (unitF53 v)) ^ 80) ∂nuA n ≤ ENNReal.ofReal (K2 ^ 80)

/-- The realized `LJ_hyp` for every direction `v ≠ 0`. -/
def LatitudeMoment160 (n : ℕ) (K2 : ℝ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), winC c τ → ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
    ∫⁻ θ, ENNReal.ofReal (psiK fK ((c, τ), θ) a v ^ 80) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K2 / n) ^ 80) ∧
    ∫⁻ θ, ENNReal.ofReal (psiK sK ((c, τ), θ) a v ^ 80) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * (2 / n) * K2 / n) ^ 80)

theorem latitudeMoment160_of_jacobian (hn : 1 ≤ n) {K2 : ℝ} (hJM : JacobianMoment160 n K2) :
    LatitudeMoment160 n K2 := by
  intro c τ hw a v hv
  obtain ⟨hJf, hJs⟩ := hJM c τ hw a v hv
  have hc : c ≠ 0 := window_c_ne hn hw
  set s := latitude (n := n) (√(normSq c)) τ a with hsdef
  have hs : s ^ 2 ≤ 1 := latitude_sq_le _ _ _
  set x := xLat (rc c) s (unitF53 v) with hx
  set y := xLatH (rc c) s v with hy
  have hyx : y = radF53 v • x := xLatH_eq _ _ _
  have hy0 : y ≠ 0 := xLatH_ne_zero hn _ hs hv
  have hae := noKink_nuA hn hy0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1s : 0 ≤ 1 - s ^ 2 := by linarith
  have hvpos : 0 < radF53 v := radF_pos hv
  refine ⟨?_, ?_⟩
  · calc ∫⁻ θ, ENNReal.ofReal (psiK fK ((c, τ), θ) a v ^ 80) ∂nuA n
        ≤ ∫⁻ θ, ENNReal.ofReal (((1 - s ^ 2) / n) ^ 80) *
            ENNReal.ofReal (latSq (gF ((c, τ), θ) x) (uHat (rc c)) (dirW (rc c) (unitF53 v))
              ^ 80) ∂nuA n := by
          refine lintegral_mono_ae (hae.mono fun θ hθ => ?_)
          have h := psiK_f_le160 ((c, τ), θ) a v hn hc hv hθ
          have e1 : gF ((c, τ), θ) (xLatH (repK ((c, τ), θ)) (latK ((c, τ), θ) a) v) =
              gF ((c, τ), θ) x := by
            change gF ((c, τ), θ) y = gF ((c, τ), θ) x
            rw [hyx, gF_smul _ hvpos]
          rw [e1] at h
          have hnn : (0 : ℝ) ≤ ((1 - s ^ 2) / n) ^ 80 := pow_nonneg (div_nonneg h1s hn0.le) 80
          rw [← ENNReal.ofReal_mul hnn]
          refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
          change ((1 - s ^ 2) * latSq (gF ((c, τ), θ) x) (uHat (rc c))
            (dirW (rc c) (unitF53 v)) / n) ^ 80 = _
          rw [← mul_pow]; congr 1; ring
      _ = ENNReal.ofReal (((1 - s ^ 2) / n) ^ 80) *
            ∫⁻ θ, ENNReal.ofReal (latSq (gF ((c, τ), θ) x) (uHat (rc c))
              (dirW (rc c) (unitF53 v)) ^ 80) ∂nuA n :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (((1 - s ^ 2) / n) ^ 80) * ENNReal.ofReal (K2 ^ 80) := by gcongr
      _ = ENNReal.ofReal (((1 - s ^ 2) * K2 / n) ^ 80) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]; congr 2; ring
  · have hm : (2 / (mA n : ℝ)) = 2 / n / n := by
      unfold mA; push_cast; field_simp
    calc ∫⁻ θ, ENNReal.ofReal (psiK sK ((c, τ), θ) a v ^ 80) ∂nuA n
        ≤ ∫⁻ θ, ENNReal.ofReal (((1 - s ^ 2) * (2 / n) / n) ^ 80) *
            ENNReal.ofReal (latSq (gS ((c, τ), θ) x) (uHat (rc c)) (dirW (rc c) (unitF53 v))
              ^ 80) ∂nuA n := by
          refine lintegral_mono_ae (hae.mono fun θ hθ => ?_)
          have h := psiK_s_le160 ((c, τ), θ) a v hn hc hv hθ
          have e1 : gS ((c, τ), θ) (xLatH (repK ((c, τ), θ)) (latK ((c, τ), θ) a) v) =
              gS ((c, τ), θ) x := by
            change gS ((c, τ), θ) y = gS ((c, τ), θ) x
            rw [hyx, gS_smul _ hvpos]
          rw [e1] at h
          have hnn : (0 : ℝ) ≤ ((1 - s ^ 2) * (2 / n) / n) ^ 80 :=
            pow_nonneg (div_nonneg (mul_nonneg h1s (by positivity)) hn0.le) 80
          rw [← ENNReal.ofReal_mul hnn]
          refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
          change ((1 - s ^ 2) * (2 / (mA n : ℝ)) * latSq (gS ((c, τ), θ) x) (uHat (rc c))
            (dirW (rc c) (unitF53 v))) ^ 80 = _
          rw [← mul_pow, hm]; congr 1; ring
      _ = ENNReal.ofReal (((1 - s ^ 2) * (2 / n) / n) ^ 80) *
            ∫⁻ θ, ENNReal.ofReal (latSq (gS ((c, τ), θ) x) (uHat (rc c))
              (dirW (rc c) (unitF53 v)) ^ 80) ∂nuA n :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (((1 - s ^ 2) * (2 / n) / n) ^ 80) * ENNReal.ofReal (K2 ^ 80) := by
          gcongr
      _ = ENNReal.ofReal (((1 - s ^ 2) * (2 / n) * K2 / n) ^ 80) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]; congr 2; ring

end BstLean.Part212
