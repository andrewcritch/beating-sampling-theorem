import BstLean.Part292CoefficientMoments
import BstLean.Part223ScalarRA

/-! Latitude-factored scalar statistics for the actual order-104 row supplier. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part171
open BstLean.Part220 BstLean.Part223

noncomputable def latitudeRAData (q σ sp D V P : ℝ) : RAData where
  Smin := q*σ^2
  Smax := sp^2
  D := q*D
  H := q*D
  V := q*V+(q*D)^2
  P := P/q^4
  topF := 0
  topW := 0

theorem latitudeRAData_bounds {q lo hi σ sp D V P O : ℝ} (n : ℕ)
    (hlo : 0 < lo) (hql : lo ≤ q) (hqh : q ≤ hi) (hσ : 0 < σ)
    (hsp : 0 ≤ sp) (hD : 0 ≤ D) (hV : 0 ≤ V) (hP : 0 ≤ P) (hO : 0 ≤ O) :
    let d := latitudeRAData q σ sp D V P
    let Γ := tA n*O^2+sp^2
    let C := sqrt (tA n)*O
    d.f0 n O ≤ lowF0 lo hi σ Γ D V P ∧
    d.f1 n O ≤ lowF1 lo hi σ C D V P ∧
    d.f2 ≤ lowF2 hi σ D ∧
    d.w0 n O ≤ lowW0 lo hi σ Γ D V P ∧
    d.w1 n O ≤ lowW1 lo hi σ C sp D V P ∧
    d.w2 n O ≤ lowW2 lo hi C D P := by
  have hq : 0 ≤ q := hlo.le.trans hql
  have ht := tA_nonneg n
  simp only [latitudeRAData, RAData.f0, RAData.f1, RAData.f2,
    RAData.w0, RAData.w1, RAData.w2, sqrt_mul hq, sqrt_sq hσ.le, sqrt_sq hsp]
  exact collected_coefficients_bound hlo hql hqh hσ (by positivity)
    (by positivity) hsp hD hV hP

theorem latitudeRAData_nonneg {q σ sp D V P O : ℝ} (n : ℕ)
    (hq : 0 ≤ q) (hσ : 0 ≤ σ) (hsp : 0 ≤ sp)
    (hD : 0 ≤ D) (hV : 0 ≤ V) (hP : 0 ≤ P) (hO : 0 ≤ O) :
    let d := latitudeRAData q σ sp D V P
    0 ≤ d.f0 n O ∧ 0 ≤ d.f1 n O ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 n O ∧ 0 ≤ d.w1 n O ∧ 0 ≤ d.w2 n O := by
  have ht := tA_nonneg n
  have hp0 := (BstLean.Part153.phiG_pos 0).le
  have hp1 := (BstLean.Part153.phiG_pos 1).le
  simp only [latitudeRAData, RAData.f0, RAData.f1, RAData.f2,
    RAData.w0, RAData.w1, RAData.w2, AF0, AF1, AF2, AW0, AW1, AW2]
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem latitude_coefficient_moments {J : ℕ} (n : ℕ) (ν : Measure (Fin J))
    (hmass : ν Set.univ ≤ 1) (q D V P : Fin J → ℝ)
    {d v p lo hi σ sp O : ℝ}
    (hD : MomentBound ν 416 D d) (hV : MomentBound ν 416 V v)
    (hP : MomentBound ν 104 P p)
    (hD0 : ∀ g, 0 ≤ D g) (hV0 : ∀ g, 0 ≤ V g) (hP0 : ∀ g, 0 ≤ P g)
    (hlo : 0 < lo) (hql : ∀ g, lo ≤ q g) (hqh : ∀ g, q g ≤ hi)
    (hhi : 0 ≤ hi) (hσ : 0 < σ) (hsp : 0 ≤ sp) (hO : 0 ≤ O) :
    let R := fun g => latitudeRAData (q g) σ sp (D g) (V g) (P g)
    let Γ := tA n*O^2+sp^2
    let C := sqrt (tA n)*O
    MomentBound ν 104 (fun g => (R g).f0 n O) (lowF0 lo hi σ Γ d v p) ∧
    MomentBound ν 104 (fun g => (R g).f1 n O) (lowF1 lo hi σ C d v p) ∧
    MomentBound ν 104 (fun g => (R g).f2) (lowF2 hi σ d) ∧
    MomentBound ν 104 (fun g => (R g).w0 n O) (lowW0 lo hi σ Γ d v p) ∧
    MomentBound ν 104 (fun g => (R g).w1 n O) (lowW1 lo hi σ C sp d v p) ∧
    MomentBound ν 104 (fun g => (R g).w2 n O) (lowW2 lo hi C d p) := by
  have ht := tA_nonneg n
  have h := collected_coefficient_moments hmass hD hV hP hD0 hV0 hlo.le hhi hσ.le
    (by positivity : 0 ≤ tA n*O^2+sp^2) (by positivity : 0 ≤ sqrt (tA n)*O) hsp
  have hb g := latitudeRAData_bounds n hlo (hql g) (hqh g) hσ hsp (hD0 g) (hV0 g) (hP0 g) hO
  have hz g := latitudeRAData_nonneg n (hlo.le.trans (hql g)) hσ.le hsp
    (hD0 g) (hV0 g) (hP0 g) hO
  refine ⟨h.1.mono (measurable_of_finite _) (fun g => ?_),
    h.2.1.mono (measurable_of_finite _) (fun g => ?_),
    h.2.2.1.mono (measurable_of_finite _) (fun g => ?_),
    h.2.2.2.1.mono (measurable_of_finite _) (fun g => ?_),
    h.2.2.2.2.1.mono (measurable_of_finite _) (fun g => ?_),
    h.2.2.2.2.2.mono (measurable_of_finite _) (fun g => ?_)⟩
  · rw [abs_of_nonneg (hz g).1]; exact (hb g).1.trans (le_abs_self _)
  · rw [abs_of_nonneg (hz g).2.1]; exact (hb g).2.1.trans (le_abs_self _)
  · rw [abs_of_nonneg (hz g).2.2.1]; exact (hb g).2.2.1.trans (le_abs_self _)
  · rw [abs_of_nonneg (hz g).2.2.2.1]; exact (hb g).2.2.2.1.trans (le_abs_self _)
  · rw [abs_of_nonneg (hz g).2.2.2.2.1]; exact (hb g).2.2.2.2.1.trans (le_abs_self _)
  · rw [abs_of_nonneg (hz g).2.2.2.2.2]; exact (hb g).2.2.2.2.2.trans (le_abs_self _)

end BstLean.Part292
