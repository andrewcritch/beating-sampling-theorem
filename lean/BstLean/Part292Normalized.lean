import BstLean.Part292Collected

/-! Explicit homogeneity identities for the six collected coefficients. -/
namespace BstLean.Part292
open Real BstLean.Part153

noncomputable def normF0 (x lo hi s G d v p : ℝ) : ℝ :=
  sqrt hi*phiG 0/(2*s)*d*x+
    phiG 0/(2*sqrt 2*s^3)*(v/sqrt lo*x+sqrt hi*d^2*x^3)+
    (3/2)*phiG 0*G/(s*sqrt lo*lo^4)*p*x^7
noncomputable def normF1 (x lo hi s C d v p : ℝ) : ℝ :=
  phiG 1/s^2*(sqrt d*sqrt v*x+sqrt hi*sqrt d*d*x^2)+
    4*sqrt 2*C/lo^4*p*x^7
noncomputable def normF2 (x hi s d : ℝ) : ℝ := sqrt hi*phiG 0/(sqrt 2*s)*d*x
noncomputable def normW0 (x lo hi s G d v p : ℝ) : ℝ :=
  hi*d*x+phiG 1/(2*s^2)*(v*x+hi*d^2*x^3)+4*G/lo^4*p*x^7
noncomputable def normW1 (x lo hi s C sp d v p : ℝ) : ℝ :=
  sqrt 2*phiG 0/s*(sqrt hi*sqrt d*sqrt v*x+hi*sqrt d*d*x^2)+
    4*sqrt 2*C*sp/lo^4*p*x^7
noncomputable def normW2 (x lo hi C d p : ℝ) : ℝ := hi*d*x+28*C^2/lo^4*p*x^7

theorem sqrt_div_even_pow {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (k : ℕ) :
    sqrt (d/r^(2*k)) = sqrt d/r^k := by
  rw [sqrt_div hd, show r^(2*k)=(r^k)^2 by rw [← pow_mul]; congr 1; omega,
    sqrt_sq (pow_nonneg hr k)]

theorem collected_scale {r lo s : ℝ} (hr : 0 < r) (hlo : 0 < lo) (hs : 0 < s)
    (hi G C sp d v p : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v) :
    r^3*lowF0 lo hi (s/r) (G/r^2) (d/r^6) (v/r^8) (p/r^16) =
      normF0 (1/r^2) lo hi s G d v p ∧
    r^3*lowF1 lo hi (s/r) (C/r) (d/r^6) (v/r^8) (p/r^16) =
      normF1 (1/r^2) lo hi s C d v p ∧
    r^3*lowF2 hi (s/r) (d/r^6) = normF2 (1/r^2) hi s d ∧
    r^4*lowW0 lo hi (s/r) (G/r^2) (d/r^6) (v/r^8) (p/r^16) =
      normW0 (1/r^2) lo hi s G d v p ∧
    r^4*lowW1 lo hi (s/r) (C/r) (sp/r) (d/r^6) (v/r^8) (p/r^16) =
      normW1 (1/r^2) lo hi s C sp d v p ∧
    r^4*lowW2 lo hi (C/r) (d/r^6) (p/r^16) = normW2 (1/r^2) lo hi C d p := by
  have hl : sqrt lo ≠ 0 := (sqrt_pos.mpr hlo).ne'
  have h2 : sqrt (2 : ℝ) ≠ 0 := by positivity
  have hd' : sqrt (d/r^6) = sqrt d/r^3 := sqrt_div_even_pow hr.le hd 3
  have hv' : sqrt (v/r^8) = sqrt v/r^4 := sqrt_div_even_pow hr.le hv 4
  simp only [lowF0, lowF1, lowF2, lowW0, lowW1, lowW2,
    normF0, normF1, normF2, normW0, normW1, normW2, hd', hv']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

end BstLean.Part292
