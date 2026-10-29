import BstLean.Part211HS
import BstLean.Part206MA

/-! Scalar reductions of the sharp MA second moment. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part154 (K0 nuR)

theorem MA_rest_term {R N θ τ cs δe H S k k3 s2 G h : ℝ}
    (hR : 0 < R) (hN : 0 < N) (hτ : 0 < τ) (hcs : 0 < cs) (hδ : δe < 1)
    (hk : 0 < k) (hk3 : 0 < k3)
    (hU : R * (2 / N / N) * θ = 2 * τ ^ 2 / N) (hsc : cs * τ ^ 2 ≤ s2)
    (hG : (1 - δe) * (2 / N) * R ≤ G) (hh0 : 0 ≤ h)
    (hh : h ≤ 4 * τ ^ 4 * H / N) (hS : H * (θ * √θ) ≤ S) :
    2 * (K0 * √(k * k3) * h / (√s2 * √G)) ≤
      R * (2 / N / N) * (4 * K0 * √(k * k3) * S / √(2 * cs * (1 - δe))) := by
  have hs : 0 < s2 := (mul_pos hcs (sq_pos_of_pos hτ)).trans_le hsc
  have hg : 0 < G := (by positivity : 0 < (1 - δe) * (2 / N) * R).trans_le hG
  have h1 := BstLean.Part160.term1_alg (cH := 1) (hH := H) hR hN hτ hcs hδ
    (sqrt_pos.mpr hk) (sqrt_pos.mpr hk3) hU hsc hs hG hh0 (by simpa only [mul_one] using hh)
  have he : √(s2 / (√k) ^ 2 * (G / (√k3) ^ 2)) = √s2 * √G / √(k * k3) := by
    rw [sq_sqrt hk.le, sq_sqrt hk3.le,
      show s2 / k * (G / k3) = (s2 * G) / (k * k3) by ring,
      sqrt_div (mul_nonneg hs.le hg.le), sqrt_mul hs.le]
  rw [he, ← sqrt_mul hk.le] at h1
  have he1 : K0 * (h / (√s2 * √G / √(k * k3))) =
      K0 * √(k * k3) * h / (√s2 * √G) := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
    ring
  rw [he1] at h1
  refine h1.trans ?_
  have h2 := mul_le_mul_of_nonneg_left hS
    (show 0 ≤ R * (2 / N / N) * (4 * K0 * √(k * k3) / √(2 * cs * (1 - δe))) by
      have := BstLean.Part154.K0_pos
      positivity)
  convert h2 using 1 <;> ring

theorem MA_tail_term {R N w s2 G k k3 p p3 : ℝ}
    (hR : 0 ≤ R) (hN : 0 < N) (hw : 0 ≤ w) (hs : 0 ≤ s2) (hsG : s2 ≤ G)
    (hG : G ≤ 4 * w / N * R) (hk : 0 < k) (hk3 : 0 < k3)
    (hp : 0 ≤ p) (hp3 : 0 ≤ p3) :
    2 * (√s2 / 4 * (√s2 * p / √k + √G * p3 / √k3)) ≤
      R * (2 / N / N) * (w * N * (p / √k + p3 / √k3)) := by
  let U := 4 * w / N * R
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hss : √s2 * √s2 ≤ U := by rw [mul_self_sqrt hs]; exact hsG.trans hG
  have hsg : √s2 * √G ≤ U := by
    rw [← sqrt_mul hs]
    refine sqrt_le_iff.mpr ⟨hU, ?_⟩
    simpa only [sq] using (mul_le_mul (hsG.trans hG) hG (hs.trans hsG) hU)
  have h := add_le_add (mul_le_mul_of_nonneg_right hss
    (show 0 ≤ p / √k by positivity)) (mul_le_mul_of_nonneg_right hsg
    (show 0 ≤ p3 / √k3 by positivity))
  have he : R * (2 / N / N) * (w * N * (p / √k + p3 / √k3)) =
      (U * (p / √k) + U * (p3 / √k3)) / 2 := by
    dsimp [U]
    field_simp
    ring
  rw [he]
  ring_nf at h ⊢
  linarith only [h]

theorem MA_linear_term {R N θ τ cs w L r rb G s2 pb : ℝ}
    (hR : 0 < R) (hN : 0 < N) (hτ : 0 < τ) (hcs : 0 < cs) (hw : 0 ≤ w)
    (hU : R * (2 / N / N) * θ = 2 * τ ^ 2 / N)
    (hL : L ^ 2 = 4 * w * τ ^ 2 / N) (hr : 0 ≤ r) (hrb : r ≤ rb)
    (hrbe : rb = 4 * w / (cs * N)) (hG0 : 0 ≤ G)
    (hG : G ≤ 4 * w / N * R) (hsc : cs * τ ^ 2 ≤ s2) :
    2 * (L ^ 2 * (1 / π * (2 * r + (6863 / 10000) * (G / s2) * nuR r) + pb)) ≤
      R * (2 / N / N) *
        (4 * w * ((2 * θ * rb + (6863 / 10000) * rb * N * nuR rb) / π + θ * pb)) := by
  have hs : 0 < s2 := (mul_pos hcs (sq_pos_of_pos hτ)).trans_le hsc
  have hν := BstLean.Part160.nuR_monoI hr hrb
  have hν0 : 0 ≤ nuR r := by unfold nuR; positivity
  have hb : L ^ 2 * (G / s2) ≤ R * (2 / N / N) * (2 * w * rb * N) := by
    have h1 : G / s2 ≤ (4 * w / N * R) / (cs * τ ^ 2) :=
      div_le_div₀ (hG0.trans hG) hG (by positivity) hsc
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg L)
    have h3 : L ^ 2 * ((4 * w / N * R) / (cs * τ ^ 2)) =
        R * (2 / N / N) * (2 * w * rb * N) := by
      rw [hL, hrbe]
      field_simp
      ring
    exact h2.trans_eq h3
  have hb0 : 0 ≤ R * (2 / N / N) * (2 * w * rb * N) := by
    have : 0 ≤ rb := hr.trans hrb
    positivity
  have hbν := mul_le_mul hb hν hν0 hb0
  have hLU : 2 * L ^ 2 = R * (2 / N / N) * θ * (4 * w) := by rw [hU, hL]; ring
  have h1 := mul_le_mul_of_nonneg_left hrb (show 0 ≤ 2 * L ^ 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hbν (by norm_num : (0 : ℝ) ≤ 6863 / 10000)
  have h3 : 2 * (L ^ 2 * (1 / π * (2 * r + (6863 / 10000) * (G / s2) * nuR r) + pb)) =
      (1 / π) * (2 * (2 * L ^ 2 * r) + 2 * ((6863 / 10000) *
        (L ^ 2 * (G / s2) * nuR r))) + 2 * L ^ 2 * pb := by ring
  have h4 : R * (2 / N / N) *
      (4 * w * ((2 * θ * rb + (6863 / 10000) * rb * N * nuR rb) / π + θ * pb)) =
      (1 / π) * (2 * (R * (2 / N / N) * θ * (4 * w) * rb) +
        2 * ((6863 / 10000) * (R * (2 / N / N) * (2 * w * rb * N) * nuR rb))) +
      R * (2 / N / N) * θ * (4 * w) * pb := by ring
  rw [h3, h4, ← hLU]
  have h5 : 2 * (2 * L ^ 2 * r) + 2 * ((6863 / 10000) * (L ^ 2 * (G / s2) * nuR r)) ≤
      2 * (2 * L ^ 2 * rb) +
      2 * ((6863 / 10000) * (R * (2 / N / N) * (2 * w * rb * N) * nuR rb)) := by linarith
  exact add_le_add (mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 1 / π)) le_rfl

#print axioms MA_tail_term
#print axioms MA_linear_term
#print axioms MA_rest_term
end BstLean.Part211
