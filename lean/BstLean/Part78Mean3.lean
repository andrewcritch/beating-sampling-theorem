import BstLean.Part78Mean
import BstLean.Part78Defs3

/-!
# Part 78: `wQId`, the pointwise identity for `E_W (F_x − E_y F_y)²`
-/

namespace BstLean.Part78

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)

variable {n : ℕ}

/-- `∫_W F_x · (∫_y F_y) = ∫_y ∫_W F_x F_y` for a separable sum. -/
lemma sep_swap_cross {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype K]
    {μ : Measure Ω} {ν : Measure X} (c : K → Ω → ℝ) (ψ : K → X → ℝ)
    (hc2 : ∀ k l, Integrable (fun W => c k W * c l W) μ)
    (hψ : ∀ k, Integrable (ψ k) ν) (x : X) :
    ∫ W, (∑ k, c k W * ψ k x) * (∫ y, ∑ k, c k W * ψ k y ∂ν) ∂μ =
      ∫ y, ∫ W, (∑ k, c k W * ψ k x) * (∑ k, c k W * ψ k y) ∂μ ∂ν := by
  simp_rw [← integral_const_mul, sep_mul c ψ c ψ]
  exact sep_swap (fun (kl : K × K) (W : Ω) => c kl.1 W * c kl.2 W)
    (fun (kl : K × K) y => ψ kl.1 x * ψ kl.2 y) (fun kl => hc2 kl.1 kl.2)
    (fun kl => (hψ kl.2).const_mul _)

/-- `E_y R(x,y)`. -/
lemma sph_row (hn : 1 ≤ n) (A T Fr : ℝ) (x : Fin n → ℝ) :
    ∫ y, (A * kap x y + T * (kap x x * kap y y) + Fr * kap x y ^ 2) ∂uniformSphere n =
      A * (∫ y, kap x y ∂uniformSphere n) + T * (kap x x * tG n) +
        Fr * ∫ y, kap x y ^ 2 ∂uniformSphere n := by
  have h1 : Integrable (fun x : Fin n → ℝ => kap x x) (uniformSphere n) := sph_int hn cont_kap_diag
  have i1 : Integrable (fun y : Fin n → ℝ => kap x y) (uniformSphere n) :=
    sph_int hn (cont_kap_right x)
  have i2 : Integrable (fun y : Fin n → ℝ => kap x y ^ 2) (uniformSphere n) :=
    sph_int hn ((cont_kap_right x).pow 2)
  have h : ∀ y : Fin n → ℝ, A * kap x y + T * (kap x x * kap y y) + Fr * kap x y ^ 2 =
      A * kap x y + ((T * kap x x) * kap y y + Fr * kap x y ^ 2) := by intro y; ring
  simp_rw [h]
  have e1 := integral_add (i1.const_mul A) ((h1.const_mul (T * kap x x)).add (i2.const_mul Fr))
  have e2 := integral_add (h1.const_mul (T * kap x x)) (i2.const_mul Fr)
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]
  unfold tG
  ring

/-- **The pointwise identity.** -/
theorem wQId (n : ℕ) (hn : 1 ≤ n) (hW : WickTwoPoint) : WQId n := by
  intro a H hH x
  have gA : Good (stdGauss (WIdx n)) (fun W => ∫ y, FG a H W y ∂uniformSphere n) := by
    simp_rw [intF_eq hn]
    exact Good.sum _ fun k _ => (good_cc a H k).mul_const _
  have gF : Good (stdGauss (WIdx n)) (fun W => FG a H W x) := by
    simp_rw [FG_eq]
    exact Good.sum _ fun k _ => (good_cc a H k).mul_const _
  have hc2 : ∀ k l, Integrable (fun W => cc H k (a, W) * cc H l (a, W)) (stdGauss (WIdx n)) :=
    fun k l => ((good_cc a H k).mul (good_cc a H l)).integrable
  have T1 : ∫ W, FG a H W x ^ 2 ∂stdGauss (WIdx n) =
      nsq a * kap x x + trH H ^ 2 * (kap x x * kap x x) + 2 * frobH H * kap x x ^ 2 := by
    simp_rw [sq (FG a H _ _)]
    exact wick2 hW a H hH x x
  have T2 : ∫ W, FG a H W x * (∫ y, FG a H W y ∂uniformSphere n) ∂stdGauss (WIdx n) =
      nsq a * (∫ y, kap x y ∂uniformSphere n) + trH H ^ 2 * (kap x x * tG n) +
        2 * frobH H * ∫ y, kap x y ^ 2 ∂uniformSphere n := by
    have h : ∫ W, FG a H W x * (∫ y, FG a H W y ∂uniformSphere n) ∂stdGauss (WIdx n) =
        ∫ y, ∫ W, FG a H W x * FG a H W y ∂stdGauss (WIdx n) ∂uniformSphere n := by
      simp_rw [FG_eq]
      exact sep_swap_cross (μ := stdGauss (WIdx n)) (ν := uniformSphere n)
        (fun k W => cc H k (a, W)) psi hc2 (int_psi hn) x
    rw [h]
    simp_rw [wick2 hW a H hH]
    exact sph_row hn _ _ _ x
  have T3 : ∫ W, (∫ y, FG a H W y ∂uniformSphere n) ^ 2 ∂stdGauss (WIdx n) =
      nsq a * mm1 n + trH H ^ 2 * tG n ^ 2 + 2 * frobH H * ss2 n := by
    have h : ∫ W, (∫ x, FG a H W x ∂uniformSphere n) ^ 2 ∂stdGauss (WIdx n) =
        ∫ x, ∫ y, ∫ W, FG a H W x * FG a H W y ∂stdGauss (WIdx n)
          ∂uniformSphere n ∂uniformSphere n := by
      simp_rw [FG_eq]
      exact sep_swap_two (μ := stdGauss (WIdx n)) (ν := uniformSphere n)
        (fun k W => cc H k (a, W)) psi hc2 (int_psi hn)
    rw [h]
    simp_rw [wick2 hW a H hH]
    exact sph_off hn _ _ _
  unfold wQ
  have h : ∀ W, (FG a H W x - ∫ y, FG a H W y ∂uniformSphere n) ^ 2 =
      FG a H W x ^ 2 - 2 * (FG a H W x * ∫ y, FG a H W y ∂uniformSphere n) +
        (∫ y, FG a H W y ∂uniformSphere n) ^ 2 := by intro W; ring
  simp_rw [h]
  have e1 := integral_add (((gF.pow 2).integrable).sub (((gF.mul gA).integrable).const_mul 2))
    (gA.pow 2).integrable
  have e2 := integral_sub ((gF.pow 2).integrable) (((gF.mul gA).integrable).const_mul 2)
  simp only [Pi.sub_apply] at e1
  rw [e1, e2, integral_const_mul, T1, T2, T3]
  ring

end BstLean.Part78

#print axioms BstLean.Part78.wQId
