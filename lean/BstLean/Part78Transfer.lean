import BstLean.Part78Gauss
import BstLean.Part78Mean

/-!
# Part 78: the transfer from the Gaussian model to the coefficient sphere, pointwise part

`(u, W)` is the Gaussian coefficient vector, `r = ‖(u, W)‖`, `τ = √𝒟 / r`. The original polynomial is
`f = (f₀, ℓ₀, H₀)`; the scaled one is `ℓ = ℓ₀/√𝒟`, `H = H₀/𝒟`.

* `qexp`: `f((u + z)/r) = f(u/r) + τ ℓ·z + τ² (2Hu·z + zᵀHz)`.
* `varU_affine_lower`: `Var(K + τ g + τ c h) ≥ τ²((1−λ) Var g − c² Var h/λ)`.
* `pw_core`: the variance and the error on the sphere in terms of the Gaussian quantities.
* `det_core`: off the bad events there is no failure (real arithmetic).
-/

namespace BstLean.Part78

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)

variable {n : ℕ}

lemma abc_sq (A B C : ℝ) : (A + B + C) ^ 2 ≤ 11 / 10 * A ^ 2 + 22 * B ^ 2 + 22 * C ^ 2 := by
  nlinarith [sq_nonneg (A - 10 * (B + C)), sq_nonneg (B - C)]

/-- **Deterministic core.** -/
lemma det_core {τ VS VGa VQ eS eG e2 trt Wfv v nR δ ε ε₁ κ lam TQ T2 : ℝ}
    (hτ : |τ - 1| ≤ δ) (hδ : δ ≤ 1 / 100)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hVQ0 : 0 ≤ VQ) (hv : 0 ≤ v) (hTQ : 0 ≤ TQ)
    (hT2 : 0 ≤ T2) (hnR : 0 ≤ nR)
    (hVS : τ ^ 2 * ((1 - lam) * VGa - (1 / lam) * (τ - 1) ^ 2 * VQ) ≤ VS)
    (heS : eS = τ * eG + τ * (τ - 1) * e2 + 3 / 2 * trt * (τ ^ 2 - 1))
    (h1 : κ * Wfv ≤ VGa) (h2 : VQ ≤ TQ * v) (h3 : e2 ^ 2 ≤ T2 * v) (h4 : eG ^ 2 ≤ ε₁ ^ 2 * Wfv)
    (h5 : trt ^ 2 ≤ nR * v) (h6 : v ≤ 100 / 449 * Wfv)
    (hnum : 11 / 10 * ε₁ ^ 2 + (22 * δ ^ 2 * T2 + 207 * δ ^ 2 * nR + ε ^ 2 * δ ^ 2 * TQ / lam)
      * (100 / 449) ≤ ε ^ 2 * (1 - lam) * κ) :
    eS ^ 2 ≤ ε ^ 2 * VS := by
  obtain ⟨hτl, hτu⟩ := abs_le.mp hτ
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hτ
  have hτlo : 99 / 100 ≤ τ := by linarith
  have hτhi : τ ≤ 101 / 100 := by linarith
  have hd2 : (τ - 1) ^ 2 ≤ δ ^ 2 := by nlinarith
  have hd20 : 0 ≤ (τ - 1) ^ 2 := sq_nonneg _
  have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg _
  have hbb : ((τ - 1) * e2) ^ 2 ≤ δ ^ 2 * (T2 * v) := by
    have : ((τ - 1) * e2) ^ 2 = (τ - 1) ^ 2 * e2 ^ 2 := by ring
    rw [this]
    exact mul_le_mul hd2 h3 (sq_nonneg _) (sq_nonneg _)
  have hτ1 : (τ + 1) ^ 2 ≤ 409 / 100 * τ ^ 2 := by nlinarith
  have hcc : (3 / 2 * trt * (τ - 1) * (τ + 1)) ^ 2 ≤ τ ^ 2 * (47 / 5) * (δ ^ 2 * (nR * v)) := by
    have e : (3 / 2 * trt * (τ - 1) * (τ + 1)) ^ 2 =
        9 / 4 * ((τ + 1) ^ 2 * ((τ - 1) ^ 2 * trt ^ 2)) := by ring
    have m1 : (τ - 1) ^ 2 * trt ^ 2 ≤ δ ^ 2 * (nR * v) :=
      mul_le_mul hd2 h5 (sq_nonneg _) (sq_nonneg _)
    have m0 : 0 ≤ (τ - 1) ^ 2 * trt ^ 2 := by positivity
    have m3 := mul_le_mul hτ1 m1 m0 (by positivity : (0 : ℝ) ≤ 409 / 100 * τ ^ 2)
    have m4 : 0 ≤ τ ^ 2 * (δ ^ 2 * (nR * v)) := by positivity
    rw [e]
    linarith
  have key : eS ^ 2 ≤ 11 / 10 * (τ ^ 2 * eG ^ 2) + 22 * (τ ^ 2 * ((τ - 1) * e2) ^ 2) +
      22 * (3 / 2 * trt * (τ - 1) * (τ + 1)) ^ 2 := by
    have : eS = τ * eG + τ * ((τ - 1) * e2) + 3 / 2 * trt * (τ - 1) * (τ + 1) := by
      rw [heS]; ring
    have h := abc_sq (τ * eG) (τ * ((τ - 1) * e2)) (3 / 2 * trt * (τ - 1) * (τ + 1))
    have e1 : (τ * eG) ^ 2 = τ ^ 2 * eG ^ 2 := by ring
    have e2' : (τ * ((τ - 1) * e2)) ^ 2 = τ ^ 2 * ((τ - 1) * e2) ^ 2 := by ring
    rw [e1, e2'] at h
    rw [this]; exact h
  have hlamVQ : (1 / lam) * (τ - 1) ^ 2 * VQ ≤ (1 / lam) * (δ ^ 2 * (TQ * v)) := by
    have : (1 / lam) * (τ - 1) ^ 2 * VQ = (1 / lam) * ((τ - 1) ^ 2 * VQ) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hd2 h2 hVQ0 (sq_nonneg _)) (by positivity)
  have hVS' : τ ^ 2 * ((1 - lam) * (κ * Wfv) - (1 / lam) * (δ ^ 2 * (TQ * v))) ≤ VS := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hτ2) hVS
    have : (1 - lam) * (κ * Wfv) ≤ (1 - lam) * VGa :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  -- the scalar inequality, before the factor `τ²`
  have hW0 : 0 ≤ Wfv := by linarith
  have hcoef : 0 ≤ 22 * δ ^ 2 * T2 + 207 * δ ^ 2 * nR + ε ^ 2 * δ ^ 2 * TQ / lam := by positivity
  have hsc : 11 / 10 * (ε₁ ^ 2 * Wfv) + 22 * (δ ^ 2 * (T2 * v)) + 22 * (47 / 5) * (δ ^ 2 * (nR * v))
      ≤ ε ^ 2 * ((1 - lam) * (κ * Wfv) - (1 / lam) * (δ ^ 2 * (TQ * v))) := by
    have a1 := mul_le_mul_of_nonneg_right hnum hW0
    have a2 := mul_le_mul_of_nonneg_left h6 hcoef
    have a3 : ε ^ 2 * ((1 / lam) * (δ ^ 2 * (TQ * v))) = ε ^ 2 * δ ^ 2 * TQ / lam * v := by
      ring
    have a4 : 0 ≤ δ ^ 2 * (nR * v) := by positivity
    rw [mul_sub, a3]
    linarith
  calc eS ^ 2 ≤ 11 / 10 * (τ ^ 2 * eG ^ 2) + 22 * (τ ^ 2 * ((τ - 1) * e2) ^ 2) +
      22 * (3 / 2 * trt * (τ - 1) * (τ + 1)) ^ 2 := key
    _ ≤ τ ^ 2 * (11 / 10 * (ε₁ ^ 2 * Wfv) + 22 * (δ ^ 2 * (T2 * v))
          + 22 * (47 / 5) * (δ ^ 2 * (nR * v))) := by
        have q1 := mul_le_mul_of_nonneg_left h4 hτ2
        have q2 := mul_le_mul_of_nonneg_left hbb hτ2
        linarith
    _ ≤ τ ^ 2 * (ε ^ 2 * ((1 - lam) * (κ * Wfv) - (1 / lam) * (δ ^ 2 * (TQ * v)))) :=
        mul_le_mul_of_nonneg_left hsc hτ2
    _ = ε ^ 2 * (τ ^ 2 * ((1 - lam) * (κ * Wfv) - (1 / lam) * (δ ^ 2 * (TQ * v)))) := by ring
    _ ≤ ε ^ 2 * VS := mul_le_mul_of_nonneg_left hVS' (sq_nonneg _)

/-- `f((u+z)·s) = f(u·s) + τ ℓ·z + τ²(2Hu·z + zᵀHz)`, `τ = √𝒟 s`. -/
lemma qexp (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (H₀ H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (sD D s : ℝ) (hsD : sD ^ 2 = D) (hℓ : ∀ i, ℓ₀ i = sD * ℓ i) (hHs : ∀ i j, H₀ i j = D * H i j)
    (u z : Fin n → ℝ) :
    qfun f0 ℓ₀ H₀ (fun i => s * (u i + z i)) =
      qfun f0 ℓ₀ H₀ (fun i => s * u i) + (sD * s) * (∑ i, ℓ i * z i) +
        (sD * s) ^ 2 * (∑ i, (2 * ∑ j, H i j * u j) * z i + ∑ i, ∑ j, H i j * z i * z j) := by
  unfold qfun
  simp only [hℓ, hHs]
  have e1 : ∑ i, sD * ℓ i * (s * (u i + z i)) =
      ∑ i, sD * ℓ i * (s * u i) + sD * s * ∑ i, ℓ i * z i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have sw : ∑ i, ∑ j, H i j * u i * z j = ∑ i, ∑ j, H i j * u j * z i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.apply i j]
  have e2 : ∑ i, ∑ j, D * H i j * (s * (u i + z i)) * (s * (u j + z j)) =
      ∑ i, ∑ j, D * H i j * (s * u i) * (s * u j) + D * s ^ 2 * (∑ i, ∑ j, H i j * u i * z j)
        + D * s ^ 2 * (∑ i, ∑ j, H i j * u j * z i) + D * s ^ 2 * (∑ i, ∑ j, H i j * z i * z j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ i, (2 * ∑ j, H i j * u j) * z i = 2 * ∑ i, ∑ j, H i j * u j * z i := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, sw, ← hsD]
  ring

/-- `Var(K + τ g + τ c h) ≥ τ²((1−λ) Var g − c² Var h/λ)`. -/
lemma varU_affine_lower (hn : 1 ≤ n) {g h : (Fin n → ℝ) → ℝ} (hg : Continuous g)
    (hh : Continuous h) (K0 τ c lam : ℝ) (hl0 : 0 < lam) :
    τ ^ 2 * ((1 - lam) * varU (uniformSphere n) g - (1 / lam) * c ^ 2 * varU (uniformSphere n) h) ≤
      varU (uniformSphere n) (fun x => K0 + τ * g x + τ * c * h x) ∧
    ∫ x, (K0 + τ * g x + τ * c * h x) ∂uniformSphere n =
      K0 + τ * ∫ x, g x ∂uniformSphere n + τ * c * ∫ x, h x ∂uniformSphere n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have ig := sph_int hn hg
  have ih := sph_int hn hh
  have hmean : ∫ x, (K0 + τ * g x + τ * c * h x) ∂uniformSphere n =
      K0 + τ * ∫ x, g x ∂uniformSphere n + τ * c * ∫ x, h x ∂uniformSphere n := by
    rw [integral_add (f := fun x => K0 + τ * g x) (g := fun x => τ * c * h x)
        ((integrable_const _).add (ig.const_mul _)) (ih.const_mul _),
      integral_add (f := fun _ => K0) (g := fun x => τ * g x)
        (integrable_const _) (ig.const_mul _), integral_const_mul, integral_const_mul]
    simp
  refine ⟨?_, hmean⟩
  unfold varU
  rw [hmean]
  set mg := ∫ x, g x ∂uniformSphere n
  set mh := ∫ x, h x ∂uniformSphere n
  have cg : Continuous fun x => (g x - mg) ^ 2 := (hg.sub continuous_const).pow 2
  have ch : Continuous fun x => (h x - mh) ^ 2 := (hh.sub continuous_const).pow 2
  have e : τ ^ 2 * ((1 - lam) * ∫ x, (g x - mg) ^ 2 ∂uniformSphere n -
      (1 / lam) * c ^ 2 * ∫ x, (h x - mh) ^ 2 ∂uniformSphere n) =
      ∫ x, τ ^ 2 * ((1 - lam) * (g x - mg) ^ 2 - (1 / lam) * c ^ 2 * (h x - mh) ^ 2)
        ∂uniformSphere n := by
    rw [integral_const_mul, integral_sub (((sph_int hn cg).const_mul _))
      ((sph_int hn ch).const_mul _), integral_const_mul, integral_const_mul]
  rw [e]
  apply integral_mono
  · exact sph_int hn (continuous_const.mul
      ((continuous_const.mul cg).sub (continuous_const.mul ch)))
  · exact sph_int hn ((((continuous_const.add (continuous_const.mul hg)).add
      (continuous_const.mul hh)).sub continuous_const).pow 2)
  · intro x
    show τ ^ 2 * ((1 - lam) * (g x - mg) ^ 2 - (1 / lam) * c ^ 2 * (h x - mh) ^ 2) ≤
      (K0 + τ * g x + τ * c * h x - (K0 + τ * mg + τ * c * mh)) ^ 2
    set G := g x - mg
    set Y := c * (h x - mh) with hY
    have h1 : 0 ≤ (lam * G + Y) ^ 2 / lam := by positivity
    have h2 : (lam * G + Y) ^ 2 / lam = lam * G ^ 2 + 2 * G * Y + Y ^ 2 / lam := by
      field_simp; ring
    have h3 : (1 / lam) * c ^ 2 * (h x - mh) ^ 2 = Y ^ 2 / lam := by rw [hY]; ring
    have key : (1 - lam) * G ^ 2 - Y ^ 2 / lam ≤ (G + Y) ^ 2 := by nlinarith [sq_nonneg Y]
    have e4 : (K0 + τ * g x + τ * c * h x - (K0 + τ * mg + τ * c * mh)) ^ 2 = τ ^ 2 * (G + Y) ^ 2 := by
      rw [hY]; ring
    rw [e4, h3]
    exact mul_le_mul_of_nonneg_left key (sq_nonneg _)

lemma FG_split (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (W : WIdx n → ℝ)
    (x : Fin n → ℝ) :
    FG (aU ℓ H u) H W x = FG ℓ 0 W x + FG (aU 0 H u) H W x := by
  unfold FG Phi aU
  simp only [Matrix.zero_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    add_mul, Finset.sum_add_distrib]
  ring

lemma FG_lin (ℓ : Fin n → ℝ) (W : WIdx n → ℝ) (x : Fin n → ℝ) :
    FG ℓ 0 W x = ∑ i, ℓ i * zv W (pf x) i := by
  unfold FG Phi
  simp

lemma FG_quad (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (W : WIdx n → ℝ) (x : Fin n → ℝ) :
    FG (aU 0 H u) H W x = ∑ i, (2 * ∑ j, H i j * u j) * zv W (pf x) i +
      ∑ i, ∑ j, H i j * zv W (pf x) i * zv W (pf x) j := by
  unfold FG Phi aU
  simp

/-- **The sphere quantities in terms of the Gaussian ones**, at one point `(u, W)`. -/
lemma pw_core (hn : 1 ≤ n) (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (H₀ H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) (sD D s : ℝ) (hsD : sD ^ 2 = D) (hD : D ≠ 0) (hℓ : ∀ i, ℓ₀ i = sD * ℓ i)
    (hHs : ∀ i j, H₀ i j = D * H i j) (u : Fin n → ℝ) (W : WIdx n → ℝ) (lam : ℝ) (hl0 : 0 < lam) :
    (sD * s) ^ 2 * ((1 - lam) * VG (aU ℓ H u) H W -
        (1 / lam) * (sD * s - 1) ^ 2 * VG (aU 0 H u) H W) ≤
      varU (uniformSphere n) (fun x => qfun f0 ℓ₀ H₀ (fun i => s * (u i + zv W (pf x) i))) ∧
    (∫ x, qfun f0 ℓ₀ H₀ (fun i => s * (u i + zv W (pf x) i)) ∂uniformSphere n) -
        (qfun f0 ℓ₀ H₀ (fun i => s * u i) + 3 / 2 / D * trH H₀) =
      (sD * s) * errG (aU ℓ H u) H W + (sD * s) * (sD * s - 1) * errG (aU 0 H u) H W +
        3 / 2 * trH H * ((sD * s) ^ 2 - 1) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  set τ := sD * s with hτ
  set K0 := qfun f0 ℓ₀ H₀ (fun i => s * u i) with hK0
  have hS : (fun x => qfun f0 ℓ₀ H₀ (fun i => s * (u i + zv W (pf x) i))) =
      fun x => K0 + τ * FG (aU ℓ H u) H W x + τ * (τ - 1) * FG (aU 0 H u) H W x := by
    funext x
    rw [qexp f0 ℓ₀ ℓ H₀ H hH sD D s hsD hℓ hHs u (zv W (pf x)), FG_split, FG_lin, FG_quad]
    ring
  have cg := cont_FG (aU ℓ H u) H W
  have ch := cont_FG (aU 0 H u) H W
  obtain ⟨hv, hm⟩ := varU_affine_lower hn cg ch K0 τ (τ - 1) lam hl0
  rw [hS]
  refine ⟨hv, ?_⟩
  rw [hm]
  have htr : trH H₀ = D * trH H := by
    unfold trH; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hHs i i
  unfold errG
  rw [htr]
  field_simp
  ring

end BstLean.Part78
