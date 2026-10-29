import BstLean.Part82Defs
import BstLean.Part78Transfer

/-!
# Part 82: the transfer from the Gaussian model to the coefficient sphere, pointwise part

`(u, W)` is the Gaussian coefficient vector, `r = ‖(u, W)‖`, `s = 1/r`, `τ = √𝒟 s`. The original
cubic is `(f₀, ℓ₀, H₀, T₀)`; the scaled one is `ℓ = ℓ₀/√𝒟`, `H = H₀/𝒟`, `T = T₀/𝒟^{3/2}`.

* `cexp`: `f(s(u + z)) = f(su) + τ P₁ + τ² P₂ + τ³ P₃`, `P₁ = ℓ·z`, `P₂ = 2Hu·z + zᵀHz`,
  `P₃ = 3T[u,u,z] + 3T[u,z,z] + T[z,z,z]`; `P₁ + P₂ + P₃` is the Gaussian-model output.
* `pw_core3`: the variance and the error on the sphere in terms of the Gaussian quantities.
* `det_core3`: off the bad events there is no failure (real arithmetic).
-/

namespace BstLean.Part82

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)
open BstLean.Part78 (nsq frobH trH zv)

variable {n : ℕ}

/-! ## The pieces -/

/-- `2Hu`. -/
def a2U (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 2 * ∑ j, H i j * u j

/-- `3T[u,u,·]`. -/
def a3U (T : T3 n) (u : Fin n → ℝ) : Fin n → ℝ := fun i => 3 * ∑ j, ∑ k, T i j k * u j * u k

/-- `3T[u,·,·]`. -/
def H3U (T : T3 n) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => 3 * ∑ k, T i j k * u k

/-- The zero 3-tensor. -/
def zeroT : T3 n := fun _ _ _ => 0

def linZ (a z : Fin n → ℝ) : ℝ := ∑ i, a i * z i

def quadZ (H : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : ℝ := ∑ i, ∑ j, H i j * z i * z j

def cubZ (T : T3 n) (z : Fin n → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, T i j k * z i * z j * z k

lemma Phi3_eq {J : Type*} [Fintype J] (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (W : J × Fin n → ℝ) (p : J → ℝ) :
    Phi3 a H T W p = linZ a (zv W p) + quadZ H (zv W p) + cubZ T (zv W p) := rfl

lemma cfun_eq (f0 : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n)
    (y : Fin n → ℝ) : cfun f0 ℓ H T y = f0 + linZ ℓ y + quadZ H y + cubZ T y := rfl

lemma quadZ_zero (z : Fin n → ℝ) : quadZ (0 : Matrix (Fin n) (Fin n) ℝ) z = 0 := by
  simp [quadZ]

lemma cubZ_zero (z : Fin n → ℝ) : cubZ (zeroT : T3 n) z = 0 := by
  simp [cubZ, zeroT]

lemma sumT_swap12 {T : T3 n} (hT : SymT T) (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ k, T i j k * f i j k = ∑ i, ∑ j, ∑ k, T i j k * f j i k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [(hT j i k).1]

lemma sumT_swap23 {T : T3 n} (hT : SymT T) (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ k, T i j k * f i j k = ∑ i, ∑ j, ∑ k, T i j k * f i k j := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [(hT i k j).2]

lemma linZ_add (a u z : Fin n → ℝ) : linZ a (fun i => u i + z i) = linZ a u + linZ a z := by
  unfold linZ
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma quadZ_add (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (u z : Fin n → ℝ) :
    quadZ H (fun i => u i + z i) = quadZ H u + linZ (a2U H u) z + quadZ H z := by
  unfold quadZ linZ a2U
  have sw : ∑ i, ∑ j, H i j * u i * z j = ∑ i, ∑ j, H i j * u j * z i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.apply i j]
  have e2 : ∑ i, ∑ j, H i j * (u i + z i) * (u j + z j) =
      ∑ i, ∑ j, H i j * u i * u j + (∑ i, ∑ j, H i j * u i * z j)
        + (∑ i, ∑ j, H i j * u j * z i) + (∑ i, ∑ j, H i j * z i * z j) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ i, (2 * ∑ j, H i j * u j) * z i = 2 * ∑ i, ∑ j, H i j * u j * z i := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e2, e3, sw]
  ring

lemma cubZ_add (T : T3 n) (hT : SymT T) (u z : Fin n → ℝ) :
    cubZ T (fun i => u i + z i) =
      cubZ T u + linZ (a3U T u) z + quadZ (H3U T u) z + cubZ T z := by
  unfold cubZ linZ quadZ a3U H3U
  simp only [Matrix.of_apply]
  set A1 := ∑ i, ∑ j, ∑ k, T i j k * (z i * u j * u k) with hA1
  set B1 := ∑ i, ∑ j, ∑ k, T i j k * (z i * z j * u k) with hB1
  have hA2 : ∑ i, ∑ j, ∑ k, T i j k * (u i * z j * u k) = A1 := by
    rw [hA1, sumT_swap12 hT (fun i j k => z i * u j * u k)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have hA3 : ∑ i, ∑ j, ∑ k, T i j k * (u i * u j * z k) = A1 := by
    rw [← hA2, sumT_swap23 hT (fun i j k => u i * z j * u k)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have hB2 : ∑ i, ∑ j, ∑ k, T i j k * (z i * u j * z k) = B1 := by
    rw [hB1, sumT_swap23 hT (fun i j k => z i * z j * u k)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have hB3 : ∑ i, ∑ j, ∑ k, T i j k * (u i * z j * z k) = B1 := by
    rw [← hB2, sumT_swap12 hT (fun i j k => z i * u j * z k)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have e1 : ∑ i, ∑ j, ∑ k, T i j k * (u i + z i) * (u j + z j) * (u k + z k) =
      (∑ i, ∑ j, ∑ k, T i j k * u i * u j * u k) +
        ((∑ i, ∑ j, ∑ k, T i j k * (z i * u j * u k)) +
          (∑ i, ∑ j, ∑ k, T i j k * (u i * z j * u k)) +
          (∑ i, ∑ j, ∑ k, T i j k * (u i * u j * z k))) +
        ((∑ i, ∑ j, ∑ k, T i j k * (z i * z j * u k)) +
          (∑ i, ∑ j, ∑ k, T i j k * (z i * u j * z k)) +
          (∑ i, ∑ j, ∑ k, T i j k * (u i * z j * z k))) +
        (∑ i, ∑ j, ∑ k, T i j k * z i * z j * z k) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ i, (3 * ∑ j, ∑ k, T i j k * u j * u k) * z i = 3 * A1 := by
    rw [hA1]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have e3 : ∑ i, ∑ j, (3 * ∑ k, T i j k * u k) * z i * z j = 3 * B1 := by
    rw [hB1]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2, e3, hA2, hA3, hB2, hB3]
  ring

lemma linZ_scale (sD s : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (hℓ : ∀ i, ℓ₀ i = sD * ℓ i) (y : Fin n → ℝ) :
    linZ ℓ₀ (fun i => s * y i) = (sD * s) * linZ ℓ y := by
  unfold linZ
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hℓ]; ring

lemma quadZ_scale (sD D s : ℝ) (hsD : sD ^ 2 = D) (H₀ H : Matrix (Fin n) (Fin n) ℝ)
    (hHs : ∀ i j, H₀ i j = D * H i j) (y : Fin n → ℝ) :
    quadZ H₀ (fun i => s * y i) = (sD * s) ^ 2 * quadZ H y := by
  unfold quadZ
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hHs, ← hsD]; ring

lemma cubZ_scale (sD D s : ℝ) (hsD : sD ^ 2 = D) (T₀ T : T3 n)
    (hTs : ∀ i j k, T₀ i j k = D * sD * T i j k) (y : Fin n → ℝ) :
    cubZ T₀ (fun i => s * y i) = (sD * s) ^ 3 * cubZ T y := by
  unfold cubZ
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => by rw [hTs, ← hsD]; ring

/-- `f(s(u+z)) = f(su) + τ P₁ + τ² P₂ + τ³ P₃`, `τ = √𝒟 s`. -/
lemma cexp (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (H₀ H : Matrix (Fin n) (Fin n) ℝ) (T₀ T : T3 n)
    (hH : H.IsSymm) (hT : SymT T) (sD D s : ℝ) (hsD : sD ^ 2 = D)
    (hℓ : ∀ i, ℓ₀ i = sD * ℓ i) (hHs : ∀ i j, H₀ i j = D * H i j)
    (hTs : ∀ i j k, T₀ i j k = D * sD * T i j k) (u z : Fin n → ℝ) :
    cfun f0 ℓ₀ H₀ T₀ (fun i => s * (u i + z i)) =
      cfun f0 ℓ₀ H₀ T₀ (fun i => s * u i) + (sD * s) * linZ ℓ z +
        (sD * s) ^ 2 * (linZ (a2U H u) z + quadZ H z) +
        (sD * s) ^ 3 * (linZ (a3U T u) z + quadZ (H3U T u) z + cubZ T z) := by
  rw [cfun_eq, cfun_eq]
  rw [linZ_scale sD s ℓ₀ ℓ hℓ (fun i => u i + z i), linZ_scale sD s ℓ₀ ℓ hℓ u,
    quadZ_scale sD D s hsD H₀ H hHs (fun i => u i + z i), quadZ_scale sD D s hsD H₀ H hHs u,
    cubZ_scale sD D s hsD T₀ T hTs (fun i => u i + z i), cubZ_scale sD D s hsD T₀ T hTs u,
    linZ_add, quadZ_add H hH, cubZ_add T hT]
  ring

/-! ## The Gaussian-model output and its pieces -/

lemma linZ_aU3 (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (u z : Fin n → ℝ) :
    linZ (aU3 ℓ H T u) z = linZ ℓ z + linZ (a2U H u) z + linZ (a3U T u) z := by
  unfold linZ aU3 a2U a3U
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma quadZ_HU3 (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (u z : Fin n → ℝ) :
    quadZ (HU3 H T u) z = quadZ H z + quadZ (H3U T u) z := by
  unfold quadZ HU3 H3U
  simp only [Matrix.of_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The Gaussian-model output is the sum of the three pieces. -/
lemma FG3_split (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (u : Fin n → ℝ)
    (W : WIdx3 n → ℝ) (x : Fin n → ℝ) :
    FG3 (aU3 ℓ H T u) (HU3 H T u) T W x =
      FG3 ℓ 0 zeroT W x + FG3 (a2U H u) H zeroT W x + FG3 (a3U T u) (H3U T u) T W x := by
  unfold FG3
  simp only [Phi3_eq, linZ_aU3, quadZ_HU3, quadZ_zero, cubZ_zero]
  ring

lemma FG3_p1 (ℓ : Fin n → ℝ) (W : WIdx3 n → ℝ) (x : Fin n → ℝ) :
    FG3 ℓ 0 zeroT W x = linZ ℓ (zv W (pf3 x)) := by
  unfold FG3
  simp only [Phi3_eq, quadZ_zero, cubZ_zero]
  ring

lemma FG3_p2 (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (W : WIdx3 n → ℝ) (x : Fin n → ℝ) :
    FG3 (a2U H u) H zeroT W x = linZ (a2U H u) (zv W (pf3 x)) + quadZ H (zv W (pf3 x)) := by
  unfold FG3
  simp only [Phi3_eq, cubZ_zero]
  ring

lemma FG3_p3 (T : T3 n) (u : Fin n → ℝ) (W : WIdx3 n → ℝ) (x : Fin n → ℝ) :
    FG3 (a3U T u) (H3U T u) T W x = linZ (a3U T u) (zv W (pf3 x)) +
      quadZ (H3U T u) (zv W (pf3 x)) + cubZ T (zv W (pf3 x)) := by
  unfold FG3
  simp only [Phi3_eq]

lemma trH_zero : trH (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by simp [trH]

lemma trH_H3U (T : T3 n) (hT : SymT T) (u : Fin n → ℝ) :
    trH (H3U T u) = 3 * ∑ i, trT T i * u i := by
  unfold trH H3U trT
  simp only [Matrix.of_apply]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hT i i k).2, (hT i k i).1]

lemma trH_HU3 (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (hT : SymT T) (u : Fin n → ℝ) :
    trH (HU3 H T u) = trH H + 3 * ∑ i, trT T i * u i := by
  rw [← trH_H3U T hT u]
  unfold trH HU3 H3U
  simp only [Matrix.of_apply]
  rw [← Finset.sum_add_distrib]

/-! ## Variance of a sum -/

lemma varU_add_le (hn : 1 ≤ n) {g h : (Fin n → ℝ) → ℝ} (hg : Continuous g) (hh : Continuous h)
    (c₂ c₃ : ℝ) :
    varU (uniformSphere n) (fun x => c₂ * g x + c₃ * h x) ≤
      2 * c₂ ^ 2 * varU (uniformSphere n) g + 2 * c₃ ^ 2 * varU (uniformSphere n) h := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have ig := BstLean.Part78.sph_int hn hg
  have ih := BstLean.Part78.sph_int hn hh
  have hmean : ∫ x, (c₂ * g x + c₃ * h x) ∂uniformSphere n =
      c₂ * ∫ x, g x ∂uniformSphere n + c₃ * ∫ x, h x ∂uniformSphere n := by
    rw [integral_add (ig.const_mul _) (ih.const_mul _), integral_const_mul, integral_const_mul]
  unfold varU
  rw [hmean]
  set mg := ∫ x, g x ∂uniformSphere n
  set mh := ∫ x, h x ∂uniformSphere n
  have cg : Continuous fun x => (g x - mg) ^ 2 := (hg.sub continuous_const).pow 2
  have ch : Continuous fun x => (h x - mh) ^ 2 := (hh.sub continuous_const).pow 2
  have e : 2 * c₂ ^ 2 * ∫ x, (g x - mg) ^ 2 ∂uniformSphere n +
      2 * c₃ ^ 2 * ∫ x, (h x - mh) ^ 2 ∂uniformSphere n =
      ∫ x, (2 * c₂ ^ 2 * (g x - mg) ^ 2 + 2 * c₃ ^ 2 * (h x - mh) ^ 2) ∂uniformSphere n := by
    rw [integral_add ((BstLean.Part78.sph_int hn cg).const_mul _)
      ((BstLean.Part78.sph_int hn ch).const_mul _), integral_const_mul, integral_const_mul]
  rw [e]
  apply integral_mono
  · exact BstLean.Part78.sph_int hn ((((continuous_const.mul hg).add
      (continuous_const.mul hh)).sub continuous_const).pow 2)
  · exact BstLean.Part78.sph_int hn ((continuous_const.mul cg).add (continuous_const.mul ch))
  · intro x
    show (c₂ * g x + c₃ * h x - (c₂ * mg + c₃ * mh)) ^ 2 ≤
      2 * c₂ ^ 2 * (g x - mg) ^ 2 + 2 * c₃ ^ 2 * (h x - mh) ^ 2
    nlinarith [sq_nonneg (c₂ * (g x - mg) - c₃ * (h x - mh))]

/-! ## The sphere quantities in terms of the Gaussian ones -/

/-- **The sphere quantities in terms of the Gaussian ones**, at one point `(u, W)`. -/
lemma pw_core3 (hn : 1 ≤ n) (hR : RegIface3 n) (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ)
    (H₀ H : Matrix (Fin n) (Fin n) ℝ) (T₀ T : T3 n) (hH : H.IsSymm) (hT : SymT T)
    (sD D s : ℝ) (hsD : sD ^ 2 = D) (hD : D ≠ 0)
    (hℓ : ∀ i, ℓ₀ i = sD * ℓ i) (hHs : ∀ i j, H₀ i j = D * H i j)
    (hTs : ∀ i j k, T₀ i j k = D * sD * T i j k)
    (u : Fin n → ℝ) (W : WIdx3 n → ℝ) (lam : ℝ) (hl0 : 0 < lam) :
    (sD * s) ^ 2 * ((1 - lam) * VG3 (aU3 ℓ H T u) (HU3 H T u) T W -
        (2 / lam) * ((sD * s - 1) ^ 2 * VG3 (a2U H u) H zeroT W +
          ((sD * s) ^ 2 - 1) ^ 2 * VG3 (a3U T u) (H3U T u) T W)) ≤
      varU (uniformSphere n)
        (fun x => cfun f0 ℓ₀ H₀ T₀ (fun i => s * (u i + zv W (pf3 x) i))) ∧
    (∫ x, cfun f0 ℓ₀ H₀ T₀ (fun i => s * (u i + zv W (pf3 x) i)) ∂uniformSphere n) -
        (cfun f0 ℓ₀ H₀ T₀ (fun i => s * u i) +
          5 / 3 / D * (trH H₀ + 3 * ∑ i, trT T₀ i * (s * u i))) =
      (sD * s) * errG3 (aU3 ℓ H T u) (HU3 H T u) T W +
        (sD * s) * (sD * s - 1) * errG3 (a2U H u) H zeroT W +
        (sD * s) * ((sD * s) ^ 2 - 1) * errG3 (a3U T u) (H3U T u) T W +
        5 / 3 * trH H * ((sD * s) ^ 2 - 1) +
        5 * (∑ i, trT T i * u i) * (sD * s) * ((sD * s) ^ 2 - 1) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  set τ := sD * s with hτ
  set K0 := cfun f0 ℓ₀ H₀ T₀ (fun i => s * u i) with hK0
  set g := FG3 (aU3 ℓ H T u) (HU3 H T u) T W with hg
  set h2 := FG3 (a2U H u) H zeroT W with hh2
  set h3 := FG3 (a3U T u) (H3U T u) T W with hh3
  have cg : Continuous g := (hR T).2.2 _ _ _
  have ch2 : Continuous h2 := (hR zeroT).2.2 _ _ _
  have ch3 : Continuous h3 := (hR T).2.2 _ _ _
  set hh : (Fin n → ℝ) → ℝ := fun x => (τ - 1) * h2 x + (τ ^ 2 - 1) * h3 x with hhh
  have chh : Continuous hh := (continuous_const.mul ch2).add (continuous_const.mul ch3)
  have hS : (fun x => cfun f0 ℓ₀ H₀ T₀ (fun i => s * (u i + zv W (pf3 x) i))) =
      fun x => K0 + τ * g x + τ * 1 * hh x := by
    funext x
    rw [cexp f0 ℓ₀ ℓ H₀ H T₀ T hH hT sD D s hsD hℓ hHs hTs u (zv W (pf3 x))]
    simp only [hg, hh2, hh3, hhh, FG3_split, FG3_p1, FG3_p2, FG3_p3]
    ring
  obtain ⟨hv, hm⟩ := BstLean.Part78.varU_affine_lower hn cg chh K0 τ 1 lam hl0
  have hvh := varU_add_le hn ch2 ch3 (τ - 1) (τ ^ 2 - 1)
  rw [hS]
  refine ⟨le_trans ?_ hv, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg τ)
    have h1 : (1 / lam) * 1 ^ 2 * varU (uniformSphere n) hh ≤
        (2 / lam) * ((τ - 1) ^ 2 * varU (uniformSphere n) h2 +
          (τ ^ 2 - 1) ^ 2 * varU (uniformSphere n) h3) := by
      have h0 : 0 ≤ 1 / lam := by positivity
      have := mul_le_mul_of_nonneg_left hvh h0
      refine le_trans (le_of_eq (by ring)) (this.trans (le_of_eq ?_))
      field_simp
    show (1 - lam) * varU (uniformSphere n) g - (2 / lam) * ((τ - 1) ^ 2 *
      varU (uniformSphere n) h2 + (τ ^ 2 - 1) ^ 2 * varU (uniformSphere n) h3) ≤
      (1 - lam) * varU (uniformSphere n) g - (1 / lam) * 1 ^ 2 * varU (uniformSphere n) hh
    linarith
  · rw [hm]
    have ih2 := BstLean.Part78.sph_int hn ch2
    have ih3 := BstLean.Part78.sph_int hn ch3
    have hmh : ∫ x, hh x ∂uniformSphere n =
        (τ - 1) * ∫ x, h2 x ∂uniformSphere n + (τ ^ 2 - 1) * ∫ x, h3 x ∂uniformSphere n := by
      rw [hhh, integral_add (ih2.const_mul _) (ih3.const_mul _), integral_const_mul,
        integral_const_mul]
    rw [hmh]
    have htr : trH H₀ = D * trH H := by
      unfold trH; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hHs i i
    have htrT : ∀ i, trT T₀ i = D * sD * trT T i := by
      intro i; unfold trT; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => hTs i j j
    have hbu : ∑ i, trT T₀ i * (s * u i) = D * τ * ∑ i, trT T i * u i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [htrT, hτ]; ring
    unfold errG3
    rw [htr, hbu, trH_HU3 H T hT u, trH_H3U T hT u]
    field_simp
    ring

/-! ## The deterministic core -/

lemma two_sq (A B : ℝ) (η : ℝ) (hη : 0 < η) :
    (A + B) ^ 2 ≤ (1 + η) * A ^ 2 + (1 + 1 / η) * B ^ 2 := by
  have h1 : 0 ≤ (η * A - B) ^ 2 / η := by positivity
  have h2 : (η * A - B) ^ 2 / η = η * A ^ 2 - 2 * A * B + B ^ 2 / η := by
    field_simp; ring
  have h3 : (1 + 1 / η) * B ^ 2 = B ^ 2 + B ^ 2 / η := by ring
  rw [h3]
  nlinarith

lemma four_sq (A B C E : ℝ) : (A + B + C + E) ^ 2 ≤ 4 * (A ^ 2 + B ^ 2 + C ^ 2 + E ^ 2) := by
  nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - E), sq_nonneg (B - C),
    sq_nonneg (B - E), sq_nonneg (C - E)]

/-- **Deterministic core.** -/
lemma det_core3 {τ VS VGa V2 V3 eS eG e2 e3 trh bu Wfv δ ε ε₁ κ lam η BV BE BT BB : ℝ}
    (hτ : |τ - 1| ≤ δ) (hδ : δ ≤ 1 / 100)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hη : 0 < η) (hV2 : 0 ≤ V2) (hV3 : 0 ≤ V3)
    (hW : 0 ≤ Wfv)
    (hVS : τ ^ 2 * ((1 - lam) * VGa -
      (2 / lam) * ((τ - 1) ^ 2 * V2 + (τ ^ 2 - 1) ^ 2 * V3)) ≤ VS)
    (heS : eS = τ * eG + τ * (τ - 1) * e2 + τ * (τ ^ 2 - 1) * e3 + 5 / 3 * trh * (τ ^ 2 - 1) +
      5 * bu * τ * (τ ^ 2 - 1))
    (h1 : κ * Wfv ≤ VGa) (h4 : eG ^ 2 ≤ ε₁ ^ 2 * Wfv)
    (hY : V2 + 5 * V3 ≤ BV * Wfv) (hE : e2 ^ 2 + 5 * e3 ^ 2 ≤ BE * Wfv)
    (hT : trh ^ 2 ≤ BT * Wfv) (hB : bu ^ 2 ≤ BB * Wfv)
    (hnum : (1 + η) * ε₁ ^ 2 + (1 + 1 / η) * 4 * δ ^ 2 * (BE + 12 * BT + 102 * BB) +
      ε ^ 2 * (2 / lam) * δ ^ 2 * BV ≤ ε ^ 2 * (1 - lam) * κ) :
    eS ^ 2 ≤ ε ^ 2 * VS := by
  obtain ⟨hτl, hτu⟩ := abs_le.mp hτ
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hτ
  have hτlo : 99 / 100 ≤ τ := by linarith
  have hτhi : τ ≤ 101 / 100 := by linarith
  have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg _
  have hd2 : (τ - 1) ^ 2 ≤ δ ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hp1 : (τ + 1) ^ 2 ≤ 405 / 100 := by
    have h := mul_le_mul (show τ + 1 ≤ 201 / 100 by linarith) (show τ + 1 ≤ 201 / 100 by linarith)
      (by linarith) (by norm_num)
    rw [sq]; linarith
  have hd4s : (τ ^ 2 - 1) ^ 2 ≤ 405 / 100 * δ ^ 2 := by
    have e : (τ ^ 2 - 1) ^ 2 = (τ + 1) ^ 2 * (τ - 1) ^ 2 := by ring
    rw [e]
    exact mul_le_mul hp1 hd2 (sq_nonneg _) (by norm_num)
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg _
  have hd4 : (τ ^ 2 - 1) ^ 2 ≤ 5 * δ ^ 2 := by linarith
  have hτ2lo : 98 / 100 ≤ τ ^ 2 := by
    have h := mul_le_mul hτlo hτlo (by norm_num) (by linarith)
    rw [sq]; linarith
  have hd4' : (τ ^ 2 - 1) ^ 2 ≤ 12 * τ ^ 2 * (9 / 25 * δ ^ 2) := by
    have := mul_le_mul_of_nonneg_right hτ2lo hδ2
    linarith
  -- the remainder of the error
  set R := τ * (τ - 1) * e2 + τ * (τ ^ 2 - 1) * e3 + 5 / 3 * trh * (τ ^ 2 - 1) +
    5 * bu * τ * (τ ^ 2 - 1) with hRdef
  have e2nn : 0 ≤ e2 ^ 2 := sq_nonneg _
  have e3nn : 0 ≤ e3 ^ 2 := sq_nonneg _
  have hR : R ^ 2 ≤ τ ^ 2 * (4 * δ ^ 2 * (BE + 12 * BT + 102 * BB) * Wfv) := by
    have h4s := four_sq (τ * (τ - 1) * e2) (τ * (τ ^ 2 - 1) * e3) (5 / 3 * trh * (τ ^ 2 - 1))
      (5 * bu * τ * (τ ^ 2 - 1))
    have t1 : (τ * (τ - 1) * e2) ^ 2 ≤ τ ^ 2 * (δ ^ 2 * e2 ^ 2) := by
      have : (τ * (τ - 1) * e2) ^ 2 = τ ^ 2 * ((τ - 1) ^ 2 * e2 ^ 2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd2 e2nn) hτ2
    have t2 : (τ * (τ ^ 2 - 1) * e3) ^ 2 ≤ τ ^ 2 * (δ ^ 2 * (5 * e3 ^ 2)) := by
      have : (τ * (τ ^ 2 - 1) * e3) ^ 2 = τ ^ 2 * ((τ ^ 2 - 1) ^ 2 * e3 ^ 2) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left _ hτ2
      have := mul_le_mul_of_nonneg_right hd4 e3nn
      linarith
    have t3 : (5 / 3 * trh * (τ ^ 2 - 1)) ^ 2 ≤ τ ^ 2 * (δ ^ 2 * (12 * (BT * Wfv))) := by
      have : (5 / 3 * trh * (τ ^ 2 - 1)) ^ 2 = 25 / 9 * ((τ ^ 2 - 1) ^ 2 * trh ^ 2) := by ring
      rw [this]
      have m1 := mul_le_mul hd4' hT (sq_nonneg _) (by positivity)
      linarith [m1]
    have t4 : (5 * bu * τ * (τ ^ 2 - 1)) ^ 2 ≤ τ ^ 2 * (δ ^ 2 * (102 * (BB * Wfv))) := by
      have : (5 * bu * τ * (τ ^ 2 - 1)) ^ 2 = τ ^ 2 * (25 * ((τ ^ 2 - 1) ^ 2 * bu ^ 2)) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left _ hτ2
      have hBB : 0 ≤ BB * Wfv := le_trans (sq_nonneg _) hB
      have m1 := mul_le_mul hd4s hB (sq_nonneg _) (by positivity)
      linarith [m1, mul_nonneg hδ2 hBB]
    have t12 : τ ^ 2 * (δ ^ 2 * e2 ^ 2) + τ ^ 2 * (δ ^ 2 * (5 * e3 ^ 2)) ≤
        τ ^ 2 * (δ ^ 2 * (BE * Wfv)) := by
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (sq_nonneg δ)) hτ2
      linarith [this]
    calc R ^ 2 ≤ 4 * ((τ * (τ - 1) * e2) ^ 2 + (τ * (τ ^ 2 - 1) * e3) ^ 2 +
          (5 / 3 * trh * (τ ^ 2 - 1)) ^ 2 + (5 * bu * τ * (τ ^ 2 - 1)) ^ 2) := h4s
      _ ≤ 4 * (τ ^ 2 * (δ ^ 2 * (BE * Wfv)) + τ ^ 2 * (δ ^ 2 * (12 * (BT * Wfv))) +
          τ ^ 2 * (δ ^ 2 * (102 * (BB * Wfv)))) := by linarith
      _ = τ ^ 2 * (4 * δ ^ 2 * (BE + 12 * BT + 102 * BB) * Wfv) := by ring
  have key : eS ^ 2 ≤ (1 + η) * (τ ^ 2 * eG ^ 2) + (1 + 1 / η) * R ^ 2 := by
    have : eS = τ * eG + R := by rw [heS, hRdef]; ring
    have h := two_sq (τ * eG) R η hη
    have e1 : (τ * eG) ^ 2 = τ ^ 2 * eG ^ 2 := by ring
    rw [e1] at h
    rw [this]; exact h
  -- the variance
  have hYv : (τ - 1) ^ 2 * V2 + (τ ^ 2 - 1) ^ 2 * V3 ≤ δ ^ 2 * (BV * Wfv) := by
    have a1 := mul_le_mul_of_nonneg_right hd2 hV2
    have a2 := mul_le_mul_of_nonneg_right hd4 hV3
    have a3 := mul_le_mul_of_nonneg_left hY (sq_nonneg δ)
    linarith
  have hVS' : τ ^ 2 * ((1 - lam) * (κ * Wfv) - (2 / lam) * (δ ^ 2 * (BV * Wfv))) ≤ VS := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hτ2) hVS
    have b1 : (1 - lam) * (κ * Wfv) ≤ (1 - lam) * VGa :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have b2 : (2 / lam) * ((τ - 1) ^ 2 * V2 + (τ ^ 2 - 1) ^ 2 * V3) ≤
        (2 / lam) * (δ ^ 2 * (BV * Wfv)) :=
      mul_le_mul_of_nonneg_left hYv (by positivity)
    linarith
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  have hsc : (1 + η) * (ε₁ ^ 2 * Wfv) +
      (1 + 1 / η) * (4 * δ ^ 2 * (BE + 12 * BT + 102 * BB) * Wfv) ≤
      ε ^ 2 * ((1 - lam) * (κ * Wfv) - (2 / lam) * (δ ^ 2 * (BV * Wfv))) := by
    have a1 := mul_le_mul_of_nonneg_right hnum hW
    linarith [a1]
  calc eS ^ 2 ≤ (1 + η) * (τ ^ 2 * eG ^ 2) + (1 + 1 / η) * R ^ 2 := key
    _ ≤ τ ^ 2 * ((1 + η) * (ε₁ ^ 2 * Wfv) +
          (1 + 1 / η) * (4 * δ ^ 2 * (BE + 12 * BT + 102 * BB) * Wfv)) := by
        have q1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hτ2)
          (by linarith : (0 : ℝ) ≤ 1 + η)
        have q2 := mul_le_mul_of_nonneg_left hR hη1
        linarith [q1, q2]
    _ ≤ τ ^ 2 * (ε ^ 2 * ((1 - lam) * (κ * Wfv) - (2 / lam) * (δ ^ 2 * (BV * Wfv)))) :=
        mul_le_mul_of_nonneg_left hsc hτ2
    _ = ε ^ 2 * (τ ^ 2 * ((1 - lam) * (κ * Wfv) - (2 / lam) * (δ ^ 2 * (BV * Wfv)))) := by ring
    _ ≤ ε ^ 2 * VS := mul_le_mul_of_nonneg_left hVS' (sq_nonneg _)

end BstLean.Part82

#print axioms BstLean.Part82.pw_core3
#print axioms BstLean.Part82.det_core3
