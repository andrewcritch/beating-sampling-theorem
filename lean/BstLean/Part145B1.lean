import BstLean.Part132Persp

/-!
# Part 145, bias of one ReLU layer, file `B1`: the tangent of `κ` with a remainder

This file has no probability. It has the pointwise tools for the bias bound `rF0_bias`
(file `Part145B2`).

* `kg ρ = (π − arccos ρ)/π`: the derivative of `κ`.
* `kappa_tangent_ge` (T1): `κ(ρ) ≥ κ(ρ₀) + kg(ρ₀)(ρ − ρ₀)` on `[−1, 1]` (convexity).
* `arccos_sub_le`: `|arccos x − arccos y| ≤ π·√(|x − y|/2)` on `[−1, 1]`.
* `kappa_tangent_le` (T2): `κ(ρ) ≤ κ(ρ₀) + kg(ρ₀)(ρ − ρ₀) + |ρ − ρ₀|·√(|ρ − ρ₀|/2)` on `[−1, 1]`.
* `persp_mono_left`: `p ↦ L_G(p, c)` is nondecreasing on `p ≥ |c|`.
* `persp_tangent_le`: the tangent plane of the perspective with a remainder.
* `rem_young`: the remainder is at most a quadratic expression (Young inequalities).
* `sqrt_mul_ge`: `√x·√y ≥ (x + y)/2 − (x − 1)² − (y − 1)²`.
* `persp_sqrt_lower`, `persp_sqrt_upper`: the two bounds of `L_κ(√x·√y, c)` that the
  probability argument integrates.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open Real Set
open BstLean.Part130 BstLean.Part132

/-- The derivative of `κ`: `kg ρ = (π − arccos ρ)/π`. -/
noncomputable def kg (ρ : ℝ) : ℝ := (π - Real.arccos ρ) / π

lemma kg_nonneg (ρ : ℝ) : 0 ≤ kg ρ := (kappa_deriv_bounds ρ).1

lemma kg_le_one (ρ : ℝ) : kg ρ ≤ 1 := (kappa_deriv_bounds ρ).2

/-- `κ(ρ) − kg(ρ)·ρ = √(1 − ρ²)/π`. -/
lemma kappa_sub_kg (ρ : ℝ) : kappa ρ - kg ρ * ρ = Real.sqrt (1 - ρ ^ 2) / π := by
  unfold kappa kg
  field_simp
  ring

/-- **(T1) The tangent of `κ` is below `κ`**: `κ(ρ) ≥ κ(ρ₀) + kg(ρ₀)(ρ − ρ₀)` on `[−1, 1]`. -/
theorem kappa_tangent_ge {ρ ρ₀ : ℝ} (hρ : ρ ∈ Icc (-1 : ℝ) 1) (hρ₀ : ρ₀ ∈ Icc (-1 : ℝ) 1) :
    kappa ρ₀ + kg ρ₀ * (ρ - ρ₀) ≤ kappa ρ := by
  rcases eq_or_lt_of_le hρ₀.2 with h1 | h1
  · rw [h1]
    have h := kGood_kappa.self_le hρ
    have e : kg 1 = 1 := by
      unfold kg
      rw [Real.arccos_one, sub_zero, div_self Real.pi_ne_zero]
    rw [e, kappa_one]
    linarith
  rcases eq_or_lt_of_le hρ₀.1 with h0 | h0
  · rw [← h0]
    have h := kGood_kappa.nonneg_on hρ
    have e : kg (-1) = 0 := by
      unfold kg
      rw [Real.arccos_neg_one, sub_self, zero_div]
    rw [e, kappa_neg_one]
    linarith
  have hd := hasDerivAt_kappa h0 h1
  rcases lt_trichotomy ρ ρ₀ with h | h | h
  · have hs := kappa_convexOn.slope_le_of_hasDerivAt hρ hρ₀ h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at hs
    unfold kg
    linarith
  · rw [h]
    simp
  · have hs := kappa_convexOn.le_slope_of_hasDerivAt hρ₀ hρ h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at hs
    unfold kg
    linarith

lemma arccos_sub_le_aux {x y : ℝ} (hx : -1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    Real.arccos x - Real.arccos y ≤ π * Real.sqrt ((y - x) / 2) := by
  have hp := Real.pi_pos
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : ℝ, θ₁ = Real.arccos x := ⟨_, rfl⟩
  obtain ⟨θ₂, hθ₂⟩ : ∃ θ₂ : ℝ, θ₂ = Real.arccos y := ⟨_, rfl⟩
  have h21 : θ₂ ≤ θ₁ := by rw [hθ₁, hθ₂]; exact Real.arccos_le_arccos hxy
  have h20 : 0 ≤ θ₂ := by rw [hθ₂]; exact Real.arccos_nonneg y
  have h1π : θ₁ ≤ π := by rw [hθ₁]; exact Real.arccos_le_pi x
  have ex : Real.cos θ₁ = x := by rw [hθ₁]; exact Real.cos_arccos hx (hxy.trans hy)
  have ey : Real.cos θ₂ = y := by rw [hθ₂]; exact Real.cos_arccos (hx.trans hxy) hy
  rw [← hθ₁, ← hθ₂]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (θ₁ - θ₂) / 2 := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = (θ₁ + θ₂) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ π / 2 := by rw [hδ]; linarith
  have hsd : 2 / π * δ ≤ Real.sin δ := Real.mul_le_sin hδ0 hδ1
  have hw0 : 0 ≤ 2 / π * δ := by positivity
  have hsσ : Real.sin δ ≤ Real.sin σ := by
    rcases le_total σ (π / 2) with h | h
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h (by rw [hδ, hσ]; linarith)
    · rw [← Real.sin_pi_sub σ]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
        (by rw [hδ, hσ]; linarith)
  have hcos : y - x = 2 * Real.sin σ * Real.sin δ := by
    have h := Real.cos_sub_cos θ₂ θ₁
    have e1 : (θ₂ + θ₁) / 2 = σ := by rw [hσ]; ring
    have e2 : (θ₂ - θ₁) / 2 = -δ := by rw [hδ]; ring
    rw [e1, e2, Real.sin_neg, ex, ey] at h
    rw [h]
    ring
  have hs0 : 0 ≤ Real.sin δ := hw0.trans hsd
  have hle : (2 / π * δ) ^ 2 ≤ (y - x) / 2 := by
    have h1 : (2 / π * δ) ^ 2 ≤ Real.sin δ ^ 2 := pow_le_pow_left₀ hw0 hsd 2
    have h2 : Real.sin δ ^ 2 ≤ Real.sin σ * Real.sin δ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hsσ hs0
    rw [hcos]
    linarith
  have hfin : 2 / π * δ ≤ Real.sqrt ((y - x) / 2) := Real.le_sqrt_of_sq_le hle
  have e : θ₁ - θ₂ = π * (2 / π * δ) := by
    rw [hδ]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hfin hp.le

/-- `|arccos x − arccos y| ≤ π·√(|x − y|/2)` on `[−1, 1]`. -/
theorem arccos_sub_le {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |Real.arccos x - Real.arccos y| ≤ π * Real.sqrt (|x - y| / 2) := by
  rcases le_total x y with h | h
  · have h1 := arccos_sub_le_aux hx.1 h hy.2
    have h2 := Real.arccos_le_arccos h
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), neg_sub]
    exact h1
  · have h1 := arccos_sub_le_aux hy.1 h hx.2
    have h2 := Real.arccos_le_arccos h
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), neg_sub]
    exact h1

/-- **(T2) The tangent of `κ` with a remainder of order `3/2`**:
`κ(ρ) ≤ κ(ρ₀) + kg(ρ₀)(ρ − ρ₀) + |ρ − ρ₀|·√(|ρ − ρ₀|/2)` on `[−1, 1]`. -/
theorem kappa_tangent_le {ρ ρ₀ : ℝ} (hρ : ρ ∈ Icc (-1 : ℝ) 1) (hρ₀ : ρ₀ ∈ Icc (-1 : ℝ) 1) :
    kappa ρ ≤ kappa ρ₀ + kg ρ₀ * (ρ - ρ₀) + |ρ - ρ₀| * Real.sqrt (|ρ - ρ₀| / 2) := by
  have hp := Real.pi_pos
  have h1 := kappa_tangent_ge hρ₀ hρ
  have hA := arccos_sub_le hρ hρ₀
  have e : kg ρ - kg ρ₀ = (Real.arccos ρ₀ - Real.arccos ρ) / π := by
    unfold kg
    field_simp
    ring
  have hk : |kg ρ - kg ρ₀| ≤ Real.sqrt (|ρ - ρ₀| / 2) := by
    rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_sub_comm]
    linarith
  have key : (kg ρ - kg ρ₀) * (ρ - ρ₀) ≤ |ρ - ρ₀| * Real.sqrt (|ρ - ρ₀| / 2) := by
    calc (kg ρ - kg ρ₀) * (ρ - ρ₀) ≤ |(kg ρ - kg ρ₀) * (ρ - ρ₀)| := le_abs_self _
      _ = |ρ - ρ₀| * |kg ρ - kg ρ₀| := by rw [abs_mul, mul_comm]
      _ ≤ |ρ - ρ₀| * Real.sqrt (|ρ - ρ₀| / 2) :=
          mul_le_mul_of_nonneg_left hk (abs_nonneg _)
  nlinarith [key, h1]

/-! ## The perspective function -/

/-- `p ↦ L_G(p, c)` is nondecreasing on `p ≥ |c|`. -/
lemma persp_mono_left {G : ℝ → ℝ} (hG : KGood G) {p p' c : ℝ} (hp : 0 ≤ p) (hc : |c| ≤ p)
    (hpp : p ≤ p') : persp G p c ≤ persp G p' c := by
  obtain ⟨a, b, ha0, ha1, hb0, hb1, heq, hab⟩ := hG.support (div_mem_Icc hp hc)
  have h1 : persp G p c = a * p + b * c := by
    rcases eq_or_lt_of_le hp with h | h
    · subst h
      have : c = 0 := abs_nonpos_iff.mp hc
      simp [persp, this]
    · exact persp_eq heq (by field_simp)
  have h2 := persp_ge hab (hp.trans hpp) (hc.trans hpp)
  have h3 := mul_le_mul_of_nonneg_left hpp ha0
  linarith

/-- **The tangent plane of the perspective of `κ` with a remainder.** The reference cosine is
`ρ₀ ∈ [0, 1]`; `d = c − ρ₀·p`. The remainder is `|d|·√|d|` for `p ≥ 1/2`, and it is at most
`|d|` for `p < 1/2`. -/
lemma persp_tangent_le {ρ₀ : ℝ} (h0 : 0 ≤ ρ₀) (h1 : ρ₀ ≤ 1) {p c : ℝ} (hp : 0 ≤ p)
    (hc : |c| ≤ p) :
    persp kappa p c ≤ (kappa ρ₀ - kg ρ₀ * ρ₀) * p + kg ρ₀ * c +
      (|c - ρ₀ * p| * Real.sqrt |c - ρ₀ * p| + |c - ρ₀ * p| * (2 * |p - 1|)) := by
  rcases eq_or_lt_of_le hp with h | h
  · subst h
    have hc0 : c = 0 := abs_nonpos_iff.mp hc
    subst hc0
    simp [persp]
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = c - ρ₀ * p := ⟨_, rfl⟩
  rw [← hd]
  have hmem := div_mem_Icc hp hc
  have hT := kappa_tangent_le hmem (ρ₀ := ρ₀) ⟨by linarith, h1⟩
  have ed : c / p - ρ₀ = d / p := by
    rw [hd]
    field_simp
  rw [ed, abs_div, abs_of_pos h] at hT
  have hmul := mul_le_mul_of_nonneg_left hT hp
  have e1 : p * (kappa ρ₀ + kg ρ₀ * (d / p) + |d| / p * Real.sqrt (|d| / p / 2)) =
      (kappa ρ₀ - kg ρ₀ * ρ₀) * p + kg ρ₀ * c + |d| * Real.sqrt (|d| / p / 2) := by
    rw [hd]
    field_simp
    ring
  rw [e1] at hmul
  have hcc := abs_le.mp hc
  have hρp : 0 ≤ ρ₀ * p := mul_nonneg h0 hp
  have hρp1 : ρ₀ * p ≤ p := by nlinarith
  have hd2 : |d| ≤ 2 * p := by
    rw [hd, abs_le]
    constructor <;> linarith
  have hd0 : 0 ≤ |d| := abs_nonneg d
  have hrem : |d| * Real.sqrt (|d| / p / 2) ≤
      |d| * Real.sqrt |d| + |d| * (2 * |p - 1|) := by
    rcases le_or_gt (1 / 2) p with hh | hh
    · have hle : Real.sqrt (|d| / p / 2) ≤ Real.sqrt |d| := by
        refine Real.sqrt_le_sqrt ?_
        rw [div_div, div_le_iff₀ (by positivity)]
        nlinarith
      have t1 := mul_le_mul_of_nonneg_left hle hd0
      have t2 : 0 ≤ |d| * (2 * |p - 1|) := by positivity
      linarith
    · have hle : Real.sqrt (|d| / p / 2) ≤ 1 := by
        rw [← Real.sqrt_one]
        refine Real.sqrt_le_sqrt ?_
        rw [div_div, div_le_one (by positivity)]
        linarith
      have h3 : 1 ≤ 2 * |p - 1| := by
        rw [abs_of_neg (by linarith)]
        linarith
      have t1 := mul_le_mul_of_nonneg_left hle hd0
      have t2 := mul_le_mul_of_nonneg_left h3 hd0
      have t3 : 0 ≤ |d| * Real.sqrt |d| := mul_nonneg hd0 (Real.sqrt_nonneg _)
      linarith
  unfold persp
  linarith

/-- **Young inequalities for the remainder**, with a free scale `r > 0`. -/
lemma rem_young {r : ℝ} (hr : 0 < r) (d p : ℝ) :
    |d| * Real.sqrt |d| + |d| * (2 * |p - 1|) ≤
      d ^ 2 * (3 / (4 * r) + 1) + r ^ 3 / 4 + (p - 1) ^ 2 := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt |d| := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = |d| := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hss : s * s = D := by rw [hs, hD]; exact Real.mul_self_sqrt (abs_nonneg d)
  have hD0 : 0 ≤ D := by rw [hD]; exact abs_nonneg d
  have hd2 : d ^ 2 = D ^ 2 := by rw [hD, sq_abs]
  rw [← hs, ← hD, hd2, ← sq_abs (p - 1)]
  have A1 : D * s ≤ D ^ 2 / (2 * r) + r * D / 2 := by
    rw [← hss]
    have h1 : 0 ≤ s ^ 2 * (s - r) ^ 2 / (2 * r) := by positivity
    have e : (s * s) ^ 2 / (2 * r) + r * (s * s) / 2 - s * s * s =
        s ^ 2 * (s - r) ^ 2 / (2 * r) := by
      field_simp
      ring
    linarith
  have A2 : r * D / 2 ≤ D ^ 2 / (4 * r) + r ^ 3 / 4 := by
    have h1 : 0 ≤ (D - r ^ 2) ^ 2 / (4 * r) := by positivity
    have e : D ^ 2 / (4 * r) + r ^ 3 / 4 - r * D / 2 = (D - r ^ 2) ^ 2 / (4 * r) := by
      field_simp
      ring
    linarith
  have A3 : D * (2 * |p - 1|) ≤ D ^ 2 + |p - 1| ^ 2 := by
    nlinarith [sq_nonneg (D - |p - 1|)]
  have e3 : D ^ 2 * (3 / (4 * r) + 1) = D ^ 2 / (2 * r) + D ^ 2 / (4 * r) + D ^ 2 := by
    field_simp
    ring
  rw [e3]
  linarith

lemma sqrt_mul_ge_aux {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s * s + t * t) / 2 - ((s * s - 1) ^ 2 + (t * t - 1) ^ 2) ≤ s * t := by
  have h1 : 0 ≤ (s - 1) ^ 2 * s * (s + 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hs) (by linarith)
  have h2 : 0 ≤ (t - 1) ^ 2 * t * (t + 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) ht) (by linarith)
  nlinarith [sq_nonneg (s + t - 2), h1, h2]

/-- `√x·√y ≥ (x + y)/2 − (x − 1)² − (y − 1)²` for `x, y ≥ 0`. -/
lemma sqrt_mul_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) / 2 - ((x - 1) ^ 2 + (y - 1) ^ 2) ≤ Real.sqrt x * Real.sqrt y := by
  have h := sqrt_mul_ge_aux (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  rwa [Real.mul_self_sqrt hx, Real.mul_self_sqrt hy] at h

/-- **The lower bound** of `L_κ(√x·√y, c)` from a supporting line `s ↦ a + b·s` of `κ` with
`a ≥ 0`. -/
lemma persp_sqrt_lower {a b : ℝ} (ha0 : 0 ≤ a)
    (hab : ∀ s ∈ Icc (-1 : ℝ) 1, a + b * s ≤ kappa s) {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hc : |c| ≤ Real.sqrt x * Real.sqrt y) :
    a * ((x + y) / 2 - ((x - 1) ^ 2 + (y - 1) ^ 2)) + b * c ≤
      persp kappa (Real.sqrt x * Real.sqrt y) c := by
  have h1 := persp_ge hab (mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)) hc
  have h2 := mul_le_mul_of_nonneg_left (sqrt_mul_ge hx hy) ha0
  linarith

/-- **The upper bound** of `L_κ(√x·√y, c)`: the tangent plane at the reference cosine `ρ₀`
in the variables `((x + y)/2, c)`, and a quadratic remainder with a free scale `r > 0`. -/
lemma persp_sqrt_upper {ρ₀ : ℝ} (h0 : 0 ≤ ρ₀) (h1 : ρ₀ ≤ 1) {r : ℝ} (hr : 0 < r) {x y c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : |c| ≤ Real.sqrt x * Real.sqrt y) :
    persp kappa (Real.sqrt x * Real.sqrt y) c ≤
      (kappa ρ₀ - kg ρ₀ * ρ₀) * ((x + y) / 2) + kg ρ₀ * c +
        (c - ρ₀ * ((x + y) / 2)) ^ 2 * (3 / (4 * r) + 1) + r ^ 3 / 4 +
        ((x - 1) ^ 2 + (y - 1) ^ 2) / 2 := by
  have hpp : Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.mul_self_sqrt hx,
      Real.mul_self_sqrt hy]
  have hm := persp_mono_left kGood_kappa
    (mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)) hc hpp
  have hT := persp_tangent_le h0 h1 (p := (x + y) / 2) (c := c) (by positivity) (hc.trans hpp)
  have hY := rem_young hr (c - ρ₀ * ((x + y) / 2)) ((x + y) / 2)
  have h3 : ((x + y) / 2 - 1) ^ 2 ≤ ((x - 1) ^ 2 + (y - 1) ^ 2) / 2 := by
    nlinarith [sq_nonneg (x - y)]
  linarith

end BstLean.Part145

open BstLean.Part145 in
#print axioms kappa_tangent_ge
open BstLean.Part145 in
#print axioms kappa_tangent_le
open BstLean.Part145 in
#print axioms persp_sqrt_lower
open BstLean.Part145 in
#print axioms persp_sqrt_upper
