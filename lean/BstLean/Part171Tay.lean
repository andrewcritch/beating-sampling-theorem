import BstLean.Part154MFcalc
import BstLean.Part170All

/-!
# Part 171 (file `Tay`): the Taylor remainders of `G` and `G₂` with a general step

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, the Taylor terms `T₁–T₅` (`t7:p08:T`) and `U₁–U₅` (`t7:p08:U`).
`G(a, v) = E ReLU(a + √v Z) = psiS √v a` and `G₂(a, v) = E ReLU(a + √v Z)² = G2 √v a`.

* **`G_taylor_gen`**: on `v ≥ s²/2`,
  `|G(a + d, v) − G(a, s²) − Φ(a/s)d − φ(a/s)(v − s²)/(2s)| ≤
   ½(√2φ(0)d²/s + 2φ(1)|d||v − s²|/s² + φ(0)(v − s²)²/(√2 s³))`
  (Part 154's `G_taylor` has the step `d = (β − 1)a`).
* **`G_rough_gen`**: for `v ≥ 0`, the same remainder is `≤ 2|d| + (3/2)φ(0)|v − s²|/s`.
* **`G2_closed`**: `G₂(a, s²) = (a² + s²)Φ(a/s) + a s φ(a/s)` for `s > 0`.
* **`G2_taylor`**: on `v ≥ s²/2`,
  `|G₂(a + d, v) − G₂(a, s²) − 2ψ_s(a)d − Φ(a/s)(v − s²)| ≤
   d² + √2φ(0)|d||v − s²|/s + φ(1)(v − s²)²/(2s²)`.
* **`G2_rough`**: for `v ≥ 0`, the same remainder is
  `≤ (a + d)² + a² + 2(|a| + s)|d| + 2v + 2s²`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter
open BstLean.Part130 (relu)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG hasDerivAt_PhiG hasDerivAt_phiG phiG_pos PhiG_pos PhiG_le_one)
open BstLean.Part154 (phiG_le_zero abs_mul_phiG_le abs_sq_sub_one_mul_phiG_le taylor2 sqrt_lower
  psiS_closed phiG_zero_eq)
open BstLean.Part170 (G2)

/-- **The second-order Taylor bound of `G`** with a general step `d`, on `v ≥ s²/2`. -/
theorem G_taylor_gen {s v a d : ℝ} (hs : 0 < s) (hv : s ^ 2 / 2 ≤ v) :
    |psiS (√v) (a + d) - psiS s a -
        (PhiG (a / s) * d + phiG (a / s) / (2 * s) * (v - s ^ 2))| ≤
      1 / 2 * (√2 * phiG 0 / s * d ^ 2 +
        2 * phiG 1 / s ^ 2 * (|d| * |v - s ^ 2|) +
        phiG 0 / (√2 * s ^ 3) * (v - s ^ 2) ^ 2) := by
  have hv0 : 0 < v := by nlinarith [sq_pos_of_pos hs]
  set r := √2 with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set dτ := d with hdτ
  set dv := v - s ^ 2 with hdv
  let w : ℝ → ℝ := fun t => s ^ 2 + t * dv
  let u : ℝ → ℝ := fun t => √(w t)
  let τ : ℝ → ℝ := fun t => a + t * dτ
  let z : ℝ → ℝ := fun t => τ t / u t
  let H : ℝ → ℝ := fun t => τ t * PhiG (z t) + u t * phiG (z t)
  let H1 : ℝ → ℝ := fun t => PhiG (z t) * dτ + phiG (z t) * (dv / (2 * u t))
  let H2 : ℝ → ℝ := fun t => phiG (z t) / u t * dτ ^ 2 - z t * phiG (z t) / u t ^ 2 * (dτ * dv) +
    (z t ^ 2 - 1) * phiG (z t) / (4 * u t ^ 3) * dv ^ 2
  have hw : ∀ t ∈ Set.Icc (0 : ℝ) 1, s ^ 2 / 2 ≤ w t := by
    intro t ht
    have e : w t = (1 - t) * s ^ 2 + t * v := by simp only [w, hdv]; ring
    rw [e]; nlinarith [ht.1, ht.2, sq_pos_of_pos hs]
  have hw0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < w t := fun t ht => by
    have := hw t ht; nlinarith [sq_pos_of_pos hs]
  have hu0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < u t := fun t ht => Real.sqrt_pos.mpr (hw0 t ht)
  have hu2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, u t ^ 2 = w t := fun t ht => Real.sq_sqrt (hw0 t ht).le
  have dw : ∀ t, HasDerivAt w dv t := by
    intro t
    have := ((hasDerivAt_id t).mul_const dv).const_add (s ^ 2)
    simpa [w] using this
  have dτ' : ∀ t, HasDerivAt τ dτ t := by
    intro t
    have := ((hasDerivAt_id t).mul_const dτ).const_add a
    simpa [τ] using this
  have du : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (dv / (2 * u t)) t := by
    intro t ht
    have := (Real.hasDerivAt_sqrt (hw0 t ht).ne').comp t (dw t)
    have e : dv / (2 * u t) = 1 / (2 * √(w t)) * dv := by simp only [u]; ring
    rw [e]; exact this
  have dz : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt z (dτ / u t - z t * dv / (2 * u t ^ 2)) t := by
    intro t ht
    have := (dτ' t).div (du t ht) (hu0 t ht).ne'
    convert this using 1
    have := (hu0 t ht).ne'
    simp only [z]; field_simp
  have dΦ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => PhiG (z t)) (phiG (z t) * (dτ / u t - z t * dv / (2 * u t ^ 2))) t :=
    fun t ht => (hasDerivAt_PhiG (z t)).comp t (dz t ht)
  have dφ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => phiG (z t))
        (-(z t * phiG (z t)) * (dτ / u t - z t * dv / (2 * u t ^ 2))) t :=
    fun t ht => (hasDerivAt_phiG (z t)).comp t (dz t ht)
  have dH : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt H (H1 t) t := by
    intro t ht
    have := ((dτ' t).mul (dΦ t ht)).add ((du t ht).mul (dφ t ht))
    convert this using 1
    have h0 := (hu0 t ht).ne'
    have hz : τ t = z t * u t := by simp only [z]; field_simp
    simp only [H1]; rw [hz]; field_simp; ring
  have dH1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt H1 (H2 t) t := by
    intro t ht
    have h0 := (hu0 t ht).ne'
    have dq : HasDerivAt (fun t => dv / (2 * u t)) (-(dv * (2 * (dv / (2 * u t)))) / (2 * u t) ^ 2) t := by
      have := (hasDerivAt_const t dv).div ((du t ht).const_mul 2) (by positivity)
      convert this using 1
      simp
    have := ((dΦ t ht).mul_const dτ).add ((dφ t ht).mul dq)
    convert this using 1
    simp only [H2]; field_simp; ring
  set M := r * phiG 0 / s * d ^ 2 +
        2 * phiG 1 / s ^ 2 * (|d| * |dv|) +
        phiG 0 / (r * s ^ 3) * dv ^ 2 with hM
  have hφ0 : 0 < phiG 0 := phiG_pos 0
  have hφ1 : 0 < phiG 1 := phiG_pos 1
  have bM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |H2 t| ≤ M := by
    intro t ht
    have hut := hu0 t ht
    have hsu : s ≤ u t * r := sqrt_lower hs (hw t ht)
    have hu2' := hu2 t ht
    have hwt := hw t ht
    have hφz := phiG_pos (z t)
    have cA : |phiG (z t) / u t| ≤ r * phiG 0 / s := by
      rw [abs_of_pos (by positivity), div_le_div_iff₀ hut hs]
      have := phiG_le_zero (z t)
      calc phiG (z t) * s ≤ phiG 0 * (u t * r) := by gcongr
        _ = r * phiG 0 * u t := by ring
    have cB : |z t * phiG (z t) / u t ^ 2| ≤ 2 * phiG 1 / s ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos hφz, abs_of_pos (by positivity : 0 < u t ^ 2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have := abs_mul_phiG_le (z t)
      have h2 : s ^ 2 ≤ 2 * u t ^ 2 := by linarith
      calc |z t| * phiG (z t) * s ^ 2 ≤ phiG 1 * (2 * u t ^ 2) := by
            gcongr
        _ = 2 * phiG 1 * u t ^ 2 := by ring
    have cC : |(z t ^ 2 - 1) * phiG (z t) / (4 * u t ^ 3)| ≤ phiG 0 / (r * s ^ 3) := by
      rw [abs_div, abs_mul, abs_of_pos hφz, abs_of_pos (by positivity : 0 < 4 * u t ^ 3),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have := abs_sq_sub_one_mul_phiG_le (z t)
      have h3 : r * s ^ 3 ≤ 4 * u t ^ 3 := by
        have h4 : s ^ 3 ≤ (u t * r) ^ 3 := pow_le_pow_left₀ hs.le hsu 3
        have e : (u t * r) ^ 3 = 2 * r * u t ^ 3 := by linear_combination (r * u t ^ 3) * hr2
        have e2 : 4 * u t ^ 3 = r * (2 * r * u t ^ 3) := by linear_combination (-2 * u t ^ 3) * hr2
        rw [e2]; rw [e] at h4; gcongr
      exact mul_le_mul this h3 (by positivity) hφ0.le
    have e1 : |dτ ^ 2| = d ^ 2 := by rw [abs_of_nonneg (sq_nonneg _)]
    have e2 : |dτ * dv| = |d| * |dv| := by rw [abs_mul]
    have e3 : |dv ^ 2| = dv ^ 2 := abs_of_nonneg (sq_nonneg _)
    have key : |H2 t| ≤ (|phiG (z t) / u t| * |dτ ^ 2|) +
        (|z t * phiG (z t) / u t ^ 2| * |dτ * dv|) +
        (|(z t ^ 2 - 1) * phiG (z t) / (4 * u t ^ 3)| * |dv ^ 2|) := by
      simp only [H2, ← abs_mul]
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    rw [e1, e2, e3] at key
    have hA := mul_le_mul_of_nonneg_right cA (by positivity : (0 : ℝ) ≤ d ^ 2)
    have hB := mul_le_mul_of_nonneg_right cB (by positivity : (0 : ℝ) ≤ |d| * |dv|)
    have hC := mul_le_mul_of_nonneg_right cC (by positivity : (0 : ℝ) ≤ dv ^ 2)
    rw [hM]; linarith
  have T := taylor2 dH dH1 bM
  have eu0 : u 0 = s := by simp only [u, w]; rw [zero_mul, add_zero]; exact Real.sqrt_sq hs.le
  have eu1 : u 1 = √v := by simp only [u, w, hdv]; congr 1; ring
  have eτ0 : τ 0 = a := by simp [τ]
  have eτ1 : τ 1 = a + d := by simp only [τ, hdτ]; ring
  have eH0 : H 0 = psiS s a := by
    simp only [H, z]; rw [eu0, eτ0]; exact (psiS_closed hs a).symm
  have eH1 : H 1 = psiS (√v) (a + d) := by
    simp only [H, z]; rw [eu1, eτ1]; exact (psiS_closed (Real.sqrt_pos.mpr hv0) _).symm
  have eH10 : H1 0 = PhiG (a / s) * d + phiG (a / s) / (2 * s) * dv := by
    simp only [H1, z]; rw [eu0, eτ0]; ring
  rw [eH0, eH1, eH10] at T
  calc _ ≤ M / 2 := T
    _ = _ := by ring

/-- **The bound of the remainder of `G` off the good set** (`v ≥ 0` only). -/
theorem G_rough_gen {s v a d : ℝ} (hs : 0 < s) (hv : 0 ≤ v) :
    |psiS (√v) (a + d) - psiS s a -
        (PhiG (a / s) * d + phiG (a / s) / (2 * s) * (v - s ^ 2))| ≤
      2 * |d| + 3 / 2 * phiG 0 / s * |v - s ^ 2| := by
  have hφ0 : 0 < phiG 0 := phiG_pos 0
  have hu : 0 ≤ √v := Real.sqrt_nonneg v
  have hu2 : √v ^ 2 = v := Real.sq_sqrt hv
  have i1 : |√v - s| ≤ |v - s ^ 2| / s := by
    rw [le_div_iff₀ hs]
    have e : v - s ^ 2 = (√v - s) * (√v + s) := by linear_combination -hu2
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < √v + s)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have a1 : |psiS (√v) (a + d) - psiS (√v) a| ≤ |d| := by
    refine (BstLean.Part141.psiS_lip_x _ _ _).trans (le_of_eq ?_)
    congr 1; ring
  have a2 : |psiS (√v) a - psiS s a| ≤ phiG 0 / s * |v - s ^ 2| := by
    refine (BstLean.Part150.psiS_lip_s_phi _ _ _).trans ?_
    rw [phiG_zero_eq, one_div]
    calc (√(2 * π))⁻¹ * |√v - s| ≤ (√(2 * π))⁻¹ * (|v - s ^ 2| / s) := by gcongr
      _ = _ := by ring
  have a3 : |PhiG (a / s) * d| ≤ |d| := by
    rw [abs_mul, abs_of_pos (PhiG_pos _)]
    exact mul_le_of_le_one_left (by positivity) (PhiG_le_one _)
  have a4 : |phiG (a / s) / (2 * s) * (v - s ^ 2)| ≤ 1 / 2 * (phiG 0 / s * |v - s ^ 2|) := by
    rw [abs_mul, abs_of_pos (by have := phiG_pos (a / s); positivity)]
    have := phiG_le_zero (a / s)
    calc phiG (a / s) / (2 * s) * |v - s ^ 2| ≤ phiG 0 / (2 * s) * |v - s ^ 2| := by gcongr
      _ = _ := by ring
  have a5 : 0 ≤ phiG 0 / s * |v - s ^ 2| := by positivity
  have e : 3 / 2 * phiG 0 / s * |v - s ^ 2| = 3 / 2 * (phiG 0 / s * |v - s ^ 2|) := by ring
  rw [e]
  rw [abs_le] at a1 a2 a3 a4 ⊢
  obtain ⟨a11, a12⟩ := a1
  obtain ⟨a21, a22⟩ := a2
  obtain ⟨a31, a32⟩ := a3
  obtain ⟨a41, a42⟩ := a4
  constructor <;> linarith

/-! ## `G₂` -/

lemma G2_nonneg (σ y : ℝ) : 0 ≤ G2 σ y := integral_nonneg fun _ => sq_nonneg _

lemma G2_le (σ y : ℝ) : G2 σ y ≤ y ^ 2 + σ ^ 2 := by
  have h := BstLean.Part153.m2_add σ y
  have h2 : 0 ≤ ∫ z, relu (-y + σ * z) ^ 2 ∂gaussianReal 0 1 := integral_nonneg fun _ => sq_nonneg _
  unfold G2; linarith

lemma G2_one (x : ℝ) : G2 1 x = (x ^ 2 + 1) * PhiG x + x * phiG x := by
  unfold G2
  have e : (fun z : ℝ => relu (x + 1 * z) ^ 2) =
      (Ioi (-x)).indicator (fun z => x ^ 2 + (2 * x) * z + z ^ 2) := by
    funext z
    by_cases hz : z ∈ Ioi (-x)
    · rw [indicator_of_mem hz, one_mul, BstLean.Part130.relu_of_nonneg]
      · ring
      · have := mem_Ioi.mp hz; linarith
    · rw [indicator_of_notMem hz, one_mul, BstLean.Part130.relu_of_nonpos]
      · ring
      · have := not_lt.mp (fun h => hz (mem_Ioi.mpr h)); linarith
  have h1 : IntegrableOn (fun z : ℝ => z) (Ioi (-x)) (gaussianReal 0 1) :=
    BstLean.Part153.intOn_id _
  have h2 : IntegrableOn (fun z : ℝ => z ^ 2) (Ioi (-x)) (gaussianReal 0 1) :=
    (BstLean.Part130.integrable_pow_gauss 2).integrableOn
  have i0 : IntegrableOn (fun _ : ℝ => x ^ 2) (Ioi (-x)) (gaussianReal 0 1) :=
    (integrable_const _).integrableOn
  have i1 : IntegrableOn (fun z : ℝ => 2 * x * z) (Ioi (-x)) (gaussianReal 0 1) := h1.const_mul _
  have i01 : IntegrableOn (fun z : ℝ => x ^ 2 + 2 * x * z) (Ioi (-x)) (gaussianReal 0 1) := i0.add i1
  rw [e, integral_indicator measurableSet_Ioi, integral_add i01 h2, integral_add i0 i1,
    setIntegral_const, integral_const_mul, BstLean.Part153.int_z, BstLean.Part153.int_z2]
  simp only [smul_eq_mul, PhiG]
  ring

/-- **`G₂(a, s²) = (a² + s²)Φ(a/s) + a s φ(a/s)`** for `s > 0`. -/
theorem G2_closed {s : ℝ} (hs : 0 < s) (a : ℝ) :
    G2 s a = (a ^ 2 + s ^ 2) * PhiG (a / s) + a * s * phiG (a / s) := by
  have e : G2 s a = s ^ 2 * G2 1 (a / s) := by
    unfold G2
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show relu (a + s * z) ^ 2 = s ^ 2 * relu (a / s + 1 * z) ^ 2
    rw [← mul_pow, ← BstLean.Part130.relu_mul_of_nonneg hs.le]
    congr 2; field_simp
  rw [e, G2_one]
  field_simp

/-- **The second-order Taylor bound of `G₂`** with a general step `d`, on `v ≥ s²/2`. -/
theorem G2_taylor {s v a d : ℝ} (hs : 0 < s) (hv : s ^ 2 / 2 ≤ v) :
    |G2 (√v) (a + d) - G2 s a -
        (2 * psiS s a * d + PhiG (a / s) * (v - s ^ 2))| ≤
      d ^ 2 + √2 * phiG 0 / s * (|d| * |v - s ^ 2|) + phiG 1 / (2 * s ^ 2) * (v - s ^ 2) ^ 2 := by
  have hv0 : 0 < v := by nlinarith [sq_pos_of_pos hs]
  set r := √2 with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set dτ := d with hdτ
  set dv := v - s ^ 2 with hdv
  let w : ℝ → ℝ := fun t => s ^ 2 + t * dv
  let u : ℝ → ℝ := fun t => √(w t)
  let τ : ℝ → ℝ := fun t => a + t * dτ
  let z : ℝ → ℝ := fun t => τ t / u t
  let H : ℝ → ℝ := fun t => (τ t ^ 2 + u t ^ 2) * PhiG (z t) + τ t * u t * phiG (z t)
  let H1 : ℝ → ℝ := fun t => 2 * (τ t * PhiG (z t) + u t * phiG (z t)) * dτ + PhiG (z t) * dv
  let H2 : ℝ → ℝ := fun t => 2 * PhiG (z t) * dτ ^ 2 + 2 * (phiG (z t) / u t) * (dτ * dv) -
    z t * phiG (z t) / (2 * u t ^ 2) * dv ^ 2
  have hw : ∀ t ∈ Set.Icc (0 : ℝ) 1, s ^ 2 / 2 ≤ w t := by
    intro t ht
    have e : w t = (1 - t) * s ^ 2 + t * v := by simp only [w, hdv]; ring
    rw [e]; nlinarith [ht.1, ht.2, sq_pos_of_pos hs]
  have hw0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < w t := fun t ht => by
    have := hw t ht; nlinarith [sq_pos_of_pos hs]
  have hu0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < u t := fun t ht => Real.sqrt_pos.mpr (hw0 t ht)
  have hu2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, u t ^ 2 = w t := fun t ht => Real.sq_sqrt (hw0 t ht).le
  have dw : ∀ t, HasDerivAt w dv t := by
    intro t
    have := ((hasDerivAt_id t).mul_const dv).const_add (s ^ 2)
    simpa [w] using this
  have dτ' : ∀ t, HasDerivAt τ dτ t := by
    intro t
    have := ((hasDerivAt_id t).mul_const dτ).const_add a
    simpa [τ] using this
  have du : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (dv / (2 * u t)) t := by
    intro t ht
    have := (Real.hasDerivAt_sqrt (hw0 t ht).ne').comp t (dw t)
    have e : dv / (2 * u t) = 1 / (2 * √(w t)) * dv := by simp only [u]; ring
    rw [e]; exact this
  have dz : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt z (dτ / u t - z t * dv / (2 * u t ^ 2)) t := by
    intro t ht
    have := (dτ' t).div (du t ht) (hu0 t ht).ne'
    convert this using 1
    have := (hu0 t ht).ne'
    simp only [z]; field_simp
  have dΦ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => PhiG (z t)) (phiG (z t) * (dτ / u t - z t * dv / (2 * u t ^ 2))) t :=
    fun t ht => (hasDerivAt_PhiG (z t)).comp t (dz t ht)
  have dφ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => phiG (z t))
        (-(z t * phiG (z t)) * (dτ / u t - z t * dv / (2 * u t ^ 2))) t :=
    fun t ht => (hasDerivAt_phiG (z t)).comp t (dz t ht)
  have dH : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt H (H1 t) t := by
    intro t ht
    have hτ2 : HasDerivAt (fun t => τ t ^ 2 + u t ^ 2) (2 * τ t * dτ + 2 * u t * (dv / (2 * u t))) t := by
      have := ((dτ' t).pow 2).add ((du t ht).pow 2)
      convert this using 1; push_cast; ring
    have := (hτ2.mul (dΦ t ht)).add (((dτ' t).mul (du t ht)).mul (dφ t ht))
    simp only [Pi.mul_apply] at this
    convert this using 1
    have h0 := (hu0 t ht).ne'
    have hz : τ t = z t * u t := by simp only [z]; field_simp
    simp only [H1]; rw [hz]; field_simp; ring
  have dH1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt H1 (H2 t) t := by
    intro t ht
    have h0 := (hu0 t ht).ne'
    have hψ : HasDerivAt (fun t => τ t * PhiG (z t) + u t * phiG (z t))
        (dτ * PhiG (z t) + τ t * (phiG (z t) * (dτ / u t - z t * dv / (2 * u t ^ 2))) +
          (dv / (2 * u t) * phiG (z t) +
            u t * (-(z t * phiG (z t)) * (dτ / u t - z t * dv / (2 * u t ^ 2))))) t :=
      ((dτ' t).mul (dΦ t ht)).add ((du t ht).mul (dφ t ht))
    have := ((hψ.const_mul 2).mul_const dτ).add ((dΦ t ht).mul_const dv)
    convert this using 1
    have hz : τ t = z t * u t := by simp only [z]; field_simp
    simp only [H2]; rw [hz]; field_simp; ring
  set M := 2 * d ^ 2 + 2 * (r * phiG 0 / s) * (|d| * |dv|) + phiG 1 / s ^ 2 * dv ^ 2 with hM
  have hφ0 : 0 < phiG 0 := phiG_pos 0
  have hφ1 : 0 < phiG 1 := phiG_pos 1
  have bM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |H2 t| ≤ M := by
    intro t ht
    have hut := hu0 t ht
    have hsu : s ≤ u t * r := sqrt_lower hs (hw t ht)
    have hu2' := hu2 t ht
    have hwt := hw t ht
    have hφz := phiG_pos (z t)
    have cA : |2 * PhiG (z t)| ≤ 2 := by
      rw [abs_of_pos (by have := PhiG_pos (z t); positivity)]
      have := PhiG_le_one (z t); linarith
    have cB : |2 * (phiG (z t) / u t)| ≤ 2 * (r * phiG 0 / s) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos (by positivity)]
      have hin : phiG (z t) / u t ≤ r * phiG 0 / s := by
        rw [div_le_div_iff₀ hut hs]
        have := phiG_le_zero (z t)
        calc phiG (z t) * s ≤ phiG 0 * (u t * r) := by gcongr
          _ = r * phiG 0 * u t := by ring
      linarith
    have cC : |z t * phiG (z t) / (2 * u t ^ 2)| ≤ phiG 1 / s ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos hφz, abs_of_pos (by positivity : 0 < 2 * u t ^ 2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have := abs_mul_phiG_le (z t)
      have h2 : s ^ 2 ≤ 2 * u t ^ 2 := by linarith
      calc |z t| * phiG (z t) * s ^ 2 ≤ phiG 1 * (2 * u t ^ 2) := by
            gcongr
        _ = phiG 1 * (2 * u t ^ 2) := rfl
    have e1 : |dτ ^ 2| = d ^ 2 := by rw [abs_of_nonneg (sq_nonneg _)]
    have e2 : |dτ * dv| = |d| * |dv| := by rw [abs_mul]
    have e3 : |dv ^ 2| = dv ^ 2 := abs_of_nonneg (sq_nonneg _)
    have key : |H2 t| ≤ (|2 * PhiG (z t)| * |dτ ^ 2|) +
        (|2 * (phiG (z t) / u t)| * |dτ * dv|) +
        (|z t * phiG (z t) / (2 * u t ^ 2)| * |dv ^ 2|) := by
      simp only [H2, ← abs_mul]
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    rw [e1, e2, e3] at key
    have hA := mul_le_mul_of_nonneg_right cA (by positivity : (0 : ℝ) ≤ d ^ 2)
    have hB := mul_le_mul_of_nonneg_right cB (by positivity : (0 : ℝ) ≤ |d| * |dv|)
    have hC := mul_le_mul_of_nonneg_right cC (by positivity : (0 : ℝ) ≤ dv ^ 2)
    rw [hM]; linarith
  have T := taylor2 dH dH1 bM
  have eu0 : u 0 = s := by simp only [u, w]; rw [zero_mul, add_zero]; exact Real.sqrt_sq hs.le
  have eu1 : u 1 = √v := by simp only [u, w, hdv]; congr 1; ring
  have eτ0 : τ 0 = a := by simp [τ]
  have eτ1 : τ 1 = a + d := by simp only [τ, hdτ]; ring
  have eH0 : H 0 = G2 s a := by
    simp only [H, z]; rw [eu0, eτ0]; rw [G2_closed hs a]
  have eH1 : H 1 = G2 (√v) (a + d) := by
    simp only [H, z]; rw [eu1, eτ1]; rw [G2_closed (Real.sqrt_pos.mpr hv0) _]
  have eH10 : H1 0 = 2 * psiS s a * d + PhiG (a / s) * dv := by
    simp only [H1, z]; rw [eu0, eτ0, psiS_closed hs a]
  rw [eH0, eH1, eH10] at T
  calc _ ≤ M / 2 := T
    _ = _ := by rw [hM]; ring

/-- **The bound of the remainder of `G₂` off the good set** (`v ≥ 0` only). -/
theorem G2_rough {s v a d : ℝ} (hs : 0 < s) (hv : 0 ≤ v) :
    |G2 (√v) (a + d) - G2 s a - (2 * psiS s a * d + PhiG (a / s) * (v - s ^ 2))| ≤
      (a + d) ^ 2 + a ^ 2 + 2 * (|a| + s) * |d| + 2 * v + 2 * s ^ 2 := by
  have h1 := G2_nonneg (√v) (a + d)
  have h2 := G2_le (√v) (a + d)
  have h3 := G2_nonneg s a
  have h4 := G2_le s a
  rw [Real.sq_sqrt hv] at h2
  have hψ0 := BstLean.Part137.psiS_nonneg s a
  have hψ := BstLean.Part154.psiS_le_abs s a
  have hc : √(2 / π) ≤ 1 := by
    rw [Real.sqrt_le_one]
    rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  rw [abs_of_pos hs] at hψ
  have hψ' : psiS s a ≤ |a| + s := by nlinarith
  have hP0 := PhiG_pos (a / s)
  have hP1 := PhiG_le_one (a / s)
  have hd := abs_nonneg d
  have hl1 : |2 * psiS s a * d| ≤ 2 * (|a| + s) * |d| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hψ0]
    gcongr
  have hl2 : |PhiG (a / s) * (v - s ^ 2)| ≤ v + s ^ 2 := by
    rw [abs_mul, abs_of_pos hP0]
    have : |v - s ^ 2| ≤ v + s ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg s]
    calc PhiG (a / s) * |v - s ^ 2| ≤ 1 * |v - s ^ 2| := by gcongr
      _ ≤ v + s ^ 2 := by linarith
  have hm : |G2 (√v) (a + d) - G2 s a| ≤ (a + d) ^ 2 + v + (a ^ 2 + s ^ 2) := by
    rw [abs_le]; constructor <;> linarith
  calc _ ≤ |G2 (√v) (a + d) - G2 s a| + |2 * psiS s a * d + PhiG (a / s) * (v - s ^ 2)| :=
        abs_sub _ _
    _ ≤ |G2 (√v) (a + d) - G2 s a| + (|2 * psiS s a * d| + |PhiG (a / s) * (v - s ^ 2)|) :=
        by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

end BstLean.Part171
