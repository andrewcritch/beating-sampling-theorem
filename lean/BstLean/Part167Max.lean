import BstLean.Part167PB

/-!
# Part 167 (file `Max`): the maximum of `m` Gaussian row lengths (the factor `M_ℓ` of LJ)

No proof is left open; no `native_decide` or `axiom` is used.

`G = (G_i)_{i < m}` are independent standard Gaussian vectors of `ℝ^d` (the transverse parts of the
rows of `A₁`, Part 162's `rows_map`), `Mx G = max_i |G_i|`.

* **`young_pow`**: `x ≤ x^q/(q K^{q−1}) + (1 − 1/q) K` (`x ≥ 0`, `K > 0`).
* **`max_mom`**: `E Mx^{128} ≤ m^{1/q}·(d + 128q)^{64}` for every `q ≥ 1` (paper: `M_ℓ`, order `ℓ`;
  the moment of order `128q` with a union over the `m` rows and the chi moments). With
  `m = n²`, `d = n − 2` and `q = 16` this is `(√n)^{128}(1 + o(1))`.
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 measurable_radF)

variable {m d : ℕ}

lemma univ_ne (hm : 0 < m) : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- `max_i |G_i|`. -/
noncomputable def Mx (hm : 0 < m) (G : Fin m → Fin d → ℝ) : ℝ :=
  Finset.univ.sup' (univ_ne hm) fun i => radF53 (G i)

lemma Mx_nonneg (hm : 0 < m) (G : Fin m → Fin d → ℝ) : 0 ≤ Mx hm G :=
  (BstLean.Part162.radF_nonneg (G ⟨0, hm⟩)).trans
    (Finset.le_sup' (fun i => radF53 (G i)) (Finset.mem_univ _))

lemma Mx_pow_le (hm : 0 < m) (G : Fin m → Fin d → ℝ) (k : ℕ) :
    Mx hm G ^ k ≤ ∑ i, radF53 (G i) ^ k := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (univ_ne hm)
    (fun i => radF53 (G i))
  rw [Mx, hi]
  exact Finset.single_le_sum (f := fun i => radF53 (G i) ^ k)
    (fun j _ => pow_nonneg (BstLean.Part162.radF_nonneg _) _) (Finset.mem_univ i)

lemma measurable_Mx (hm : 0 < m) : Measurable (Mx (d := d) hm) := by
  have e : Mx (d := d) hm = (Finset.univ.sup' (univ_ne hm)
      fun (i : Fin m) (G : Fin m → Fin d → ℝ) => radF53 (G i)) := by
    funext G; unfold Mx; rw [Finset.sup'_apply]
  rw [e]
  exact Finset.measurable_sup' _ fun i _ => measurable_radF.comp (measurable_pi_apply i)

/-- Young's inequality (tangent line of `x^q`). -/
lemma young_pow {x K : ℝ} (hx : 0 ≤ x) (hK : 0 < K) {q : ℕ} (hq : 1 ≤ q) :
    x ≤ x ^ q / (q * K ^ (q - 1)) + (1 - 1 / q) * K := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ x / K - 1 by
    have : 0 ≤ x / K := by positivity
    linarith) q
  rw [add_sub_cancel, div_pow] at hb
  have hKq : 0 < K ^ q := by positivity
  rw [le_div_iff₀ hKq] at hb
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hKp : 0 < K ^ p := by positivity
  rw [pow_succ] at hb
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  push_cast at hb ⊢
  have e : (1 + (↑p + 1) * (x / K - 1)) * (K ^ p * K) =
      (↑p + 1) * x * K ^ p - p * K ^ p * K := by
    field_simp; ring
  rw [e] at hb
  have e2 : (1 - 1 / ((p : ℝ) + 1)) * K * ((↑p + 1) * K ^ p) = p * K ^ p * K := by
    field_simp; ring
  nlinarith [e2]

/-- **The maximum row length**: `E Mx^{128} ≤ m^{1/q}(d + 128q)^{64}`. -/
theorem max_mom (hm : 0 < m) {q : ℕ} (hq : 1 ≤ q) :
    ∫⁻ G, ENNReal.ofReal (Mx hm G ^ 128) ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
      ENNReal.ofReal ((m : ℝ) ^ ((1 : ℝ) / q) * ((d : ℝ) + 128 * q) ^ 64) := by
  set Q := Measure.pi (fun _ : Fin m => stdGauss (Fin d))
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set K : ℝ := (m : ℝ) ^ ((1 : ℝ) / q) * ((d : ℝ) + 128 * q) ^ 64 with hK
  have hK0 : 0 < K := by
    have : 0 < (d : ℝ) + 128 * q := by positivity
    positivity
  have hKq : K ^ q = m * ((d : ℝ) + 128 * q) ^ (64 * q) := by
    rw [hK, mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ ((1 : ℝ) / q)), ← Real.rpow_mul (by positivity),
      one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one, ← pow_mul]
  -- the high moment
  have hhigh : ∫⁻ G, ENNReal.ofReal ((Mx hm G ^ 128) ^ q) ∂Q ≤ ENNReal.ofReal (K ^ q) := by
    have hpt : ∀ G : Fin m → Fin d → ℝ, ENNReal.ofReal ((Mx hm G ^ 128) ^ q) ≤
        ∑ i, ENNReal.ofReal ((∑ j, G i j ^ 2) ^ (64 * q)) := by
      intro G
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [← pow_mul]
      refine (Mx_pow_le hm G (128 * q)).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show 128 * q = 2 * (64 * q) by ring, pow_mul, BstLean.Part162.radF_sq]
    refine (lintegral_mono hpt).trans ?_
    have hmi : ∀ i : Fin m, Measurable (fun G : Fin m → Fin d → ℝ =>
        ENNReal.ofReal ((∑ j, G i j ^ 2) ^ (64 * q))) := fun i =>
      ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp (measurable_pi_apply i)).pow_const 2).pow_const _)
    rw [lintegral_finsetSum _ (fun i _ => hmi i)]
    have hrow : ∀ i : Fin m, ∫⁻ G, ENNReal.ofReal ((∑ j, G i j ^ 2) ^ (64 * q)) ∂Q ≤
        ENNReal.ofReal (((d : ℝ) + 2 * (64 * q : ℕ)) ^ (64 * q)) := by
      intro i
      have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin m => stdGauss (Fin d)) i
      have hf : Measurable (fun g : Fin d → ℝ => ENNReal.ofReal ((∑ j, g j ^ 2) ^ (64 * q))) :=
        ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ =>
          (measurable_pi_apply j).pow_const 2).pow_const _)
      have := hmp.lintegral_comp hf
      simp only [Function.eval] at this
      rw [this]
      have h := BstLean.Part166.chi_mom (ι := Fin d) (64 * q)
      simpa using h
    calc ∑ i : Fin m, ∫⁻ G, ENNReal.ofReal ((∑ j, G i j ^ 2) ^ (64 * q)) ∂Q
        ≤ ∑ _i : Fin m, ENNReal.ofReal (((d : ℝ) + 2 * (64 * q : ℕ)) ^ (64 * q)) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = ENNReal.ofReal (K ^ q) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKq,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; push_cast; ring
  -- Young
  have hpt : ∀ G : Fin m → Fin d → ℝ, ENNReal.ofReal (Mx hm G ^ 128) ≤
      ENNReal.ofReal (1 / (q * K ^ (q - 1))) * ENNReal.ofReal ((Mx hm G ^ 128) ^ q) +
        ENNReal.ofReal ((1 - 1 / q) * K) := by
    intro G
    have h1 : 0 ≤ 1 - 1 / (q : ℝ) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hqR
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := young_pow (pow_nonneg (Mx_nonneg hm G) 128) hK0 hq
    rw [div_eq_mul_one_div] at this
    linarith
  refine (lintegral_mono hpt).trans ?_
  have hmeas : Measurable (fun G : Fin m → Fin d → ℝ => ENNReal.ofReal ((Mx hm G ^ 128) ^ q)) :=
    ENNReal.measurable_ofReal.comp (((measurable_Mx hm).pow_const 128).pow_const q)
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hmeas, lintegral_const,
    measure_univ, mul_one]
  have h1 : 0 ≤ 1 - 1 / (q : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact hqR
  calc ENNReal.ofReal (1 / (q * K ^ (q - 1))) * ∫⁻ G, ENNReal.ofReal ((Mx hm G ^ 128) ^ q) ∂Q +
        ENNReal.ofReal ((1 - 1 / q) * K)
      ≤ ENNReal.ofReal (1 / (q * K ^ (q - 1))) * ENNReal.ofReal (K ^ q) +
          ENNReal.ofReal ((1 - 1 / q) * K) := by gcongr
    _ = ENNReal.ofReal K := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [pow_succ]
        push_cast
        field_simp
        ring

end BstLean.Part167
