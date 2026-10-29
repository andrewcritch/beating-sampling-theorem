import BstLean.Part169Ineq

/-!
# Part 169 (file `Scale`): the scale price and the exceptional mass of Part 08

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, "The scale price and the corrected exceptional-mass step",
formulas `t7:p08:scale` and `t7:p08:mass`.

Notation (per latitude): `f̄`, `ω̄` the full latitude means, `V = Var_v f`,
`S̄ = γ(ω̄ − f̄² − V)`; `f̃`, `ω̃` the tables, `S̃ = γ·max(1/5, ω̃ − f̃²)`;
`Δ_f = f̄ − f̃`, `Δ_ω = ω̄ − ω̃`, `Δ_S = S̃/S̄ − 1`.

* **`scale_pt`**: if `S̄ ≥ γd` with `d ≥ 1/5`, then
  `|Δ_S| ≤ (|Δ_ω| + 2|f̄||Δ_f| + Δ_f² + |V|)/d` (the un-floored identity
  `(S̄/γ)Δ_S = −Δ_ω + 2f̄Δ_f − Δ_f² + V`, and the floor does not increase `|Δ_S|`).
* **`scale_L2`** (paper `t7:p08:scale`): from `‖nΔ_ω‖_8 ≤ a_ω`, `‖nΔ_f‖_8 ≤ a_f`,
  `‖f̄‖_4 ≤ H_f`, `‖nV‖_2 ≤ C_v` on `K` (mass at most one):
  `‖nΔ_S‖_{L²(K)} ≤ B_S = (a_ω + 2H_f a_f + a_f²/n + C_v)/d`.
* **`scale_mass`** (paper `t7:p08:mass`): if moreover `0 ≤ V ≤ v_max` on `K`,
  `T = ε − v_max/d > 0` and `‖f̄‖_24 ≤ H_f`, then
  `μ(K ∩ {|Δ_S| > ε}) ≤ ((a_ω + 2H_f a_f)/(0.99 d n T))⁶ + (a_f²/(0.01 d n² T))⁴`.
-/

namespace BstLean.Part169

open MeasureTheory Real

/-- **The pointwise scale bound with the floor.** -/
theorem scale_pt {γ d fb ft wb wt V : ℝ} (hγ : 0 < γ) (hd : 1 / 5 ≤ d)
    (hSbd : γ * d ≤ γ * (wb - fb ^ 2 - V)) :
    |γ * max (1 / 5) (wt - ft ^ 2) / (γ * (wb - fb ^ 2 - V)) - 1| ≤
      (|wb - wt| + 2 * |fb| * |fb - ft| + (fb - ft) ^ 2 + |V|) / d := by
  set Sb := γ * (wb - fb ^ 2 - V) with hSb
  have hd0 : 0 < d := by linarith
  have hSb0 : 0 < Sb := lt_of_lt_of_le (mul_pos hγ hd0) hSbd
  set X := |wb - wt| + 2 * |fb| * |fb - ft| + (fb - ft) ^ 2 + |V| with hX
  -- the un-floored difference
  have hD : |γ * (wt - ft ^ 2) - Sb| ≤ γ * X := by
    have e : γ * (wt - ft ^ 2) - Sb = γ * (-(wb - wt) + 2 * fb * (fb - ft) - (fb - ft) ^ 2 + V) := by
      rw [hSb]; ring
    rw [e, abs_mul, abs_of_pos hγ]
    refine mul_le_mul_of_nonneg_left ?_ hγ.le
    calc |-(wb - wt) + 2 * fb * (fb - ft) - (fb - ft) ^ 2 + V|
        ≤ |-(wb - wt)| + |2 * fb * (fb - ft)| + |(fb - ft) ^ 2| + |V| := by
          have h1 := abs_add_le (-(wb - wt) + 2 * fb * (fb - ft) - (fb - ft) ^ 2) V
          have h2 := abs_sub (-(wb - wt) + 2 * fb * (fb - ft)) ((fb - ft) ^ 2)
          have h3 := abs_add_le (-(wb - wt)) (2 * fb * (fb - ft))
          linarith
      _ = X := by
          simp only [abs_neg, abs_mul, abs_two, abs_pow, sq_abs, hX]
  have hF : |γ * max (1 / 5) (wt - ft ^ 2) - Sb| ≤ γ * X := by
    by_cases h : 1 / 5 ≤ wt - ft ^ 2
    · rw [max_eq_right h]; exact hD
    · push Not at h
      rw [max_eq_left h.le]
      have h1 : γ * (1 / 5) ≤ Sb := (mul_le_mul_of_nonneg_left hd hγ.le).trans hSbd
      have h2 : γ * (wt - ft ^ 2) < γ * (1 / 5) := mul_lt_mul_of_pos_left h hγ
      rw [abs_of_nonpos (by linarith)]
      have := (abs_le.mp hD).1
      linarith
  have e : γ * max (1 / 5) (wt - ft ^ 2) / Sb - 1 = (γ * max (1 / 5) (wt - ft ^ 2) - Sb) / Sb := by
    field_simp
  rw [e, abs_div, abs_of_pos hSb0, div_le_div_iff₀ hSb0 hd0]
  calc |γ * max (1 / 5) (wt - ft ^ 2) - Sb| * d ≤ γ * X * d :=
        mul_le_mul_of_nonneg_right hF hd0.le
    _ = X * (γ * d) := by ring
    _ ≤ X * Sb := mul_le_mul_of_nonneg_left hSbd (by positivity)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {K : Set α}

/-- **The scale price** `B_S` (paper `t7:p08:scale`). -/
theorem scale_L2 (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) (n : ℕ) (hn : 0 < n) {γ d aw af Hf Cv : ℝ}
    (hγ : 0 < γ) (hd : 1 / 5 ≤ d) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    {fb ft wb wt V : α → ℝ} (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb)
    (mwt : Measurable wt) (mV : Measurable V)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a))
    (iW2 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 2) K μ)
    (iW8 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 8) K μ)
    (iF4 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 4) K μ)
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 8) K μ)
    (if4 : IntegrableOn (fun a => fb a ^ 4) K μ)
    (ifF : IntegrableOn (fun a => fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2) K μ)
    (iV : IntegrableOn (fun a => ((n : ℝ) * V a) ^ 2) K μ)
    (hW8 : ∫ a in K, ((n : ℝ) * (wb a - wt a)) ^ 8 ∂μ ≤ aw ^ 8)
    (hF8 : ∫ a in K, ((n : ℝ) * (fb a - ft a)) ^ 8 ∂μ ≤ af ^ 8)
    (hf4 : ∫ a in K, fb a ^ 4 ∂μ ≤ Hf ^ 4)
    (hV : ∫ a in K, ((n : ℝ) * V a) ^ 2 ∂μ ≤ Cv ^ 2) :
    IntegrableOn (fun a => ((n : ℝ) * (γ * max (1 / 5) (wt a - ft a ^ 2) /
        (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2) K μ ∧
      ∫ a in K, ((n : ℝ) * (γ * max (1 / 5) (wt a - ft a ^ 2) /
        (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2 ∂μ ≤
        ((aw + 2 * Hf * af + af ^ 2 / n + Cv) / d) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : 0 < d := by linarith
  -- the four terms, divided by `d`
  set x1 : α → ℝ := fun a => |(n : ℝ) * (wb a - wt a)| / d with hx1
  set x2 : α → ℝ := fun a => 2 * |fb a| * |(n : ℝ) * (fb a - ft a)| / d with hx2
  set x3 : α → ℝ := fun a => ((n : ℝ) * (fb a - ft a)) ^ 2 / n / d with hx3
  set x4 : α → ℝ := fun a => |(n : ℝ) * V a| / d with hx4
  have m1 : Measurable x1 := ((mwb.sub mwt).const_mul _).abs.div_const _
  have m2 : Measurable x2 :=
    (((mfb.abs).const_mul 2).mul ((mfb.sub mft).const_mul _).abs).div_const _
  have m3 : Measurable x3 := ((((mfb.sub mft).const_mul _).pow_const 2).div_const _).div_const _
  have m4 : Measurable x4 := ((mV.const_mul _).abs).div_const _
  -- the four `L²` bounds
  have b1 : ∫ a in K, x1 a ^ 2 ∂μ ≤ (aw / d) ^ 2 := by
    have h2 := sq_int_le_of_pow8 μ hK1 haw iW2 iW8 hW8
    have e : ∀ a, x1 a ^ 2 = ((n : ℝ) * (wb a - wt a)) ^ 2 / d ^ 2 := by
      intro a; simp only [hx1]; rw [div_pow, sq_abs]
    simp only [e]; rw [integral_div, div_pow]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have b2 : ∫ a in K, x2 a ^ 2 ∂μ ≤ (2 * Hf * af / d) ^ 2 := by
    have h4 := pow4_int_le_of_pow8 μ hK1 haf iF4 iF8 hF8
    have hh := int_sq_mul_le if4 iF4 ifF hHf haf hf4 h4
    have e : ∀ a, x2 a ^ 2 = 4 / d ^ 2 * (fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2) := by
      intro a; simp only [hx2]; rw [div_pow, mul_pow, mul_pow, sq_abs, sq_abs]; ring
    simp only [e]; rw [integral_const_mul]
    have := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ 4 / d ^ 2)
    calc 4 / d ^ 2 * ∫ a in K, fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2 ∂μ
        ≤ 4 / d ^ 2 * (Hf ^ 2 * af ^ 2) := this
      _ = (2 * Hf * af / d) ^ 2 := by field_simp; ring
  have b3 : ∫ a in K, x3 a ^ 2 ∂μ ≤ (af ^ 2 / n / d) ^ 2 := by
    have h4 := pow4_int_le_of_pow8 μ hK1 haf iF4 iF8 hF8
    have e : ∀ a, x3 a ^ 2 = ((n : ℝ) * (fb a - ft a)) ^ 4 / (n ^ 2 * d ^ 2) := by
      intro a; simp only [hx3]; field_simp
    simp only [e]; rw [integral_div]
    calc (∫ a in K, ((n : ℝ) * (fb a - ft a)) ^ 4 ∂μ) / (n ^ 2 * d ^ 2)
        ≤ af ^ 4 / (n ^ 2 * d ^ 2) := div_le_div_of_nonneg_right h4 (by positivity)
      _ = (af ^ 2 / n / d) ^ 2 := by field_simp
  have b4 : ∫ a in K, x4 a ^ 2 ∂μ ≤ (Cv / d) ^ 2 := by
    have e : ∀ a, x4 a ^ 2 = ((n : ℝ) * V a) ^ 2 / d ^ 2 := by
      intro a; simp only [hx4]; rw [div_pow, sq_abs]
    simp only [e]; rw [integral_div, div_pow]
    exact div_le_div_of_nonneg_right hV (by positivity)
  -- integrability of the squares
  have j1 : IntegrableOn (fun a => x1 a ^ 2) K μ := by
    have e : (fun a => x1 a ^ 2) = fun a => ((n : ℝ) * (wb a - wt a)) ^ 2 / d ^ 2 := by
      funext a; simp only [hx1]; rw [div_pow, sq_abs]
    rw [e]; exact iW2.div_const _
  have j2 : IntegrableOn (fun a => x2 a ^ 2) K μ := by
    have e : (fun a => x2 a ^ 2) = fun a => 4 / d ^ 2 * (fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2) := by
      funext a; simp only [hx2]; rw [div_pow, mul_pow, mul_pow, sq_abs, sq_abs]; ring
    rw [e]; exact ifF.const_mul _
  have j3 : IntegrableOn (fun a => x3 a ^ 2) K μ := by
    have e : (fun a => x3 a ^ 2) = fun a => ((n : ℝ) * (fb a - ft a)) ^ 4 / (n ^ 2 * d ^ 2) := by
      funext a; simp only [hx3]; field_simp
    rw [e]; exact iF4.div_const _
  have j4 : IntegrableOn (fun a => x4 a ^ 2) K μ := by
    have e : (fun a => x4 a ^ 2) = fun a => ((n : ℝ) * V a) ^ 2 / d ^ 2 := by
      funext a; simp only [hx4]; rw [div_pow, sq_abs]
    rw [e]; exact iV.div_const _
  -- Minkowski three times
  obtain ⟨k12, s12⟩ := int_sq_add m1.aestronglyMeasurable m2.aestronglyMeasurable j1 j2
    (by positivity) (by positivity) b1 b2
  obtain ⟨k123, s123⟩ := int_sq_add (m1.add m2).aestronglyMeasurable m3.aestronglyMeasurable
    k12 j3 (by positivity) (by positivity) s12 b3
  obtain ⟨k1234, s1234⟩ := int_sq_add ((m1.add m2).add m3).aestronglyMeasurable
    m4.aestronglyMeasurable k123 j4 (by positivity) (by positivity) s123 b4
  -- the pointwise bound
  set sumX : α → ℝ := fun a => x1 a + x2 a + x3 a + x4 a with hsum
  have hpt : ∀ a ∈ K, ((n : ℝ) * (γ * max (1 / 5) (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2 ≤ (x1 a + x2 a + x3 a + x4 a) ^ 2 := by
    intro a ha
    have hs := scale_pt (wt := wt a) (ft := ft a) hγ hd (hSbd a ha)
    have h0 : 0 ≤ x1 a + x2 a + x3 a + x4 a := by
      simp only [hx1, hx2, hx3, hx4]; positivity
    have hle : |(n : ℝ) * (γ * max (1 / 5) (wt a - ft a ^ 2) /
        (γ * (wb a - fb a ^ 2 - V a)) - 1)| ≤ x1 a + x2 a + x3 a + x4 a := by
      rw [abs_mul, abs_of_pos hnR]
      have := mul_le_mul_of_nonneg_left hs hnR.le
      refine this.trans (le_of_eq ?_)
      simp only [hx1, hx2, hx3, hx4]
      simp only [abs_mul, abs_of_pos hnR]
      field_simp
    calc _ = |(n : ℝ) * (γ * max (1 / 5) (wt a - ft a ^ 2) /
          (γ * (wb a - fb a ^ 2 - V a)) - 1)| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hle 2
  have mS : Measurable (fun a => ((n : ℝ) * (γ * max (1 / 5) (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2) :=
    (((((measurable_const.max (mwt.sub (mft.pow_const 2))).const_mul γ).div
      (((mwb.sub (mfb.pow_const 2)).sub mV).const_mul γ)).sub_const 1).const_mul _).pow_const 2
  have iS : IntegrableOn (fun a => ((n : ℝ) * (γ * max (1 / 5) (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2) K μ := by
    refine Integrable.mono' k1234 mS.aestronglyMeasurable ((ae_restrict_iff' hK).mpr
      (Filter.Eventually.of_forall fun a ha => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt a ha
  refine ⟨iS, ?_⟩
  refine (setIntegral_mono_on iS k1234 hK hpt).trans (s1234.trans (le_of_eq ?_))
  field_simp

/-- **The exceptional mass** (paper `t7:p08:mass`): the kept mass where the relative scale
error exceeds `ε`. -/
theorem scale_mass (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) (n : ℕ) (hn : 0 < n)
    {γ d ε vmax aw af Hf : ℝ} (hγ : 0 < γ) (hd : 1 / 5 ≤ d) (haw : 0 < aw) (haf : 0 < af)
    (hHf : 0 < Hf) (hT : 0 < ε - vmax / d)
    {fb ft wb wt V : α → ℝ} (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb)
    (mwt : Measurable wt)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a))
    (hVm : ∀ a ∈ K, |V a| ≤ vmax)
    (iW6 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 6) K μ)
    (iW8 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 8) K μ)
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 8) K μ)
    (if24 : IntegrableOn (fun a => fb a ^ 24) K μ)
    (ifF : IntegrableOn (fun a => fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6) K μ)
    (hW8 : ∫ a in K, ((n : ℝ) * (wb a - wt a)) ^ 8 ∂μ ≤ aw ^ 8)
    (hF8 : ∫ a in K, ((n : ℝ) * (fb a - ft a)) ^ 8 ∂μ ≤ af ^ 8)
    (hf24 : ∫ a in K, fb a ^ 24 ∂μ ≤ Hf ^ 24) :
    μ.real (K ∩ {a | ε < |γ * max (1 / 5) (wt a - ft a ^ 2) /
        (γ * (wb a - fb a ^ 2 - V a)) - 1|}) ≤
      ((aw + 2 * Hf * af) / (99 / 100 * d * n * (ε - vmax / d))) ^ 6 +
        (af ^ 2 / (1 / 100 * d * n ^ 2 * (ε - vmax / d))) ^ 4 := by
  set T := ε - vmax / d with hTd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : 0 < d := by linarith
  set x : α → ℝ := fun a => |(n : ℝ) * (wb a - wt a)| with hx
  set y : α → ℝ := fun a => 2 * |fb a| * |(n : ℝ) * (fb a - ft a)| with hy
  set P1 : α → ℝ := fun a => (x a + y a) / (n * d) with hP1
  set P2 : α → ℝ := fun a => ((n : ℝ) * (fb a - ft a)) ^ 2 / (n ^ 2 * d) with hP2
  have mx : Measurable x := ((mwb.sub mwt).const_mul _).abs
  have my : Measurable y := ((mfb.abs).const_mul 2).mul ((mfb.sub mft).const_mul _).abs
  have mP1 : Measurable P1 := (mx.add my).div_const _
  have mP2 : Measurable P2 := (((mfb.sub mft).const_mul _).pow_const 2).div_const _
  have hx0 : ∀ a, 0 ≤ x a := fun a => abs_nonneg _
  have hy0 : ∀ a, 0 ≤ y a := fun a => by simp only [hy]; positivity
  -- the split of the exceptional set
  have hsub : K ∩ {a | ε < |γ * max (1 / 5) (wt a - ft a ^ 2) / (γ * (wb a - fb a ^ 2 - V a)) - 1|}
      ⊆ (K ∩ {a | (99 / 100 * T) ^ 6 ≤ P1 a ^ 6}) ∪ (K ∩ {a | (1 / 100 * T) ^ 4 ≤ P2 a ^ 4}) := by
    rintro a ⟨ha, hε⟩
    simp only [Set.mem_ofPred_eq] at hε
    have hs := scale_pt (wt := wt a) (ft := ft a) hγ hd (hSbd a ha)
    have e : (|wb a - wt a| + 2 * |fb a| * |fb a - ft a| + (fb a - ft a) ^ 2 + |V a|) / d =
        P1 a + P2 a + |V a| / d := by
      simp only [hP1, hP2, hx, hy, abs_mul, abs_of_pos hnR]
      field_simp
    rw [e] at hs
    have hV : |V a| / d ≤ vmax / d := div_le_div_of_nonneg_right (hVm a ha) hd0.le
    have hTP : T < P1 a + P2 a := by rw [hTd]; linarith
    have hP10 : 0 ≤ P1 a := by simp only [hP1]; have := hx0 a; have := hy0 a; positivity
    have hP20 : 0 ≤ P2 a := by simp only [hP2]; positivity
    by_cases h1 : 99 / 100 * T ≤ P1 a
    · left; exact ⟨ha, pow_le_pow_left₀ (by positivity) h1 6⟩
    · right
      refine ⟨ha, pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1 / 100 * T) ?_ 4⟩
      push Not at h1; linarith
  -- the sixth moment of `P1`
  have i6x : IntegrableOn (fun a => x a ^ 6) K μ := by
    have e : (fun a => x a ^ 6) = fun a => ((n : ℝ) * (wb a - wt a)) ^ 6 := by
      funext a; simp only [hx]; exact Even.pow_abs (by decide) _
    rw [e]; exact iW6
  have i6y : IntegrableOn (fun a => y a ^ 6) K μ := by
    have e : (fun a => y a ^ 6) = fun a => 64 * (fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6) := by
      funext a; simp only [hy]
      rw [mul_pow, mul_pow, Even.pow_abs (by decide), Even.pow_abs (by decide)]; ring
    rw [e]; exact ifF.const_mul _
  have b6x : ∫ a in K, x a ^ 6 ∂μ ≤ aw ^ 6 := by
    have e : (fun a => x a ^ 6) = fun a => ((n : ℝ) * (wb a - wt a)) ^ 6 := by
      funext a; simp only [hx]; exact Even.pow_abs (by decide) _
    rw [e]; exact int_pow6_of_pow8 hK1 haw iW6 iW8 hW8
  have b6y : ∫ a in K, y a ^ 6 ∂μ ≤ (2 * Hf * af) ^ 6 := by
    have e : (fun a => y a ^ 6) = fun a => 64 * (fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6) := by
      funext a; simp only [hy]
      rw [mul_pow, mul_pow, Even.pow_abs (by decide), Even.pow_abs (by decide)]; ring
    rw [e, integral_const_mul]
    have hh := int_pow6_mul_le if24 iF8 ifF hHf haf hf24 hF8
    have := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 64)
    calc 64 * ∫ a in K, fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6 ∂μ ≤ 64 * (Hf ^ 6 * af ^ 6) := this
      _ = (2 * Hf * af) ^ 6 := by ring
  obtain ⟨ixy, bxy⟩ := int_pow6_add mx.aestronglyMeasurable my.aestronglyMeasurable hx0 hy0
    i6x i6y haw (by positivity) b6x b6y
  have iP1 : IntegrableOn (fun a => P1 a ^ 6) K μ := by
    have e : (fun a => P1 a ^ 6) = fun a => (x a + y a) ^ 6 / (n * d) ^ 6 := by
      funext a; simp only [hP1]; rw [div_pow]
    rw [e]; exact ixy.div_const _
  have bP1 : ∫ a in K, P1 a ^ 6 ∂μ ≤ (aw + 2 * Hf * af) ^ 6 / (n * d) ^ 6 := by
    have e : (fun a => P1 a ^ 6) = fun a => (x a + y a) ^ 6 / (n * d) ^ 6 := by
      funext a; simp only [hP1]; rw [div_pow]
    rw [e, integral_div]
    exact div_le_div_of_nonneg_right bxy (by positivity)
  have iP2 : IntegrableOn (fun a => P2 a ^ 4) K μ := by
    have e : (fun a => P2 a ^ 4) = fun a => ((n : ℝ) * (fb a - ft a)) ^ 8 / (n ^ 2 * d) ^ 4 := by
      funext a; simp only [hP2]; rw [div_pow]; ring
    rw [e]; exact iF8.div_const _
  have bP2 : ∫ a in K, P2 a ^ 4 ∂μ ≤ af ^ 8 / (n ^ 2 * d) ^ 4 := by
    have e : (fun a => P2 a ^ 4) = fun a => ((n : ℝ) * (fb a - ft a)) ^ 8 / (n ^ 2 * d) ^ 4 := by
      funext a; simp only [hP2]; rw [div_pow]; ring
    rw [e, integral_div]
    exact div_le_div_of_nonneg_right hF8 (by positivity)
  -- Markov
  have k1 := markov_on hK (mP1.pow_const 6) (fun a _ => by
    simp only [hP1]; have := hx0 a; have := hy0 a; positivity) iP1
    (by positivity : (0:ℝ) < (99 / 100 * T) ^ 6)
  have k2 := markov_on hK (mP2.pow_const 4) (fun a _ => by simp only [hP2]; positivity) iP2
    (by positivity : (0:ℝ) < (1 / 100 * T) ^ 4)
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add ?_ ?_))
  · refine k1.trans ?_
    calc (∫ a in K, P1 a ^ 6 ∂μ) / (99 / 100 * T) ^ 6
        ≤ (aw + 2 * Hf * af) ^ 6 / (n * d) ^ 6 / (99 / 100 * T) ^ 6 :=
          div_le_div_of_nonneg_right bP1 (by positivity)
      _ = ((aw + 2 * Hf * af) / (99 / 100 * d * n * T)) ^ 6 := by field_simp
  · refine k2.trans ?_
    calc (∫ a in K, P2 a ^ 4 ∂μ) / (1 / 100 * T) ^ 4
        ≤ af ^ 8 / (n ^ 2 * d) ^ 4 / (1 / 100 * T) ^ 4 :=
          div_le_div_of_nonneg_right bP2 (by positivity)
      _ = (af ^ 2 / (1 / 100 * d * n ^ 2 * T)) ^ 4 := by field_simp

end BstLean.Part169
