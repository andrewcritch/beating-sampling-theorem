import BstLean.Part186RA1

/-!
# Part 186 (file `RA2`): the eighth and fourth moments of a sum of independent polynomial rows

No proof is left open; no `native_decide` or `axiom` is used.

* `qp c₀ c₁ c₂ x = c₀ + c₁x + c₂x²`; `Sb`, `M8`: the crude row-moment bounds;
* `Zmom`: `E(Σ_j (q(R_j) − μ))⁸ ≤ M₈`, `μ = c₀ + 2c₁ + 8c₂` (Part 184's `mom8_pi`);
* **`sum8_pi`**, **`sum4_pi`** (product over the rows), **`sum8_two`**, **`sum4_two`** (the two
  Gaussian vectors `ξ₁, ξ₂`).
-/

namespace BstLean.Part186.RA

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)

/-- The polynomial row bound. -/
def qp (c0 c1 c2 x : ℝ) : ℝ := c0 + c1 * x + c2 * x ^ 2

lemma qp_nonneg {c0 c1 c2 x : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (hx : 0 ≤ x) :
    0 ≤ qp c0 c1 c2 x := by unfold qp; positivity

lemma qp_le {c0 c1 c2 x : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (hx : 0 ≤ x) :
    qp c0 c1 c2 x ≤ (c0 + c1 + c2) * (1 + x) ^ 2 := by
  unfold qp
  have a1 : c0 ≤ c0 * (1 + x) ^ 2 := le_mul_of_one_le_right h0 (by nlinarith)
  have a2 : c1 * x ≤ c1 * (1 + x) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) h1
  have a3 : c2 * x ^ 2 ≤ c2 * (1 + x) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) h2
  nlinarith

lemma one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    (1 + x) ^ (j + 1) ≤ 2 ^ j * (1 + x ^ (j + 1)) := by
  have h := two_point zero_le_one hx one_pos j
  norm_num at h
  linarith

lemma measurable_qpRR (c0 c1 c2 : ℝ) : Measurable (fun p : ℝ × ℝ => qp c0 c1 c2 (RR p)) := by
  unfold qp RR; fun_prop

/-- The pointwise majorant of a centred row power. -/
lemma cen_pow_le {c0 c1 c2 μ x : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (hμ : 0 ≤ μ)
    (hx : 0 ≤ x) (k : ℕ) :
    |qp c0 c1 c2 x - μ| ^ (k + 1) ≤
      (c0 + c1 + c2) ^ (k + 1) * (2 ^ (2 * k + 1) * (1 + x ^ (2 * k + 2))) + μ ^ (k + 1) := by
  set a := qp c0 c1 c2 x
  have ha : 0 ≤ a := qp_nonneg h0 h1 h2 hx
  have hab : |a - μ| ≤ max a μ := abs_le.mpr ⟨by have := le_max_right a μ; linarith,
    by have := le_max_left a μ; linarith⟩
  have hm : max a μ ^ (k + 1) ≤ a ^ (k + 1) + μ ^ (k + 1) := by
    rcases le_total a μ with h | h
    · rw [max_eq_right h]; have := pow_nonneg ha (k + 1); linarith
    · rw [max_eq_left h]; have := pow_nonneg hμ (k + 1); linarith
  have hK : 0 ≤ c0 + c1 + c2 := by positivity
  have h3 : a ^ (k + 1) ≤ ((c0 + c1 + c2) * (1 + x) ^ 2) ^ (k + 1) :=
    pow_le_pow_left₀ ha (qp_le h0 h1 h2 hx) _
  have h4 : ((c0 + c1 + c2) * (1 + x) ^ 2) ^ (k + 1) =
      (c0 + c1 + c2) ^ (k + 1) * (1 + x) ^ (2 * k + 1 + 1) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  have h5 := one_add_pow_le hx (2 * k + 1)
  calc |a - μ| ^ (k + 1) ≤ max a μ ^ (k + 1) := pow_le_pow_left₀ (abs_nonneg _) hab _
    _ ≤ a ^ (k + 1) + μ ^ (k + 1) := hm
    _ ≤ (c0 + c1 + c2) ^ (k + 1) * (2 ^ (2 * k + 1) * (1 + x ^ (2 * k + 2))) + μ ^ (k + 1) := by
        rw [h4] at h3
        have := mul_le_mul_of_nonneg_left h5 (pow_nonneg hK (k + 1))
        linarith

lemma int_maj (j : ℕ) (A B : ℝ) : Integrable (fun p => A * (1 + RR p ^ j) + B) ρ2 ∧
    ∫ p, (A * (1 + RR p ^ j) + B) ∂ρ2 = A * (1 + ∫ p, RR p ^ j ∂ρ2) + B := by
  have hi := (int_RR_pow j).1
  have i1 : Integrable (fun p => A * (1 + RR p ^ j)) ρ2 :=
    ((integrable_const 1).add hi).const_mul A
  refine ⟨i1.add (integrable_const B), ?_⟩
  rw [integral_add i1 (integrable_const B), integral_const_mul,
    integral_add (integrable_const 1) hi]
  simp

lemma int_qpRR {c0 c1 c2 : ℝ} : Integrable (fun p => qp c0 c1 c2 (RR p)) ρ2 ∧
    ∫ p, qp c0 c1 c2 (RR p) ∂ρ2 = c0 + 2 * c1 + 8 * c2 := by
  have i1 : Integrable (fun p => RR p) ρ2 := by simpa using (int_RR_pow 1).1
  have i2 := (int_RR_pow 2).1
  have ia : Integrable (fun p => c0 + c1 * RR p) ρ2 := (integrable_const c0).add (i1.const_mul c1)
  have ib : Integrable (fun p => c2 * RR p ^ 2) ρ2 := i2.const_mul c2
  unfold qp
  refine ⟨ia.add ib, ?_⟩
  rw [integral_add ia ib, integral_add (integrable_const c0) (i1.const_mul c1), integral_const_mul,
    integral_const_mul, ER1, ER2]
  simp; ring

/-- The crude bound of `S_k`. -/
noncomputable def Sb (m : ℕ) (K μ E : ℝ) (k : ℕ) : ℝ :=
  m * (K ^ k * (2 ^ (2 * k - 1) * (1 + E)) + μ ^ k)

/-- The crude eighth-moment bound of the centred sum. -/
noncomputable def M8 (m : ℕ) (K μ : ℝ) : ℝ :=
  105 * Sb m K μ 384 2 ^ 4 + 490 * Sb m K μ 384 2 ^ 2 * Sb m K μ 10321920 4 +
    63 * Sb m K μ 10321920 4 ^ 2 + 56 * Sb m K μ 384 2 * Sb m K μ 1961990553600 6 +
    Sb m K μ 1371195958099968000 8

lemma Sb_nonneg {m : ℕ} {K μ E : ℝ} (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hE : 0 ≤ E) (k : ℕ) :
    0 ≤ Sb m K μ E k := by unfold Sb; positivity

/-- **The eighth moment of the centred sum.** -/
theorem Zmom {m : ℕ} {c0 c1 c2 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) :
    ∫⁻ y, ENNReal.ofReal ((∑ j : Fin m, (qp c0 c1 c2 (RR (y j)) - (c0 + 2 * c1 + 8 * c2))) ^ 8)
      ∂(Measure.pi fun _ : Fin m => ρ2) ≤
      ENNReal.ofReal (M8 m (c0 + c1 + c2) (c0 + 2 * c1 + 8 * c2)) := by
  set μ := c0 + 2 * c1 + 8 * c2 with hμd
  set K := c0 + c1 + c2 with hKd
  have hμ : 0 ≤ μ := by positivity
  have hK : 0 ≤ K := by positivity
  set ψ : ℝ × ℝ → ℝ := fun p => qp c0 c1 c2 (RR p) - μ with hψd
  set φ : Fin m → ℝ × ℝ → ℝ := fun _ => ψ with hφd
  have hψm : Measurable ψ := (measurable_qpRR c0 c1 c2).sub measurable_const
  have hm : ∀ j, Measurable (φ j) := fun j => hψm
  -- the majorants
  have hmaj : ∀ k : ℕ, ∀ p, |ψ p| ^ (k + 1) ≤
      K ^ (k + 1) * 2 ^ (2 * k + 1) * (1 + RR p ^ (2 * k + 2)) + μ ^ (k + 1) := by
    intro k p
    have := cen_pow_le h0 h1 h2 hμ (RR_nonneg p) k
    simp only [hψd]; linarith
  have hint : ∀ k : ℕ, Integrable (fun p => |ψ p| ^ (k + 1)) ρ2 := by
    intro k
    refine Integrable.mono' (int_maj (2 * k + 2) (K ^ (k + 1) * 2 ^ (2 * k + 1)) (μ ^ (k + 1))).1
      (((hψm).abs.pow_const _).aestronglyMeasurable) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hmaj k p
  have hi : ∀ j, Integrable (fun x => φ j x ^ 8) ρ2 := by
    intro j
    have e : (fun x => φ j x ^ 8) = fun x => |ψ x| ^ (7 + 1) := by
      funext x; rw [show 7 + 1 = 8 by rfl, Even.pow_abs (by decide)]
    rw [e]; exact hint 7
  have h0' : ∀ j, ∫ x, φ j x ∂ρ2 = 0 := by
    intro j
    simp only [hφd, hψd]
    rw [integral_sub int_qpRR.1 (integrable_const μ), int_qpRR.2]
    simp [hμd]
  have hmom := BstLean.Part184.mom8_pi_lint ρ2 φ hm hi h0'
  refine hmom.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the row moments
  have hS : ∀ (k : ℕ) (E : ℝ), ∫ p, RR p ^ (2 * k + 2) ∂ρ2 = E →
      BstLean.Part184.Smom ρ2 φ (k + 1) ≤ Sb m K μ E (k + 1) := by
    intro k E hE
    unfold BstLean.Part184.Smom Sb
    have e1 : ∀ j : Fin m, ∫ x, |φ j x| ^ (k + 1) ∂ρ2 = ∫ x, |ψ x| ^ (k + 1) ∂ρ2 :=
      fun j => rfl
    simp only [e1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hb := int_maj (2 * k + 2) (K ^ (k + 1) * 2 ^ (2 * k + 1)) (μ ^ (k + 1))
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => by positivity) hb.1
      (Filter.Eventually.of_forall fun p => hmaj k p)).trans (le_of_eq ?_)
    rw [hb.2, hE, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    ring
  have s2 := hS 1 384 ER4
  have s4 := hS 3 10321920 ER8
  have s6 := hS 5 1961990553600 ER12
  have s8 := hS 7 1371195958099968000 ER16
  have p2 := BstLean.Part184.Smom_nonneg ρ2 φ 2
  have p4 := BstLean.Part184.Smom_nonneg ρ2 φ 4
  have p6 := BstLean.Part184.Smom_nonneg ρ2 φ 6
  have q2 := Sb_nonneg (m := m) hK hμ (by norm_num : (0 : ℝ) ≤ 384) 2
  unfold M8
  gcongr

/-- The two Gaussian vectors `ξ₁, ξ₂` as one product over the rows `(ξ₁_j, ξ₂_j)`. -/
lemma lint_transfer {m : ℕ} (H : (Fin m → ℝ × ℝ) → ENNReal) (hH : Measurable H) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, H (fun j => (ξ₁ j, ξ₂ j)) ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      ∫⁻ y, H y ∂(Measure.pi fun _ : Fin m => ρ2) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m) (fun _ => g1) (fun _ => g1)
  set G : (Fin m → ℝ) × (Fin m → ℝ) → ENNReal := fun p => H (fun j => (p.1 j, p.2 j)) with hGd
  have hG : Measurable G := hH.comp (by fun_prop)
  have e1 : ∫⁻ ξ₁, ∫⁻ ξ₂, H (fun j => (ξ₁ j, ξ₂ j)) ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      ∫⁻ p, G p ∂((stdGauss (Fin m)).prod (stdGauss (Fin m))) :=
    (lintegral_prod G hG.aemeasurable).symm
  rw [e1]
  have e2 : (stdGauss (Fin m)).prod (stdGauss (Fin m)) =
      (Measure.pi fun _ : Fin m => g1).prod (Measure.pi fun _ : Fin m => g1) := rfl
  rw [e2, ← hmp.lintegral_comp hG]
  rfl

lemma sum_split {m : ℕ} (f : Fin m → ℝ) (μ : ℝ) :
    ∑ j, f j = m * μ + ∑ j, (f j - μ) := by
  rw [Finset.sum_sub_distrib]; simp

/-- **The eighth moment of a sum of independent polynomial rows.** -/
theorem sum8_two {m : ℕ} {c0 c1 c2 ε : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (hε : 0 < ε) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((∑ j : Fin m, qp c0 c1 c2 (ξ₁ j ^ 2 + ξ₂ j ^ 2)) ^ 8)
      ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((1 + ε) ^ 7 * (m * (c0 + 2 * c1 + 8 * c2)) ^ 8 +
        (1 + 1 / ε) ^ 7 * M8 m (c0 + c1 + c2) (c0 + 2 * c1 + 8 * c2)) := by
  set μ := c0 + 2 * c1 + 8 * c2 with hμd
  have hμ : 0 ≤ μ := by positivity
  set A := (1 + ε) ^ 7 * (m * μ) ^ 8
  set B := (1 + 1 / ε) ^ 7
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hH : Measurable (fun y : Fin m → ℝ × ℝ =>
      ENNReal.ofReal ((∑ j, qp c0 c1 c2 (RR (y j))) ^ 8)) := by
    refine ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ => ?_).pow_const 8)
    exact (measurable_qpRR c0 c1 c2).comp (measurable_pi_apply j)
  have e := lint_transfer _ hH
  simp only [RR] at e
  rw [e]
  set Z : (Fin m → ℝ × ℝ) → ℝ := fun y => ∑ j, (qp c0 c1 c2 (RR (y j)) - μ) with hZd
  have hpt : ∀ y : Fin m → ℝ × ℝ, (∑ j, qp c0 c1 c2 ((y j).1 ^ 2 + (y j).2 ^ 2)) ^ 8 ≤
      A + B * Z y ^ 8 := by
    intro y
    have hs := sum_split (fun j => qp c0 c1 c2 (RR (y j))) μ
    simp only [RR] at hs
    rw [hs]
    have hm0 : 0 ≤ (m : ℝ) * μ := by positivity
    have t := two_point hm0 (abs_nonneg (Z y)) hε 7
    have habs : |(m : ℝ) * μ + Z y| ≤ (m : ℝ) * μ + |Z y| := by
      refine (abs_add_le _ _).trans ?_; rw [abs_of_nonneg hm0]
    calc ((m : ℝ) * μ + ∑ j, (qp c0 c1 c2 ((y j).1 ^ 2 + (y j).2 ^ 2) - μ)) ^ 8
        = |(m : ℝ) * μ + Z y| ^ 8 := by rw [Even.pow_abs (by decide)]; rfl
      _ ≤ ((m : ℝ) * μ + |Z y|) ^ (7 + 1) := pow_le_pow_left₀ (abs_nonneg _) habs 8
      _ ≤ A + B * Z y ^ 8 := by
        refine t.trans (le_of_eq ?_)
        rw [show 7 + 1 = 8 by rfl, Even.pow_abs (by decide)]
  have hZm : Measurable (fun y => ENNReal.ofReal (Z y ^ 8)) := by
    refine ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ => ?_).pow_const 8)
    exact ((measurable_qpRR c0 c1 c2).comp (measurable_pi_apply j)).sub measurable_const
  calc ∫⁻ y, ENNReal.ofReal ((∑ j, qp c0 c1 c2 ((y j).1 ^ 2 + (y j).2 ^ 2)) ^ 8)
        ∂(Measure.pi fun _ : Fin m => ρ2)
      ≤ ∫⁻ y, (ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal (Z y ^ 8))
          ∂(Measure.pi fun _ : Fin m => ρ2) := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_add hA (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt y)
    _ = ENNReal.ofReal A + ENNReal.ofReal B *
          ∫⁻ y, ENNReal.ofReal (Z y ^ 8) ∂(Measure.pi fun _ : Fin m => ρ2) := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul _ hZm, lintegral_const,
          measure_univ, mul_one]
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal (M8 m (c0 + c1 + c2) μ) := by
        gcongr; exact Zmom h0 h1 h2
    _ = _ := by
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_add hA (by
          have : 0 ≤ M8 m (c0 + c1 + c2) μ := by
            unfold M8
            have q := fun (E : ℝ) (hE : 0 ≤ E) (k : ℕ) =>
              Sb_nonneg (m := m) (K := c0 + c1 + c2) (by positivity) hμ hE k
            have := q 384 (by norm_num) 2; have := q 10321920 (by norm_num) 4
            have := q 1961990553600 (by norm_num) 6; have := q 1371195958099968000 (by norm_num) 8
            positivity
          positivity)]

lemma M8_nonneg {m : ℕ} {K μ : ℝ} (hK : 0 ≤ K) (hμ : 0 ≤ μ) : 0 ≤ M8 m K μ := by
  unfold M8
  have q := fun (E : ℝ) (hE : 0 ≤ E) (k : ℕ) => Sb_nonneg (m := m) hK hμ hE k
  have := q 384 (by norm_num) 2; have := q 10321920 (by norm_num) 4
  have := q 1961990553600 (by norm_num) 6; have := q 1371195958099968000 (by norm_num) 8
  positivity

/-- **The fourth moment of a sum of independent polynomial rows** (any `t > 0`). -/
theorem sum4_two {m : ℕ} {c0 c1 c2 ε t : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (hε : 0 < ε) (ht : 0 < t) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((∑ j : Fin m, qp c0 c1 c2 (ξ₁ j ^ 2 + ξ₂ j ^ 2)) ^ 4)
      ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((1 + ε) ^ 3 * (m * (c0 + 2 * c1 + 8 * c2)) ^ 4 +
        (1 + 1 / ε) ^ 3 * (M8 m (c0 + c1 + c2) (c0 + 2 * c1 + 8 * c2) / (2 * t) + t / 2)) := by
  set μ := c0 + 2 * c1 + 8 * c2 with hμd
  have hμ : 0 ≤ μ := by positivity
  set A := (1 + ε) ^ 3 * (m * μ) ^ 4 + (1 + 1 / ε) ^ 3 * (t / 2)
  set B := (1 + 1 / ε) ^ 3 / (2 * t)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hH : Measurable (fun y : Fin m → ℝ × ℝ =>
      ENNReal.ofReal ((∑ j, qp c0 c1 c2 (RR (y j))) ^ 4)) := by
    refine ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ => ?_).pow_const 4)
    exact (measurable_qpRR c0 c1 c2).comp (measurable_pi_apply j)
  have e := lint_transfer _ hH
  simp only [RR] at e
  rw [e]
  set Z : (Fin m → ℝ × ℝ) → ℝ := fun y => ∑ j, (qp c0 c1 c2 (RR (y j)) - μ) with hZd
  have hpt : ∀ y : Fin m → ℝ × ℝ, (∑ j, qp c0 c1 c2 ((y j).1 ^ 2 + (y j).2 ^ 2)) ^ 4 ≤
      A + B * Z y ^ 8 := by
    intro y
    have hs := sum_split (fun j => qp c0 c1 c2 (RR (y j))) μ
    simp only [RR] at hs
    rw [hs]
    have hm0 : 0 ≤ (m : ℝ) * μ := by positivity
    have tp := two_point hm0 (abs_nonneg (Z y)) hε 3
    have habs : |(m : ℝ) * μ + Z y| ≤ (m : ℝ) * μ + |Z y| := by
      refine (abs_add_le _ _).trans ?_; rw [abs_of_nonneg hm0]
    have h4 : |Z y| ^ 4 ≤ Z y ^ 8 / (2 * t) + t / 2 := by
      have e8 : Z y ^ 8 = (|Z y| ^ 4) ^ 2 := by
        rw [← pow_mul, Even.pow_abs (by decide)]
      rw [e8, div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|Z y| ^ 4 - t)]
    have hc : 0 ≤ (1 + 1 / ε) ^ 3 := by positivity
    calc ((m : ℝ) * μ + ∑ j, (qp c0 c1 c2 ((y j).1 ^ 2 + (y j).2 ^ 2) - μ)) ^ 4
        = |(m : ℝ) * μ + Z y| ^ 4 := by rw [Even.pow_abs (by decide)]; rfl
      _ ≤ ((m : ℝ) * μ + |Z y|) ^ (3 + 1) := pow_le_pow_left₀ (abs_nonneg _) habs 4
      _ ≤ (1 + ε) ^ 3 * ((m : ℝ) * μ) ^ (3 + 1) + (1 + 1 / ε) ^ 3 * |Z y| ^ (3 + 1) := tp
      _ ≤ A + B * Z y ^ 8 := by
        have := mul_le_mul_of_nonneg_left h4 hc
        simp only [A, B]
        rw [show 3 + 1 = 4 by rfl]
        have e3 : (1 + 1 / ε) ^ 3 * (Z y ^ 8 / (2 * t) + t / 2) =
          (1 + 1 / ε) ^ 3 * (t / 2) + (1 + 1 / ε) ^ 3 / (2 * t) * Z y ^ 8 := by ring
        linarith
  have hZm : Measurable (fun y => ENNReal.ofReal (Z y ^ 8)) := by
    refine ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ => ?_).pow_const 8)
    exact ((measurable_qpRR c0 c1 c2).comp (measurable_pi_apply j)).sub measurable_const
  have hM := M8_nonneg (m := m) (K := c0 + c1 + c2) (by positivity) hμ
  calc ∫⁻ y, ENNReal.ofReal ((∑ j, qp c0 c1 c2 ((y j).1 ^ 2 + (y j).2 ^ 2)) ^ 4)
        ∂(Measure.pi fun _ : Fin m => ρ2)
      ≤ ∫⁻ y, (ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal (Z y ^ 8))
          ∂(Measure.pi fun _ : Fin m => ρ2) := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_add hA (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt y)
    _ = ENNReal.ofReal A + ENNReal.ofReal B *
          ∫⁻ y, ENNReal.ofReal (Z y ^ 8) ∂(Measure.pi fun _ : Fin m => ρ2) := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul _ hZm, lintegral_const,
          measure_univ, mul_one]
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal (M8 m (c0 + c1 + c2) μ) := by
        gcongr; exact Zmom h0 h1 h2
    _ = _ := by
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_add hA (by positivity)]
        congr 1
        simp only [A, B]; ring

end BstLean.Part186.RA
