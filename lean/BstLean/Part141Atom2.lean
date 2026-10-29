import BstLean.Part141Atom

/-!
# Part 141, optional: a SECOND-ORDER finite ReLU sum (atoms at the conditional means of the cells)

Role: `delegations/statements/p141-spec.md`, item 1 (an improvement of `atomSum141`).

The cells are those of `Part141Defs` (`quant q R`): the interior cells are the intervals
`[j/q, (j+1)/q)`, `−Rq < j < Rq`; the cell `j = −Rq` is `{z < −R + 1/q}`; the cell `j = Rq` is
`{z ≥ R}`. The weights are the rational weights `pQ q R D` of `Part141Defs`.

* `atomZ q R j`, `mR q R ℓ`: the real atoms: `−R`, `R` for the two tail cells, and the conditional
  mean of a standard Gaussian number in the cell for an interior cell.
* `zM q R E ℓ = ⌊E·mR ℓ⌋/E`: the rational atoms.
* `atom_couple2`: `|Σ_ℓ pR ℓ·relu(x + s·mR ℓ) − ψ_s(x)| ≤ s·(6/5/q² + 12/2^R)`.
* **`atomSum2_141`**: `|Σ_ℓ pQ ℓ·relu(x + s·zM ℓ) − ψ_s(x)| ≤
  s·(2/q² + 16/2^R + 4(R + 1)²q/D + 1/E)`, every `x`, every `s ≥ 0`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part137

/-! ## Definitions -/

/-- The real atom of the cell with index `j`. -/
noncomputable def atomZ (q R : ℕ) (j : ℤ) : ℝ :=
  if j = -((R * q : ℕ) : ℤ) then -(R : ℝ)
  else if j = ((R * q : ℕ) : ℤ) then (R : ℝ)
  else (∫ z in {z : ℝ | quant q R z = j}, z ∂gaussianReal 0 1) /
    (gaussianReal 0 1).real {z : ℝ | quant q R z = j}

/-- **The real atoms**: `−R` and `R` for the two tail cells, the conditional mean for an interior
cell. -/
noncomputable def mR (q R : ℕ) : Fin (2 * R * q + 1) → ℝ := fun ℓ => atomZ q R (off q R ℓ)

/-- **The rational atoms**: `⌊E·mR ℓ⌋/E`. -/
noncomputable def zM (q R E : ℕ) : Fin (2 * R * q + 1) → ℚ := fun ℓ =>
  ((⌊(E : ℝ) * mR q R ℓ⌋ : ℤ) : ℚ) / (E : ℚ)

/-! ## The clipping and the cells -/

lemma clip_eq (R : ℕ) {z : ℝ} (h1 : -(R : ℝ) ≤ z) (h2 : z ≤ R) :
    max (-(R : ℝ)) (min (R : ℝ) z) = z := by
  rw [min_eq_right h2, max_eq_right h1]

lemma clip_le (R : ℕ) (z : ℝ) : max (-(R : ℝ)) (min (R : ℝ) z) ≤ R := by
  have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  exact max_le (by linarith) (min_le_left _ _)

lemma clip_lt {R : ℕ} {z : ℝ} (h : max (-(R : ℝ)) (min (R : ℝ) z) < R) : z < R := by
  by_contra hz
  push Not at hz
  have : (R : ℝ) ≤ max (-(R : ℝ)) (min (R : ℝ) z) := by
    rw [min_eq_left hz]
    exact le_max_right _ _
  linarith

lemma clip_gt {R : ℕ} {z : ℝ} (h : -(R : ℝ) < max (-(R : ℝ)) (min (R : ℝ) z)) : -(R : ℝ) < z := by
  by_contra hz
  push Not at hz
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  rw [min_eq_right (by linarith), max_eq_left hz] at h
  exact lt_irrefl _ h

lemma quant_bounds (q R : ℕ) (z : ℝ) :
    ((quant q R z : ℤ) : ℝ) ≤ max (-(R : ℝ)) (min (R : ℝ) z) * (q : ℝ) ∧
      max (-(R : ℝ)) (min (R : ℝ) z) * (q : ℝ) < ((quant q R z : ℤ) : ℝ) + 1 :=
  ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

lemma quant_range (q R : ℕ) (z : ℝ) :
    -((R * q : ℕ) : ℤ) ≤ quant q R z ∧ quant q R z ≤ ((R * q : ℕ) : ℤ) := by
  obtain ⟨ℓ, hℓ⟩ := quant_mem q R z
  have h1 : (ℓ : ℕ) < 2 * R * q + 1 := ℓ.isLt
  have h2 : 2 * R * q = 2 * (R * q) := by ring
  rw [hℓ]
  unfold off
  omega

/-- An interior cell is an interval of length `1/q`. -/
lemma cell_interior {q R : ℕ} (hq : 1 ≤ q) {j : ℤ} (h1 : -((R * q : ℕ) : ℤ) < j)
    (h2 : j < ((R * q : ℕ) : ℤ)) :
    {z : ℝ | quant q R z = j} = Set.Ico ((j : ℝ) / q) (((j : ℝ) + 1) / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1' : -((R : ℝ) * q) + 1 ≤ (j : ℝ) := by
    have h : -((R * q : ℕ) : ℤ) + 1 ≤ j := by omega
    have h' := (Int.cast_le (R := ℝ)).mpr h
    push_cast at h'
    linarith
  have h2' : (j : ℝ) + 1 ≤ (R : ℝ) * q := by
    have h : j + 1 ≤ ((R * q : ℕ) : ℤ) := by omega
    have h' := (Int.cast_le (R := ℝ)).mpr h
    push_cast at h'
    linarith
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_Ico]
  unfold quant
  rw [Int.floor_eq_iff]
  constructor
  · rintro ⟨ha, hb⟩
    have c1 : -(R : ℝ) < max (-(R : ℝ)) (min (R : ℝ) z) := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hq'.le
      linarith
    have c2 : max (-(R : ℝ)) (min (R : ℝ) z) < R := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hq'.le
      linarith
    rw [clip_eq R (clip_gt c1).le (clip_lt c2).le] at ha hb
    exact ⟨by rw [div_le_iff₀ hq']; exact ha, by rw [lt_div_iff₀ hq']; exact hb⟩
  · rintro ⟨ha, hb⟩
    rw [div_le_iff₀ hq'] at ha
    rw [lt_div_iff₀ hq'] at hb
    have z1 : -(R : ℝ) ≤ z := by
      by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_right hc hq'
      linarith
    have z2 : z ≤ R := by
      by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_right hc hq'
      linarith
    rw [clip_eq R z1 z2]
    exact ⟨ha, hb⟩

lemma gauss_Ico_pos {a b : ℝ} (h : a < b) : 0 < (gaussianReal 0 1).real (Set.Ico a b) := by
  have hne : gaussianReal 0 1 (Set.Ico a b) ≠ 0 := by
    intro h0
    have h1 := gaussianReal_absolutelyContinuous' 0 (one_ne_zero) h0
    rw [Real.volume_Ico] at h1
    simp at h1
    linarith
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

lemma integrable_id_gauss : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
  simpa using integrable_pow_gauss 1

/-- The atom of a cell is in the closure of the cell (for the clipped variable). -/
lemma atom_mem {q R : ℕ} (hq : 1 ≤ q) {j : ℤ} (h1 : -((R * q : ℕ) : ℤ) ≤ j)
    (h2 : j ≤ ((R * q : ℕ) : ℤ)) :
    (j : ℝ) / q ≤ atomZ q R j ∧ atomZ q R j ≤ ((j : ℝ) + 1) / q ∧ atomZ q R j ≤ R ∧
      -(R : ℝ) ≤ atomZ q R j := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have h1' : -((R : ℝ) * q) ≤ (j : ℝ) := by
    have h' := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at h'
    linarith
  have h2' : (j : ℝ) ≤ (R : ℝ) * q := by
    have h' := (Int.cast_le (R := ℝ)).mpr h2
    push_cast at h'
    linarith
  have hlow : -(R : ℝ) ≤ (j : ℝ) / q := by
    rw [le_div_iff₀ hq']
    linarith
  unfold atomZ
  by_cases e1 : j = -((R * q : ℕ) : ℤ)
  · rw [if_pos e1]
    have ej : (j : ℝ) = -((R : ℝ) * q) := by rw [e1]; push_cast; ring
    refine ⟨?_, ?_, by linarith, le_rfl⟩
    · rw [div_le_iff₀ hq']; linarith
    · rw [le_div_iff₀ hq']; linarith
  · rw [if_neg e1]
    by_cases e2 : j = ((R * q : ℕ) : ℤ)
    · rw [if_pos e2]
      have ej : (j : ℝ) = (R : ℝ) * q := by rw [e2]; push_cast; ring
      refine ⟨?_, ?_, le_rfl, by linarith⟩
      · rw [div_le_iff₀ hq']; linarith
      · rw [le_div_iff₀ hq']; linarith
    · rw [if_neg e2]
      have hlt1 : -((R * q : ℕ) : ℤ) < j := lt_of_le_of_ne h1 (Ne.symm e1)
      have hlt2 : j < ((R * q : ℕ) : ℤ) := lt_of_le_of_ne h2 e2
      have h2'' : (j : ℝ) + 1 ≤ (R : ℝ) * q := by
        have h : j + 1 ≤ ((R * q : ℕ) : ℤ) := by omega
        have h' := (Int.cast_le (R := ℝ)).mpr h
        push_cast at h'
        linarith
      rw [cell_interior hq hlt1 hlt2]
      set a : ℝ := (j : ℝ) / q with ha
      set b : ℝ := ((j : ℝ) + 1) / q with hb
      have hab : a < b := by
        rw [ha, hb]
        exact div_lt_div_of_pos_right (by linarith) hq'
      have hp := gauss_Ico_pos hab
      have hi : IntegrableOn (fun z : ℝ => z) (Set.Ico a b) (gaussianReal 0 1) :=
        integrable_id_gauss.integrableOn
      have l1 : a * (gaussianReal 0 1).real (Set.Ico a b) ≤
          ∫ z in Set.Ico a b, z ∂gaussianReal 0 1 := by
        have h := setIntegral_mono_on (μ := gaussianReal 0 1)
          (integrable_const a).integrableOn hi measurableSet_Ico (fun z hz => hz.1)
        rw [setIntegral_const, smul_eq_mul] at h
        linarith [mul_comm a ((gaussianReal 0 1).real (Set.Ico a b))]
      have l2 : ∫ z in Set.Ico a b, z ∂gaussianReal 0 1 ≤
          b * (gaussianReal 0 1).real (Set.Ico a b) := by
        have h := setIntegral_mono_on (μ := gaussianReal 0 1) hi
          (integrable_const b).integrableOn measurableSet_Ico (fun z hz => hz.2.le)
        rw [setIntegral_const, smul_eq_mul] at h
        linarith [mul_comm b ((gaussianReal 0 1).real (Set.Ico a b))]
      have hbR : b ≤ R := by
        rw [hb, div_le_iff₀ hq']
        exact h2''
      have u1 : a ≤ (∫ z in Set.Ico a b, z ∂gaussianReal 0 1) /
          (gaussianReal 0 1).real (Set.Ico a b) := by
        rw [le_div_iff₀ hp]; exact l1
      have u2 : (∫ z in Set.Ico a b, z ∂gaussianReal 0 1) /
          (gaussianReal 0 1).real (Set.Ico a b) ≤ b := by
        rw [div_le_iff₀ hp]; exact l2
      exact ⟨u1, u2, u2.trans hbR, hlow.trans u1⟩

/-- `|clip(z) − atom(z)| ≤ 1/q`. -/
lemma clip_atom {q : ℕ} (hq : 1 ≤ q) (R : ℕ) (z : ℝ) :
    |max (-(R : ℝ)) (min (R : ℝ) z) - atomZ q R (quant q R z)| ≤ 1 / (q : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨r1, r2⟩ := quant_range q R z
  obtain ⟨b1, b2⟩ := quant_bounds q R z
  obtain ⟨a1, a2, -, -⟩ := atom_mem hq r1 r2
  set c : ℝ := max (-(R : ℝ)) (min (R : ℝ) z)
  set k : ℝ := ((quant q R z : ℤ) : ℝ)
  have c1 : k / q ≤ c := by rw [div_le_iff₀ hq']; exact b1
  have c2 : c < (k + 1) / q := by rw [lt_div_iff₀ hq']; exact b2
  have e : (k + 1) / q - k / q = 1 / (q : ℝ) := by ring
  rw [abs_le]
  constructor <;> linarith

/-! ## The tail function and the density bound -/

/-- `exp(|z| − R)`: a bound of the clipping error and of the indicator of `|z| > R`. -/
noncomputable def exT (R : ℕ) (z : ℝ) : ℝ := rexp (|z| - R)

lemma exT_pos (R : ℕ) (z : ℝ) : 0 < exT R z := Real.exp_pos _

lemma exT_le (R : ℕ) (z : ℝ) :
    exT R z ≤ (rexp (1 * z) + rexp (-1 * z)) * rexp (-(R : ℝ)) := by
  unfold exT
  rw [sub_eq_add_neg, Real.exp_add]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h, one_mul]
    linarith [Real.exp_pos (-1 * z)]
  · rw [abs_of_nonpos h, neg_one_mul]
    linarith [Real.exp_pos (1 * z)]

lemma exT_int (R : ℕ) : Integrable (exT R) (gaussianReal 0 1) ∧
    ∫ z, exT R z ∂gaussianReal 0 1 ≤ 4 / (2 : ℝ) ^ R := by
  have ie : ∀ t : ℝ, Integrable (fun z : ℝ => rexp (t * z)) (gaussianReal 0 1) := fun t =>
    integrable_exp_mul_gaussianReal t
  have i2 : Integrable (fun a : ℝ => (rexp (1 * a) + rexp (-1 * a)) * rexp (-(R : ℝ)))
      (gaussianReal 0 1) := ((ie 1).add (ie (-1))).mul_const _
  have hc : Continuous (exT R) := by
    unfold exT
    exact Real.continuous_exp.comp (continuous_abs.sub continuous_const)
  have hi : Integrable (exT R) (gaussianReal 0 1) := by
    refine Integrable.mono' i2 hc.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exT_pos R z)]
    exact exT_le R z
  refine ⟨hi, ?_⟩
  have h := integral_mono hi i2 (exT_le R)
  rw [integral_mul_const, integral_add (ie 1) (ie (-1)), mgf_gauss, mgf_gauss] at h
  have e1 : ((1 : ℝ)) ^ 2 / 2 = 1 / 2 := by norm_num
  have e2 : ((-1 : ℝ)) ^ 2 / 2 = 1 / 2 := by norm_num
  rw [e1, e2] at h
  have h1 := exp_half_le
  have h2 := exp_neg_nat_le R
  have h3 : (0 : ℝ) ≤ rexp (-(R : ℝ)) := (Real.exp_pos _).le
  have h4 : (rexp (1 / 2) + rexp (1 / 2)) * rexp (-(R : ℝ)) ≤ 4 * (1 / (2 : ℝ) ^ R) :=
    mul_le_mul (by linarith) h2 h3 (by norm_num)
  have e3 : (4 : ℝ) / (2 : ℝ) ^ R = 4 * (1 / (2 : ℝ) ^ R) := by ring
  rw [e3]
  linarith

/-- The standard Gaussian density is at most `2/5`: `Pr(a ≤ Z ≤ b) ≤ (2/5)(b − a)`. -/
lemma gauss_Icc_le {a b : ℝ} (h : a ≤ b) :
    (gaussianReal 0 1).real (Set.Icc a b) ≤ 2 / 5 * (b - a) := by
  have hpdf : ∀ x, gaussianPDFReal 0 1 x ≤ 2 / 5 := by
    intro x
    unfold gaussianPDFReal
    have h1 : (5 / 2 : ℝ) ≤ √(2 * π * ((1 : NNReal) : ℝ)) := by
      rw [NNReal.coe_one, mul_one]
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.pi_gt_d2]
    have h2 : (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹ ≤ 2 / 5 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 5 / 2) h1
      norm_num at this ⊢
      linarith
    have h3 : rexp (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
    calc _ ≤ (2 / 5 : ℝ) * 1 := mul_le_mul h2 h3 (Real.exp_pos _).le (by norm_num)
      _ = 2 / 5 := by ring
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
      fun x _ => gaussianPDFReal_nonneg _ _ _)]
  calc ∫ x in Set.Icc a b, gaussianPDFReal 0 1 x ≤ ∫ x in Set.Icc a b, (2 / 5 : ℝ) :=
        setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          (continuousOn_const.integrableOn_Icc) measurableSet_Icc (fun x _ => hpdf x)
    _ = 2 / 5 * (b - a) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le h, smul_eq_mul]
        ring

/-! ## The integral of a function of the cell times an integrable function -/

lemma cell_integral2 (q R : ℕ) {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1)) (F : ℤ → ℝ) :
    Integrable (fun z => F (quant q R z) * h z) (gaussianReal 0 1) ∧
      ∫ z, F (quant q R z) * h z ∂gaussianReal 0 1 =
        ∑ ℓ, F (off q R ℓ) *
          ∫ z in {z : ℝ | quant q R z = off q R ℓ}, h z ∂gaussianReal 0 1 := by
  have hpt : ∀ z, F (quant q R z) * h z = ∑ ℓ, ({z : ℝ | quant q R z = off q R ℓ}).indicator
      (fun z => F (off q R ℓ) * h z) z := by
    intro z
    obtain ⟨ℓ0, h0⟩ := quant_mem q R z
    rw [Finset.sum_eq_single ℓ0]
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ | quant q R z = off q R ℓ0} from h0), h0]
    · intro b _ hb
      exact Set.indicator_of_notMem
        (show z ∉ {z : ℝ | quant q R z = off q R b} from
          fun hh => hb (off_inj q R (Eq.trans (Eq.symm hh) h0))) _
    · intro hne
      exact absurd (Finset.mem_univ _) hne
  have hint : ∀ ℓ, Integrable (({z : ℝ | quant q R z = off q R ℓ}).indicator
      (fun z => F (off q R ℓ) * h z)) (gaussianReal 0 1) := fun ℓ =>
    (hh.const_mul _).indicator (measurableSet_cell q R ℓ)
  have e : (fun z => F (quant q R z) * h z) = fun z => ∑ ℓ,
      ({z : ℝ | quant q R z = off q R ℓ}).indicator (fun z => F (off q R ℓ) * h z) z :=
    funext hpt
  rw [e]
  refine ⟨integrable_finsetSum _ (fun ℓ _ => hint ℓ), ?_⟩
  rw [integral_finsetSum _ (fun ℓ _ => hint ℓ)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hind := integral_indicator (μ := gaussianReal 0 1)
    (f := fun z => F (off q R ℓ) * h z) (measurableSet_cell q R ℓ)
  rw [hind]
  exact integral_const_mul _ _

/-! ## Pointwise bounds -/

/-- The second-order remainder of `relu`. -/
lemma rho_bound (u v : ℝ) :
    0 ≤ relu u - relu v - (if 0 < v then (1 : ℝ) else 0) * (u - v) ∧
    relu u - relu v - (if 0 < v then (1 : ℝ) else 0) * (u - v) ≤ |u - v| ∧
    (relu u - relu v - (if 0 < v then (1 : ℝ) else 0) * (u - v) = 0 ∨ |u| ≤ |u - v|) := by
  by_cases hv : 0 < v
  · rw [if_pos hv, relu_of_nonneg hv.le]
    rcases le_total 0 u with hu | hu
    · rw [relu_of_nonneg hu]
      exact ⟨by linarith, by linarith [abs_nonneg (u - v)], Or.inl (by ring)⟩
    · rw [relu_of_nonpos hu]
      have e : |u - v| = v - u := by rw [abs_of_nonpos (by linarith)]; ring
      have e2 : |u| = -u := abs_of_nonpos hu
      exact ⟨by linarith, by rw [e]; linarith, Or.inr (by rw [e, e2]; linarith)⟩
  · rw [if_neg hv, relu_of_nonpos (not_lt.mp hv)]
    have hv' := not_lt.mp hv
    rcases le_total 0 u with hu | hu
    · rw [relu_of_nonneg hu]
      have e : |u - v| = u - v := abs_of_nonneg (by linarith)
      exact ⟨by linarith, by rw [e]; linarith, Or.inr (by rw [e, abs_of_nonneg hu]; linarith)⟩
    · rw [relu_of_nonpos hu]
      exact ⟨by simp, by simp, Or.inl (by ring)⟩

/-- On the two tail cells: `|z − atom| ≤ (1/q)·1_{[−R, −R + 1/q]}(z) + exp(|z| − R)`. -/
lemma tail_pt {q R : ℕ} (hq : 1 ≤ q) (hR : 1 ≤ R) (z : ℝ)
    (h : quant q R z = -((R * q : ℕ) : ℤ) ∨ quant q R z = ((R * q : ℕ) : ℤ)) :
    |z - atomZ q R (quant q R z) * 1| ≤
      (Set.Icc (-(R : ℝ)) (-(R : ℝ) + 1 / q)).indicator (fun _ => 1 / (q : ℝ)) z + exT R z := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRq : (1 : ℝ) ≤ (R : ℝ) * q := by nlinarith
  obtain ⟨b1, b2⟩ := quant_bounds q R z
  have hex := exT_pos R z
  have hind0 : 0 ≤ (Set.Icc (-(R : ℝ)) (-(R : ℝ) + 1 / q)).indicator
      (fun _ => 1 / (q : ℝ)) z := Set.indicator_nonneg (fun _ _ => by positivity) _
  have hexp : |z| - R + 1 ≤ exT R z := Real.add_one_le_exp _
  rw [mul_one]
  rcases h with h | h
  · have eA : atomZ q R (-((R * q : ℕ) : ℤ)) = -(R : ℝ) := by unfold atomZ; rw [if_pos rfl]
    rw [h] at b2 ⊢
    rw [eA]
    push_cast at b2
    by_cases hz : z < -(R : ℝ)
    · have e1 : |z| = -z := abs_of_nonpos (by linarith)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · push Not at hz
      have c2 : max (-(R : ℝ)) (min (R : ℝ) z) < R := by
        by_contra hc
        push Not at hc
        have := mul_le_mul_of_nonneg_right hc hq'.le
        linarith
      have z2 := clip_lt c2
      rw [clip_eq R hz z2.le] at b2
      have hzq : z < -(R : ℝ) + 1 / q := by
        rw [← sub_lt_iff_lt_add', lt_div_iff₀ hq']
        linarith
      rw [Set.indicator_of_mem (show z ∈ Set.Icc (-(R : ℝ)) (-(R : ℝ) + 1 / q) from
        ⟨hz, hzq.le⟩), abs_of_nonneg (by linarith)]
      linarith
  · have hK : (1 : ℤ) ≤ ((R * q : ℕ) : ℤ) := by
      have : 1 ≤ R * q := Nat.mul_pos hR hq
      exact_mod_cast this
    have eA : atomZ q R (((R * q : ℕ) : ℤ)) = (R : ℝ) := by
      unfold atomZ
      rw [if_neg (by omega), if_pos rfl]
    rw [h] at b1 ⊢
    rw [eA]
    push_cast at b1
    have c1 : (R : ℝ) ≤ max (-(R : ℝ)) (min (R : ℝ) z) := by
      by_contra hc
      push Not at hc
      have := mul_lt_mul_of_pos_right hc hq'
      linarith
    have hz : (R : ℝ) ≤ z := by
      by_contra hc
      push Not at hc
      rw [min_eq_right hc.le] at c1
      have : max (-(R : ℝ)) z < R := max_lt (by linarith) hc
      linarith
    have e1 : |z| = z := abs_of_nonneg (by linarith)
    rw [abs_of_nonneg (by linarith)]
    linarith

/-! ## The coupling with the conditional means -/

/-- **The second-order coupling.**
`|Σ_ℓ pR ℓ·relu(x + s·mR ℓ) − ψ_s(x)| ≤ s·(6/5/q² + 12/2^R)`. -/
theorem atom_couple2 {q R : ℕ} (hq : 1 ≤ q) (hR : 1 ≤ R) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    |atomSum (pR q R) (mR q R) s x - psiS s x| ≤
      s * (6 / 5 / (q : ℝ) ^ 2 + 12 / (2 : ℝ) ^ R) := by
  rcases hs.eq_or_lt with h0 | hs'
  · subst h0
    have e1 : atomSum (pR q R) (mR q R) 0 x = relu x := by
      unfold atomSum
      simp only [zero_mul, add_zero]
      rw [← Finset.sum_mul, pR_sum, one_mul]
    have e2 : psiS 0 x = relu x := by unfold psiS; simp
    rw [e1, e2]
    simp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ht1 : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hq']; exact hqR
  have ht0 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  set γ := gaussianReal 0 1 with hγ
  set G : ℤ → ℝ := fun k => if 0 < x + s * atomZ q R k then 1 else 0 with hG
  set I : Set ℝ := Set.Icc (-(R : ℝ)) (-(R : ℝ) + 1 / q) with hI
  set w : ℝ → ℝ := fun z => I.indicator (fun _ => 1 / (q : ℝ)) z + exT R z with hw
  set B : Set ℝ := Set.Icc (-x / s - 1 / q) (-x / s + 1 / q) with hB
  set bd : ℝ → ℝ := fun z => B.indicator (fun _ => s * (1 / (q : ℝ))) z +
    s * (1 / (q : ℝ) + 1) * exT R z with hbd
  obtain ⟨hi2, hv2⟩ := cell_integral q R (fun k : ℤ => relu (x + s * atomZ q R k))
  have ev : atomSum (pR q R) (mR q R) s x =
      ∫ z, relu (x + s * atomZ q R (quant q R z)) ∂γ := by
    rw [hv2]
    rfl
  obtain ⟨hiA, hvA⟩ := cell_integral2 q R integrable_id_gauss G
  obtain ⟨hiB, hvB⟩ := cell_integral2 q R (integrable_const (1 : ℝ))
    (fun k => G k * atomZ q R k)
  obtain ⟨hEi, hEb⟩ := exT_int R
  have hwi : Integrable w γ := ((integrable_const _).indicator measurableSet_Icc).add hEi
  have hw0 : ∀ z, 0 ≤ w z := fun z =>
    add_nonneg (Set.indicator_nonneg (fun _ _ => ht0.le) _) (exT_pos R z).le
  obtain ⟨hiW, hvW⟩ := cell_integral2 q R hwi (fun _ => 1)
  have hbdi : Integrable bd γ :=
    ((integrable_const _).indicator measurableSet_Icc).add (hEi.const_mul _)
  set lin : ℝ → ℝ := fun z => s * (G (quant q R z) * z -
    G (quant q R z) * atomZ q R (quant q R z) * 1) with hlin
  have hlini : Integrable lin γ := (hiA.sub hiB).const_mul s
  set r : ℝ → ℝ := fun z => relu (x + s * z) - relu (x + s * atomZ q R (quant q R z)) - lin z
    with hr
  have hri : Integrable r γ := ((integrable_relu_shift x s).sub hi2).sub hlini
  have hsplit : ∫ z, relu (x + s * z) ∂γ - ∫ z, relu (x + s * atomZ q R (quant q R z)) ∂γ =
      ∫ z, lin z ∂γ + ∫ z, r z ∂γ := by
    rw [← integral_sub (integrable_relu_shift x s) hi2, ← integral_add hlini hri]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hr]
    ring
  -- the linear part
  have hJ : ∀ ℓ : Fin (2 * R * q + 1),
      |(∫ z in {z : ℝ | quant q R z = off q R ℓ}, z ∂γ) -
        atomZ q R (off q R ℓ) * ∫ z in {z : ℝ | quant q R z = off q R ℓ}, (1 : ℝ) ∂γ| ≤
      ∫ z in {z : ℝ | quant q R z = off q R ℓ}, w z ∂γ := by
    intro ℓ
    set C : Set ℝ := {z : ℝ | quant q R z = off q R ℓ} with hC
    have mC : MeasurableSet C := measurableSet_cell q R ℓ
    by_cases htail : off q R ℓ = -((R * q : ℕ) : ℤ) ∨ off q R ℓ = ((R * q : ℕ) : ℤ)
    · have e : (∫ z in C, z ∂γ) - atomZ q R (off q R ℓ) * ∫ z in C, (1 : ℝ) ∂γ =
          ∫ z in C, (z - atomZ q R (off q R ℓ) * 1) ∂γ := by
        rw [integral_sub integrable_id_gauss.integrableOn
          ((integrable_const (1 : ℝ)).const_mul _).integrableOn, integral_const_mul]
      rw [e]
      have hfi : Integrable (fun z : ℝ => z - atomZ q R (off q R ℓ) * 1) γ :=
        integrable_id_gauss.sub (integrable_const _)
      refine abs_integral_le_integral_abs.trans ?_
      refine setIntegral_mono_on hfi.abs.integrableOn hwi.integrableOn mC (fun z hz => ?_)
      have hz' : quant q R z = off q R ℓ := hz
      have := tail_pt hq hR z (by rw [hz']; exact htail)
      rw [hz'] at this
      exact this
    · push Not at htail
      have e0 : (∫ z in C, z ∂γ) - atomZ q R (off q R ℓ) * ∫ z in C, (1 : ℝ) ∂γ = 0 := by
        unfold atomZ
        rw [if_neg htail.1, if_neg htail.2, setIntegral_const, smul_eq_mul, mul_one]
        by_cases hp : γ.real C = 0
        · have h0 : γ C = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hp
          rw [setIntegral_measure_zero _ h0]
          simp
        · rw [div_mul_cancel₀ _ hp, sub_self]
      rw [e0, abs_zero]
      exact setIntegral_nonneg mC (fun z _ => hw0 z)
  have hG1 : ∀ k, |G k| ≤ 1 := by
    intro k
    simp only [hG]
    split_ifs <;> simp
  have hlinb : |∫ z, lin z ∂γ| ≤ s * ∫ z, w z ∂γ := by
    have e : ∫ z, lin z ∂γ = s * ∑ ℓ : Fin (2 * R * q + 1), G (off q R ℓ) *
        ((∫ z in {z : ℝ | quant q R z = off q R ℓ}, z ∂γ) -
          atomZ q R (off q R ℓ) * ∫ z in {z : ℝ | quant q R z = off q R ℓ}, (1 : ℝ) ∂γ) := by
      simp only [hlin]
      rw [integral_const_mul, integral_sub hiA hiB, hvA, hvB, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    have e2 : ∫ z, w z ∂γ = ∑ ℓ : Fin (2 * R * q + 1),
        ∫ z in {z : ℝ | quant q R z = off q R ℓ}, w z ∂γ := by
      have := hvW
      simp only [one_mul] at this
      exact this
    rw [e, abs_mul, abs_of_pos hs', e2]
    refine mul_le_mul_of_nonneg_left ?_ hs
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
    rw [abs_mul]
    calc |G (off q R ℓ)| * _ ≤ 1 * _ :=
          mul_le_mul_of_nonneg_right (hG1 _) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hJ ℓ
  have hwint : ∫ z, w z ∂γ ≤ 2 / 5 / (q : ℝ) ^ 2 + 4 / (2 : ℝ) ^ R := by
    simp only [hw]
    rw [integral_add ((integrable_const _).indicator measurableSet_Icc) hEi,
      integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    have h1 := gauss_Icc_le (a := -(R : ℝ)) (b := -(R : ℝ) + 1 / q) (by linarith)
    have h2 : γ.real I * (1 / (q : ℝ)) ≤ 2 / 5 * (1 / (q : ℝ)) * (1 / (q : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ ht0.le
      rw [hI]
      linarith
    have e : 2 / 5 * (1 / (q : ℝ)) * (1 / (q : ℝ)) = 2 / 5 / (q : ℝ) ^ 2 := by
      field_simp
    linarith
  -- the remainder
  have hrpt : ∀ z, |r z| ≤ bd z := by
    intro z
    set A : ℝ := atomZ q R (quant q R z) with hA
    obtain ⟨p1, p2, p3⟩ := rho_bound (x + s * z) (x + s * A)
    have er : r z = relu (x + s * z) - relu (x + s * A) -
        (if 0 < x + s * A then (1 : ℝ) else 0) * (x + s * z - (x + s * A)) := by
      simp only [hr, hlin, hG]
      ring
    rw [er, abs_of_nonneg p1]
    have hca := clip_atom hq R z
    have hcz := clip_err R z
    have ed : |x + s * z - (x + s * A)| = s * |z - A| := by
      rw [show x + s * z - (x + s * A) = s * (z - A) by ring, abs_mul, abs_of_pos hs']
    rw [ed] at p2 p3
    have hex0 := exT_pos R z
    have hind0 : 0 ≤ B.indicator (fun _ => s * (1 / (q : ℝ))) z :=
      Set.indicator_nonneg (fun _ _ => by positivity) _
    have hpos2 : 0 ≤ s * (1 / (q : ℝ) + 1) * exT R z := by positivity
    simp only [hbd]
    by_cases hz : |z| ≤ R
    · rw [clip_eq R (neg_le_of_abs_le hz) (le_of_abs_le hz)] at hca
      have hle : s * |z - A| ≤ s * (1 / (q : ℝ)) := mul_le_mul_of_nonneg_left hca hs
      by_cases hBz : z ∈ B
      · rw [Set.indicator_of_mem hBz]
        linarith
      · rcases p3 with p3 | p3
        · rw [p3]
          linarith
        · exfalso
          apply hBz
          have h3 := abs_le.mp (p3.trans hle)
          constructor
          · rw [sub_le_iff_le_add, div_le_iff₀ hs']
            have : (z + 1 / (q : ℝ)) * s = s * z + s * (1 / (q : ℝ)) := by ring
            rw [this]
            linarith [h3.1]
          · rw [← sub_le_iff_le_add, le_div_iff₀ hs']
            have : (z - 1 / (q : ℝ)) * s = s * z - s * (1 / (q : ℝ)) := by ring
            rw [this]
            linarith [h3.2]
    · push Not at hz
      have hone : 1 ≤ exT R z := by
        unfold exT
        exact Real.one_le_exp (by linarith)
      have hzA : |z - A| ≤ exT R z + 1 / (q : ℝ) := by
        have h := abs_sub_le z (max (-(R : ℝ)) (min (R : ℝ) z)) A
        have h' : |z - max (-(R : ℝ)) (min (R : ℝ) z)| ≤ exT R z := by
          rw [abs_sub_comm]
          exact hcz
        linarith
      have h1 : 1 / (q : ℝ) ≤ 1 / (q : ℝ) * exT R z := le_mul_of_one_le_right ht0.le hone
      have h2 : s * |z - A| ≤ s * ((1 / (q : ℝ) + 1) * exT R z) :=
        mul_le_mul_of_nonneg_left (by linarith) hs
      have e : s * ((1 / (q : ℝ) + 1) * exT R z) = s * (1 / (q : ℝ) + 1) * exT R z := by ring
      linarith
  have hrb : |∫ z, r z ∂γ| ≤ s * (4 / 5 / (q : ℝ) ^ 2 + 8 / (2 : ℝ) ^ R) := by
    have h1 : |∫ z, r z ∂γ| ≤ ∫ z, bd z ∂γ := by
      have := norm_integral_le_of_norm_le hbdi
        (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hrpt z)
      rwa [Real.norm_eq_abs] at this
    refine h1.trans ?_
    simp only [hbd]
    rw [integral_add ((integrable_const _).indicator measurableSet_Icc) (hEi.const_mul _),
      integral_indicator_const _ measurableSet_Icc, smul_eq_mul, integral_const_mul]
    have hB1 := gauss_Icc_le (a := -x / s - 1 / q) (b := -x / s + 1 / q) (by linarith)
    have h2 : γ.real B * (s * (1 / (q : ℝ))) ≤ 2 / 5 * (2 * (1 / (q : ℝ))) * (s * (1 / (q : ℝ))) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [hB]
      linarith
    have h3 : s * (1 / (q : ℝ) + 1) * ∫ z, exT R z ∂γ ≤ s * 2 * (4 / (2 : ℝ) ^ R) := by
      have hE0 : 0 ≤ ∫ z, exT R z ∂γ := integral_nonneg fun z => (exT_pos R z).le
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hs) hEb hE0 (by positivity)
    have e : 2 / 5 * (2 * (1 / (q : ℝ))) * (s * (1 / (q : ℝ))) + s * 2 * (4 / (2 : ℝ) ^ R) =
        s * (4 / 5 / (q : ℝ) ^ 2 + 8 / (2 : ℝ) ^ R) := by
      field_simp
      ring
    linarith
  rw [ev, abs_sub_comm]
  unfold psiS
  rw [hsplit]
  have h1 := abs_add_le (∫ z, lin z ∂γ) (∫ z, r z ∂γ)
  have h2 : s * ∫ z, w z ∂γ ≤ s * (2 / 5 / (q : ℝ) ^ 2 + 4 / (2 : ℝ) ^ R) :=
    mul_le_mul_of_nonneg_left hwint hs
  have e : s * (6 / 5 / (q : ℝ) ^ 2 + 12 / (2 : ℝ) ^ R) =
      s * (2 / 5 / (q : ℝ) ^ 2 + 4 / (2 : ℝ) ^ R) +
        s * (4 / 5 / (q : ℝ) ^ 2 + 8 / (2 : ℝ) ^ R) := by ring
  rw [e]
  linarith

/-! ## Rational atoms and rational weights -/

lemma mR_abs {q R : ℕ} (hq : 1 ≤ q) (ℓ : Fin (2 * R * q + 1)) : |mR q R ℓ| ≤ R := by
  have h1 : (ℓ : ℕ) < 2 * R * q + 1 := ℓ.isLt
  have h2 : 2 * R * q = 2 * (R * q) := by ring
  obtain ⟨-, -, a3, a4⟩ := atom_mem (q := q) (R := R) hq (j := off q R ℓ)
    (by unfold off; omega) (by unfold off; omega)
  exact abs_le.mpr ⟨a4, a3⟩

lemma zM_cast (q R E : ℕ) (ℓ : Fin (2 * R * q + 1)) :
    ((zM q R E ℓ : ℚ) : ℝ) = ((⌊(E : ℝ) * mR q R ℓ⌋ : ℤ) : ℝ) / (E : ℝ) := by
  unfold zM
  push_cast
  rfl

lemma zM_err {q R E : ℕ} (hE : 1 ≤ E) (ℓ : Fin (2 * R * q + 1)) :
    |((zM q R E ℓ : ℚ) : ℝ) - mR q R ℓ| ≤ 1 / (E : ℝ) := by
  rw [zM_cast, abs_le]
  have h1 := fl_le hE (mR q R ℓ)
  have h2 := fl_ge hE (mR q R ℓ)
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have : (0 : ℝ) ≤ 1 / (E : ℝ) := by positivity
  constructor <;> linarith

/-- The change from the real atoms to the rational atoms costs at most `s/E`. -/
theorem atom_ratAtoms {q R E : ℕ} (hE : 1 ≤ E) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    |atomSum (pR q R) (fun ℓ => ((zM q R E ℓ : ℚ) : ℝ)) s x - atomSum (pR q R) (mR q R) s x| ≤
      s * (1 / (E : ℝ)) := by
  unfold atomSum
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ ℓ ∈ (Finset.univ : Finset (Fin (2 * R * q + 1))),
      |pR q R ℓ * relu (x + s * ((zM q R E ℓ : ℚ) : ℝ)) - pR q R ℓ * relu (x + s * mR q R ℓ)| ≤
      pR q R ℓ * (s * (1 / (E : ℝ))) := by
    intro ℓ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (pR_nonneg q R ℓ)]
    refine mul_le_mul_of_nonneg_left ?_ (pR_nonneg q R ℓ)
    refine (relu_lip _ _).trans ?_
    rw [show x + s * ((zM q R E ℓ : ℚ) : ℝ) - (x + s * mR q R ℓ) =
      s * (((zM q R E ℓ : ℚ) : ℝ) - mR q R ℓ) by ring, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (zM_err hE ℓ) hs
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, pR_sum, one_mul]

/-- **Lemma R for general atoms** in `[−M, M]`: the change from the cell probabilities to the
rational weights costs at most `s·4MRq/D`. -/
theorem atom_round_gen {q R D : ℕ} (hD : 1 ≤ D) {s : ℝ} (hs : 0 ≤ s) (x : ℝ)
    (z : Fin (2 * R * q + 1) → ℝ) {M : ℝ} (hz : ∀ ℓ, |z ℓ| ≤ M) :
    |atomSum (fun ℓ => ((pQ q R D ℓ : ℚ) : ℝ)) z s x - atomSum (pR q R) z s x| ≤
      s * (4 * M * (R : ℝ) * (q : ℝ) / (D : ℝ)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set g : Fin (2 * R * q + 1) → ℝ := fun ℓ => relu (x + s * z ℓ) with hg
  set fl : Fin (2 * R * q + 1) → ℝ := fun ℓ => ((⌊(D : ℝ) * pR q R ℓ⌋ : ℤ) : ℝ) / (D : ℝ)
    with hfl
  set E := Finset.univ.erase (0 : Fin (2 * R * q + 1)) with hE
  have hp0 := Finset.add_sum_erase Finset.univ (pR q R)
    (Finset.mem_univ (0 : Fin (2 * R * q + 1)))
  rw [pR_sum, ← hE] at hp0
  have key : atomSum (fun ℓ => ((pQ q R D ℓ : ℚ) : ℝ)) z s x - atomSum (pR q R) z s x =
      ∑ ℓ ∈ E, (pR q R ℓ - fl ℓ) * (g 0 - g ℓ) := by
    unfold atomSum
    beta_reduce
    rw [← Finset.sum_sub_distrib,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 * R * q + 1))), ← hE]
    have hne : ∀ ℓ ∈ E, ((pQ q R D ℓ : ℚ) : ℝ) * relu (x + s * z ℓ) -
        pR q R ℓ * relu (x + s * z ℓ) = -((pR q R ℓ - fl ℓ) * g ℓ) := by
      intro ℓ hℓ
      rw [pQ_ne_real q R D (Finset.ne_of_mem_erase hℓ)]
      simp only [hg, hfl]
      ring
    rw [Finset.sum_congr rfl hne, pQ_zero_real, Finset.sum_neg_distrib]
    have e1 : ∑ ℓ ∈ E, (pR q R ℓ - fl ℓ) * (g 0 - g ℓ) =
        (∑ ℓ ∈ E, pR q R ℓ - ∑ ℓ ∈ E, fl ℓ) * g 0 - ∑ ℓ ∈ E, (pR q R ℓ - fl ℓ) * g ℓ := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1]
    have e2 : pR q R 0 = 1 - ∑ ℓ ∈ E, pR q R ℓ := by linarith
    rw [e2]
    change (1 - ∑ ℓ ∈ E, fl ℓ) * g 0 - (1 - ∑ ℓ ∈ E, pR q R ℓ) * g 0 +
      -∑ ℓ ∈ E, (pR q R ℓ - fl ℓ) * g ℓ = _
    ring
  rw [key]
  have hterm : ∀ ℓ ∈ E, |(pR q R ℓ - fl ℓ) * (g 0 - g ℓ)| ≤ 1 / (D : ℝ) * (s * (2 * M)) := by
    intro ℓ _
    have a1 : 0 ≤ pR q R ℓ - fl ℓ := sub_nonneg.2 (fl_le hD _)
    have a2 : pR q R ℓ - fl ℓ ≤ 1 / (D : ℝ) := by linarith [fl_ge hD (pR q R ℓ)]
    have a3 : |g 0 - g ℓ| ≤ s * (2 * M) := by
      refine (relu_lip _ _).trans ?_
      rw [show x + s * z 0 - (x + s * z ℓ) = s * (z 0 - z ℓ) by ring, abs_mul, abs_of_nonneg hs]
      refine mul_le_mul_of_nonneg_left ?_ hs
      have h1 := abs_sub (z 0) (z ℓ)
      linarith [hz 0, hz ℓ]
    have hM : 0 ≤ M := (abs_nonneg _).trans (hz 0)
    rw [abs_mul, abs_of_nonneg a1]
    exact mul_le_mul a2 a3 (abs_nonneg _) (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
  rw [Finset.sum_const, nsmul_eq_mul, hE, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- **The second-order finite ReLU sum (`atomSum2_141`).** With the rational weights `pQ q R D`
and the rational atoms `zM q R E` (the conditional means of the cells, rounded): for every `x`
and every `s ≥ 0`,
`|Σ_ℓ pQ ℓ·relu(x + s·zM ℓ) − ψ_s(x)| ≤ s·(2/q² + 16/2^R + 4(R + 1)²q/D + 1/E)`. -/
theorem atomSum2_141 {q R D E : ℕ} (hq : 1 ≤ q) (hR : 1 ≤ R) (hD : 1 ≤ D) (hE : 1 ≤ E) {s : ℝ}
    (hs : 0 ≤ s) (x : ℝ) :
    |atomSum (fun ℓ => ((pQ q R D ℓ : ℚ) : ℝ)) (fun ℓ => ((zM q R E ℓ : ℚ) : ℝ)) s x -
        psiS s x| ≤
      s * (2 / (q : ℝ) ^ 2 + 16 / (2 : ℝ) ^ R + 4 * ((R : ℝ) + 1) ^ 2 * (q : ℝ) / (D : ℝ) +
        1 / (E : ℝ)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hE' : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hzb : ∀ ℓ : Fin (2 * R * q + 1), |((zM q R E ℓ : ℚ) : ℝ)| ≤ (R : ℝ) + 1 := by
    intro ℓ
    have h1 := zM_err (q := q) (R := R) hE ℓ
    have h2 := mR_abs (R := R) hq ℓ
    have h3 : 1 / (E : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hE'
    have h4 := abs_add_le (((zM q R E ℓ : ℚ) : ℝ) - mR q R ℓ) (mR q R ℓ)
    rw [sub_add_cancel] at h4
    linarith
  have h1 := atom_round_gen (q := q) (R := R) hD hs x (fun ℓ => ((zM q R E ℓ : ℚ) : ℝ)) hzb
  have h2 := atom_ratAtoms (q := q) (R := R) hE hs x
  have h3 := atom_couple2 hq hR hs x
  have t1 := abs_sub_le
    (atomSum (fun ℓ => ((pQ q R D ℓ : ℚ) : ℝ)) (fun ℓ => ((zM q R E ℓ : ℚ) : ℝ)) s x)
    (atomSum (pR q R) (fun ℓ => ((zM q R E ℓ : ℚ) : ℝ)) s x) (psiS s x)
  have t2 := abs_sub_le
    (atomSum (pR q R) (fun ℓ => ((zM q R E ℓ : ℚ) : ℝ)) s x)
    (atomSum (pR q R) (mR q R) s x) (psiS s x)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ R := by positivity
  have c1 : 6 / 5 / (q : ℝ) ^ 2 + 12 / (2 : ℝ) ^ R ≤ 2 / (q : ℝ) ^ 2 + 16 / (2 : ℝ) ^ R := by
    have a1 : 6 / 5 / (q : ℝ) ^ 2 ≤ 2 / (q : ℝ) ^ 2 := by
      rw [div_le_div_iff_of_pos_right (by positivity)]; norm_num
    have a2 : 12 / (2 : ℝ) ^ R ≤ 16 / (2 : ℝ) ^ R := by
      rw [div_le_div_iff_of_pos_right hpow]; norm_num
    linarith
  have c2 : 4 * ((R : ℝ) + 1) * (R : ℝ) * (q : ℝ) / (D : ℝ) ≤
      4 * ((R : ℝ) + 1) ^ 2 * (q : ℝ) / (D : ℝ) := by
    rw [div_le_div_iff_of_pos_right hD']
    nlinarith
  have hfin : s * (4 * ((R : ℝ) + 1) * (R : ℝ) * (q : ℝ) / (D : ℝ)) + s * (1 / (E : ℝ)) +
      s * (6 / 5 / (q : ℝ) ^ 2 + 12 / (2 : ℝ) ^ R) ≤
      s * (2 / (q : ℝ) ^ 2 + 16 / (2 : ℝ) ^ R + 4 * ((R : ℝ) + 1) ^ 2 * (q : ℝ) / (D : ℝ) +
        1 / (E : ℝ)) := by
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) hs
  linarith

end BstLean.Part141

open BstLean.Part141 in
#print axioms atom_couple2
open BstLean.Part141 in
#print axioms atomSum2_141
