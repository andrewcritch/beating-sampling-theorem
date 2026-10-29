import BstLean.Part151JF4

/-!
# Part 151: Lemma JF in the document's form, the two conditional fourth moments

Role: `proofs/option-n/theorem5-08-F-rows.tex`, Lemma JF, the two steps of its proof.
`Q = jacFro F₁ F₂ y = ‖J_F(y)‖²_F`, `Wd = ‖D₁F₁‖²_F = Σ_i Σ_l (maskedF F₁ y i l)²`, `t = 2/m`.

* `half_pow_le`: `E[1(w·h > 0)·q(w)]^p ≤ (1/2)·E q(w)^p` for an even `q ≥ 0`, `w = c·ξ`.
* **`lemmaJF4_inner`** (fix `F₁`, integrate `F₂`): `E (Q − Wd)⁴ ≤ t⁴·Wd⁴·((841/2)·m + (75/16)·m²)`
  (the document: `1680·m + (75/16)·m²`).
* `Wd_mean`: `E Wd = m` for `y ≠ 0`.
* **`lemmaJF4_W`** (integrate `F₁`): `E (Wd − m)⁴ ≤ m·(64ρ_n + 8) + 3m²(1 + 4/n)²`,
  `ρ_n = 1 + 36/n + 112/n² + 48/n³` (the document: `16·E w⁴·m + 3(1 + 4/n)²m²` with
  `E w⁴ = 8(1 + 2/n)(1 + 4/n)(1 + 6/n)`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part149 (stdGauss_normSq)

/-! ## Half-spaces and powers -/

section half

variable {d : ℕ}

/-- For an even measurable `q ≥ 0`, `c ≠ 0`, `p ≥ 1`: if `E q(cξ)^p ≤ K` then
`E (1[(cξ)·h > 0]·q(cξ))^p ≤ K/2` (for `h = 0` the left side is `0`). -/
lemma half_pow_le (h : Fin d → ℝ) {c : ℝ} (hc : c ≠ 0) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) (hev : ∀ w, q (-w) = q w) {p : ℕ} (hp : 1 ≤ p) {K : ℝ} (_hK : 0 ≤ K)
    (hb : ∫⁻ ξ, ENNReal.ofReal (q (c • ξ) ^ p) ∂stdGauss (Fin d) ≤ ENNReal.ofReal K) :
    ∫⁻ ξ, ENNReal.ofReal ((if 0 < (c • ξ) ⬝ᵥ h then q (c • ξ) else 0) ^ p) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (K / 2) := by
  have hp0 : p ≠ 0 := by omega
  have e : ∀ ξ : Fin d → ℝ,
      ENNReal.ofReal ((if 0 < (c • ξ) ⬝ᵥ h then q (c • ξ) else 0) ^ p) =
        if 0 < (c • ξ) ⬝ᵥ h then ENNReal.ofReal (q (c • ξ) ^ p) else 0 := by
    intro ξ
    by_cases hpos : 0 < (c • ξ) ⬝ᵥ h
    · simp only [hpos, ↓reduceIte]
    · simp only [hpos, ↓reduceIte, zero_pow hp0, ENNReal.ofReal_zero]
  simp_rw [e]
  by_cases hh : h = 0
  · subst hh
    simp
  · set N : (Fin d → ℝ) → ℝ≥0∞ := fun w => ENNReal.ofReal (q w ^ p) with hN
    have mN : Measurable N := ENNReal.measurable_ofReal.comp (hq.pow_const p)
    have hevN : ∀ w, N (-w) = N w := fun w => by simp only [hN]; rw [hev]
    have h2 := half_lint hh hc mN hevN
    have h3 : (2 : ℝ≥0∞) * ∫⁻ ξ, (if 0 < (c • ξ) ⬝ᵥ h then N (c • ξ) else 0)
        ∂stdGauss (Fin d) ≤ 2 * ENNReal.ofReal (K / 2) := by
      rw [h2]
      refine hb.trans (le_of_eq ?_)
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h3

/-- The same with equality, for `h ≠ 0` and `p = 1`. -/
lemma half_one_eq {h : Fin d → ℝ} (hh : h ≠ 0) {c : ℝ} (hc : c ≠ 0) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) (hev : ∀ w, q (-w) = q w) {K : ℝ} (_hK : 0 ≤ K)
    (hb : ∫⁻ ξ, ENNReal.ofReal (q (c • ξ)) ∂stdGauss (Fin d) = ENNReal.ofReal K) :
    ∫⁻ ξ, ENNReal.ofReal (if 0 < (c • ξ) ⬝ᵥ h then q (c • ξ) else 0) ∂stdGauss (Fin d) =
      ENNReal.ofReal (K / 2) := by
  have e : ∀ ξ : Fin d → ℝ,
      ENNReal.ofReal (if 0 < (c • ξ) ⬝ᵥ h then q (c • ξ) else 0) =
        if 0 < (c • ξ) ⬝ᵥ h then ENNReal.ofReal (q (c • ξ)) else 0 := by
    intro ξ
    by_cases hpos : 0 < (c • ξ) ⬝ᵥ h
    · simp only [hpos, ↓reduceIte]
    · simp only [hpos, ↓reduceIte, ENNReal.ofReal_zero]
  simp_rw [e]
  set N : (Fin d → ℝ) → ℝ≥0∞ := fun w => ENNReal.ofReal (q w) with hN
  have mN : Measurable N := ENNReal.measurable_ofReal.comp hq
  have hevN : ∀ w, N (-w) = N w := fun w => by simp only [hN]; rw [hev]
  have h2 := half_lint hh hc mN hevN
  have h3 : (2 : ℝ≥0∞) * ∫⁻ ξ, (if 0 < (c • ξ) ⬝ᵥ h then N (c • ξ) else 0)
      ∂stdGauss (Fin d) = 2 * ENNReal.ofReal (K / 2) := by
    rw [h2]
    refine hb.trans ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h3

end half

/-! ## The step over `F₂` -/

section inner

variable {n m : ℕ}

/-- The quadratic form `|w·B|² = Σ_l (Σ_i w_i B_il)²`. -/
noncomputable def qJ (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) : ℝ :=
  ∑ l, (∑ i, w i * B i l) ^ 2

lemma qJ_nonneg (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) : 0 ≤ qJ B w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma measurable_qJ (B : Matrix (Fin m) (Fin n) ℝ) : Measurable (qJ B) := by
  unfold qJ; fun_prop

lemma qJ_neg (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) : qJ B (-w) = qJ B w := by
  unfold qJ
  refine Finset.sum_congr rfl fun l _ => ?_
  have : ∑ i, (-w) i * B i l = -∑ i, w i * B i l := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [this, neg_sq]

/-- The second and the fourth moment of the quadratic form `qJ B` at a Gaussian row:
`E q² ≤ 3v²W²`, `E q⁴ ≤ 105v⁴W⁴`, `W = ‖B‖²_F`. -/
lemma qJ_mom (hn : 1 ≤ n) (B : Matrix (Fin m) (Fin n) ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ ξ, ENNReal.ofReal (qJ B (√v • ξ) ^ 2) ∂stdGauss (Fin m) ≤
        ENNReal.ofReal (3 * v ^ 2 * (∑ i, ∑ l, B i l ^ 2) ^ 2) ∧
    ∫⁻ ξ, ENNReal.ofReal (qJ B (√v • ξ) ^ 4) ∂stdGauss (Fin m) ≤
        ENNReal.ofReal (105 * v ^ 4 * (∑ i, ∑ l, B i l ^ 2) ^ 4) := by
  set P : Measure Unit := Measure.dirac () with hP
  set b : Fin n → Unit → Fin m → ℝ := fun l _ i => B i l
  have hbm : ∀ l, Measurable (b l) := fun l => measurable_const
  have hK : ∀ (l : Fin n) (ω : Unit), normSq (b l ω) ≤ ∑ i, ∑ l', B i l' ^ 2 := by
    intro l ω
    have : normSq (b l ω) = ∑ i, B i l ^ 2 := rfl
    rw [this, Finset.sum_comm]
    exact Finset.single_le_sum (f := fun l => ∑ i, B i l ^ 2)
      (fun l _ => Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.mem_univ l)
  have eq : ∀ w : Fin m → ℝ, sumQ P b w = qJ B w := by
    intro w
    unfold sumQ qJ
    rw [hP, integral_dirac]
    rfl
  have eT : sumT P b = ∑ i, ∑ l, B i l ^ 2 := by
    unfold sumT
    rw [hP, integral_dirac, Finset.sum_comm]
    rfl
  have h2 := sumQ_sq P hn hbm hK hv
  have h4 := sumQ_four P hn hbm hK hv
  rw [eT] at h2 h4
  refine ⟨le_trans (le_of_eq (lintegral_congr fun ξ => ?_)) h2,
    le_trans (le_of_eq (lintegral_congr fun ξ => ?_)) h4⟩
  · rw [eq]
  · rw [eq]

lemma phiJ_eq (F₁ : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ) (y : Fin n → ℝ) :
    phiJ F₁ w y = if 0 < w ⬝ᵥ reluV (F₁ *ᵥ y) then qJ (maskedF F₁ y) w else 0 := rfl

/-- The moments of the row term `phiJ` at a Gaussian row: `E = (v/2)W`, `E² ≤ (3/2)v²W²`,
`E⁴ ≤ (105/2)v⁴W⁴`, `W = ‖D₁F₁‖²_F`. -/
lemma phiJ_mom (hn : 1 ≤ n) (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) {v : ℝ}
    (hv : 0 < v) :
    ∫⁻ ξ, ENNReal.ofReal (phiJ F₁ (√v • ξ) y) ∂stdGauss (Fin m) =
        ENNReal.ofReal (v / 2 * ∑ i, ∑ l, maskedF F₁ y i l ^ 2) ∧
    ∫⁻ ξ, ENNReal.ofReal (phiJ F₁ (√v • ξ) y ^ 2) ∂stdGauss (Fin m) ≤
        ENNReal.ofReal (3 / 2 * v ^ 2 * (∑ i, ∑ l, maskedF F₁ y i l ^ 2) ^ 2) ∧
    ∫⁻ ξ, ENNReal.ofReal (phiJ F₁ (√v • ξ) y ^ 4) ∂stdGauss (Fin m) ≤
        ENNReal.ofReal (105 / 2 * v ^ 4 * (∑ i, ∑ l, maskedF F₁ y i l ^ 2) ^ 4) := by
  have hc : √v ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  set B := maskedF F₁ y with hB
  set h := reluV (F₁ *ᵥ y) with hh
  obtain ⟨q2, q4⟩ := qJ_mom hn B hv.le
  have hW0 : 0 ≤ ∑ i, ∑ l, B i l ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => sq_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · have h2 := half_second B h hc (fun h0 => maskedF_zero_of F₁ y h0)
    rw [Real.sq_sqrt hv.le] at h2
    rw [← h2]
    refine lintegral_congr fun ξ => ?_
    change ENNReal.ofReal (if 0 < (√v • ξ) ⬝ᵥ h then qJ B (√v • ξ) else 0) = _
    by_cases hpos : 0 < (√v • ξ) ⬝ᵥ h
    · simp only [hpos, ↓reduceIte]; rfl
    · simp only [hpos, ↓reduceIte, ENNReal.ofReal_zero]
  · have h2 := half_pow_le h hc (measurable_qJ B) (qJ_neg B) (p := 2) (by norm_num)
      (by positivity) q2
    refine h2.trans (le_of_eq ?_)
    congr 1; ring
  · have h4 := half_pow_le h hc (measurable_qJ B) (qJ_neg B) (p := 4) (by norm_num)
      (by positivity) q4
    refine h4.trans (le_of_eq ?_)
    congr 1; ring

lemma measurable_phiJ_w (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    Measurable (fun w : Fin m → ℝ => phiJ F₁ w y) :=
  (measurable_phiJ F₁).comp (measurable_id.prodMk measurable_const)

/-- **Lemma JF, the step over `F₂`, fourth moment** (fix `F₁`; integrate `F₂`): for
`n, m ≥ 1` and every `y`:
`E (‖J_F(y)‖²_F − ‖D₁F₁‖²_F)⁴ ≤ t⁴·‖D₁F₁‖⁸_F·((841/2)·m + (75/16)·m²)`, `t = 2/m`. -/
theorem lemmaJF4_inner (hn : 1 ≤ n) (hm : 1 ≤ m) (F₁ : Matrix (Fin m) (Fin n) ℝ)
    (y : Fin n → ℝ) :
    ∫⁻ F₂, ENNReal.ofReal ((jacFro F₁ F₂ y - ∑ i, ∑ l, maskedF F₁ y i l ^ 2) ^ 4)
        ∂gaussMat m m (2 / (m : ℝ)) ≤
      ENNReal.ofReal ((2 / (m : ℝ)) ^ 4 * (∑ i, ∑ l, maskedF F₁ y i l ^ 2) ^ 4 *
        (841 / 2 * m + 75 / 16 * (m : ℝ) ^ 2)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set t : ℝ := 2 / (m : ℝ) with ht
  set Wd : ℝ := ∑ i, ∑ l, maskedF F₁ y i l ^ 2 with hWd
  have hW0 : 0 ≤ Wd :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => sq_nonneg _
  obtain ⟨p1, p2, p4⟩ := phiJ_mom hn F₁ y hv
  set f : (Fin m → ℝ) → ℝ := fun w => phiJ F₁ w y with hf
  have mf : Measurable f := measurable_phiJ_w F₁ y
  have hf0 : ∀ w, 0 ≤ f w := fun w => phiJ_nonneg _ _ _
  have r1 : ∫⁻ r, ENNReal.ofReal (f r) ∂rowDist m t = ENNReal.ofReal (t / 2 * Wd) := by
    rw [lintegral_rowDist t (F := fun r => ENNReal.ofReal (f r))
      (ENNReal.measurable_ofReal.comp mf)]
    exact p1
  have r2 : ∫⁻ r, ENNReal.ofReal (f r ^ 2) ∂rowDist m t ≤
      ENNReal.ofReal (3 / 2 * t ^ 2 * Wd ^ 2) := by
    rw [lintegral_rowDist t (F := fun r => ENNReal.ofReal (f r ^ 2))
      (ENNReal.measurable_ofReal.comp (mf.pow_const 2))]
    exact p2
  have r4 : ∫⁻ r, ENNReal.ofReal (f r ^ 4) ∂rowDist m t ≤
      ENNReal.ofReal (105 / 2 * t ^ 4 * Wd ^ 4) := by
    rw [lintegral_rowDist t (F := fun r => ENNReal.ofReal (f r ^ 4))
      (ENNReal.measurable_ofReal.comp (mf.pow_const 4))]
    exact p4
  obtain ⟨iS, hS⟩ := four_centred (rowDist m t) mf hf0 (c := t / 2 * Wd)
    (b₂ := 3 / 2 * t ^ 2 * Wd ^ 2) (b₄ := 105 / 2 * t ^ 4 * Wd ^ 4) (by positivity)
    (by positivity) (by positivity) r1 r2 r4 m
  have ec : (m : ℝ) * (t / 2 * Wd) = Wd := by rw [ht]; field_simp
  rw [ec] at iS hS
  -- transfer to the Gaussian matrix
  have mG : Measurable (fun F₂ : Matrix (Fin m) (Fin m) ℝ =>
      ENNReal.ofReal ((jacFro F₁ F₂ y - Wd) ^ 4)) := by
    have h0 : Measurable (fun F₂ : Matrix (Fin m) (Fin m) ℝ => ∑ j, f (rowOf j F₂)) :=
      Finset.measurable_sum _ fun j _ => mf.comp (measurable_rowOf j)
    have e1 : (fun F₂ : Matrix (Fin m) (Fin m) ℝ => jacFro F₁ F₂ y) =
        fun F₂ => ∑ j, f (rowOf j F₂) := by
      funext F₂
      rw [jacFro_rows]
      exact Finset.sum_congr rfl fun j _ => rfl
    have h1 : Measurable (fun F₂ : Matrix (Fin m) (Fin m) ℝ => jacFro F₁ F₂ y) := e1 ▸ h0
    exact ENNReal.measurable_ofReal.comp ((h1.sub measurable_const).pow_const 4)
  rw [gaussMat_rows, lintegral_map mG measurable_ofRows]
  have ej : ∀ us : Fin m → Fin m → ℝ,
      jacFro F₁ (Matrix.of us : Matrix (Fin m) (Fin m) ℝ) y = ∑ j, f (us j) := by
    intro us
    rw [jacFro_rows]
    exact Finset.sum_congr rfl fun j _ => rfl
  simp_rw [ej]
  rw [← ofReal_integral_eq_lintegral_ofReal iS
    (Filter.Eventually.of_forall fun us => by positivity)]
  refine ENNReal.ofReal_le_ofReal (hS.trans (le_of_eq ?_))
  ring

end inner

/-! ## The step over `F₁` -/

section outer

variable {n m : ℕ}

/-- The row term of `‖D₁F₁‖²_F`: `1[f·y > 0]·|f|²`. -/
noncomputable def psiJ (y : Fin n → ℝ) (f : Fin n → ℝ) : ℝ :=
  if 0 < f ⬝ᵥ y then normSq f else 0

lemma psiJ_nonneg (y f : Fin n → ℝ) : 0 ≤ psiJ y f := by
  unfold psiJ; split_ifs
  · exact normSq_nonneg _
  · exact le_rfl

lemma measurable_psiJ (y : Fin n → ℝ) : Measurable (psiJ y) := by
  unfold psiJ
  refine Measurable.ite (measurableSet_lt measurable_const ?_) measurable_normSq measurable_const
  simp only [dotProduct]; fun_prop

lemma Wd_rows (F₁ : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    ∑ i, ∑ l, maskedF F₁ y i l ^ 2 = ∑ i, psiJ y (rowOf i F₁) := maskedF_fro F₁ y

/-- `ρ_n = 1 + 36/n + 112/n² + 48/n³`: a bound of `E|ξ|⁸/n⁴`. -/
noncomputable def rhoJ (n : ℕ) : ℝ := 1 + 36 / (n : ℝ) + 112 / (n : ℝ) ^ 2 + 48 / (n : ℝ) ^ 3

/-- The moments of the row term `psiJ` at a Gaussian row with entry variance `2/n`, `y ≠ 0`:
`E = 1`, `E² ≤ 2 + 4/n`, `E⁴ ≤ 8ρ_n`. -/
lemma psiJ_mom (hn : 1 ≤ n) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ∫⁻ ξ, ENNReal.ofReal (psiJ y (√(2 / (n : ℝ)) • ξ)) ∂stdGauss (Fin n) = ENNReal.ofReal 1 ∧
    ∫⁻ ξ, ENNReal.ofReal (psiJ y (√(2 / (n : ℝ)) • ξ) ^ 2) ∂stdGauss (Fin n) ≤
        ENNReal.ofReal (2 + 4 / (n : ℝ)) ∧
    ∫⁻ ξ, ENNReal.ofReal (psiJ y (√(2 / (n : ℝ)) • ξ) ^ 4) ∂stdGauss (Fin n) ≤
        ENNReal.ofReal (8 * rhoJ n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hc : √(2 / (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hev : ∀ w : Fin n → ℝ, normSq (-w) = normSq w := fun w => BstLean.Part135.normSq_neg w
  have epow : ∀ (p : ℕ) (ξ : Fin n → ℝ), ENNReal.ofReal (normSq (√(2 / (n : ℝ)) • ξ) ^ p) =
      ENNReal.ofReal ((2 / (n : ℝ)) ^ p) * ENNReal.ofReal (normSq ξ ^ p) := by
    intro p ξ
    rw [normSq_smul, Real.sq_sqrt hv.le, mul_pow, ENNReal.ofReal_mul (by positivity)]
  obtain ⟨hi, hval⟩ := stdGauss_normSq n
  -- the three moments of `|cξ|²`
  have m1 : ∫⁻ ξ : Fin n → ℝ, ENNReal.ofReal (normSq (√(2 / (n : ℝ)) • ξ)) ∂stdGauss (Fin n) =
      ENNReal.ofReal 2 := by
    have e : ∀ ξ : Fin n → ℝ, ENNReal.ofReal (normSq (√(2 / (n : ℝ)) • ξ)) =
        ENNReal.ofReal (2 / (n : ℝ) * normSq ξ) := by
      intro ξ; rw [normSq_smul, Real.sq_sqrt hv.le]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _)
      (Filter.Eventually.of_forall fun ξ => mul_nonneg hv.le (normSq_nonneg _)),
      integral_const_mul, hval]
    congr 1; field_simp
  have m2 : ∫⁻ ξ : Fin n → ℝ, ENNReal.ofReal (normSq (√(2 / (n : ℝ)) • ξ) ^ 2)
      ∂stdGauss (Fin n) ≤ ENNReal.ofReal (2 * (2 + 4 / (n : ℝ))) := by
    simp_rw [epow 2]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, chi_two,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    field_simp
    ring
  have m4 : ∫⁻ ξ : Fin n → ℝ, ENNReal.ofReal (normSq (√(2 / (n : ℝ)) • ξ) ^ 4)
      ∂stdGauss (Fin n) ≤ ENNReal.ofReal (2 * (8 * rhoJ n)) := by
    simp_rw [epow 4]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl (chi_four_le n)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    unfold rhoJ
    field_simp
    ring
  have hr0 : 0 ≤ rhoJ n := by unfold rhoJ; positivity
  refine ⟨?_, ?_, ?_⟩
  · have h := half_one_eq hy hc measurable_normSq hev (K := 2) (by norm_num) m1
    simpa [psiJ] using h
  · have h := half_pow_le y hc measurable_normSq hev (p := 2) (by norm_num)
      (by positivity) m2
    refine h.trans (le_of_eq ?_)
    congr 1; ring
  · have h := half_pow_le y hc measurable_normSq hev (p := 4) (by norm_num)
      (by positivity) m4
    refine h.trans (le_of_eq ?_)
    congr 1; ring

/-- **`E ‖D₁F₁‖²_F = m`** for `y ≠ 0` (`F₁ ∼ gaussMat m n (2/n)`). -/
theorem Wd_mean (hn : 1 ≤ n) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ∫⁻ F₁, ENNReal.ofReal (∑ i, ∑ l, maskedF F₁ y i l ^ 2) ∂gaussMat m n (2 / (n : ℝ)) =
      ENNReal.ofReal (m : ℝ) := by
  obtain ⟨p1, -, -⟩ := psiJ_mom hn hy
  simp_rw [Wd_rows]
  have e : ∀ F₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (∑ i, psiJ y (rowOf i F₁)) =
      ∑ i, ENNReal.ofReal (psiJ y (rowOf i F₁)) := fun F₁ =>
    ENNReal.ofReal_sum_of_nonneg fun i _ => psiJ_nonneg _ _
  simp_rw [e]
  rw [lintegral_finsetSum (μ := gaussMat m n (2 / (n : ℝ))) Finset.univ
    (f := fun i (F₁ : Matrix (Fin m) (Fin n) ℝ) => ENNReal.ofReal (psiJ y (rowOf i F₁)))
    fun i _ => ENNReal.measurable_ofReal.comp ((measurable_psiJ y).comp (measurable_rowOf i))]
  have hrow : ∀ i : Fin m, ∫⁻ F₁ : Matrix (Fin m) (Fin n) ℝ,
      ENNReal.ofReal (psiJ y (rowOf i F₁)) ∂gaussMat m n (2 / (n : ℝ)) = ENNReal.ofReal 1 := by
    intro i
    rw [row_map i _ (F := fun w => ENNReal.ofReal (psiJ y w))
      (ENNReal.measurable_ofReal.comp (measurable_psiJ y))]
    exact p1
  simp_rw [hrow]
  simp

/-- **Lemma JF, the step over `F₁`, fourth moment**: for `n ≥ 1`, `y ≠ 0`:
`E (‖D₁F₁‖²_F − m)⁴ ≤ m·(64ρ_n + 8) + 3m²·(1 + 4/n)²`. -/
theorem lemmaJF4_W (hn : 1 ≤ n) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ∫⁻ F₁, ENNReal.ofReal ((∑ i, ∑ l, maskedF F₁ y i l ^ 2 - m) ^ 4)
        ∂gaussMat m n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (m * (64 * rhoJ n + 8) + 3 * (m : ℝ) ^ 2 * (1 + 4 / (n : ℝ)) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : 0 ≤ rhoJ n := by unfold rhoJ; positivity
  obtain ⟨p1, p2, p4⟩ := psiJ_mom hn hy
  set v : ℝ := 2 / (n : ℝ) with hv
  have mf : Measurable (psiJ y) := measurable_psiJ y
  have r1 : ∫⁻ r, ENNReal.ofReal (psiJ y r) ∂rowDist n v = ENNReal.ofReal 1 := by
    rw [lintegral_rowDist v (F := fun r => ENNReal.ofReal (psiJ y r))
      (ENNReal.measurable_ofReal.comp mf)]
    exact p1
  have r2 : ∫⁻ r, ENNReal.ofReal (psiJ y r ^ 2) ∂rowDist n v ≤
      ENNReal.ofReal (2 + 4 / (n : ℝ)) := by
    rw [lintegral_rowDist v (F := fun r => ENNReal.ofReal (psiJ y r ^ 2))
      (ENNReal.measurable_ofReal.comp (mf.pow_const 2))]
    exact p2
  have r4 : ∫⁻ r, ENNReal.ofReal (psiJ y r ^ 4) ∂rowDist n v ≤ ENNReal.ofReal (8 * rhoJ n) := by
    rw [lintegral_rowDist v (F := fun r => ENNReal.ofReal (psiJ y r ^ 4))
      (ENNReal.measurable_ofReal.comp (mf.pow_const 4))]
    exact p4
  obtain ⟨iS, hS⟩ := four_centred (rowDist n v) mf (psiJ_nonneg y) (c := 1)
    (b₂ := 2 + 4 / (n : ℝ)) (b₄ := 8 * rhoJ n) (by norm_num) (by positivity) (by positivity)
    r1 r2 r4 m
  rw [mul_one] at iS hS
  have mG : Measurable (fun F₁ : Matrix (Fin m) (Fin n) ℝ =>
      ENNReal.ofReal ((∑ i, psiJ y (rowOf i F₁) - m) ^ 4)) :=
    ENNReal.measurable_ofReal.comp (((Finset.measurable_sum _ fun i _ =>
      mf.comp (measurable_rowOf i)).sub measurable_const).pow_const 4)
  simp_rw [Wd_rows]
  rw [gaussMat_rows, lintegral_map mG measurable_ofRows]
  have ej : ∀ us : Fin m → Fin n → ℝ, ∑ i, psiJ y (rowOf i (Matrix.of us : Matrix (Fin m)
      (Fin n) ℝ)) = ∑ i, psiJ y (us i) := fun us => rfl
  simp_rw [ej]
  rw [← ofReal_integral_eq_lintegral_ofReal iS
    (Filter.Eventually.of_forall fun us => by positivity)]
  refine ENNReal.ofReal_le_ofReal (hS.trans (le_of_eq ?_))
  ring

end outer

end BstLean.Part151
