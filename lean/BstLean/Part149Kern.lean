import BstLean.Part136Kern
import BstLean.Part145C2
import BstLean.Part134Split

/-!
# Part 149, helper `Kern`: the Gram kernel of the hidden layers at two points of the cheap stand-in

Role: `delegations/statements/p149-spec.md`.

`θ = (M₁, M₂)` are the two hidden matrices of a random ReLU network with `n` inputs and hidden
width `m` (`hidGauss n m`); `h(x) = hid2 M₁ M₂ x`. The two points of the cheap stand-in are
`x = sphPt (β·w₀ + τ·w₁)` and `x′ = sphPt (β·w₀ + τ·w₂)`, with `w₀, w₁, w₂` independent standard
Gaussian vectors of `ℝⁿ`; `q = β²/(β² + τ²)` is the cosine of `(β, τ, 0)` and `(β, 0, τ)`.

* `gramK_L2`: for random unit inputs `X, X′` independent of `θ`,
  `‖⟨h(X), h(X′)⟩ − (m/n)·κ(κ(⟨X, X′⟩))‖₂ ≤ (m/n)·cF2o m`. `gramD_L2`: the diagonal.
* `gauss3`: three independent standard Gaussian vectors are the three columns of a Gaussian
  matrix with `3` columns and variance `1`.
* `cheapCos_L2`: `‖⟨x, x′⟩ − q‖₂ ≤ (1 − q²)/√n + jCosC n`.
* `kk_lip`: `κ∘κ` is 1-Lipschitz on `[−1, 1]`.
* **`errK_L2`**: `‖⟨h(x), h(x′)⟩ − (m/n)·κ(κ(q))‖₂ ≤ (m/n)·(cF2o m + (1 − q²)/√n + jCosC n)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 BstLean.Part145

/-! ## The Gram kernel at two random unit inputs -/

/-- **The Gram kernel of the two hidden layers at two random unit inputs**, in `L²` over the
inputs and `(M₁, M₂)`. -/
theorem gramK_L2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {X X' : Ω → Fin n → ℝ} (hX : Measurable X)
    (hX' : Measurable X') (h1 : ∀ ω, normSq (X ω) = 1) (h1' : ∀ ω, normSq (X' ω) = 1) :
    L2le (P.prod (hidGauss n m))
      (fun z : Ω × HidParam n m => dotp (hid2 z.2.1 z.2.2 (X z.1)) (hid2 z.2.1 z.2.2 (X' z.1)) -
        (m : ℝ) / n * kappa (kappa (dotp (X z.1) (X' z.1))))
      ((m : ℝ) / n * cF2o m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have mX : Measurable (fun z : Ω × HidParam n m => hid2 z.2.1 z.2.2 (X z.1)) :=
    continuous_hid2_joint.measurable.comp (measurable_snd.prodMk (hX.comp measurable_fst))
  have mX' : Measurable (fun z : Ω × HidParam n m => hid2 z.2.1 z.2.2 (X' z.1)) :=
    continuous_hid2_joint.measurable.comp (measurable_snd.prodMk (hX'.comp measurable_fst))
  have md : Measurable (fun z : Ω × HidParam n m => dotp (X z.1) (X' z.1)) :=
    continuous_dotp.measurable.comp ((hX.comp measurable_fst).prodMk (hX'.comp measurable_fst))
  have mf : Measurable (fun z : Ω × HidParam n m =>
      dotp (hid2 z.2.1 z.2.2 (X z.1)) (hid2 z.2.1 z.2.2 (X' z.1)) -
        (m : ℝ) / n * kappa (kappa (dotp (X z.1) (X' z.1)))) :=
    (continuous_dotp.measurable.comp (mX.prodMk mX')).sub
      (measurable_const.mul (continuous_kappa.measurable.comp (continuous_kappa.measurable.comp md)))
  refine L2le.prod_const mf.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have h := hid2_dot_L2o (m₁ := m) (m₂ := m) (k := n) (v₁ := 2 / (n : ℝ)) (v₂ := 2 / (m : ℝ))
    (by positivity) (by positivity) hm hm (X ω) (X' ω)
  rw [psi_unit _ (h1 ω) (h1' ω), nrm_of_normSq_one (h1 ω), nrm_of_normSq_one (h1' ω)] at h
  have e1 : ∀ x : ℝ, (m : ℝ) / 2 * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (n : ℝ)) * x) =
      (m : ℝ) / n * x := by
    intro x
    field_simp
  rw [e1, e1] at h
  refine (h.congr_fun fun θ => ?_).congr_bound ?_
  · simp only [Function.comp]
  · unfold cF2o
    ring

/-- **The diagonal of the Gram kernel at a random unit input.** -/
theorem gramD_L2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {X : Ω → Fin n → ℝ} (hX : Measurable X)
    (h1 : ∀ ω, normSq (X ω) = 1) :
    L2le (P.prod (hidGauss n m))
      (fun z : Ω × HidParam n m => normSq (hid2 z.2.1 z.2.2 (X z.1)) - (m : ℝ) / n)
      ((m : ℝ) / n * cF2o m) :=
  (gramK_L2 P hn hm hX hX h1 h1).congr_fun fun z => by
    simp only [dotp_self, h1, kappa_one, mul_one]

/-! ## Three independent Gaussian vectors -/

lemma single_orth {i j : Fin 3} (h : i ≠ j) :
    ∑ l, (Pi.single i (1 : ℝ) : Fin 3 → ℝ) l * (Pi.single j (1 : ℝ) : Fin 3 → ℝ) l = 0 := by
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = i
  · subst hl
    simp [h]
  · simp [Pi.single_apply, hl]

lemma rowMat_single_orth (n : ℕ) {i j : Fin 3} (h : i ≠ j) :
    rowMat n (Pi.single i (1 : ℝ) : Fin 3 → ℝ) *
      (rowMat n (Pi.single j (1 : ℝ) : Fin 3 → ℝ)).transpose = 0 := by
  ext a b
  rw [rowMat_mul_transpose, single_orth h]
  simp

lemma normSq_single (j : Fin 3) : normSq (Pi.single j (1 : ℝ) : Fin 3 → ℝ) = 1 := by
  fin_cases j <;> simp [normSq, Fin.sum_univ_three]

lemma gaussMat_col (n : ℕ) (j : Fin 3) :
    (gaussMat n 3 1).map (fun M => (rowMat n (Pi.single j (1 : ℝ) : Fin 3 → ℝ)).mulVec (flat M)) =
      stdGauss (Fin n) := by
  have h := gaussMat_mulVec (m := n) (k := 3) 1 (Pi.single j (1 : ℝ))
  simp only [rowMat_mulVec]
  rw [h, normSq_single]
  simp

/-- **Three independent standard Gaussian vectors are the three columns of a Gaussian matrix.** -/
theorem gauss3 (n : ℕ) :
    (gaussMat n 3 1).map (fun M => (M.mulVec (Pi.single 0 1), M.mulVec (Pi.single 1 1),
        M.mulVec (Pi.single 2 1))) =
      (stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n))) := by
  obtain ⟨A0, hA0⟩ : ∃ A : Matrix (Fin n) (Fin n × Fin 3) ℝ,
      A = rowMat n (Pi.single 0 (1 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A : Matrix (Fin n) (Fin n × Fin 3) ℝ,
      A = rowMat n (Pi.single 1 (1 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : Matrix (Fin n) (Fin n × Fin 3) ℝ,
      A = rowMat n (Pi.single 2 (1 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n ⊕ Fin n) (Fin n × Fin 3) ℝ,
      B = Matrix.fromRows A1 A2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : (Fin n ⊕ Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ),
      s = fun f => (fun i => f (Sum.inl i), fun i => f (Sum.inr i)) := ⟨_, rfl⟩
  have ms : Measurable s := by
    rw [hs]
    exact (measurable_pi_iff.mpr fun i => measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun i => measurable_pi_apply _)
  have h01 : A0 * A1.transpose = 0 := by
    rw [hA0, hA1]; exact rowMat_single_orth n (by decide)
  have h02 : A0 * A2.transpose = 0 := by
    rw [hA0, hA2]; exact rowMat_single_orth n (by decide)
  have h12 : A1 * A2.transpose = 0 := by
    rw [hA1, hA2]; exact rowMat_single_orth n (by decide)
  have h0B : A0 * B.transpose = 0 := by
    rw [hB, Matrix.transpose_fromRows, Matrix.mul_fromCols, h01, h02]
    ext i j
    cases j <;> rfl
  have e2 : s ∘ (fun M : Matrix (Fin n) (Fin 3) ℝ => B.mulVec (flat M)) =
      fun M => (A1.mulVec (flat M), A2.mulVec (flat M)) := by
    funext M
    simp only [Function.comp, hs, hB, Matrix.fromRows_mulVec, Sum.elim_inl, Sum.elim_inr]
  have e1 : (fun M : Matrix (Fin n) (Fin 3) ℝ => (M.mulVec (Pi.single 0 1),
        M.mulVec (Pi.single 1 1), M.mulVec (Pi.single 2 1))) =
      (Prod.map id s) ∘ (fun M => (A0.mulVec (flat M), B.mulVec (flat M))) := by
    funext M
    have := congrFun e2 M
    simp only [Function.comp] at this
    simp only [Function.comp, Prod.map, id, this, hA0, hA1, hA2, rowMat_mulVec]
  have c0 : (gaussMat n 3 1).map (fun M => A0.mulVec (flat M)) = stdGauss (Fin n) := by
    rw [hA0]; exact gaussMat_col n 0
  have c1 : (gaussMat n 3 1).map (fun M => A1.mulVec (flat M)) = stdGauss (Fin n) := by
    rw [hA1]; exact gaussMat_col n 1
  have c2 : (gaussMat n 3 1).map (fun M => A2.mulVec (flat M)) = stdGauss (Fin n) := by
    rw [hA2]; exact gaussMat_col n 2
  rw [e1, ← Measure.map_map (measurable_id.prodMap ms)
      ((measurable_mulVec_flat A0).prodMk (measurable_mulVec_flat B)),
    gaussMat_indep 1 A0 B h0B, ← Measure.map_prod_map _ _ measurable_id ms, Measure.map_id, c0,
    Measure.map_map ms (measurable_mulVec_flat B), e2, gaussMat_indep 1 A1 A2 h12, c1, c2]

/-! ## The cosine of two points of the cheap stand-in -/

lemma normSq_h01 (β τ : ℝ) :
    normSq (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 1 1 : Fin 3 → ℝ)) =
      β ^ 2 + τ ^ 2 := by
  simp [normSq, Fin.sum_univ_three]

lemma normSq_h02 (β τ : ℝ) :
    normSq (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 2 1 : Fin 3 → ℝ)) =
      β ^ 2 + τ ^ 2 := by
  simp [normSq, Fin.sum_univ_three]

lemma dotp_h01_h02 (β τ : ℝ) :
    dotp (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 1 1 : Fin 3 → ℝ))
      (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 2 1 : Fin 3 → ℝ)) = β ^ 2 := by
  simp [dotp, Fin.sum_univ_three]
  ring

lemma measurable_cheapPt {n : ℕ} (β τ : ℝ) :
    Measurable (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => sphPt (β • w.1 + τ • w.2.1)) ∧
    Measurable (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => sphPt (β • w.1 + τ • w.2.2)) :=
  ⟨measurable_sphPt.comp
    (by fun_prop : Continuous fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
      β • w.1 + τ • w.2.1).measurable,
   measurable_sphPt.comp
    (by fun_prop : Continuous fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
      β • w.1 + τ • w.2.2).measurable⟩

lemma measurable_cheapDot {n : ℕ} (β τ : ℝ) :
    Measurable (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
      dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2))) :=
  continuous_dotp.measurable.comp
    ((measurable_cheapPt β τ).1.prodMk (measurable_cheapPt β τ).2)

/-- **The cosine of two points of the cheap stand-in**: `x = sphPt (β w₀ + τ w₁)`,
`x′ = sphPt (β w₀ + τ w₂)`, `q = β²/(β² + τ²)`: `‖⟨x, x′⟩ − q‖₂ ≤ (1 − q²)/√n + jCosC n`. -/
theorem cheapCos_L2 {n : ℕ} (hn : 1 ≤ n) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    L2le ((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n))))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2)) - β ^ 2 / (β ^ 2 + τ ^ 2))
      ((1 - (β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) / √(n : ℝ) + jCosC n) := by
  have hpos : 0 < β ^ 2 + τ ^ 2 := by positivity
  have hc : cosv (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 1 1 : Fin 3 → ℝ))
      (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 2 1 : Fin 3 → ℝ)) =
      β ^ 2 / (β ^ 2 + τ ^ 2) := by
    unfold cosv nrm
    rw [normSq_h01, normSq_h02, dotp_h01_h02, Real.mul_self_sqrt hpos.le]
  have key := lin_cos_L2c (n := n) (k := 3) (v := 1) one_pos hn
    (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 1 1 : Fin 3 → ℝ))
    (β • (Pi.single 0 1 : Fin 3 → ℝ) + τ • (Pi.single 2 1 : Fin 3 → ℝ))
    (by rw [normSq_h01]; exact hpos.ne') (by rw [normSq_h02]; exact hpos.ne')
  rw [hc] at key
  rw [← gauss3 n]
  have mφ : Measurable (fun M : Matrix (Fin n) (Fin 3) ℝ => (M.mulVec (Pi.single 0 1),
      M.mulVec (Pi.single 1 1), M.mulVec (Pi.single 2 1))) :=
    (measurable_mulVec_right _).prodMk ((measurable_mulVec_right _).prodMk
      (measurable_mulVec_right _))
  refine L2le.of_comp_map mφ
    ((measurable_cheapDot β τ).sub measurable_const).aestronglyMeasurable
    (key.congr_fun fun M => ?_)
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]

/-! ## `κ∘κ` is 1-Lipschitz -/

lemma kk_lip_aux {s t : ℝ} (hs : -1 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    0 ≤ kappa (kappa t) - kappa (kappa s) ∧ kappa (kappa t) - kappa (kappa s) ≤ t - s := by
  have a := kappa_lipschitz hs hst ht
  have ms := kappa_mem hs (hst.trans ht)
  have mt := kappa_mem (hs.trans hst) ht
  have b := kappa_lipschitz (s := kappa t) (t := kappa s) (by linarith) (by linarith) mt.2
  exact ⟨b.1, by linarith⟩

/-- **`κ∘κ` is 1-Lipschitz on `[−1, 1]`.** -/
theorem kk_lip {s t : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |kappa (kappa t) - kappa (kappa s)| ≤ |t - s| := by
  rcases le_total s t with h | h
  · have := kk_lip_aux hs.1 h ht.2
    rw [abs_of_nonneg this.1, abs_of_nonneg (by linarith)]
    exact this.2
  · have := kk_lip_aux ht.1 h hs.2
    rw [abs_sub_comm (kappa (kappa t)), abs_sub_comm t s, abs_of_nonneg this.1,
      abs_of_nonneg (by linarith)]
    exact this.2

/-! ## The assembled bound -/

lemma abs_cheapDot_mem {n : ℕ} (hn : 1 ≤ n) (β τ : ℝ)
    (w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) :
    dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2)) ∈ Set.Icc (-1 : ℝ) 1 := by
  have := abs_dotp_le_nrm (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2))
  rw [nrm_of_normSq_one (normSq_sphPt hn _), nrm_of_normSq_one (normSq_sphPt hn _),
    mul_one] at this
  exact abs_le.mp this

/-- The Gram kernel at the two points of the cheap stand-in, against `κ(κ(⟨x, x′⟩))`. -/
lemma cheapGram_L2 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (β τ : ℝ) :
    L2le (((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n)))).prod
        (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
             (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) -
          (m : ℝ) / n * kappa (kappa (dotp (sphPt (β • z.1.1 + τ • z.1.2.1))
            (sphPt (β • z.1.1 + τ • z.1.2.2)))))
      ((m : ℝ) / n * cF2o m) :=
  gramK_L2 ((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n)))) hn hm
    (X := fun w => sphPt (β • w.1 + τ • w.2.1)) (X' := fun w => sphPt (β • w.1 + τ • w.2.2))
    (measurable_cheapPt β τ).1 (measurable_cheapPt β τ).2
    (fun _ => normSq_sphPt hn _) (fun _ => normSq_sphPt hn _)

/-- The Lipschitz step: from the cosine to `κ(κ(cosine))`. -/
lemma cheapKK_L2 {n : ℕ} (hn : 1 ≤ n) (β τ : ℝ) {q c : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (c0 : L2le ((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n))))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2)) - q) c) :
    L2le ((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n))))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        kappa (kappa (dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2)))) -
          kappa (kappa q)) c :=
  L2le.of_abs_le
    (((continuous_kappa.comp continuous_kappa).measurable.comp
      (measurable_cheapDot β τ)).sub measurable_const).aestronglyMeasurable c0
    (fun w => kk_lip ⟨by linarith, hq1⟩ (abs_cheapDot_mem hn β τ w))

lemma errK_alg (a c k1 k2 : ℝ) : a - c * k1 + c * (k1 - k2) = a - c * k2 := by ring

lemma errK_aux {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (β τ : ℝ) {q c : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hc : 0 < c)
    (c0 : L2le ((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n))))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        dotp (sphPt (β • w.1 + τ • w.2.1)) (sphPt (β • w.1 + τ • w.2.2)) - q) c) :
    L2le (((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n)))).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
             (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) -
          (m : ℝ) / n * kappa (kappa q))
      ((m : ℝ) / n * (cF2o m + c)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn : (0 : ℝ) < (m : ℝ) / n := div_pos hm' hn'
  have c2 := ((cheapKK_L2 hn β τ hq0 hq1 c0).comp_fst (ν := hidGauss n m)).const_mul_nonneg hmn.le
  have key := (cheapGram_L2 hn hm β τ).add c2 (mul_pos hmn (Part136.cF2o_pos hm)) (mul_pos hmn hc)
  refine (key.congr_fun fun z => ?_).congr_bound (mul_add _ _ _).symm
  exact errK_alg _ _ _ _

/-- **The Gram kernel of the hidden layers at two points of the cheap stand-in**, in `L²` over
`(w₀, w₁, w₂)` and `(M₁, M₂)`; `q = β²/(β² + τ²)`. -/
theorem errK_L2 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) :
    L2le (((stdGauss (Fin n)).prod ((stdGauss (Fin n)).prod (stdGauss (Fin n)))).prod (hidGauss n m))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × HidParam n m =>
        dotp (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.1)))
             (hid2 z.2.1 z.2.2 (sphPt (β • z.1.1 + τ • z.1.2.2))) -
          (m : ℝ) / n * kappa (kappa (β ^ 2 / (β ^ 2 + τ ^ 2))))
      ((m : ℝ) / n * (cF2o m + ((1 - (β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) / √(n : ℝ) + jCosC n))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < β ^ 2 + τ ^ 2 := by positivity
  have hq0 : 0 < β ^ 2 / (β ^ 2 + τ ^ 2) := by positivity
  have hq1 : β ^ 2 / (β ^ 2 + τ ^ 2) < 1 := by
    rw [div_lt_one hpos]
    have : 0 < τ ^ 2 := by positivity
    linarith
  have hc : 0 < (1 - (β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) / √(n : ℝ) + jCosC n := by
    have := jCosC_nonneg n
    have : 0 < (1 - (β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) / √(n : ℝ) :=
      div_pos (by nlinarith) (Real.sqrt_pos.mpr hn')
    linarith
  exact errK_aux hn hm β τ hq0.le hq1.le hc (cheapCos_L2 hn hβ hτ)

end BstLean.Part149

open BstLean.Part149 in
#print axioms gramK_L2
open BstLean.Part149 in
#print axioms gramD_L2
open BstLean.Part149 in
#print axioms gauss3
open BstLean.Part149 in
#print axioms cheapCos_L2
open BstLean.Part149 in
#print axioms kk_lip
open BstLean.Part149 in
#print axioms errK_L2
