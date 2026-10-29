import BstLean.Part184DS
import BstLean.Part182EBlk2
import BstLean.Part153PPs

/-!
# Part 185 (file `D1`): the ε-net lower singular value for a row-selected, column-split block

No proof is left open; no `native_decide` or `axiom` is used.

* `d1_isOpen_low`: `{N | ∃ z, |z|² = 1 ∧ |Nz| < b}` is open (so measurable).
* **`d1_rowsel_smin`**: for a fixed `{0,1}` diagonal `d` with `K_lo ≤ ∑ d ≤ K_hi`, under
  `G ~ gaussMat M D v`: `Pr(∃ z, |z| = 1, |diag(d) G z| < √((1 − δ)vK_lo)(1 − ε) − sε)
  ≤ (2⌈√D/ε⌉ + 1)^D e^{−K_lo δ²/4} + e^{−υ²/2}`, `s = √v(√K_hi + √D + υ)`.
* **`d1_split_smin`**: the same after a column split (selection a function of `A·P`, `P·U = 0`).
-/

namespace BstLean.Part185

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part153 (nrm normSq_diag_sel measurable_submatrix_rows gaussMat_submatrix_rows)
open BstLean.Part184 (smin_net gridN)
open BstLean.Part182 (eb_rot e2_mulU_eq e2_cont_diag eb_colsplit)

variable {M k D : ℕ}

/-- The low-singular-value set is open. -/
lemma d1_isOpen_low {p q : ℕ} (b : ℝ) :
    IsOpen {N : Matrix (Fin p) (Fin q) ℝ | ∃ z : Fin q → ℝ, normSq z = 1 ∧ √(normSq (N *ᵥ z)) < b} := by
  have e : {N : Matrix (Fin p) (Fin q) ℝ | ∃ z : Fin q → ℝ, normSq z = 1 ∧ √(normSq (N *ᵥ z)) < b} =
      ⋃ z : {z : Fin q → ℝ // normSq z = 1}, {N | √(normSq (N *ᵥ z.1)) < b} := by
    ext N; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz, h⟩; exact ⟨⟨z, hz⟩, h⟩
    · rintro ⟨⟨z, hz⟩, h⟩; exact ⟨z, hz, h⟩
  rw [e]
  refine isOpen_iUnion fun z => isOpen_lt ?_ continuous_const
  unfold normSq
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

lemma d1_measurableSet_low {p q : ℕ} (b : ℝ) :
    MeasurableSet {N : Matrix (Fin p) (Fin q) ℝ | ∃ z : Fin q → ℝ, normSq z = 1 ∧
      √(normSq (N *ᵥ z)) < b} :=
  (d1_isOpen_low b).measurableSet

/-- **Row-selected ε-net lower bound** (fixed selection). -/
theorem d1_rowsel_smin {v : ℝ} (hv : 0 < v) (d : Fin M → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hD : 1 ≤ D) {Klo Khi δ ε υ : ℝ} (hKlo0 : 0 ≤ Klo) (hlo : Klo ≤ ∑ i, d i)
    (hhi : ∑ i, d i ≤ Khi) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1) (hυ : 0 ≤ υ) :
    (gaussMat M D v).real {G | ∃ z : Fin D → ℝ, normSq z = 1 ∧
        √(normSq ((Matrix.diagonal d * G) *ᵥ z)) <
          √((1 - δ) * v * Klo) * (1 - ε) - √v * (√Khi + √(D : ℝ) + υ) * ε} ≤
      (2 * gridN D ε + 1) ^ D * exp (-(Klo * δ ^ 2 / 4)) + exp (-υ ^ 2 / 2) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin M), ∀ i, i ∈ S ↔ d i = 1 :=
    ⟨Finset.univ.filter fun i => d i = 1, by simp⟩
  have hd' : ∀ i, d i = if i ∈ S then 1 else 0 := by
    intro i
    rcases hd i with h | h
    · have : i ∉ S := by rw [hS, h]; norm_num
      simp [this, h]
    · simp [(hS i).2 h, h]
  have hsum : ∑ i, d i = (S.card : ℝ) := by
    simp only [hd']
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp
  obtain ⟨K', hK'⟩ : ∃ K', S.card = K' := ⟨_, rfl⟩
  rw [hsum, hK'] at hlo hhi
  set σ := S.orderEmbOfFin hK' with hσ
  set s := √v * (√Khi + √(D : ℝ) + υ) with hs
  set b := √((1 - δ) * v * Klo) * (1 - ε) - s * ε with hb
  set b' := √((1 - δ) * v * K') * (1 - ε) - s * ε with hb'
  have hbb : b ≤ b' := by
    have : √((1 - δ) * v * Klo) ≤ √((1 - δ) * v * K') := by
      apply Real.sqrt_le_sqrt
      have : 0 ≤ (1 - δ) * v := mul_nonneg (by linarith) hv.le
      exact mul_le_mul_of_nonneg_left hlo this
    have : 0 ≤ 1 - ε := by linarith
    rw [hb, hb']; nlinarith
  have hsub : {G : Matrix (Fin M) (Fin D) ℝ | ∃ z : Fin D → ℝ, normSq z = 1 ∧
      √(normSq ((Matrix.diagonal d * G) *ᵥ z)) < b} ⊆
      (fun A : Matrix (Fin M) (Fin D) ℝ => A.submatrix σ id) ⁻¹'
        {G' | ∃ z : Fin D → ℝ, normSq z = 1 ∧ √(normSq (G' *ᵥ z)) < b'} := by
    intro G ⟨z, hz, hlt⟩
    refine ⟨z, hz, ?_⟩
    have e : normSq ((Matrix.diagonal d * G) *ᵥ z) = normSq (G.submatrix σ id *ᵥ z) := by
      rw [← Matrix.mulVec_mulVec, normSq_diag_sel d S hd' hK']
      rfl
    rw [← e]; linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [← map_measureReal_apply (measurable_submatrix_rows σ) (d1_measurableSet_low b'),
    gaussMat_submatrix_rows v σ σ.injective]
  have hsm := smin_net (K := K') (d := D) hv hD (δ := δ) (ε := ε) (s := s) h0 h1 hε0 hε1
  refine hsm.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity)) ?_)
  · have : (Klo * δ ^ 2 / 4) ≤ (K' * δ ^ 2 / 4) := by
      have := sq_nonneg δ; nlinarith
    exact Real.exp_le_exp.mpr (by linarith)
  · have ht := opN_tail' (p := K') (q := D) hv hυ
    refine le_trans (measureReal_mono (fun G hG => ?_) (measure_ne_top _ _)) ht
    simp only [Set.mem_ofPred_eq] at hG ⊢
    have : √(K' : ℝ) ≤ √Khi := Real.sqrt_le_sqrt hhi
    have hsv : 0 ≤ √v := Real.sqrt_nonneg _
    have : √v * (√(K' : ℝ) + √(D : ℝ) + υ) ≤ s := by rw [hs]; nlinarith
    linarith

/-- **The ε-net lower bound after a column split**: if the `{0,1}` row selection depends only on
`A·P` (`P` an orthogonal projection) and `P·U = 0` (`U` with orthonormal columns), then
`Pr(K_lo ≤ ∑ d ≤ K_hi ∧ ∃ z unit, |diag(d)·A·U z| < b) ≤ (2⌈√D/ε⌉+1)^D e^{−K_lo δ²/4} + e^{−υ²/2}`. -/
theorem d1_split_smin {v : ℝ} (hv : 0 < v) (P : Matrix (Fin k) (Fin k) ℝ) (hPs : Pᵀ = P)
    (hPi : P * P = P) (U : Matrix (Fin k) (Fin D) ℝ) (hU : Uᵀ * U = 1) (hPU : P * U = 0)
    (dF : Matrix (Fin M) (Fin k) ℝ → Fin M → ℝ) (hdF : Measurable dF)
    (hd01 : ∀ B i, dF B i = 0 ∨ dF B i = 1) (hD : 1 ≤ D) {Klo Khi δ ε υ : ℝ} (hKlo0 : 0 ≤ Klo)
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1) (hυ : 0 ≤ υ) :
    (gaussMat M k v) {A | Klo ≤ ∑ i, dF (A * P) i ∧ ∑ i, dF (A * P) i ≤ Khi ∧
      ∃ z : Fin D → ℝ, normSq z = 1 ∧
        √(normSq ((Matrix.diagonal (dF (A * P)) * (A * U)) *ᵥ z)) <
          √((1 - δ) * v * Klo) * (1 - ε) - √v * (√Khi + √(D : ℝ) + υ) * ε} ≤
      ENNReal.ofReal ((2 * gridN D ε + 1) ^ D * exp (-(Klo * δ ^ 2 / 4)) + exp (-υ ^ 2 / 2)) := by
  classical
  set b := √((1 - δ) * v * Klo) * (1 - ε) - √v * (√Khi + √(D : ℝ) + υ) * ε with hb
  set R := (2 * gridN D ε + 1 : ℝ) ^ D * exp (-(Klo * δ ^ 2 / 4)) + exp (-υ ^ 2 / 2) with hR
  have hR0 : 0 ≤ R := by positivity
  have hPμ : IsProbabilityMeasure (gaussMat M k v) := by unfold gaussMat; infer_instance
  have hg1 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * P) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg2 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => (A * P, A * (1 - P))) :=
    hg1.prodMk hg2
  set T := {N : Matrix (Fin M) (Fin D) ℝ | ∃ z : Fin D → ℝ, normSq z = 1 ∧
    √(normSq (N *ᵥ z)) < b} with hT
  have hTm : MeasurableSet T := d1_measurableSet_low b
  set S : Set (Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ) :=
    {q | Klo ≤ ∑ i, dF q.1 i ∧ ∑ i, dF q.1 i ≤ Khi ∧
      Matrix.diagonal (dF q.1) * (q.2 * U) ∈ T} with hSd
  have hSm : MeasurableSet S := by
    have h1 : Measurable (fun q : Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ =>
        ∑ i, dF q.1 i) :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp (hdF.comp measurable_fst)
    have hc : Measurable (fun q : Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ =>
        (dF q.1, q.2 * U)) :=
      (hdF.comp measurable_fst).prodMk ((continuous_snd.matrix_mul continuous_const).measurable)
    have hco : Measurable (fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin D) ℝ =>
        Matrix.diagonal q.1 * q.2) := (e2_cont_diag (M := M) (D := D)).measurable
    have h2 : Measurable (fun q : Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ =>
        Matrix.diagonal (dF q.1) * (q.2 * U)) := by
      have := hco.comp hc
      simpa only [Function.comp_def] using this
    exact (measurableSet_le measurable_const h1).inter
      ((measurableSet_le h1 measurable_const).inter (h2 hTm))
  have e : {A : Matrix (Fin M) (Fin k) ℝ | Klo ≤ ∑ i, dF (A * P) i ∧ ∑ i, dF (A * P) i ≤ Khi ∧
      ∃ z : Fin D → ℝ, normSq z = 1 ∧
        √(normSq ((Matrix.diagonal (dF (A * P)) * (A * U)) *ᵥ z)) < b} =
      (fun A => (A * P, A * (1 - P))) ⁻¹' S := by
    ext A
    simp only [hSd, hT, Set.mem_preimage, Set.mem_ofPred_eq, e2_mulU_eq P U hPU]
  rw [e, ← Measure.map_apply hg hSm, eb_colsplit v P hPs hPi]
  set μ₁ := (gaussMat M k v).map (fun A => A * P)
  set μ₂ := (gaussMat M k v).map (fun A => A * (1 - P))
  have : IsProbabilityMeasure μ₁ := inferInstance
  have : IsProbabilityMeasure μ₂ := inferInstance
  rw [Measure.prod_apply hSm]
  have hle : ∀ B, μ₂ (Prod.mk B ⁻¹' S) ≤ ENNReal.ofReal R := by
    intro B
    by_cases hB : Klo ≤ ∑ i, dF B i ∧ ∑ i, dF B i ≤ Khi
    · have hT' : MeasurableSet {C : Matrix (Fin M) (Fin k) ℝ |
          Matrix.diagonal (dF B) * (C * U) ∈ T} :=
        ((continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const)).measurable) hTm
      have e1 : Prod.mk B ⁻¹' S = {C : Matrix (Fin M) (Fin k) ℝ |
          Matrix.diagonal (dF B) * (C * U) ∈ T} := by
        ext C; simp [hSd, hB]
      rw [e1, Measure.map_apply hg2 hT']
      have e2 : (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) ⁻¹'
          {C | Matrix.diagonal (dF B) * (C * U) ∈ T} =
          (fun A : Matrix (Fin M) (Fin k) ℝ => (1 : Matrix (Fin M) (Fin M) ℝ)ᵀ * A * U) ⁻¹'
            {G | Matrix.diagonal (dF B) * G ∈ T} := by
        ext A; simp only [Set.mem_preimage, Set.mem_ofPred_eq, e2_mulU_eq P U hPU,
          transpose_one, Matrix.one_mul]
      rw [e2]
      have hrot := eb_rot (M := M) (k := k) (K := M) (d := D) hv.le (1 : Matrix (Fin M) (Fin M) ℝ) U
        (by simp) hU
      have hgm : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ =>
          (1 : Matrix (Fin M) (Fin M) ℝ)ᵀ * A * U) :=
        ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
      have hGm : MeasurableSet {G : Matrix (Fin M) (Fin D) ℝ | Matrix.diagonal (dF B) * G ∈ T} :=
        ((continuous_const.matrix_mul continuous_id).measurable) hTm
      rw [← Measure.map_apply hgm hGm, hrot]
      have h := d1_rowsel_smin hv (dF B) (hd01 B) hD hKlo0 hB.1 hB.2 h0 h1 hε0 hε1 hυ
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal h
    · have e1 : Prod.mk B ⁻¹' S = ∅ := by
        ext C; simp only [hSd, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        intro h; exact hB ⟨h.1, h.2.1⟩
      rw [e1, measure_empty]; exact bot_le
  calc ∫⁻ B, μ₂ (Prod.mk B ⁻¹' S) ∂μ₁ ≤ ∫⁻ _B, ENNReal.ofReal R ∂μ₁ := lintegral_mono hle
    _ = ENNReal.ofReal R := by rw [lintegral_const, measure_univ, mul_one]

end BstLean.Part185

open BstLean.Part185 in
#print axioms d1_rowsel_smin
open BstLean.Part185 in
#print axioms d1_split_smin
