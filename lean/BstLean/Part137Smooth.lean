import BstLean.Part137Inner

/-!
# Part 137, item 4, tools: one ReLU layer against a Gaussian smoothing of ReLU

Role: `delegations/statements/p137-spec.md` (item 4). Paper source: `onW16c-cx.md` §2,
`onW16-opus-prover.md` §1 (proof of H2(b): conditional row independence, the row formula for the
pair `(a, ā + sZ)`).

* `psiS s x = E_Z ReLU(x + s Z)`, `Z` standard Gaussian: the Gaussian smoothing `ψ_s` of ReLU.
* `fS s g ḡ w = ReLU(⟨w, g⟩)·ψ_s(⟨w, ḡ⟩)`: the term of one row `w`.
* `aug_integral`: a standard Gaussian vector of `ℝ^{k+1}` is a standard Gaussian number and an
  independent standard Gaussian vector of `ℝ^k`.
* `smooth_row`: for a Gaussian row `w = √v·ξ`: `E fS = c` with
  `2c = v·Φ((0, g), (s/√v, ḡ))` (the row formula for the pair `(⟨w, g⟩, ⟨w, ḡ⟩ + sZ)`), and
  `E fS² ≤ (3/2)·v²·|g|²·(s²/v + |ḡ|²) + c²`.
* `smooth_layer`: for an `m × k` Gaussian matrix `M` of entry variance `v > 0`,
  `S(M) = Σ_i ReLU((M g)_i)·ψ_s((M ḡ)_i)` has mean `m·c` and
  `E (S − m c)² ≤ m·(3/2)·v²·|g|²·(s²/v + |ḡ|²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part137

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136

/-- **The Gaussian smoothing of ReLU**: `ψ_s(x) = E_Z ReLU(x + s·Z)`, `Z` standard Gaussian. -/
noncomputable def psiS (s x : ℝ) : ℝ := ∫ z, relu (x + s * z) ∂gaussianReal 0 1

lemma relu_sq_le (t : ℝ) : relu t ^ 2 ≤ t ^ 2 := by
  have h := abs_relu_le t
  rw [← sq_abs (relu t), ← sq_abs t]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

lemma measurable_relu_shift (x s : ℝ) : Measurable (fun z : ℝ => relu (x + s * z)) :=
  measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id))

lemma integrable_relu_shift_sq (x s : ℝ) :
    Integrable (fun z : ℝ => relu (x + s * z) ^ 2) (gaussianReal 0 1) := by
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
    simpa using integrable_pow_gauss 1
  have h2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) := integrable_pow_gauss 2
  have hd : Integrable (fun z : ℝ => x ^ 2 + (2 * x * s) * z + s ^ 2 * z ^ 2) (gaussianReal 0 1) :=
    ((integrable_const _).add (h1.const_mul _)).add (h2.const_mul _)
  refine Integrable.mono' hd ((measurable_relu_shift x s).pow_const 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := relu_sq_le (x + s * z)
  nlinarith

lemma integrable_relu_shift (x s : ℝ) :
    Integrable (fun z : ℝ => relu (x + s * z)) (gaussianReal 0 1) :=
  ((memLp_two_iff_integrable_sq (measurable_relu_shift x s).aestronglyMeasurable).mpr
    (integrable_relu_shift_sq x s)).integrable one_le_two

lemma psiS_nonneg (s x : ℝ) : 0 ≤ psiS s x := integral_nonneg fun _ => relu_nonneg _

/-- `ψ_s(x)² ≤ E_Z ReLU(x + sZ)²` (Jensen). -/
lemma psiS_sq_le (s x : ℝ) : psiS s x ^ 2 ≤ ∫ z, relu (x + s * z) ^ 2 ∂gaussianReal 0 1 :=
  sq_integral_le (integrable_relu_shift_sq x s)

lemma measurable_psiS : Measurable (fun p : ℝ × ℝ => psiS p.1 p.2) := by
  have hF : Measurable (fun q : (ℝ × ℝ) × ℝ => relu (q.1.2 + q.1.1 * q.2)) :=
    (continuous_relu.comp (by fun_prop)).measurable
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

/-! ## A standard Gaussian vector with one more coordinate -/

section aug

variable {k : ℕ}

/-- A standard Gaussian vector of `ℝ^{k+1}` is a pair of a standard Gaussian number (its
coordinate `0`) and an independent standard Gaussian vector of `ℝ^k`: integrals. -/
lemma aug_integral (G : ℝ × (Fin k → ℝ) → ℝ) :
    ∫ ξ : Fin (k + 1) → ℝ, G (ξ 0, fun j => ξ j.succ) ∂stdGauss (Fin (k + 1)) =
      ∫ p, G p ∂((gaussianReal 0 1).prod (stdGauss (Fin k))) := by
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) 0
  have h := mp.integral_comp' (g := G)
  unfold stdGauss
  rw [← h]
  rfl

/-- The same for integrability. -/
lemma aug_integrable (G : ℝ × (Fin k → ℝ) → ℝ) :
    Integrable (fun ξ : Fin (k + 1) → ℝ => G (ξ 0, fun j => ξ j.succ)) (stdGauss (Fin (k + 1))) ↔
      Integrable G ((gaussianReal 0 1).prod (stdGauss (Fin k))) := by
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) 0
  have h := mp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).measurableEmbedding (g := G)
  unfold stdGauss
  rw [← h]
  rfl

end aug

/-! ## One row -/

section row

variable {k : ℕ}

/-- The term of one row `w`: `ReLU(⟨w, g⟩)·ψ_s(⟨w, ḡ⟩)`. -/
noncomputable def fS (s : ℝ) (g gb : Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  relu (∑ j, w j * g j) * psiS s (∑ j, w j * gb j)

lemma measurable_fS (s : ℝ) (g gb : Fin k → ℝ) : Measurable (fS s g gb) := by
  have h1 : ∀ g : Fin k → ℝ, Measurable (fun w : Fin k → ℝ => ∑ j, w j * g j) := fun g =>
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _
  exact (measurable_relu.comp (h1 g)).mul (measurable_psiS.comp (measurable_const.prodMk (h1 gb)))

/-- `c`: the mean of the term of one Gaussian row; `2c = v·Φ((0, g), (s/√v, ḡ))`. -/
noncomputable def cS (v s : ℝ) (g gb : Fin k → ℝ) : ℝ :=
  v * kernelPhi (Fin.cons 0 g : Fin (k + 1) → ℝ) (Fin.cons (s / √v) gb : Fin (k + 1) → ℝ) / 2

lemma normSq_cons (a : ℝ) (g : Fin k → ℝ) :
    normSq (Fin.cons a g : Fin (k + 1) → ℝ) = a ^ 2 + normSq g := by
  unfold normSq
  rw [Fin.sum_univ_succ]
  simp

lemma dotp_cons (a b : ℝ) (g g' : Fin k → ℝ) :
    dotp (Fin.cons a g : Fin (k + 1) → ℝ) (Fin.cons b g' : Fin (k + 1) → ℝ) =
      a * b + dotp g g' := by
  unfold dotp
  rw [Fin.sum_univ_succ]
  simp

/-- The one-row facts of Part 132 on the standard Gaussian vector: mean and second moment of
`ReLU(⟨w, h⟩)·ReLU(⟨w, h′⟩)`, `w = √v·ξ`. -/
lemma rowPair137 {K : ℕ} {v : ℝ} (hv : 0 ≤ v) (h h' : Fin K → ℝ) :
    Integrable (fun ξ : Fin K → ℝ => relu (∑ j, (√v • ξ) j * h j) * relu (∑ j, (√v • ξ) j * h' j))
      (stdGauss (Fin K)) ∧
    ∫ ξ : Fin K → ℝ, relu (∑ j, (√v • ξ) j * h j) * relu (∑ j, (√v • ξ) j * h' j)
      ∂stdGauss (Fin K) = v * kernelPhi h h' / 2 ∧
    Integrable (fun ξ : Fin K → ℝ => (relu (∑ j, (√v • ξ) j * h j) *
      relu (∑ j, (√v • ξ) j * h' j) - v * kernelPhi h h' / 2) ^ 2) (stdGauss (Fin K)) ∧
    ∫ ξ : Fin K → ℝ, (relu (∑ j, (√v • ξ) j * h j) * relu (∑ j, (√v • ξ) j * h' j) -
      v * kernelPhi h h' / 2) ^ 2 ∂stdGauss (Fin K) ≤ 3 / 2 * v ^ 2 * normSq h * normSq h' := by
  let f : (Fin K → ℝ) → ℝ := fun w => relu (∑ j, w j * h j) * relu (∑ j, w j * h' j)
  have hf : Measurable f :=
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).mul_const _)).mul
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _))
  have hsum : ∀ M : Matrix (Fin 1) (Fin K) ℝ,
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) = f (rowOf 0 M) := by
    intro M
    have : dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) = ∑ i : Fin 1, f (rowOf i M) := rfl
    rw [this, Fin.sum_univ_one]
  obtain ⟨iD, eD⟩ := layer_dot_relu (m := 1) hv h h'
  obtain ⟨iV, uV⟩ := layer_dot_relu_var (m := 1) hv h h'
  have e1 : ((1 : ℕ) : ℝ) / 2 * (v * kernelPhi h h') = v * kernelPhi h h' / 2 := by
    push_cast
    ring
  rw [e1] at eD iV uV
  simp_rw [hsum] at iD eD iV uV
  have hf2 : Measurable (fun w : Fin K → ℝ => (f w - v * kernelPhi h h' / 2) ^ 2) :=
    (hf.sub_const _).pow_const 2
  refine ⟨(row_integrable_iff (m := 1) v (0 : Fin 1) hf).mp iD, ?_,
    (row_integrable_iff (m := 1) v (0 : Fin 1) hf2).mp iV, ?_⟩
  · rw [← row_integral (m := 1) v (0 : Fin 1) hf]
    exact eD
  · rw [← row_integral (m := 1) v (0 : Fin 1) hf2]
    refine uV.trans (le_of_eq ?_)
    push_cast
    ring

/-- **One Gaussian row against the smoothing** (`w = √v·ξ`, `v > 0`): the mean of
`ReLU(⟨w, g⟩)·ψ_s(⟨w, ḡ⟩)` is `c`, and its second moment is at most
`(3/2)·v²·|g|²·(s²/v + |ḡ|²) + c²`. -/
theorem smooth_row {v : ℝ} (hv : 0 < v) (s : ℝ) (g gb : Fin k → ℝ) :
    Integrable (fun ξ : Fin k → ℝ => fS s g gb (√v • ξ)) (stdGauss (Fin k)) ∧
    ∫ ξ : Fin k → ℝ, fS s g gb (√v • ξ) ∂stdGauss (Fin k) = cS v s g gb ∧
    Integrable (fun ξ : Fin k → ℝ => fS s g gb (√v • ξ) ^ 2) (stdGauss (Fin k)) ∧
    ∫ ξ : Fin k → ℝ, fS s g gb (√v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      3 / 2 * v ^ 2 * normSq g * (s ^ 2 / v + normSq gb) + cS v s g gb ^ 2 := by
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  set gP : Fin (k + 1) → ℝ := Fin.cons 0 g with hgP
  set gbP : Fin (k + 1) → ℝ := Fin.cons (s / √v) gb with hgbP
  set c : ℝ := cS v s g gb with hc
  have hcdef : c = v * kernelPhi gP gbP / 2 := rfl
  -- the term as a function of the extra Gaussian number and the row
  let H : ℝ × (Fin k → ℝ) → ℝ := fun p =>
    relu (∑ j, (√v • p.2) j * g j) * relu (∑ j, (√v • p.2) j * gb j + s * p.1)
  have hHm : Measurable H := by
    have h1 : ∀ g : Fin k → ℝ, Measurable (fun p : ℝ × (Fin k → ℝ) => ∑ j, (√v • p.2) j * g j) :=
      fun g => Finset.measurable_sum _ fun j _ =>
        (((measurable_pi_apply j).comp measurable_snd).const_mul _).mul_const _
    exact (measurable_relu.comp (h1 g)).mul
      (measurable_relu.comp ((h1 gb).add (measurable_fst.const_mul s)))
  have key : ∀ ξ : Fin (k + 1) → ℝ,
      relu (∑ j, (√v • ξ) j * gP j) * relu (∑ j, (√v • ξ) j * gbP j) =
        H (ξ 0, fun j => ξ j.succ) := by
    intro ξ
    simp only [H, hgP, hgbP]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, mul_zero, zero_add]
    have e : √v * ξ 0 * (s / √v) = s * ξ 0 := by
      field_simp
    rw [e, add_comm (s * ξ 0)]
  obtain ⟨i1, e1, i2, u2⟩ := rowPair137 hv.le gP gbP
  rw [← hcdef] at e1 i2 u2
  simp_rw [key] at i1 e1 i2 u2
  rw [aug_integrable] at i1
  rw [aug_integral] at e1
  have i2' := (aug_integrable (fun p => (H p - c) ^ 2)).mp i2
  have u2' : ∫ p, (H p - c) ^ 2 ∂((gaussianReal 0 1).prod (stdGauss (Fin k))) ≤
      3 / 2 * v ^ 2 * normSq gP * normSq gbP := by
    rw [← aug_integral (fun p => (H p - c) ^ 2)]
    exact u2
  -- the second moment of `H`
  have eH2 : (fun p => H p ^ 2) = fun p => (H p - c) ^ 2 + (2 * c * H p - c ^ 2) := by
    funext p
    ring
  have iH2 : Integrable (fun p => H p ^ 2) ((gaussianReal 0 1).prod (stdGauss (Fin k))) := by
    rw [eH2]
    exact i2'.add ((i1.const_mul _).sub (integrable_const _))
  have vH2 : ∫ p, H p ^ 2 ∂((gaussianReal 0 1).prod (stdGauss (Fin k))) ≤
      3 / 2 * v ^ 2 * normSq gP * normSq gbP + c ^ 2 := by
    have iA : Integrable (fun p => 2 * c * H p) ((gaussianReal 0 1).prod (stdGauss (Fin k))) :=
      i1.const_mul _
    have iC : Integrable (fun p => 2 * c * H p - c ^ 2)
        ((gaussianReal 0 1).prod (stdGauss (Fin k))) := iA.sub (integrable_const _)
    rw [eH2, integral_add i2' iC, integral_sub iA (integrable_const _), integral_const_mul, e1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith
  -- the inner integral over the extra Gaussian number
  have inner1 : ∀ ξ : Fin k → ℝ, ∫ z, H (z, ξ) ∂gaussianReal 0 1 = fS s g gb (√v • ξ) := by
    intro ξ
    simp only [H, fS, psiS]
    rw [integral_const_mul]
  have inner2 : ∀ ξ : Fin k → ℝ, fS s g gb (√v • ξ) ^ 2 ≤ ∫ z, H (z, ξ) ^ 2 ∂gaussianReal 0 1 := by
    intro ξ
    simp only [H, fS]
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (psiS_sq_le s _) (sq_nonneg _)
  have hfm : Measurable (fun ξ : Fin k → ℝ => fS s g gb (√v • ξ)) :=
    (measurable_fS s g gb).comp (measurable_const_smul _)
  have hn : normSq gP = normSq g := by
    rw [hgP, normSq_cons]
    simp
  have hnb : normSq gbP = s ^ 2 / v + normSq gb := by
    rw [hgbP, normSq_cons, div_pow, Real.sq_sqrt hv.le]
  have iS2 : Integrable (fun ξ : Fin k → ℝ => ∫ z, H (z, ξ) ^ 2 ∂gaussianReal 0 1)
      (stdGauss (Fin k)) := iH2.integral_prod_right
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := i1.integral_prod_right
    simp_rw [inner1] at this
    exact this
  · rw [← e1, integral_prod_symm _ i1]
    simp_rw [inner1]
  · refine Integrable.mono' iS2 (hfm.pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact inner2 ξ
  · have hI : Integrable (fun ξ : Fin k → ℝ => fS s g gb (√v • ξ) ^ 2) (stdGauss (Fin k)) := by
      refine Integrable.mono' iS2 (hfm.pow_const 2).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact inner2 ξ
    calc ∫ ξ : Fin k → ℝ, fS s g gb (√v • ξ) ^ 2 ∂stdGauss (Fin k)
        ≤ ∫ ξ : Fin k → ℝ, (∫ z, H (z, ξ) ^ 2 ∂gaussianReal 0 1) ∂stdGauss (Fin k) :=
          integral_mono hI iS2 inner2
      _ = ∫ p, H p ^ 2 ∂((gaussianReal 0 1).prod (stdGauss (Fin k))) :=
          (integral_prod_symm _ iH2).symm
      _ ≤ 3 / 2 * v ^ 2 * normSq gP * normSq gbP + c ^ 2 := vH2
      _ = 3 / 2 * v ^ 2 * normSq g * (s ^ 2 / v + normSq gb) + c ^ 2 := by rw [hn, hnb]

end row

/-! ## One layer -/

/-- **One ReLU layer against the smoothing**: for an `m × k` Gaussian matrix `M` of entry
variance `v > 0`, `S(M) = Σ_i ReLU((M g)_i)·ψ_s((M ḡ)_i)` has mean `m·c`, and
`E (S − m c)² ≤ m·(3/2)·v²·|g|²·(s²/v + |ḡ|²)` (the rows are independent). -/
theorem smooth_layer {m k : ℕ} {v : ℝ} (hv : 0 < v) (s : ℝ) (g gb : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      dotp (reluV (M.mulVec g)) (fun i => psiS s ((M.mulVec gb) i))) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, dotp (reluV (M.mulVec g)) (fun i => psiS s ((M.mulVec gb) i))
      ∂gaussMat m k v = (m : ℝ) * cS v s g gb ∧
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (reluV (M.mulVec g)) (fun i => psiS s ((M.mulVec gb) i)) -
        (m : ℝ) * cS v s g gb) ^ 2) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (dotp (reluV (M.mulVec g))
        (fun i => psiS s ((M.mulVec gb) i)) - (m : ℝ) * cS v s g gb) ^ 2 ∂gaussMat m k v ≤
      (m : ℝ) * (3 / 2 * v ^ 2 * normSq g * (s ^ 2 / v + normSq gb)) := by
  obtain ⟨i1, e1, i2, u2⟩ := smooth_row hv s g gb
  have hf := measurable_fS s g gb
  have hsum : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec g)) (fun i => psiS s ((M.mulVec gb) i)) =
        ∑ i, fS s g gb (rowOf i M) := fun M => rfl
  simp_rw [hsum]
  set c := cS v s g gb with hc
  have hrow : ∀ i : Fin m, Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => fS s g gb (rowOf i M))
      (gaussMat m k v) := fun i => (row_integrable_iff (m := m) v i hf).mpr i1
  have iS : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => ∑ i, fS s g gb (rowOf i M))
      (gaussMat m k v) := integrable_finsetSum _ fun i _ => hrow i
  have eS : ∫ M : Matrix (Fin m) (Fin k) ℝ, ∑ i, fS s g gb (rowOf i M) ∂gaussMat m k v =
      (m : ℝ) * c := by
    rw [integral_finsetSum _ fun i _ => hrow i]
    simp_rw [row_integral (m := m) v _ hf, e1]
    simp
  obtain ⟨iQ, eQ⟩ := rows_sum_sq (m := m) v (fS s g gb) hf i2
  rw [e1] at eQ
  have hexp : (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, fS s g gb (rowOf i M) - (m : ℝ) * c) ^ 2) =
      fun M => (∑ i, fS s g gb (rowOf i M)) ^ 2 -
        2 * ((m : ℝ) * c) * (∑ i, fS s g gb (rowOf i M)) + ((m : ℝ) * c) ^ 2 := by
    funext M
    ring
  have iB : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      2 * ((m : ℝ) * c) * (∑ i, fS s g gb (rowOf i M))) (gaussMat m k v) := iS.const_mul _
  refine ⟨iS, eS, ?_, ?_⟩
  · rw [hexp]
    exact (iQ.sub iB).add (integrable_const _)
  · have iQB : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, fS s g gb (rowOf i M)) ^ 2 -
        2 * ((m : ℝ) * c) * (∑ i, fS s g gb (rowOf i M))) (gaussMat m k v) := iQ.sub iB
    rw [hexp, integral_add iQB (integrable_const _), integral_sub iQ iB,
      integral_const_mul, eS, eQ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have := mul_le_mul_of_nonneg_left u2 hm0
    nlinarith

end BstLean.Part137
