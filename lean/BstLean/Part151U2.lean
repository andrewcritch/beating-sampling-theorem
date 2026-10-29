import BstLean.Part151U
import BstLean.Part148GC

/-!
# Part 151, item 4 (d): Lemma U (ii), (iii): the Lipschitz constant and the two concentration events

Role: `delegations/statements/p151-spec.md`, item 4 (d). Paper source:
`proofs/option-n/theorem5-09-fluctuation.tex`, Lemma U (ii), (iii).

Fix `W`, `A₁`, `A₂` (so the centre `b = bh (W, (A₁, A₂)) ≠ 0` and the residual `r(x)` are fixed)
and `θF = (F₁, F₂)`. The last matrix `A₃` of `A` (entries `N(0, t_A)`, `t_A = 2/m_A`) takes the
place of the pair `(c_A, G)` of the document: given `c = A₃ b`, the matrix `A₃` has the
distribution of `glue b c (M′ * projPerp b)`, `M′` a Gaussian matrix (`s1_disint`, Part 134).
`LF` is a Lipschitz constant of `z_F` (a hypothesis), `Mr` a bound of `‖C_r‖_op`
(`t_A·E_ξ⟨r(x), w⟩² ≤ Mr·|w|²`, a hypothesis), `ℓ_U = √(t_F·LF²·Mr)`.

* `condConc`: a general conditional concentration lemma for `g(A₃ b, A₃)`.
* `dU_diff_sq`, **`lemmaU_ii`**, `TU_lip`: the Lipschitz constant `ℓ_U/√t_A` in the part of `A₃`
  that does not move `A₃ b`.
* `TU_glue_lip`, `cross_glue_lip`, `lemmaU_cond_TU`, `lemmaU_cond_cross`: the conditional form.
* **`lemmaU_EU`**: the event `E_U` with its charge `exp(−2u²/(π²ℓ_U²))`.
* **`lemmaU_Ecross`**: the event `E_×` with the same charge (`dU_condMean`: the conditional
  mean of `Δ_U` given `c_A` is `0`).
The constant `π²/4` of Part 148 is in the place of the constant `1` of the fact (G1).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (nrm nrm_sq nrm_nonneg)
open BstLean.Part133 (sq_integral_le)
open BstLean.Part134 (lam res sig measurable_lam measurable_sig measurable_res normSq_ne_zero
  cDist eDir measurable_mulVec_joint projPerp glue glue_res s1_disint measurable_glue
  measurable_mul_right res_self)
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint)
open BstLean.Part148 (gaussConc_mat_upper)
open BstLean.Part149 (thA tauOutOf outTrue outStand normSq_res_le lam_sq_le)
open BstLean.Part150 (CMap)

/-! ## A general conditional concentration lemma -/

section cond

variable {n m : ℕ}

/-- **Conditional Gaussian concentration given `c = M b`.** `M` is an `n × m` Gaussian matrix
with entry variance `v`, `b ≠ 0`. If for every `c` the function
`M′ ↦ g c (glue b c (M′ * projPerp b))` is Lipschitz for the Frobenius norm with constant `K`,
then `g (M b) M` is above its conditional mean given `M b` by `u` with probability at most
`exp(−2u²/(π²·v·K²))`. -/
theorem condConc {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0)
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin m) ℝ → ℝ}
    (hg : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ => g p.1 p.2)) {K : ℝ}
    (hK0 : 0 ≤ K)
    (hK : ∀ (c : Fin n → ℝ) (M M' : Matrix (Fin n) (Fin m) ℝ),
      |g c (glue b c (M * projPerp b)) - g c (glue b c (M' * projPerp b))| ≤
        K * √(∑ i, ∑ j, (M i j - M' i j) ^ 2)) {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n m v).real
        {M | (∫ M', g (M.mulVec b) (glue b (M.mulVec b) (M' * projPerp b)) ∂gaussMat n m v) + u ≤
          g (M.mulVec b) M} ≤
      Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * (v * K ^ 2))) := by
  have hΦ : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) :=
    measurable_fst.prodMk ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  have hG : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      g p.1 (glue b p.1 (p.2 * projPerp b))) := hg.comp hΦ
  set mg : (Fin n → ℝ) → ℝ := fun c =>
    ∫ M', g c (glue b c (M' * projPerp b)) ∂gaussMat n m v with hmg
  have hmgm : Measurable mg :=
    (StronglyMeasurable.integral_prod_right'
      (f := fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
        g p.1 (glue b p.1 (p.2 * projPerp b))) hG.stronglyMeasurable).measurable
  set S : Set ((Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ) := {p | mg p.1 + u ≤ g p.1 p.2} with hS
  have mS : MeasurableSet S :=
    measurableSet_le ((hmgm.comp measurable_fst).add measurable_const) hg
  have hm1 : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) :=
    (measurable_mulVec_right b).prodMk measurable_id
  have e0 : {M : Matrix (Fin n) (Fin m) ℝ |
      (∫ M', g (M.mulVec b) (glue b (M.mulVec b) (M' * projPerp b)) ∂gaussMat n m v) + u ≤
        g (M.mulVec b) M} = (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) ⁻¹' S := rfl
  set E : ℝ := Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * (v * K ^ 2))) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hle : (gaussMat n m v) ((fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) ⁻¹' S) ≤
      ENNReal.ofReal E := by
    rw [← Measure.map_apply hm1 mS, s1_disint v hb, Measure.map_apply hΦ mS,
      Measure.prod_apply (hΦ mS)]
    calc ∫⁻ c, (gaussMat n m v) (Prod.mk c ⁻¹'
          ((fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
            (p.1, glue b p.1 (p.2 * projPerp b))) ⁻¹' S)) ∂cDist n v b
        ≤ ∫⁻ _c, ENNReal.ofReal E ∂cDist n v b := by
          refine lintegral_mono fun c => ?_
          have h := gaussConc_mat_upper (g := fun M' => g c (glue b c (M' * projPerp b)))
            hK0 (hK c) hv hu
          rw [measureReal_def] at h
          exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hE0).mpr h
      _ = ENNReal.ofReal E := by simp
  rw [e0, measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hE0 hle

end cond

/-! ## The Lipschitz constant -/

section U2

variable {n : ℕ} (bh : CMap n) (W : MlpParam (2 * n) (mW n) n)
  (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

/-- `T_U = √(t_F)·|Δ_U|`, as a function of the last matrix `A₃`. -/
noncomputable def TU (θF : HidParam n (mF n)) (A₃ : Matrix (Fin n) (Fin (mA n)) ℝ) : ℝ :=
  √(2 / (mF n : ℝ) * normSq (dU bh W (A₁, A₂, A₃) θF))

/-- `ℓ_U = √(t_F·LF²·Mr)`. -/
noncomputable def ellU (n : ℕ) (LF Mr : ℝ) : ℝ := √(2 / (mF n : ℝ) * LF ^ 2 * Mr)

lemma int_bdd {f : (Fin n → ℝ) → ℝ} (hm : Measurable f) {C : ℝ} (hC : ∀ ξ, f ξ ^ 2 ≤ C) :
    Integrable f (stdGauss (Fin n)) := by
  refine Integrable.of_bound hm.aestronglyMeasurable (1 + C) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs]
  have := hC ξ
  nlinarith [sq_nonneg (|f ξ| - 1), sq_abs (f ξ)]

lemma measurable_psiF_out (θF : HidParam n (mF n)) (i : Fin (mF n))
    (B : Matrix (Fin n) (Fin (mA n)) ℝ) :
    Measurable (fun ξ => psiF θF i (B.mulVec (hU W A₁ A₂ ξ))) :=
  (continuous_psiF θF i).measurable.comp
    ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp
      (measurable_hU W A₁ A₂))

lemma psiF_out_sq_le (hn : 1 ≤ n) (θF : HidParam n (mF n)) (i : Fin (mF n))
    (B : Matrix (Fin n) (Fin (mA n)) ℝ) (ξ : Fin n → ℝ) :
    psiF θF i (B.mulVec (hU W A₁ A₂ ξ)) ^ 2 ≤
      frob θF.2 * frob θF.1 * (1 + frob B * (frob A₂ * frob A₁)) := by
  have h1 := psiF_sq_le θF i (B.mulVec (hU W A₁ A₂ ξ))
  have h2 := normSq_mulVec_le B (hU W A₁ A₂ ξ)
  have h3 := hU_le W A₁ A₂ hn ξ
  have h4 : normSq (B.mulVec (hU W A₁ A₂ ξ)) ≤ frob B * (frob A₂ * frob A₁) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (frob_nonneg _))
  have h5 : 0 ≤ frob θF.2 * frob θF.1 := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) h5)

lemma psiF_out_int (hn : 1 ≤ n) (θF : HidParam n (mF n)) (i : Fin (mF n))
    (B : Matrix (Fin n) (Fin (mA n)) ℝ) :
    Integrable (fun ξ => psiF θF i (B.mulVec (hU W A₁ A₂ ξ))) (stdGauss (Fin n)) :=
  int_bdd (measurable_psiF_out W A₁ A₂ θF i B) (psiF_out_sq_le W A₁ A₂ hn θF i B)

/-- **The core of Lemma U (ii).** If `B` and `B′` have the same image of `b` and
`B a₂(x) − B′ a₂(x) = N r(x)` for every `x`, then for every `w`:
`⟨w, Δ_U(B) − Δ_U(B′)⟩² ≤ |w|²·LF²·(Mr/t_A)·‖N‖²_F`. -/
theorem dU_diff_sq (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n)) {LF Mr : ℝ}
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    (B B' N : Matrix (Fin n) (Fin (mA n)) ℝ)
    (hbB : B.mulVec (bh (W, (A₁, A₂))) = B'.mulVec (bh (W, (A₁, A₂))))
    (hN : ∀ ξ, B.mulVec (hU W A₁ A₂ ξ) - B'.mulVec (hU W A₁ A₂ ξ) =
      N.mulVec (res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ)))
    (w : Fin (mF n) → ℝ) :
    (∑ i, w i * (dU bh W (A₁, A₂, B) θF i - dU bh W (A₁, A₂, B') θF i)) ^ 2 ≤
      normSq w * (LF ^ 2 * (Mr / (2 / (mA n : ℝ)) * frob N)) := by
  set b := bh (W, (A₁, A₂)) with hbd
  set h := hU W A₁ A₂ with hh
  have hmA : 0 < (mA n : ℝ) := by
    have : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have htA : 0 < 2 / (mA n : ℝ) := by positivity
  have hH0 : 0 ≤ frob A₂ * frob A₁ := mul_nonneg (frob_nonneg _) (frob_nonneg _)
  -- the difference of `Δ_U` is the difference of the true means
  have ed : ∀ i, dU bh W (A₁, A₂, B) θF i - dU bh W (A₁, A₂, B') θF i =
      ∫ ξ, (psiF θF i (B.mulVec (h ξ)) - psiF θF i (B'.mulVec (h ξ))) ∂stdGauss (Fin n) := by
    intro i
    rw [dU_coord bh W A₁ A₂ hn hb B θF i, dU_coord bh W A₁ A₂ hn hb B' θF i, ← hbd, hbB,
      integral_sub (psiF_out_int W A₁ A₂ hn θF i B) (psiF_out_int W A₁ A₂ hn θF i B')]
    unfold outTrue
    ring
  set f : (Fin n → ℝ) → ℝ := fun ξ =>
    ∑ i, w i * (psiF θF i (B.mulVec (h ξ)) - psiF θF i (B'.mulVec (h ξ))) with hf
  have hfm : Measurable f :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul
      ((measurable_psiF_out W A₁ A₂ θF i B).sub (measurable_psiF_out W A₁ A₂ θF i B'))
  have hsum : ∑ i, w i * (dU bh W (A₁, A₂, B) θF i - dU bh W (A₁, A₂, B') θF i) =
      ∫ ξ, f ξ ∂stdGauss (Fin n) := by
    simp_rw [ed]
    have h1 := integral_finsetSum (μ := stdGauss (Fin n)) Finset.univ
      (f := fun i ξ => w i * (psiF θF i (B.mulVec (h ξ)) - psiF θF i (B'.mulVec (h ξ))))
      (fun i _ => ((psiF_out_int W A₁ A₂ hn θF i B).sub
        (psiF_out_int W A₁ A₂ hn θF i B')).const_mul _)
    rw [hf]
    simp only
    rw [h1]
    simp_rw [integral_const_mul]
  -- pointwise bound
  set gN : (Fin n → ℝ) → ℝ := fun ξ => normSq (N.mulVec (res b (h ξ))) with hgN
  have hpt : ∀ ξ, f ξ ^ 2 ≤ normSq w * (LF ^ 2 * gN ξ) := by
    intro ξ
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w
      (fun i => psiF θF i (B.mulVec (h ξ)) - psiF θF i (B'.mulVec (h ξ)))
    have e1 : ∑ i, (psiF θF i (B.mulVec (h ξ)) - psiF θF i (B'.mulVec (h ξ))) ^ 2 =
        normSq (hid2 θF.1 θF.2 (B.mulVec (h ξ)) - hid2 θF.1 θF.2 (B'.mulVec (h ξ))) := rfl
    have h2 := hLF (B.mulVec (h ξ)) (B'.mulVec (h ξ))
    rw [hN ξ] at h2
    have hw0 : 0 ≤ normSq w := normSq_nonneg w
    calc f ξ ^ 2 ≤ (∑ i, w i ^ 2) * ∑ i, (psiF θF i (B.mulVec (h ξ)) -
          psiF θF i (B'.mulVec (h ξ))) ^ 2 := cs
      _ ≤ normSq w * (LF ^ 2 * gN ξ) := by
          rw [e1]
          exact mul_le_mul_of_nonneg_left h2 hw0
  have hres : ∀ ξ, normSq (res b (h ξ)) ≤ frob A₂ * frob A₁ := fun ξ =>
    (normSq_res_le hb _).trans (hU_le W A₁ A₂ hn ξ)
  have hgNb : ∀ ξ, gN ξ ≤ frob N * (frob A₂ * frob A₁) := fun ξ =>
    (normSq_mulVec_le N _).trans (mul_le_mul_of_nonneg_left (hres ξ) (frob_nonneg _))
  have hrm : Measurable (fun ξ => res b (h ξ)) := (measurable_res b).comp (measurable_hU W A₁ A₂)
  have hrow : ∀ i : Fin n, Measurable (fun ξ => ∑ j, res b (h ξ) j * N i j) :=
    fun i => Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp hrm).mul measurable_const
  have hrowsq : ∀ (i : Fin n) ξ, (∑ j, res b (h ξ) j * N i j) ^ 2 ≤ gN ξ := by
    intro i ξ
    have e : (∑ j, res b (h ξ) j * N i j) = (N.mulVec (res b (h ξ))) i := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e, hgN]
    unfold normSq
    exact Finset.single_le_sum (f := fun l => (N.mulVec (res b (h ξ))) l ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ i)
  have hrowint : ∀ i : Fin n, Integrable (fun ξ => (∑ j, res b (h ξ) j * N i j) ^ 2)
      (stdGauss (Fin n)) := by
    intro i
    refine Integrable.of_bound ((hrow i).pow_const 2).aestronglyMeasurable
      (frob N * (frob A₂ * frob A₁)) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hrowsq i ξ).trans (hgNb ξ)
  have egN : ∀ ξ, gN ξ = ∑ i, (∑ j, res b (h ξ) j * N i j) ^ 2 := by
    intro ξ
    rw [hgN]
    unfold normSq
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hgNint : Integrable gN (stdGauss (Fin n)) := by
    have : gN = fun ξ => ∑ i, (∑ j, res b (h ξ) j * N i j) ^ 2 := funext egN
    rw [this]
    exact integrable_finsetSum _ fun i _ => hrowint i
  have hgNI : ∫ ξ, gN ξ ∂stdGauss (Fin n) ≤ Mr / (2 / (mA n : ℝ)) * frob N := by
    have : gN = fun ξ => ∑ i, (∑ j, res b (h ξ) j * N i j) ^ 2 := funext egN
    rw [this, integral_finsetSum _ fun i _ => hrowint i]
    unfold frob
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hMr (fun j => N i j)
    rw [div_mul_eq_mul_div, le_div_iff₀ htA]
    linarith
  have hf2int : Integrable (fun ξ => f ξ ^ 2) (stdGauss (Fin n)) := by
    refine Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable
      (normSq w * (LF ^ 2 * (frob N * (frob A₂ * frob A₁))))
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine (hpt ξ).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hgNb ξ) (sq_nonneg _)) (normSq_nonneg w))
  rw [hsum]
  calc (∫ ξ, f ξ ∂stdGauss (Fin n)) ^ 2 ≤ ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n) := sq_integral_le hf2int
    _ ≤ ∫ ξ, normSq w * (LF ^ 2 * gN ξ) ∂stdGauss (Fin n) :=
        integral_mono hf2int ((hgNint.const_mul _).const_mul _) hpt
    _ = normSq w * (LF ^ 2 * ∫ ξ, gN ξ ∂stdGauss (Fin n)) := by
        rw [integral_const_mul, integral_const_mul]
    _ ≤ normSq w * (LF ^ 2 * (Mr / (2 / (mA n : ℝ)) * frob N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgNI (sq_nonneg _))
          (normSq_nonneg w)

/-- The same with the constant `ℓ_U/√t_A` and square roots. -/
theorem dU_diff_abs (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n)) {LF Mr : ℝ}
    (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    (B B' N : Matrix (Fin n) (Fin (mA n)) ℝ)
    (hbB : B.mulVec (bh (W, (A₁, A₂))) = B'.mulVec (bh (W, (A₁, A₂))))
    (hN : ∀ ξ, B.mulVec (hU W A₁ A₂ ξ) - B'.mulVec (hU W A₁ A₂ ξ) =
      N.mulVec (res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ)))
    (w : Fin (mF n) → ℝ) :
    |√(2 / (mF n : ℝ)) * ∑ i, w i * (dU bh W (A₁, A₂, B) θF i - dU bh W (A₁, A₂, B') θF i)| ≤
      √(normSq w) * (ellU n LF Mr / √(2 / (mA n : ℝ))) * √(frob N) := by
  have h := dU_diff_sq bh W A₁ A₂ hn hb θF hLF hMr B B' N hbB hN w
  have hmA : 0 < (mA n : ℝ) := by
    have : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have htA : 0 < 2 / (mA n : ℝ) := by positivity
  have htF : 0 ≤ 2 / (mF n : ℝ) := by positivity
  have hw0 := normSq_nonneg w
  have hN0 := frob_nonneg N
  set x := ∑ i, w i * (dU bh W (A₁, A₂, B) θF i - dU bh W (A₁, A₂, B') θF i) with hx
  set R : ℝ := √(normSq w) * (ellU n LF Mr / √(2 / (mA n : ℝ))) * √(frob N) with hR
  have hR0 : 0 ≤ R := by rw [hR]; unfold ellU; positivity
  have hR2 : R ^ 2 = 2 / (mF n : ℝ) * (normSq w * (LF ^ 2 * (Mr / (2 / (mA n : ℝ)) * frob N))) := by
    rw [hR]
    unfold ellU
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hw0, Real.sq_sqrt hN0, Real.sq_sqrt htA.le,
      Real.sq_sqrt (by positivity)]
    field_simp
  have h2 : (√(2 / (mF n : ℝ)) * x) ^ 2 ≤ R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt htF, hR2]
    exact mul_le_mul_of_nonneg_left h htF
  exact abs_le_of_sq_le_sq h2 hR0

/-- **Lemma U (ii), linear forms.** If `A₃` and `A₃′` have the same image of `b`, then for
every `w`: `|√t_F·⟨w, Δ_U(A₃) − Δ_U(A₃′)⟩| ≤ |w|·(ℓ_U/√t_A)·‖A₃ − A₃′‖_F`. -/
theorem lemmaU_ii (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n)) {LF Mr : ℝ}
    (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    (A₃ A₃' : Matrix (Fin n) (Fin (mA n)) ℝ)
    (h0 : (A₃ - A₃').mulVec (bh (W, (A₁, A₂))) = 0) (w : Fin (mF n) → ℝ) :
    |√(2 / (mF n : ℝ)) * ∑ i, w i *
        (dU bh W (A₁, A₂, A₃) θF i - dU bh W (A₁, A₂, A₃') θF i)| ≤
      √(normSq w) * (ellU n LF Mr / √(2 / (mA n : ℝ))) *
        √(∑ i, ∑ j, (A₃ i j - A₃' i j) ^ 2) := by
  have hbB : A₃.mulVec (bh (W, (A₁, A₂))) = A₃'.mulVec (bh (W, (A₁, A₂))) := by
    rw [Matrix.sub_mulVec] at h0
    exact sub_eq_zero.mp h0
  have hN : ∀ ξ, A₃.mulVec (hU W A₁ A₂ ξ) - A₃'.mulVec (hU W A₁ A₂ ξ) =
      (A₃ - A₃').mulVec (res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ)) := by
    intro ξ
    have e : hU W A₁ A₂ ξ = lam (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) • bh (W, (A₁, A₂)) +
        res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) := by
      unfold res; abel
    rw [← Matrix.sub_mulVec]
    conv_lhs => rw [e]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, h0, smul_zero, zero_add]
  have h := dU_diff_abs bh W A₁ A₂ hn hb θF hMr0 hLF hMr A₃ A₃' (A₃ - A₃') hbB hN w
  have e : frob (A₃ - A₃') = ∑ i, ∑ j, (A₃ i j - A₃' i j) ^ 2 := rfl
  rw [e] at h
  exact h

/-- From the linear forms to `T_U`. -/
lemma TU_diff (θF : HidParam n (mF n)) (B B' : Matrix (Fin n) (Fin (mA n)) ℝ) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ w : Fin (mF n) → ℝ, |√(2 / (mF n : ℝ)) * ∑ i, w i *
        (dU bh W (A₁, A₂, B) θF i - dU bh W (A₁, A₂, B') θF i)| ≤ √(normSq w) * C) :
    |TU bh W A₁ A₂ θF B - TU bh W A₁ A₂ θF B'| ≤ C := by
  have htF : 0 ≤ 2 / (mF n : ℝ) := by positivity
  set d := dU bh W (A₁, A₂, B) θF with hd
  set d' := dU bh W (A₁, A₂, B') θF with hd'
  have e1 : TU bh W A₁ A₂ θF B = √(2 / (mF n : ℝ)) * nrm d := by
    unfold TU nrm; exact Real.sqrt_mul htF _
  have e2 : TU bh W A₁ A₂ θF B' = √(2 / (mF n : ℝ)) * nrm d' := by
    unfold TU nrm; exact Real.sqrt_mul htF _
  have h1 := nrm_sub_abs d d'
  have h2 := hC (d - d')
  have e3 : ∑ i, (d - d') i * (d i - d' i) = normSq (d - d') := by
    unfold normSq
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [e3] at h2
  have hs0 := Real.sqrt_nonneg (2 / (mF n : ℝ))
  have hn0 := nrm_nonneg (d - d')
  have hnsq := nrm_sq (d - d')
  have h3 : √(2 / (mF n : ℝ)) * nrm (d - d') ≤ C := by
    rcases hn0.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact hC0
    · have h4 : √(2 / (mF n : ℝ)) * normSq (d - d') ≤ nrm (d - d') * C := by
        have := (le_abs_self _).trans h2
        unfold nrm
        exact this
      rw [← hnsq] at h4
      have h5 : nrm (d - d') * (√(2 / (mF n : ℝ)) * nrm (d - d')) ≤ nrm (d - d') * C := by
        nlinarith
      exact le_of_mul_le_mul_left h5 hpos
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_nonneg hs0]
  exact (mul_le_mul_of_nonneg_left h1 hs0).trans h3

/-- **Lemma U (ii) for `T_U`**: `|T_U(A₃) − T_U(A₃′)| ≤ (ℓ_U/√t_A)·‖A₃ − A₃′‖_F` if
`A₃ b = A₃′ b`. -/
theorem TU_lip (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n)) {LF Mr : ℝ}
    (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    (A₃ A₃' : Matrix (Fin n) (Fin (mA n)) ℝ)
    (h0 : (A₃ - A₃').mulVec (bh (W, (A₁, A₂))) = 0) :
    |TU bh W A₁ A₂ θF A₃ - TU bh W A₁ A₂ θF A₃'| ≤
      ellU n LF Mr / √(2 / (mA n : ℝ)) * √(∑ i, ∑ j, (A₃ i j - A₃' i j) ^ 2) := by
  refine TU_diff bh W A₁ A₂ θF A₃ A₃' (by unfold ellU; positivity) fun w => ?_
  have h := lemmaU_ii bh W A₁ A₂ hn hb θF hMr0 hLF hMr A₃ A₃' h0 w
  rw [mul_assoc] at h
  exact h

/-! ## The conditional form -/

lemma glue_b (hb : bh (W, (A₁, A₂)) ≠ 0) (c : Fin n → ℝ) (M : Matrix (Fin n) (Fin (mA n)) ℝ) :
    (glue (bh (W, (A₁, A₂))) c (M * projPerp (bh (W, (A₁, A₂))))).mulVec (bh (W, (A₁, A₂))) =
      lam (bh (W, (A₁, A₂))) (bh (W, (A₁, A₂))) • c := by
  rw [glue_res, res_self hb, Matrix.mulVec_zero, add_zero]

/-- The linear forms of `Δ_U` along the glued matrices. -/
theorem cross_glue_lip (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    (c : Fin n → ℝ) (M M' : Matrix (Fin n) (Fin (mA n)) ℝ) (w : Fin (mF n) → ℝ) :
    |√(2 / (mF n : ℝ)) * ∑ i, w i *
        (dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M * projPerp (bh (W, (A₁, A₂))))) θF i -
          dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF i)| ≤
      √(normSq w) * (ellU n LF Mr / √(2 / (mA n : ℝ))) *
        √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  have hbB := (glue_b bh W A₁ A₂ hb c M).trans (glue_b bh W A₁ A₂ hb c M').symm
  have hN : ∀ ξ, (glue (bh (W, (A₁, A₂))) c (M * projPerp (bh (W, (A₁, A₂))))).mulVec
        (hU W A₁ A₂ ξ) -
      (glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))).mulVec (hU W A₁ A₂ ξ) =
      (M - M').mulVec (res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ)) := by
    intro ξ
    rw [glue_res, glue_res, Matrix.sub_mulVec]
    abel
  have h := dU_diff_abs bh W A₁ A₂ hn hb θF hMr0 hLF hMr _ _ (M - M') hbB hN w
  have e : frob (M - M') = ∑ i, ∑ j, (M i j - M' i j) ^ 2 := rfl
  rw [e] at h
  exact h

/-- `M′ ↦ T_U(glue b c (M′ * projPerp b))` is Lipschitz with constant `ℓ_U/√t_A`. -/
theorem TU_glue_lip (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    (c : Fin n → ℝ) (M M' : Matrix (Fin n) (Fin (mA n)) ℝ) :
    |TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) c (M * projPerp (bh (W, (A₁, A₂))))) -
        TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂)))))| ≤
      ellU n LF Mr / √(2 / (mA n : ℝ)) * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  refine TU_diff bh W A₁ A₂ θF _ _ (by unfold ellU; positivity) fun w => ?_
  have h := cross_glue_lip bh W A₁ A₂ hn hb θF hMr0 hLF hMr c M M' w
  rw [mul_assoc] at h
  exact h

/-! ## The events -/

lemma measurable_dU_A3 (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    (i : Fin (mF n)) :
    Measurable (fun A₃ : Matrix (Fin n) (Fin (mA n)) ℝ => dU bh W (A₁, A₂, A₃) θF i) := by
  have h := measurable_dU_coord bh W A₁ A₂ θF i
  have e : (fun A₃ : Matrix (Fin n) (Fin (mA n)) ℝ => dU bh W (A₁, A₂, A₃) θF i) = _ :=
    funext fun A₃ => dU_coord bh W A₁ A₂ hn hb A₃ θF i
  rw [e]
  exact h

lemma measurable_TU (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n)) :
    Measurable (TU bh W A₁ A₂ θF) := by
  unfold TU normSq
  exact (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_dU_A3 bh W A₁ A₂ hn hb θF i).pow_const 2)).sqrt

lemma exp_arg (n : ℕ) (hn : 1 ≤ n) (LF Mr u : ℝ) :
    Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 *
        (2 / (mA n : ℝ) * (ellU n LF Mr / √(2 / (mA n : ℝ))) ^ 2))) =
      Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * ellU n LF Mr ^ 2)) := by
  have hmA : 0 < (mA n : ℝ) := by
    have : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have htA : 0 < 2 / (mA n : ℝ) := by positivity
  congr 3
  rw [div_pow, Real.sq_sqrt htA.le]
  field_simp

/-- **Lemma U (iii), the event `E_U`.** `mU c` is the conditional mean of `T_U` given
`c_A = c`. Over the last matrix `A₃` of `A`:
`Pr(T_U ≥ mU(A₃ b) + u) ≤ exp(−2u²/(π²ℓ_U²))`. -/
theorem lemmaU_EU (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | (∫ M', TU bh W A₁ A₂ θF (glue (bh (W, (A₁, A₂))) (A₃.mulVec (bh (W, (A₁, A₂))))
            (M' * projPerp (bh (W, (A₁, A₂))))) ∂gaussMat n (mA n) (2 / (mA n : ℝ))) + u ≤
          TU bh W A₁ A₂ θF A₃} ≤
      Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * ellU n LF Mr ^ 2)) := by
  have h := condConc (n := n) (m := mA n) (v := 2 / (mA n : ℝ)) (by positivity) hb
    (g := fun _ A₃ => TU bh W A₁ A₂ θF A₃)
    ((measurable_TU bh W A₁ A₂ hn hb θF).comp measurable_snd)
    (K := ellU n LF Mr / √(2 / (mA n : ℝ))) (by unfold ellU; positivity)
    (fun c M M' => TU_glue_lip bh W A₁ A₂ hn hb θF hMr0 hLF hMr c M M') hu
  rw [exp_arg n hn] at h
  exact h

/-- **Lemma U (iii), the event `E_×`, with the conditional mean as a subtracted term.** `w c` is
a direction (`|w c| ≤ 1`) that is a measurable function of `c_A = c`. -/
theorem lemmaU_Ecross_sub (hn : 1 ≤ n) (hb : bh (W, (A₁, A₂)) ≠ 0) (θF : HidParam n (mF n))
    {LF Mr : ℝ} (hMr0 : 0 ≤ Mr)
    (hLF : ∀ y y', normSq (hid2 θF.1 θF.2 y - hid2 θF.1 θF.2 y') ≤ LF ^ 2 * normSq (y - y'))
    (hMr : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
        Mr * ∑ j, w j ^ 2)
    {w : (Fin n → ℝ) → Fin (mF n) → ℝ} (hw : Measurable w) (hw1 : ∀ c, normSq (w c) ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat n (mA n) (2 / (mA n : ℝ))).real
        {A₃ | (∫ M', -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
            dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) (A₃.mulVec (bh (W, (A₁, A₂))))
              (M' * projPerp (bh (W, (A₁, A₂))))) θF i)
            ∂gaussMat n (mA n) (2 / (mA n : ℝ))) + u ≤
          -(√(2 / (mF n : ℝ)) * ∑ i, w (A₃.mulVec (bh (W, (A₁, A₂)))) i *
            dU bh W (A₁, A₂, A₃) θF i)} ≤
      Real.exp (-2 * u ^ 2 / (Real.pi ^ 2 * ellU n LF Mr ^ 2)) := by
  have hK0 : 0 ≤ ellU n LF Mr / √(2 / (mA n : ℝ)) := by unfold ellU; positivity
  have hgm : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin (mA n)) ℝ =>
      -(√(2 / (mF n : ℝ)) * ∑ i, w p.1 i * dU bh W (A₁, A₂, p.2) θF i)) := by
    refine (measurable_const.mul (Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_)).neg
    · exact (measurable_pi_apply i).comp (hw.comp measurable_fst)
    · exact (measurable_dU_A3 bh W A₁ A₂ hn hb θF i).comp measurable_snd
  have h := condConc (n := n) (m := mA n) (v := 2 / (mA n : ℝ)) (by positivity) hb
    (g := fun c A₃ => -(√(2 / (mF n : ℝ)) * ∑ i, w c i * dU bh W (A₁, A₂, A₃) θF i))
    hgm (K := ellU n LF Mr / √(2 / (mA n : ℝ))) hK0
    (fun c M M' => by
      have h1 := cross_glue_lip bh W A₁ A₂ hn hb θF hMr0 hLF hMr c M M' (w c)
      have hsw : √(normSq (w c)) ≤ 1 := by
        have h2 := Real.sqrt_le_sqrt (hw1 c)
        rwa [Real.sqrt_one] at h2
      have e : -(√(2 / (mF n : ℝ)) * ∑ i, w c i *
            dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M * projPerp (bh (W, (A₁, A₂))))) θF i) -
          -(√(2 / (mF n : ℝ)) * ∑ i, w c i *
            dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂))))) θF i) =
          -(√(2 / (mF n : ℝ)) * ∑ i, w c i *
            (dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M * projPerp (bh (W, (A₁, A₂))))) θF i -
              dU bh W (A₁, A₂, glue (bh (W, (A₁, A₂))) c (M' * projPerp (bh (W, (A₁, A₂)))))
                θF i)) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      rw [e, abs_neg]
      refine h1.trans ?_
      have hs0 := Real.sqrt_nonneg (∑ i, ∑ j, (M i j - M' i j) ^ 2)
      have : √(normSq (w c)) * (ellU n LF Mr / √(2 / (mA n : ℝ))) ≤
          1 * (ellU n LF Mr / √(2 / (mA n : ℝ))) := mul_le_mul_of_nonneg_right hsw hK0
      rw [one_mul] at this
      exact mul_le_mul_of_nonneg_right this hs0) hu
  rw [exp_arg n hn] at h
  exact h

end U2

end BstLean.Part151
