import BstLean.Part149CDefs
import BstLean.Part149Mean2

/-!
# Part 149, helper `Layer1`: the first hidden layer of `A` at the points of the cheap stand-in

Role: `delegations/statements/p149-spec.md`.

Do not use `sorry`, `native_decide` or `axiom`.

`A₁` is the first hidden matrix of `A` (`m × n`, distribution `gaussMat m n (2/n)`);
`a₁(x) = ReLU(A₁ x)`. `q = β²/(β² + τ²)`.

* `lay1K_L2`, `lay1D_L2`: one ReLU layer at random unit inputs: the Gram kernel against
  `(m/n)·κ(⟨X, X′⟩)` (bound `(m/n)·√(6/m)`) and the diagonal against `m/n` (bound `(m/n)·√(5/m)`).
* **`errD1_mean`**: `E_{A₁} errD1 c τ A₁ ≤ (m/n)²·(5/m)` for every centre `c` and every scalar `τ`.
* `dQ1`, **`Qk_mean`**: `E_ξ E_{A₁} Qk (κ(q)) (β·ξ) τ A₁ ≤ ((m/n)·dQ1 n m q)²` for `q` in the window
  `462/1000 ≤ q ≤ 527/1000`.
* `measurable_Qk`, `measurable_errD1`: joint measurability.
* **`dQ1_le`**: for `n ≥ 4096`, `m = mA n` and `q` in the window,
  `dQ1 ≤ 0.534859/√n + 12.51/n`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 BstLean.Part145

variable {n m : ℕ}

/-! ## One ReLU layer at random unit inputs -/

lemma measurable_relu_mulVec {Ω : Type*} [MeasurableSpace Ω] {X : Ω → Fin n → ℝ}
    (hX : Measurable X) :
    Measurable (fun z : Ω × Matrix (Fin m) (Fin n) ℝ => reluV (z.2.mulVec (X z.1))) := by
  have h := (measurable_reluV (ι := Fin m)).comp
    ((measurable_mulVec_joint (n := m) (m := n)).comp
      (measurable_snd.prodMk (hX.comp measurable_fst)))
  simp only [Function.comp_def] at h
  exact h

lemma l2_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ) :
    L2le P (fun _ : Ω => a) a :=
  ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩

/-- **The Gram kernel of one ReLU layer at two random unit inputs**, in `L²` over the inputs and
the matrix. -/
theorem lay1K_L2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hn : 1 ≤ n) (hm : 1 ≤ m) {X X' : Ω → Fin n → ℝ} (hX : Measurable X)
    (hX' : Measurable X') (h1 : ∀ ω, normSq (X ω) = 1) (h1' : ∀ ω, normSq (X' ω) = 1) :
    L2le (P.prod (gaussMat m n (2 / (n : ℝ))))
      (fun z : Ω × Matrix (Fin m) (Fin n) ℝ =>
        dotp (reluV (z.2.mulVec (X z.1))) (reluV (z.2.mulVec (X' z.1))) -
          (m : ℝ) / n * kappa (dotp (X z.1) (X' z.1)))
      ((m : ℝ) / n * √(6 / (m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have md : Measurable (fun z : Ω × Matrix (Fin m) (Fin n) ℝ => dotp (X z.1) (X' z.1)) :=
    continuous_dotp.measurable.comp ((hX.comp measurable_fst).prodMk (hX'.comp measurable_fst))
  have mf : Measurable (fun z : Ω × Matrix (Fin m) (Fin n) ℝ =>
      dotp (reluV (z.2.mulVec (X z.1))) (reluV (z.2.mulVec (X' z.1))) -
        (m : ℝ) / n * kappa (dotp (X z.1) (X' z.1))) :=
    (continuous_dotp.measurable.comp
      ((measurable_relu_mulVec hX).prodMk (measurable_relu_mulVec hX'))).sub
      (measurable_const.mul (continuous_kappa.measurable.comp md))
  refine L2le.prod mf.aestronglyMeasurable (l2_const P _) (Filter.Eventually.of_forall fun ω => ?_)
  obtain ⟨iC, uC⟩ := layer_dot_relu_var (m := m) (k := n) (v := 2 / (n : ℝ)) (by positivity)
    (X ω) (X' ω)
  have e : (m : ℝ) / 2 * (2 / (n : ℝ) * kernelPhi (X ω) (X' ω)) =
      (m : ℝ) / n * kappa (dotp (X ω) (X' ω)) := by
    rw [kernelPhi_eq_psi, psi_unit _ (h1 ω) (h1' ω)]
    ring
  rw [e] at iC uC
  refine ⟨iC, uC.trans (le_of_eq ?_)⟩
  rw [h1 ω, h1' ω, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- The variance of the squared norm after a ReLU layer: `(5m/4)·(v|h|²)²`. -/
lemma relu_sq_var1 {k : ℕ} {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * (v * normSq h)) ^ 2) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ,
      (normSq (reluV (M.mulVec h)) - (m : ℝ) / 2 * (v * normSq h)) ^ 2 ∂gaussMat m k v =
      5 * (m : ℝ) / 4 * (v * normSq h) ^ 2 := by
  obtain ⟨i1, e1⟩ := layer_relu_sq (m := m) hv h
  obtain ⟨i2, e2⟩ := layer_relu_four (m := m) hv h
  set c := (m : ℝ) / 2 * (v * normSq h) with hc
  have hexp : (fun M : Matrix (Fin m) (Fin k) ℝ => (normSq (reluV (M.mulVec h)) - c) ^ 2) =
      fun M => normSq (reluV (M.mulVec h)) ^ 2 - (2 * c * normSq (reluV (M.mulVec h)) - c ^ 2) := by
    funext M; ring
  have i3 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      2 * c * normSq (reluV (M.mulVec h)) - c ^ 2) (gaussMat m k v) :=
    (i1.const_mul _).sub (integrable_const _)
  rw [hexp]
  refine ⟨i2.sub i3, ?_⟩
  rw [integral_sub i2 i3, integral_sub (i1.const_mul _) (integrable_const _),
    integral_const_mul, e1, e2, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hc]
  ring

/-- **The diagonal of one ReLU layer at a random unit input.** -/
theorem lay1D_L2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hn : 1 ≤ n) (hm : 1 ≤ m) {X : Ω → Fin n → ℝ} (hX : Measurable X)
    (h1 : ∀ ω, normSq (X ω) = 1) :
    L2le (P.prod (gaussMat m n (2 / (n : ℝ))))
      (fun z : Ω × Matrix (Fin m) (Fin n) ℝ =>
        normSq (reluV (z.2.mulVec (X z.1))) - (m : ℝ) / n)
      ((m : ℝ) / n * √(5 / (m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have mf : Measurable (fun z : Ω × Matrix (Fin m) (Fin n) ℝ =>
      normSq (reluV (z.2.mulVec (X z.1))) - (m : ℝ) / n) :=
    (continuous_normSq.measurable.comp (measurable_relu_mulVec hX)).sub measurable_const
  refine L2le.prod mf.aestronglyMeasurable (l2_const P _) (Filter.Eventually.of_forall fun ω => ?_)
  obtain ⟨iC, eC⟩ := relu_sq_var1 (m := m) (k := n) (v := 2 / (n : ℝ)) (by positivity) (X ω)
  have e : (m : ℝ) / 2 * (2 / (n : ℝ) * normSq (X ω)) = (m : ℝ) / n := by
    rw [h1 ω]
    ring
  rw [e] at iC eC
  refine ⟨iC, le_of_eq (eC.trans ?_)⟩
  rw [h1 ω, mul_pow ((m : ℝ) / n), Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-! ## The product of the two lengths -/

/-- `|d − a·b| ≤ |a² − d| + |b² − d|` for `a, b, d ≥ 0`. -/
lemma abs_sub_mul_le {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    |d - a * b| ≤ |a ^ 2 - d| + |b ^ 2 - d| := by
  rw [abs_le]
  constructor
  · have h1 := le_abs_self (a ^ 2 - d)
    have h2 := le_abs_self (b ^ 2 - d)
    have h3 := abs_nonneg (a ^ 2 - d)
    have h4 := abs_nonneg (b ^ 2 - d)
    nlinarith [sq_nonneg (a - b)]
  · rcases le_total (a ^ 2) d with h1 | h1 <;> rcases le_total (b ^ 2) d with h2 | h2
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      rcases le_total a b with hab | hab
      · nlinarith [mul_le_mul_of_nonneg_left hab ha]
      · nlinarith [mul_le_mul_of_nonneg_left hab hb]
    · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      have hab : a ≤ b := (pow_le_pow_iff_left₀ ha hb two_ne_zero).mp (h1.trans h2)
      nlinarith [mul_le_mul_of_nonneg_left hab ha]
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
      have hab : b ≤ a := (pow_le_pow_iff_left₀ hb ha two_ne_zero).mp (h2.trans h1)
      nlinarith [mul_le_mul_of_nonneg_left hab hb]
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      have h3 : d * d ≤ a ^ 2 * b ^ 2 := mul_le_mul h1 h2 hd (by positivity)
      have h4 : d ≤ a * b := by
        by_contra h
        rw [not_le] at h
        have := mul_lt_mul'' h h (mul_nonneg ha hb) (mul_nonneg ha hb)
        nlinarith
      linarith

local notation "G1" => stdGauss (Fin n)

/-! ## The four parts in `L²` -/

/-- The remainder of `κ` after its tangent at `q`, at the cosine of the two points. -/
lemma remK_L2 (hn : 1 ≤ n) (β τ : ℝ) {q c4 : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 16 / 25)
    (c2 : L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => (cosS β τ w - q) ^ 2) c4) :
    L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
        kappa (cosS β τ w) - kappa q - kg q * (cosS β τ w - q)) (25 / 36 * c4) := by
  have c3 := c2.const_mul_nonneg (by norm_num : (0 : ℝ) ≤ 25 / 36)
  refine L2le.of_abs_le ?_ c3 fun w => ?_
  · exact (((continuous_kappa.measurable.comp (measurable_cheapDot β τ)).sub
      measurable_const).sub
        (((measurable_cheapDot β τ).sub measurable_const).const_mul (kg q))).aestronglyMeasurable
  · have hs := abs_cheapDot_mem hn β τ w
    have h0 := kappa_tangent_ge hs (ρ₀ := q) ⟨by linarith, by linarith⟩
    have h1 := kappa_quad_gen hq0 hq hs
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by positivity)]
    linarith

lemma kern1_alg (cc d ks kq g s q r p : ℝ) (hr : r = ks - kq - g * (s - q)) :
    cc - d * ks + d * g * (s - q) + d * r + kq * (d - p) = cc - kq * p := by
  rw [hr]
  ring

/-- **The first-layer kernel against `κ(q)·|a||a′|`**, in `L²` over the three Gaussian vectors
and `A₁`. -/
lemma kern1_L2 (hn : 1 ≤ n) (hm : 1 ≤ m) (β τ : ℝ) {q c1 c4 : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 16 / 25) (hkg : kg q ≤ 17 / 25) (hc1 : 0 ≤ c1) (hc4 : 0 ≤ c4)
    (c0 : L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => cosS β τ w - q) c1)
    (c2 : L2le ((G1).prod ((G1).prod G1))
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => (cosS β τ w - q) ^ 2) c4) :
    L2le (((G1).prod ((G1).prod G1)).prod (gaussMat m n (2 / (n : ℝ))))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × Matrix (Fin m) (Fin n) ℝ =>
        dotp (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1))))
            (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2)))) -
          kappa q * (nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))) *
            nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2))))))
      ((m : ℝ) / n * (√(6 / (m : ℝ)) + (17 / 25 * c1 + 25 / 36 * c4) + 2 * √(5 / (m : ℝ)))) := by
  have hd : (0 : ℝ) ≤ (m : ℝ) / n := by positivity
  have hg0 := kg_nonneg q
  have hkq := kappa_mem (t := q) (by linarith) (by linarith)
  obtain ⟨mA', mB'⟩ := measurable_cheapPt (n := n) β τ
  have uA : ∀ w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ),
      normSq (sphPt (β • w.1 + τ • w.2.1)) = 1 := fun _ => normSq_sphPt hn _
  have uB : ∀ w : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ),
      normSq (sphPt (β • w.1 + τ • w.2.2)) = 1 := fun _ => normSq_sphPt hn _
  have p1 := lay1K_L2 (m := m) ((G1).prod ((G1).prod G1)) hn hm mA' mB' uA uB
  have p2 : L2le (((G1).prod ((G1).prod G1)).prod (gaussMat m n (2 / (n : ℝ))))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × Matrix (Fin m) (Fin n) ℝ =>
        (m : ℝ) / n * kg q * (cosS β τ z.1 - q)) ((m : ℝ) / n * (17 / 25 * c1)) :=
    ((c0.comp_fst (ν := gaussMat m n (2 / (n : ℝ)))).const_mul_nonneg (mul_nonneg hd hg0)).mono
      (mul_nonneg (mul_nonneg hd hg0) hc1) (by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkg hc1) hd
        linarith)
  have p3 : L2le (((G1).prod ((G1).prod G1)).prod (gaussMat m n (2 / (n : ℝ))))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × Matrix (Fin m) (Fin n) ℝ =>
        (m : ℝ) / n * (kappa (cosS β τ z.1) - kappa q - kg q * (cosS β τ z.1 - q)))
      ((m : ℝ) / n * (25 / 36 * c4)) :=
    ((remK_L2 hn β τ hq0 hq c2).comp_fst (ν := gaussMat m n (2 / (n : ℝ)))).const_mul_nonneg hd
  have dA := lay1D_L2 (m := m) ((G1).prod ((G1).prod G1)) hn hm mA' uA
  have dB := lay1D_L2 (m := m) ((G1).prod ((G1).prod G1)) hn hm mB' uB
  have hs5 : 0 ≤ (m : ℝ) / n * √(5 / (m : ℝ)) := mul_nonneg hd (Real.sqrt_nonneg _)
  have dAB := dA.abs.addR dB.abs hs5 hs5
  have mp4 : Measurable
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × Matrix (Fin m) (Fin n) ℝ =>
        kappa q * ((m : ℝ) / n - nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))) *
          nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2)))))) :=
    (measurable_const.sub
      ((continuous_nrm.measurable.comp (measurable_relu_mulVec mA')).mul
        (continuous_nrm.measurable.comp (measurable_relu_mulVec mB')))).const_mul _
  have p4 : L2le (((G1).prod ((G1).prod G1)).prod (gaussMat m n (2 / (n : ℝ))))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × Matrix (Fin m) (Fin n) ℝ =>
        kappa q * ((m : ℝ) / n - nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))) *
          nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2))))))
      ((m : ℝ) / n * √(5 / (m : ℝ)) + (m : ℝ) / n * √(5 / (m : ℝ))) := by
    refine L2le.of_abs_le mp4.aestronglyMeasurable dAB fun z => ?_
    have h := abs_sub_mul_le
      (nrm_nonneg (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))))
      (nrm_nonneg (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2))))) hd
    rw [nrm_sq, nrm_sq] at h
    refine le_trans ?_ (le_abs_self _)
    rw [abs_mul, abs_of_nonneg hkq.1]
    calc kappa q * |(m : ℝ) / n - nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))) *
          nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2))))|
        ≤ 1 * |(m : ℝ) / n - nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))) *
          nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2))))| :=
          mul_le_mul_of_nonneg_right hkq.2 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h
  have h6 : 0 ≤ (m : ℝ) / n * √(6 / (m : ℝ)) := mul_nonneg hd (Real.sqrt_nonneg _)
  have h17 : 0 ≤ (m : ℝ) / n * (17 / 25 * c1) := mul_nonneg hd (by positivity)
  have h25 : 0 ≤ (m : ℝ) / n * (25 / 36 * c4) := mul_nonneg hd (by positivity)
  have key := ((p1.add' p2 h6 h17).add' p3 (add_nonneg h6 h17) h25).add' p4
    (add_nonneg (add_nonneg h6 h17) h25) (add_nonneg hs5 hs5)
  refine (key.congr_fun fun z => ?_).congr_bound (by ring)
  exact kern1_alg _ _ _ _ _ _ _ _ _ (by ring)

/-! ## Joint measurability -/

/-- The first hidden vector is jointly measurable in the centre, the scalar, the matrix and the
Gaussian vector. -/
lemma measurable_a1_jointL :
    Measurable (fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) × (Fin n → ℝ) =>
      a1 z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have h1 : Measurable (fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) × (Fin n → ℝ) =>
      z.1.1.1 + z.1.1.2 • z.2) :=
    (by fun_prop : Continuous fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) ×
      (Fin n → ℝ) => z.1.1.1 + z.1.1.2 • z.2).measurable
  have h := (measurable_reluV (ι := Fin m)).comp
    ((measurable_mulVec_joint (n := m) (m := n)).comp
      ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp h1)))
  simp only [Function.comp_def] at h
  exact h

lemma measurable_Qk {n m : ℕ} :
    Measurable (fun x : (ℝ × (Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ =>
      Qk x.1.1 x.1.2.1 x.1.2.2 x.2) := by
  have e1 : Measurable (fun z : ((ℝ × (Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) ×
      ((Fin n → ℝ) × (Fin n → ℝ)) => a1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.1) :=
    measurable_a1_jointL.comp
      ((((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)).comp
        (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)
        |>.prodMk (measurable_fst.comp measurable_snd))
  have e2 : Measurable (fun z : ((ℝ × (Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) ×
      ((Fin n → ℝ) × (Fin n → ℝ)) => a1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.2) :=
    measurable_a1_jointL.comp
      ((((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)).comp
        (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)
        |>.prodMk (measurable_snd.comp measurable_snd))
  have mf : Measurable (fun z : ((ℝ × (Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) ×
      ((Fin n → ℝ) × (Fin n → ℝ)) =>
      (dotp (a1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.1) (a1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.2) -
        z.1.1.1 * (nrm (a1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.1) *
          nrm (a1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2.2))) ^ 2) :=
    ((continuous_dotp.measurable.comp (e1.prodMk e2)).sub
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).mul
        ((continuous_nrm.measurable.comp e1).mul (continuous_nrm.measurable.comp e2)))).pow_const 2
  exact (mf.stronglyMeasurable.integral_prod_right'
    (ν := (stdGauss (Fin n)).prod (stdGauss (Fin n)))).measurable

lemma measurable_errD1 {n m : ℕ} :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ =>
      errD1 x.1.1 x.1.2 x.2) := by
  have mf : Measurable (fun z : (((Fin n → ℝ) × ℝ) × Matrix (Fin m) (Fin n) ℝ) × (Fin n → ℝ) =>
      (normSq (a1 z.1.1.1 z.1.1.2 z.1.2 z.2) - (m : ℝ) / n) ^ 2) :=
    ((continuous_normSq.measurable.comp measurable_a1_jointL).sub measurable_const).pow_const 2
  exact (mf.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

/-! ## The diagonal -/

/-- **The mean of the diagonal error of the first hidden layer**, for every centre `c` and every
scalar `τ`. -/
theorem errD1_mean {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) :
    ∫⁻ A₁, ENNReal.ofReal (errD1 c τ A₁) ∂gaussMat m n (2 / (n : ℝ)) ≤
      ENNReal.ofReal (((m : ℝ) / n) ^ 2 * (5 / (m : ℝ))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have mX : Measurable (fun γ : Fin n → ℝ => sphPt (c + τ • γ)) :=
    measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul τ))
  have g := lay1D_L2 (m := m) (stdGauss (Fin n)) hn hm mX (fun _ => normSq_sphPt hn _)
  obtain ⟨G, hG⟩ : ∃ G : (Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ → ENNReal,
      G = fun z => ENNReal.ofReal
        ((normSq (reluV (z.2.mulVec (sphPt (c + τ • z.1)))) - (m : ℝ) / n) ^ 2) := ⟨_, rfl⟩
  have mG : Measurable G := by
    rw [hG]
    exact (((continuous_normSq.measurable.comp (measurable_relu_mulVec mX)).sub
      measurable_const).pow_const 2).ennreal_ofReal
  have step : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ,
      ENNReal.ofReal (errD1 c τ A₁) ≤ ∫⁻ γ, G (γ, A₁) ∂stdGauss (Fin n) := by
    intro A₁
    rw [hG]
    exact ofReal_integral_le _ _ fun _ => sq_nonneg _
  calc ∫⁻ A₁, ENNReal.ofReal (errD1 c τ A₁) ∂gaussMat m n (2 / (n : ℝ))
      ≤ ∫⁻ A₁, ∫⁻ γ, G (γ, A₁) ∂stdGauss (Fin n) ∂gaussMat m n (2 / (n : ℝ)) :=
        lintegral_mono step
    _ = ∫⁻ γ, ∫⁻ A₁, G (γ, A₁) ∂gaussMat m n (2 / (n : ℝ)) ∂stdGauss (Fin n) :=
        lintegral_lintegral_swap
          (f := fun (A₁ : Matrix (Fin m) (Fin n) ℝ) (γ : Fin n → ℝ) => G (γ, A₁))
          (mG.comp measurable_swap).aemeasurable
    _ = ∫⁻ z, G z ∂((stdGauss (Fin n)).prod (gaussMat m n (2 / (n : ℝ)))) :=
        (lintegral_prod _ mG.aemeasurable).symm
    _ = ENNReal.ofReal (∫ z : (Fin n → ℝ) × Matrix (Fin m) (Fin n) ℝ,
          (normSq (reluV (z.2.mulVec (sphPt (c + τ • z.1)))) - (m : ℝ) / n) ^ 2
          ∂((stdGauss (Fin n)).prod (gaussMat m n (2 / (n : ℝ))))) := by
        rw [hG]
        exact (ofReal_integral_eq_lintegral_ofReal g.int_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (((m : ℝ) / n * √(5 / (m : ℝ))) ^ 2) := ENNReal.ofReal_le_ofReal g.le
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]

/-! ## The kernel -/

/-- The passage from an `L²` bound to the mean of `Qk`. -/
lemma Qk_of_L2 {β τ k B : ℝ}
    (g : L2le (((G1).prod ((G1).prod G1)).prod (gaussMat m n (2 / (n : ℝ))))
      (fun z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × Matrix (Fin m) (Fin n) ℝ =>
        dotp (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1))))
            (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2)))) -
          k * (nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))) *
            nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2)))))) B) :
    ∫⁻ ξ, (∫⁻ A₁, ENNReal.ofReal (Qk k (β • ξ) τ A₁) ∂gaussMat m n (2 / (n : ℝ))) ∂G1 ≤
      ENNReal.ofReal (B ^ 2) := by
  obtain ⟨G, hG⟩ : ∃ G : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) × Matrix (Fin m) (Fin n) ℝ →
      ENNReal, G = fun z => ENNReal.ofReal
        ((dotp (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1))))
            (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2)))) -
          k * (nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))) *
            nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2)))))) ^ 2) := ⟨_, rfl⟩
  obtain ⟨mA', mB'⟩ := measurable_cheapPt (n := n) β τ
  have mG : Measurable G := by
    rw [hG]
    have m1 := measurable_relu_mulVec (m := m) mA'
    have m2 := measurable_relu_mulVec (m := m) mB'
    exact (((continuous_dotp.measurable.comp (m1.prodMk m2)).sub
      (((continuous_nrm.measurable.comp m1).mul
        (continuous_nrm.measurable.comp m2)).const_mul k)).pow_const 2).ennreal_ofReal
  have step : ∀ ξ : Fin n → ℝ, ∀ A₁ : Matrix (Fin m) (Fin n) ℝ,
      ENNReal.ofReal (Qk k (β • ξ) τ A₁) ≤ ∫⁻ p, G ((ξ, p), A₁) ∂((G1).prod G1) := by
    intro ξ A₁
    rw [hG]
    exact ofReal_integral_le _ _ fun _ => sq_nonneg _
  calc ∫⁻ ξ, (∫⁻ A₁, ENNReal.ofReal (Qk k (β • ξ) τ A₁) ∂gaussMat m n (2 / (n : ℝ))) ∂G1
      ≤ ∫⁻ ξ, (∫⁻ A₁, ∫⁻ p, G ((ξ, p), A₁) ∂((G1).prod G1) ∂gaussMat m n (2 / (n : ℝ))) ∂G1 :=
        lintegral_mono fun ξ => lintegral_mono fun A₁ => step ξ A₁
    _ = ∫⁻ ξ, (∫⁻ p, ∫⁻ A₁, G ((ξ, p), A₁) ∂gaussMat m n (2 / (n : ℝ)) ∂((G1).prod G1)) ∂G1 := by
        refine lintegral_congr fun ξ => ?_
        exact lintegral_lintegral_swap
          (f := fun (A₁ : Matrix (Fin m) (Fin n) ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) =>
            G ((ξ, p), A₁))
          (mG.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aemeasurable
    _ = ∫⁻ w, (∫⁻ A₁, G (w, A₁) ∂gaussMat m n (2 / (n : ℝ))) ∂((G1).prod ((G1).prod G1)) :=
        (lintegral_prod (fun w => ∫⁻ A₁, G (w, A₁) ∂gaussMat m n (2 / (n : ℝ)))
          mG.lintegral_prod_right'.aemeasurable).symm
    _ = ∫⁻ z, G z ∂(((G1).prod ((G1).prod G1)).prod (gaussMat m n (2 / (n : ℝ)))) :=
        (lintegral_prod _ mG.aemeasurable).symm
    _ = ENNReal.ofReal (∫ z : ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) ×
            Matrix (Fin m) (Fin n) ℝ,
          (dotp (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1))))
            (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2)))) -
          k * (nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.1)))) *
            nrm (reluV (z.2.mulVec (sphPt (β • z.1.1 + τ • z.1.2.2)))))) ^ 2
          ∂(((G1).prod ((G1).prod G1)).prod (gaussMat m n (2 / (n : ℝ))))) := by
        rw [hG]
        exact (ofReal_integral_eq_lintegral_ofReal g.int_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal g.le

/-- The bound of the first-layer kernel error. -/
noncomputable def dQ1 (n m : ℕ) (q : ℝ) : ℝ :=
  √(6 / (m : ℝ)) + (17 / 25 * ((1 - q ^ 2) / √(n : ℝ) + jCosC n) + 25 / 36 * m4c n q) +
    2 * √(5 / (m : ℝ))

/-- `kg q ≤ 17/25` for `q ≤ 527/1000`. -/
lemma kg_window {q : ℝ} (hq2 : q ≤ 527 / 1000) : kg q ≤ 17 / 25 := by
  have h := kg_le_of (t := q) (a := 527 / 1000) (c := 18 / 100) hq2 (by norm_num) (by norm_num)
    (by norm_num)
  linarith

/-- **The mean of the first-layer kernel error against `κ(q)·|a||a′|`**; `q = β²/(β² + τ²)` in
the window. -/
theorem Qk_mean (hn : 1 ≤ n) (hm : 1 ≤ m) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ)
    (hq1 : 462 / 1000 ≤ β ^ 2 / (β ^ 2 + τ ^ 2)) (hq2 : β ^ 2 / (β ^ 2 + τ ^ 2) ≤ 527 / 1000) :
    ∫⁻ ξ, (∫⁻ A₁, ENNReal.ofReal (Qk (kappa (β ^ 2 / (β ^ 2 + τ ^ 2))) (β • ξ) τ A₁)
        ∂gaussMat m n (2 / (n : ℝ))) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (((m : ℝ) / n * dQ1 n m (β ^ 2 / (β ^ 2 + τ ^ 2))) ^ 2) := by
  have hc1 : 0 ≤ (1 - (β ^ 2 / (β ^ 2 + τ ^ 2)) ^ 2) / √(n : ℝ) + jCosC n :=
    add_nonneg (div_nonneg (window_nonneg hq1 hq2).1 (Real.sqrt_nonneg _)) (jCosC_nonneg n)
  have hc4 : 0 ≤ m4c n (β ^ 2 / (β ^ 2 + τ ^ 2)) := Real.sqrt_nonneg _
  have key := kern1_L2 (m := m) hn hm β τ (by linarith) (by linarith) (kg_window hq2) hc1 hc4
    (cheapCos_L2 hn hβ hτ) (cheapCos_M4 hn hβ hτ)
  unfold dQ1
  exact Qk_of_L2 key

/-! ## The numbers for `n ≥ 4096` and `m = mA n` -/

/-- **`dQ1 n (mA n) q ≤ 0.534859/√n + 12.51/n`** for `n ≥ 4096` and `q` in the window. -/
theorem dQ1_le {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq1 : 462 / 1000 ≤ q) (hq2 : q ≤ 527 / 1000) :
    dQ1 n (mA n) q ≤ 534859 / 1000000 / √(n : ℝ) + 12510 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, hy, hz, hy0, hz0, hyz, hc, hj⟩ := num_basic hn
  have h4 := m4c_window hn hq1 hq2
  rw [← hy] at h4
  have h1 : (1 - q ^ 2) / √(n : ℝ) ≤ 786556 / 1000000 * z := by
    rw [hz, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have h6 : √(6 / (mA n : ℝ)) ≤ 24495 / 10000 * y := by
    refine sqrt_le_of_sq (by positivity) ?_
    have e : 6 / (mA n : ℝ) = 6 * y ^ 2 := by rw [mA_eqR, hy]; ring
    rw [e]
    nlinarith [sq_nonneg y]
  have h5 : √(5 / (mA n : ℝ)) ≤ 223607 / 100000 * y := by
    refine sqrt_le_of_sq (by positivity) ?_
    have e : 5 / (mA n : ℝ) = 5 * y ^ 2 := by rw [mA_eqR, hy]; ring
    rw [e]
    nlinarith [sq_nonneg y]
  have e : 534859 / 1000000 / √(n : ℝ) + 12510 / 1000 / (n : ℝ) =
      534859 / 1000000 * z + 12510 / 1000 * y := by rw [hy, hz]; ring
  unfold dQ1
  rw [e]
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms errD1_mean
open BstLean.Part149 in
#print axioms Qk_mean
open BstLean.Part149 in
#print axioms measurable_Qk
open BstLean.Part149 in
#print axioms measurable_errD1
open BstLean.Part149 in
#print axioms dQ1_le
