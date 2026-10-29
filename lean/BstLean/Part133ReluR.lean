import BstLean.Part133Relu
import BstLean.Part133LinR

/-!
# Part 133, refined links: the orthogonality of link `F`, and the refined last matrix of `A`

Role: `delegations/statements/p133-spec.md`, item 3. Paper source: `onW4c-cx.md` §4 ("Link F":
the residual of `F_2` has conditional mean zero, so the two `F` errors add in squares; "Link
`A_3`": the constant `1 + √2·q`).

* `L2le.prod_orth`: `‖R + B‖₂² ≤ a² + b²` if `R` has conditional mean zero given the first
  coordinate and `B` reads the first coordinate only.
* `hid2_dot_L2o`, `KF_L2o` (constant `cF2o`): the two hidden layers with the sum of squares.
* `mlp_psi_L2r` (constant `cAr`): a whole network with `lin_layer_L2s` for the last matrix.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131 BstLean.Part132


/-! ## Orthogonality -/

/-- **Sum of squares.** `R` has mean zero in the second coordinate for every value of the first,
with section `L²` norm at most `g`; `B` reads the first coordinate only. Then
`‖R + B‖₂ ≤ √(a² + b²)` with `‖g‖₂ ≤ a`, `‖B‖₂ ≤ b`. -/
theorem L2le.prod_orth {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν] {R : α × β → ℝ} {B g : α → ℝ} {a b : ℝ}
    (hR : AEStronglyMeasurable R (μ.prod ν)) (hB : L2le μ B b) (hg : L2le μ g a)
    (h : ∀ x, Integrable (fun y => R (x, y)) ν ∧ ∫ y, R (x, y) ∂ν = 0 ∧
      Integrable (fun y => R (x, y) ^ 2) ν ∧ ∫ y, R (x, y) ^ 2 ∂ν ≤ g x ^ 2) :
    L2le (μ.prod ν) (fun z => R z + B z.1) (√(a ^ 2 + b ^ 2)) := by
  have hG : L2le μ (fun x => √(g x ^ 2 + B x ^ 2)) (√(a ^ 2 + b ^ 2)) := by
    refine L2le.of_sq_le (G := fun x => g x ^ 2 + B x ^ 2)
      (Real.continuous_sqrt.comp_aestronglyMeasurable ((hg.aesm.pow 2).add (hB.aesm.pow 2)))
      (hg.int_sq.add hB.int_sq) (fun x => le_of_eq (Real.sq_sqrt (by positivity))) ?_
    rw [integral_add hg.int_sq hB.int_sq, Real.sq_sqrt (by positivity)]
    exact add_le_add hg.le hB.le
  refine L2le.prod (hR.add hB.comp_fst.aesm) hG (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨i1, e1, i2, u2⟩ := h x
  have e : (fun y => (R (x, y) + B x) ^ 2) =
      fun y => R (x, y) ^ 2 + (2 * B x * R (x, y) + B x ^ 2) := by
    funext y; ring
  have i3 : Integrable (fun y => 2 * B x * R (x, y) + B x ^ 2) ν :=
    (i1.const_mul _).add (integrable_const _)
  refine ⟨by rw [e]; exact i2.add i3, ?_⟩
  simp only [e]
  rw [integral_add i2 i3, integral_add (i1.const_mul _) (integrable_const _), integral_const_mul,
    e1, Real.sq_sqrt (by positivity)]
  simp
  linarith

variable {m k m₁ m₂ q : ℕ}

/-- **The two hidden layers in `L²`, with the sum of squares** (link `F` of the paper). -/
theorem hid2_dot_L2o {v₁ v₂ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (y y' : Fin k → ℝ) :
    L2le ((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂))
      (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
        dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
          (m₂ : ℝ) / 2 * v₂ * ((m₁ : ℝ) / 2 * v₁ * psi (kappa ∘ kappa) y y'))
      (√(6 * (1 + 5 / (m₁ : ℝ)) / (m₂ : ℝ) + (5 * kappa 0 + √6) ^ 2 / (m₁ : ℝ)) *
        ((m₂ : ℝ) / 2 * v₂ * ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y')))) := by
  have hm₁' : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
  have hm₂' : (0 : ℝ) < m₂ := by exact_mod_cast hm₂
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have hc2 : 0 ≤ (m₂ : ℝ) / 2 * v₂ := by positivity
  have hnn := nrm_mul_nonneg y y'
  have mA : Measurable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
      dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') -
        (m₂ : ℝ) / 2 * v₂ * psi kappa (reluV (θ.1.mulVec y)) (reluV (θ.1.mulVec y'))) :=
    (continuous_dotp.comp ((continuous_hid2_param y).prodMk
      (continuous_hid2_param y'))).measurable.sub
      (((measurable_psi_relu continuous_kappa y y').comp measurable_fst).const_mul _)
  have hgA : L2le (gaussMat m₁ k v₁) (fun M₁ : Matrix (Fin m₁) (Fin k) ℝ =>
      √6 / √(m₂ : ℝ) * ((m₂ : ℝ) / 2 * v₂ *
        (nrm (reluV (M₁.mulVec y)) * nrm (reluV (M₁.mulVec y')))))
      (√6 / √(m₂ : ℝ) * ((m₂ : ℝ) / 2 * v₂ *
        (√(1 + 5 / (m₁ : ℝ)) * ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y'))))) :=
    ((relu_nrm_L2 (m := m₁) h₁ hm₁ y y').const_mul_nonneg hc2).const_mul_nonneg (by positivity)
  have hB : L2le (gaussMat m₁ k v₁)
      (fun M₁ : Matrix (Fin m₁) (Fin k) ℝ =>
        (m₂ : ℝ) / 2 * v₂ * (psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')) -
          (m₁ : ℝ) / 2 * v₁ * psi (kappa ∘ kappa) y y'))
      ((m₂ : ℝ) / 2 * v₂ * ((5 * kappa 0 + √6) / √(m₁ : ℝ) *
        ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y')))) :=
    (relu_layer_L2 (m := m₁) kGood_kappa h₁ hm₁ y y').const_mul_nonneg hc2
  have key := L2le.prod_orth (ν := gaussMat m₂ m₁ v₂) mA.aestronglyMeasurable hB hgA
    (fun M₁ => by
      obtain ⟨iD, eD⟩ := layer_dot_relu (m := m₂) h₂ (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))
      obtain ⟨iC, uC⟩ := layer_dot_relu_var (m := m₂) h₂ (reluV (M₁.mulVec y))
        (reluV (M₁.mulVec y'))
      have e : (m₂ : ℝ) / 2 * (v₂ * kernelPhi (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))) =
          (m₂ : ℝ) / 2 * v₂ * psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')) := by
        rw [kernelPhi_eq_psi]; ring
      rw [e] at iC uC eD
      have iR : Integrable (fun M₂ : Matrix (Fin m₂) (Fin m₁) ℝ =>
          dotp (reluV (M₂.mulVec (reluV (M₁.mulVec y)))) (reluV (M₂.mulVec (reluV (M₁.mulVec y')))) -
            (m₂ : ℝ) / 2 * v₂ * psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')))
          (gaussMat m₂ m₁ v₂) := iD.sub (integrable_const _)
      refine ⟨iR, ?_, iC, uC.trans (le_of_eq ?_)⟩
      · have := integral_sub iD (integrable_const ((m₂ : ℝ) / 2 * v₂ *
          psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))))
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
        rw [eD, sub_self] at this
        exact this
      · rw [mul_pow, div_pow, Real.sq_sqrt hm₂'.le, Real.sq_sqrt (by norm_num), mul_pow, mul_pow,
          mul_pow, nrm_sq, nrm_sq]
        field_simp
        ring)
  refine (key.congr_fun fun θ => ?_).congr_bound ?_
  · ring
  · set r : ℝ := (m₂ : ℝ) / 2 * v₂ * ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y')) with hr
    have hr0 : 0 ≤ r := by positivity
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 5 / (m₁ : ℝ) by positivity)
    have e : (√6 / √(m₂ : ℝ) * ((m₂ : ℝ) / 2 * v₂ *
        (√(1 + 5 / (m₁ : ℝ)) * ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y'))))) ^ 2 +
        ((m₂ : ℝ) / 2 * v₂ * ((5 * kappa 0 + √6) / √(m₁ : ℝ) *
          ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y')))) ^ 2 =
        (6 * (1 + 5 / (m₁ : ℝ)) / (m₂ : ℝ) + (5 * kappa 0 + √6) ^ 2 / (m₁ : ℝ)) * r ^ 2 := by
      have e1 : (√6 / √(m₂ : ℝ) * ((m₂ : ℝ) / 2 * v₂ *
          (√(1 + 5 / (m₁ : ℝ)) * ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y'))))) ^ 2 =
          (√6) ^ 2 / (√(m₂ : ℝ)) ^ 2 * (√(1 + 5 / (m₁ : ℝ))) ^ 2 * r ^ 2 := by
        rw [hr]; ring
      have e2 : ((m₂ : ℝ) / 2 * v₂ * ((5 * kappa 0 + √6) / √(m₁ : ℝ) *
          ((m₁ : ℝ) / 2 * v₁ * (nrm y * nrm y')))) ^ 2 =
          (5 * kappa 0 + √6) ^ 2 / (√(m₁ : ℝ)) ^ 2 * r ^ 2 := by
        rw [hr]; ring
      rw [e1, e2, hs, Real.sq_sqrt hm₂'.le, Real.sq_sqrt hm₁'.le, Real.sq_sqrt (by norm_num)]
      ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hr0]

variable {n mF : ℕ}

/-- The constant of the `F` links, with the sum of squares. -/
noncomputable def cF2o (mF : ℕ) : ℝ :=
  √(6 * (1 + 5 / (mF : ℝ)) / (mF : ℝ) + (5 * kappa 0 + √6) ^ 2 / (mF : ℝ))

/-- **The two hidden layers of `F` in `L²`, with the sum of squares.** -/
theorem KF_L2o (hn : 1 ≤ n) (hmF : 1 ≤ mF) (y y' : Fin n → ℝ) :
    L2le (mlpGauss n mF 1)
      (fun F : MlpParam n mF 1 => 2 / (mF : ℝ) * dotp (hid2 F.1 F.2.1 y) (hid2 F.1 F.2.1 y') -
        2 / (n : ℝ) * psi (kappa ∘ kappa) y y')
      (cF2o mF * (2 / (n : ℝ) * (nrm y * nrm y'))) := by
  have hmF' : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 := (hid2_dot_L2o (m₁ := mF) (m₂ := mF) (two_div_nonneg n) (two_div_nonneg mF) hmF hmF
    y y').const_mul_nonneg (show (0 : ℝ) ≤ 2 / (mF : ℝ) by positivity)
  have h1 := h0.comp_map (P := mlpGauss n mF 1)
    (φ := fun θ : MlpParam n mF 1 => (θ.1, θ.2.1)) (by fun_prop) (by unfold mlpGauss; exact map_drop3)
  refine (h1.congr_fun fun F => ?_).congr_bound ?_
  · field_simp
  · unfold cF2o
    field_simp

/-! ## A whole network, refined last matrix -/

/-- The last two matrices, for fixed first hidden vectors `g, g′`, in `L²`. -/
theorem tail_psi_L2r {G : ℝ → ℝ} (hG : KGood G) (hG0' : 3 / 10 ≤ G 0) {v₂ v₃ : ℝ} (h₂ : 0 ≤ v₂) (h₃ : 0 ≤ v₃)
    (hm₂ : 1 ≤ m₂) (hq : 1 ≤ q) (g g' : Fin m₁ → ℝ) :
    L2le ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))
      (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g'))) -
          (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂ * psi (G ∘ kappa) g g'))
      ((((1 + √2 * G 0) / √(q : ℝ) + 2 * K4 q * G 0 / (q : ℝ)) * √(1 + 5 / (m₂ : ℝ)) + (5 * G 0 + √6) / √(m₂ : ℝ)) *
        ((q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g')))) := by
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hK4 : 0 ≤ K4 q := Real.sqrt_nonneg _
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hc3 : 0 ≤ (q : ℝ) * v₃ := by positivity
  have hnn := nrm_mul_nonneg g g'
  have hmeas : Measurable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g')))) := by
    have c : ∀ g : Fin m₁ → ℝ, Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ ×
        Matrix (Fin q) (Fin m₂) ℝ => θ.2.mulVec (reluV (θ.1.mulVec g))) := fun g =>
      Continuous.matrix_mulVec continuous_snd
        (continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_const))
    exact Measurable.comp (g := fun p : (Fin q → ℝ) × (Fin q → ℝ) => psi G p.1 p.2)
      (f := fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        (θ.2.mulVec (reluV (θ.1.mulVec g)), θ.2.mulVec (reluV (θ.1.mulVec g'))))
      (measurable_psi hG.cont) ((c g).prodMk (c g')).measurable
  have mA : Measurable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g'))) -
        (q : ℝ) * v₃ * psi G (reluV (θ.1.mulVec g)) (reluV (θ.1.mulVec g'))) :=
    hmeas.sub (((measurable_psi_relu hG.cont g g').comp measurable_fst).const_mul _)
  have hgA : L2le (gaussMat m₂ m₁ v₂) (fun M₂ : Matrix (Fin m₂) (Fin m₁) ℝ =>
      ((1 + √2 * G 0) / √(q : ℝ) + 2 * K4 q * G 0 / (q : ℝ)) * ((q : ℝ) * v₃ *
        (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g')))))
      (((1 + √2 * G 0) / √(q : ℝ) + 2 * K4 q * G 0 / (q : ℝ)) * ((q : ℝ) * v₃ *
        (√(1 + 5 / (m₂ : ℝ)) * ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g'))))) :=
    ((relu_nrm_L2 (m := m₂) h₂ hm₂ g g').const_mul_nonneg hc3).const_mul_nonneg (by positivity)
  have hA : L2le ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))
      (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g'))) -
          (q : ℝ) * v₃ * psi G (reluV (θ.1.mulVec g)) (reluV (θ.1.mulVec g')))
      (((1 + √2 * G 0) / √(q : ℝ) + 2 * K4 q * G 0 / (q : ℝ)) * ((q : ℝ) * v₃ *
        (√(1 + 5 / (m₂ : ℝ)) * ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g'))))) :=
    L2le.prod' mA.aestronglyMeasurable hgA (Filter.Eventually.of_forall fun M₂ =>
      lin_layer_L2s (m := q) hG hG0' h₃ hq (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g'))
        (dotp_relu_nonneg _ _))
  have hB : L2le ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))
      (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        (q : ℝ) * v₃ * (psi G (reluV (θ.1.mulVec g)) (reluV (θ.1.mulVec g')) -
          (m₂ : ℝ) / 2 * v₂ * psi (G ∘ kappa) g g'))
      ((q : ℝ) * v₃ * ((5 * G 0 + √6) / √(m₂ : ℝ) *
        ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g')))) :=
    ((relu_layer_L2 (m := m₂) hG h₂ hm₂ g g').const_mul_nonneg hc3).comp_fst
  have hsum := hA.add0 hB (by positivity) (by positivity)
  refine (hsum.congr_fun fun θ => ?_).congr_bound ?_
  · ring
  · ring

/-- The constant of the links of a whole network, with the refined last matrix. -/
noncomputable def cAr (G : ℝ → ℝ) (m q : ℕ) : ℝ :=
  ((1 + √2 * G 0) / √(q : ℝ) + 2 * K4 q * G 0 / (q : ℝ)) * (1 + 5 / (m : ℝ)) +
    (5 * G 0 + √6) / √(m : ℝ) * √(1 + 5 / (m : ℝ)) + (5 + √6) / √(m : ℝ)

/-- **A whole random ReLU MLP in `L²`** (links `A_3`, `A_2`, `A_1`). -/
theorem mlp_psi_L2r {G : ℝ → ℝ} (hG : KGood G) (hG0' : 3 / 10 ≤ G 0) {m : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (z z' : Fin k → ℝ) :
    L2le (mlpGauss k m q)
      (fun θ : MlpParam k m q => psi G (mlpEval θ z) (mlpEval θ z') -
        2 * (q : ℝ) / k * psi (G ∘ kappa ∘ kappa) z z')
      (cAr G m q * (2 * (q : ℝ) / k * (nrm z * nrm z'))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hK4 : 0 ≤ K4 q := Real.sqrt_nonneg _
  have hGk := hG.comp_kappa
  have hGk0 : 0 ≤ (G ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have hGk1 : (G ∘ kappa) 0 ≤ 1 := hGk.le_one KGood.zero_mem
  have h1 : (0 : ℝ) ≤ 2 / (k : ℝ) := two_div_nonneg k
  have h2 : (0 : ℝ) ≤ 2 / (m : ℝ) := two_div_nonneg m
  have hnn := nrm_mul_nonneg z z'
  set K : ℝ := ((1 + √2 * G 0) / √(q : ℝ) + 2 * K4 q * G 0 / (q : ℝ)) * √(1 + 5 / (m : ℝ)) + (5 * G 0 + √6) / √(m : ℝ)
    with hK
  have hK0 : 0 ≤ K := by positivity
  set c3 : ℝ := (q : ℝ) * (2 / (m : ℝ)) with hc3
  set c2 : ℝ := (m : ℝ) / 2 * (2 / (m : ℝ)) with hc2
  have hc30 : 0 ≤ c3 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have mA : Measurable (fun θ : MlpParam k m q =>
      psi G (mlpEval θ z) (mlpEval θ z') -
        c3 * (c2 * psi (G ∘ kappa) (reluV (θ.1.mulVec z)) (reluV (θ.1.mulVec z')))) :=
    (measurable_psi_mlp hG.cont z z').sub
      ((((measurable_psi_relu hGk.cont z z').comp measurable_fst).const_mul _).const_mul _)
  have hgA : L2le (gaussMat m k (2 / (k : ℝ))) (fun M₁ : Matrix (Fin m) (Fin k) ℝ =>
      K * (c3 * (c2 * (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z'))))))
      (K * (c3 * (c2 * (√(1 + 5 / (m : ℝ)) *
        ((m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z')))))) :=
    (((relu_nrm_L2 (m := m) h1 hm z z').const_mul_nonneg hc20).const_mul_nonneg
      hc30).const_mul_nonneg hK0
  have hA : L2le (mlpGauss k m q) (fun θ : MlpParam k m q =>
      psi G (mlpEval θ z) (mlpEval θ z') -
        c3 * (c2 * psi (G ∘ kappa) (reluV (θ.1.mulVec z)) (reluV (θ.1.mulVec z'))))
      (K * (c3 * (c2 * (√(1 + 5 / (m : ℝ)) *
        ((m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z')))))) := by
    unfold mlpGauss at mA ⊢
    exact L2le.prod' mA.aestronglyMeasurable hgA (Filter.Eventually.of_forall fun M₁ =>
      tail_psi_L2r (m₂ := m) (q := q) hG hG0' h2 h2 hm hq (reluV (M₁.mulVec z))
        (reluV (M₁.mulVec z')))
  have hB0 : L2le (gaussMat m k (2 / (k : ℝ))) (fun M₁ : Matrix (Fin m) (Fin k) ℝ =>
      c3 * (c2 * (psi (G ∘ kappa) (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) -
        (m : ℝ) / 2 * (2 / (k : ℝ)) * psi ((G ∘ kappa) ∘ kappa) z z')))
      (c3 * (c2 * ((5 + √6) / √(m : ℝ) * ((m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z'))))) := by
    refine ((((relu_layer_L2 (m := m) hGk h1 hm z z').mono (by positivity) ?_).const_mul_nonneg
      hc20).const_mul_nonneg hc30)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    linarith
  have hB : L2le (mlpGauss k m q) (fun θ : MlpParam k m q =>
      c3 * (c2 * (psi (G ∘ kappa) (reluV (θ.1.mulVec z)) (reluV (θ.1.mulVec z')) -
        (m : ℝ) / 2 * (2 / (k : ℝ)) * psi ((G ∘ kappa) ∘ kappa) z z')))
      (c3 * (c2 * ((5 + √6) / √(m : ℝ) * ((m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z'))))) := by
    unfold mlpGauss
    exact hB0.comp_fst
  have hsum := hA.add0 hB (by positivity) (by positivity)
  have hc2e : c2 = 1 := by rw [hc2]; field_simp
  have hcomp : psi (G ∘ kappa ∘ kappa) z z' = psi ((G ∘ kappa) ∘ kappa) z z' := rfl
  refine (hsum.congr_fun fun θ => ?_).congr_bound ?_
  · rw [hcomp, hc2e, hc3]
    field_simp
    ring
  · unfold cAr
    rw [hK, hc2e, hc3]
    have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + 5 / (m : ℝ) by positivity)
    set s : ℝ := √(1 + 5 / (m : ℝ)) with hsd
    rw [← hs]
    field_simp

end BstLean.Part133

open BstLean.Part133 in
#print axioms L2le.prod_orth
open BstLean.Part133 in
#print axioms hid2_dot_L2o
open BstLean.Part133 in
#print axioms KF_L2o
open BstLean.Part133 in
#print axioms mlp_psi_L2r
