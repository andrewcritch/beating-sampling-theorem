import BstLean.Part109Defs

/-!
# Part 109: the error of the linear part is a centred Gaussian variable in `A₁` (Lemma V)

* `linErrTail109 : LinTail109 → LinErrTail109`
* `vtotLe109 : VtotLe109`

For fixed `W`, `τ`, `ℓ`, blocks `ω`: `qLin A ℓ x = Σ_c A c · fe ℓ c x` with the feature
`fe ℓ c x = ℓ_a · x^α` (`c = (a, α)`), so `g − B`, `g − ∫ φ dν`, `∫ φ dν − ∫ φ dμ` are linear
functionals `Σ_c A c · D c` of `A`. Under `bwGauss n n dA 1` the second moment of such a functional
is `Σ_c (D c / √w_c)²`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part109

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105
open BstLean.Part107 (qLin)
open BstLean.Part108

section gauss

variable {ι : Type*} [Fintype ι]

lemma le_g_pair [DecidableEq ι] (i j : ι) :
    ∫ z, z i * z j ∂stdGauss ι = if i = j then 1 else 0 := by
  have hw := BstLean.Part35.stdGauss_wick_step i 1 (fun _ : Fin 1 => j)
  simpa [eq_comm] using hw

lemma le_g_pair_int (i j : ι) : Integrable (fun z : ι → ℝ => z i * z j) (stdGauss ι) := by
  have h := BstLean.Part48.gauss_poly_integrable
    (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial ι ℝ)
  simp only [map_mul, MvPolynomial.eval_X] at h
  exact h

/-- `E (d·ξ)² = |d|²`. -/
lemma le_lin_sq (d : ι → ℝ) : ∫ ξ, (∑ c, d c * ξ c) ^ 2 ∂stdGauss ι = ∑ c, d c ^ 2 := by
  classical
  have e : ∀ ξ : ι → ℝ, (∑ c, d c * ξ c) ^ 2 = ∑ c, ∑ c', (d c * d c') * (ξ c * ξ c') := by
    intro ξ
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ =>
    (le_g_pair_int c c').const_mul _]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun c' _ => (le_g_pair_int c c').const_mul _]
  simp only [integral_const_mul, le_g_pair]
  simp [sq]

/-- The Euclidean triangle inequality. -/
lemma le_tri (a b : ι → ℝ) :
    Real.sqrt (∑ c, (a c + b c) ^ 2) ≤ Real.sqrt (∑ c, a c ^ 2) + Real.sqrt (∑ c, b c ^ 2) := by
  have ha : 0 ≤ ∑ c, a c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ ∑ c, b c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  rw [Real.sqrt_le_left (by positivity)]
  have e : ∑ c, (a c + b c) ^ 2 = ∑ c, a c ^ 2 + 2 * ∑ c, a c * b c + ∑ c, b c ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e, add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith

end gauss

section feat

variable {N n dW dA k : ℕ}

/-- The feature of the coefficient `c = (a, α)`: `ℓ_a · x^α`. -/
noncomputable def fe (ℓ : Fin n → ℝ) (c : CoefIdx n n dA) (x : Fin n → ℝ) : ℝ :=
  ℓ c.1 * monoVal x c.2

lemma qLin_fe (A : CoefIdx n n dA → ℝ) (ℓ x : Fin n → ℝ) :
    qLin A ℓ x = ∑ c, A c * fe ℓ c x := by
  unfold qLin dot bwEval fe
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma continuous_fe (ℓ : Fin n → ℝ) (c : CoefIdx n n dA) : Continuous (fe ℓ c) := by
  unfold fe
  exact continuous_const.mul (BstLean.Part106.continuous_monoVal c.2)

/-- Integrals of the linear part along a map into the closed unit ball are linear in `A`. -/
lemma int_lin {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (g : α → Fin n → ℝ) (hg : Measurable g) (hb : ∀ a, ∑ i, g a i ^ 2 ≤ 1)
    (A : CoefIdx n n dA → ℝ) (ℓ : Fin n → ℝ) :
    ∫ a, qLin A ℓ (g a) ∂P = ∑ c, A c * ∫ a, fe ℓ c (g a) ∂P := by
  have hi : ∀ c : CoefIdx n n dA, Integrable (fun a => fe ℓ c (g a)) P := by
    intro c
    obtain ⟨M, hM⟩ := cont_bdd_ball (fe ℓ c) (continuous_fe ℓ c)
    exact Integrable.mono' (integrable_const M)
      ((continuous_fe ℓ c).measurable.comp hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by simpa using hM (g a) (hb a))
  simp_rw [qLin_fe]
  rw [integral_finsetSum _ fun c _ => (hi c).const_mul _]
  simp only [integral_const_mul]

/-- The second moment under `bwGauss` of a linear functional of the coefficients. -/
lemma second (D : CoefIdx n n dA → ℝ) :
    ∫ A, (∑ c, A c * D c) ^ 2 ∂bwGauss n n dA 1 =
      ∑ c, (D c / Real.sqrt (bwWeight c.2)) ^ 2 := by
  have hm : Measurable (fun A : CoefIdx n n dA → ℝ => (∑ c, A c * D c) ^ 2) := by fun_prop
  rw [bwGauss_integral 1 _ hm, ← le_lin_sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [bwOfCoord, one_smul]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The tail under `bwGauss` of a linear functional of the coefficients. -/
lemma tailLin (h : LinTail109) (D : CoefIdx n n dA → ℝ) (V t : ℝ) (ht : 0 ≤ t)
    (hV : V = ∑ c, (D c / Real.sqrt (bwWeight c.2)) ^ 2) :
    (bwGauss n n dA 1).real {A | t * Real.sqrt V < |∑ c, A c * D c|} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  have hS : MeasurableSet {A : CoefIdx n n dA → ℝ | t * Real.sqrt V < |∑ c, A c * D c|} :=
    measurableSet_lt measurable_const (by fun_prop)
  unfold bwGauss
  rw [map_measureReal_apply (measurable_bwGaussMap 1) hS]
  refine le_trans (le_of_eq ?_)
    (h (CoefIdx n n dA) (fun c => D c / Real.sqrt (bwWeight c.2)) t ht)
  congr 1
  ext ξ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, bwOfCoord, one_smul, hV]
  have e : ∑ c, ξ c / Real.sqrt (bwWeight c.2) * D c =
      ∑ c, D c / Real.sqrt (bwWeight c.2) * ξ c :=
    Finset.sum_congr rfl fun c _ => by ring
  rw [e]

variable (W : CoefIdx N n dW → ℝ) (τ : ℝ) (ℓ : Fin n → ℝ) (ω : Draws N n k)

/-- The sample mean of a feature. -/
noncomputable def gS (dA : ℕ) (c : CoefIdx n n dA) : ℝ :=
  (∑ i, fe ℓ c (BstLean.Part106.standIn W τ (ω i))) / (k : ℝ)

/-- The mean of a feature under the stand-in. -/
noncomputable def bN (dA : ℕ) (c : CoefIdx n n dA) : ℝ :=
  ∫ p, fe ℓ c (BstLean.Part106.standIn W τ p) ∂((uniformSphere N).prod (stdGauss (Fin n)))

/-- The mean of a feature under `μ_W`. -/
noncomputable def bM (dA : ℕ) (c : CoefIdx n n dA) : ℝ :=
  ∫ u, fe ℓ c (sphProj (bwEval W u)) ∂uniformSphere N

lemma gVal_lin (A : CoefIdx n n dA → ℝ) :
    BstLean.Part106.gVal W τ (fun y => qLin A ℓ y) ω = ∑ c, A c * gS W τ ℓ ω dA c := by
  unfold BstLean.Part106.gVal gS
  simp_rw [qLin_fe]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.mul_sum, mul_div_assoc]

lemma Bu_lin (hN : 1 ≤ N) (A : CoefIdx n n dA → ℝ) :
    Bu W (fun y => qLin A ℓ y) = ∑ c, A c * bM W ℓ dA c := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  unfold Bu bM
  exact int_lin (uniformSphere N) (fun u => sphProj (bwEval W u)) (measurable_muMap W)
    (fun u => BstLean.Part106.sphProj_sq_le _) A ℓ

lemma Bnu_lin (hN : 1 ≤ N) (A : CoefIdx n n dA → ℝ) :
    Bnu W τ (fun y => qLin A ℓ y) = ∑ c, A c * bN W τ ℓ dA c := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  unfold Bnu bN
  exact int_lin ((uniformSphere N).prod (stdGauss (Fin n))) (BstLean.Part106.standIn W τ)
    (BstLean.Part106.measurable_standIn W τ) (fun p => BstLean.Part106.sphProj_sq_le _) A ℓ

lemma Vtot_eq (hN : 1 ≤ N) :
    Vtot dA W τ ℓ ω =
      ∑ c, ((gS W τ ℓ ω dA c - bM W ℓ dA c) / Real.sqrt (bwWeight c.2)) ^ 2 := by
  unfold Vtot Err
  rw [← second]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  simp only [gVal_lin, Bu_lin W ℓ hN, ← Finset.sum_sub_distrib, mul_sub]

lemma Vsamp_eq (hN : 1 ≤ N) :
    Vsamp dA W τ ℓ ω =
      ∑ c, ((gS W τ ℓ ω dA c - bN W τ ℓ dA c) / Real.sqrt (bwWeight c.2)) ^ 2 := by
  unfold Vsamp
  rw [← second]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  simp only [gVal_lin, Bnu_lin W τ ℓ hN, ← Finset.sum_sub_distrib, mul_sub]

lemma VWd_eq (hN : 1 ≤ N) :
    VWd dA W τ ℓ =
      ∑ c, ((bN W τ ℓ dA c - bM W ℓ dA c) / Real.sqrt (bwWeight c.2)) ^ 2 := by
  unfold VWd
  rw [← second]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  simp only [Bnu_lin W τ ℓ hN, Bu_lin W ℓ hN, ← Finset.sum_sub_distrib, mul_sub]

end feat

/-- **Lemma V**: the tail of the error of the linear part over `A₁`. -/
theorem linErrTail109 (h : LinTail109) : LinErrTail109 := by
  intro N n dW dA k hN _ W τ ℓ ω t ht
  have e : {A : CoefIdx n n dA → ℝ | t * Real.sqrt (Vtot dA W τ ℓ ω) <
        |Err W τ (fun y => qLin A ℓ y) ω|} =
      {A | t * Real.sqrt (Vtot dA W τ ℓ ω) <
        |∑ c, A c * (gS W τ ℓ ω dA c - bM W ℓ dA c)|} := by
    ext A
    simp only [Set.mem_ofPred_eq, Err, gVal_lin, Bu_lin W ℓ hN, ← Finset.sum_sub_distrib, mul_sub]
  rw [e]
  exact tailLin h _ _ t ht (Vtot_eq W τ ℓ ω hN)

/-- `√Vtot ≤ √Vsamp + √V_W`. -/
theorem vtotLe109 : VtotLe109 := by
  intro N n dW dA k hN _ W τ ℓ ω
  rw [Vtot_eq W τ ℓ ω hN, Vsamp_eq W τ ℓ ω hN, VWd_eq W τ ℓ hN]
  refine le_trans (le_of_eq ?_) (le_tri _ _)
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring

end BstLean.Part109

#print axioms BstLean.Part109.linErrTail109
#print axioms BstLean.Part109.vtotLe109
