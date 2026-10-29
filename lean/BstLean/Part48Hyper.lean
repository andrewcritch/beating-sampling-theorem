import BstLean.Part48Defs
import BstLean.Part48Var

/-!
# Part 48, wave 1: a dimension-free fourth moment for Gaussian polynomials (omQ4 §3) — proved

Specification: `delegations/answers/p48-spec-opus.md`, §3 and §5.

Claim. For every degree `h` there is `K_h > 0` such that every real polynomial `P` of total degree
`≤ h` in independent standard Gaussians (any finite index type `ι`) has `E P⁴ ≤ K_h (E P²)²`.
`K_h` does not depend on `ι`. The proof gives `K_h = (16 D_h)^h` with an inexplicit `D_h ≥ 1`.

Route used (an Efron–Stein induction on the variables, in the style of `Part41Hyper.bonami_bound`;
no Hermite polynomials and no Wick formula).
1. Split one variable: `P(x, z) = Σ_{b ≤ s} x^b R_b(z)` (`splitQ`, `splitQ_eval`), `deg R_b ≤ s − b`.
   Put `A(z) = E_x P = Σ_b m_b R_b(z)` (`Apol`) and `B = P − A = Σ_{b ≥ 1} (x^b − m_b) R_b(z)`
   (`Bpol`, `decomp`). `E_x B = 0`, so `E[U(z)·B] = 0` for every polynomial `U` (`I_orth`).
2. `E P² = E A² + E B²` (`mom2`) and `E P⁴ = E A⁴ + 6 E A²B² + 4 E AB³ + E B⁴` (`mom4`).
3. `E A⁴ ≤ c^s (E A²)²` by induction (`deg A ≤ s`, one variable fewer).
4. `E B⁴ ≤ D c^{s−1} (E B²)²` (`B4_upper`, `B2_lower`): `(Σ_b u_b)⁴ ≤ (s+1)³ Σ_b u_b⁴`, the induction
   hypothesis for each `R_b` (`deg R_b ≤ s − 1`), and the 1-D Gram bound
   `E_x(Σ_{b=1}^s r_b (x^b − m_b))² ≥ λ_H Σ r_b²` (`pd1`, `pdH`: compactness of the unit sphere and
   `E q² > 0` for a nonzero polynomial `q`, `sq_int_pos`).
5. Cauchy–Schwarz (`poly_cs`, `cs_T2`, `cs_T3`) and `step_arith` close the step with `c = 16 D`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part48

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)

private lemma int_pow1 (b : ℕ) : Integrable (fun x : ℝ => x ^ b) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
    (μ := gaussianReal 0 1) (by simp) b

private lemma int_poly1 (p : Polynomial ℝ) : Integrable (fun x => p.eval x) (gaussianReal 0 1) := by
  rw [show (fun x => p.eval x) = fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i from
    funext fun x => Polynomial.eval_eq_sum_range x]
  exact integrable_finsetSum _ fun i _ => (int_pow1 i).const_mul _

/-- Gaussian moment `m_b = E x^b`. -/
private noncomputable def gm (b : ℕ) : ℝ := ∫ y, y ^ b ∂gaussianReal 0 1

/-- The polynomial `Σ_{i<H} v_i (X^{i+1} − m_{i+1})`. -/
private noncomputable def cpoly (H : ℕ) (v : Fin H → ℝ) : Polynomial ℝ :=
  ∑ i : Fin H, Polynomial.C (v i) * (Polynomial.X ^ (i.1 + 1) - Polynomial.C (gm (i.1 + 1)))

private lemma cpoly_coeff (H : ℕ) (v : Fin H → ℝ) (i : Fin H) : (cpoly H v).coeff (i.1 + 1) = v i := by
  classical
  simp only [cpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_C]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have : ¬ (i.1 = j.1) := fun h => hji (Fin.ext h.symm)
    simp [this]
  · simp

private lemma sq_int_pos (p : Polynomial ℝ) (hp : p ≠ 0) :
    0 < ∫ x, (p.eval x) ^ 2 ∂gaussianReal 0 1 := by
  have hint : Integrable (fun x => (p.eval x) ^ 2) (gaussianReal 0 1) := by
    have := int_poly1 (p ^ 2); simp only [Polynomial.eval_pow] at this; exact this
  rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint]
  have hfin : Set.Finite {x | p.IsRoot x} := Polynomial.finite_setOfPred_isRoot hp
  have h0 : gaussianReal 0 1 {x | p.IsRoot x} = 0 :=
    gaussianReal_absolutelyContinuous 0 (by norm_num) (hfin.measure_zero volume)
  have hsupp : Function.support (fun x => (p.eval x) ^ 2) = {x | p.IsRoot x}ᶜ := by
    ext x; simp [Polynomial.IsRoot]
  rw [hsupp, measure_compl (hfin.measurableSet) (measure_ne_top _ _), h0, measure_univ]
  simp

private noncomputable def cp (i : ℕ) : Polynomial ℝ := Polynomial.X ^ (i + 1) - Polynomial.C (gm (i + 1))

private noncomputable def gram (H : ℕ) (i j : Fin H) : ℝ :=
  ∫ x, (cp i.1 * cp j.1).eval x ∂gaussianReal 0 1

private lemma qf_eq (H : ℕ) (v : Fin H → ℝ) :
    ∫ x, ((cpoly H v).eval x) ^ 2 ∂gaussianReal 0 1 = ∑ i, ∑ j, v i * v j * gram H i j := by
  have hev : ∀ x, (cpoly H v).eval x = ∑ i : Fin H, v i * (cp i.1).eval x := by
    intro x; simp [cpoly, cp, Polynomial.eval_finsetSum]
  have hsq : ∀ x, ((cpoly H v).eval x) ^ 2 =
      ∑ i : Fin H, ∑ j : Fin H, v i * v j * (cp i.1 * cp j.1).eval x := by
    intro x
    rw [hev, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul]; ring
  simp_rw [hsq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (int_poly1 _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (int_poly1 _).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]; rfl

private lemma pd1 (H : ℕ) : ∃ lam : ℝ, 0 < lam ∧ ∀ v : Fin H → ℝ,
    lam * ∑ i, v i ^ 2 ≤ ∫ x, ((cpoly H v).eval x) ^ 2 ∂gaussianReal 0 1 := by
  classical
  set Qf : (Fin H → ℝ) → ℝ := fun v => ∑ i, ∑ j, v i * v j * gram H i j with hQf
  have hQc : Continuous Qf := by rw [hQf]; fun_prop
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst hH
    exact ⟨1, one_pos, fun v => by simp; exact integral_nonneg fun _ => sq_nonneg _⟩
  set S : Set (Fin H → ℝ) := {v | ∑ i, v i ^ 2 = 1} with hS
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by fun_prop) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun v hv => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
        Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [hv] at h1
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (v i), sq_abs (v i)]
  have hSne : S.Nonempty := ⟨Pi.single ⟨0, hH⟩ 1, by simp [hS, Pi.single_apply]⟩
  obtain ⟨v0, hv0S, hmin⟩ := hSc.exists_isMinOn hSne hQc.continuousOn
  have hv0 : v0 ≠ 0 := by
    intro h; rw [h] at hv0S; simp [hS] at hv0S
  have hcp0 : cpoly H v0 ≠ 0 := by
    intro h
    apply hv0
    funext i
    have := cpoly_coeff H v0 i
    rw [h, Polynomial.coeff_zero] at this
    simpa using this.symm
  have hlam : 0 < Qf v0 := by
    have := sq_int_pos _ hcp0
    rwa [qf_eq] at this
  refine ⟨Qf v0, hlam, fun v => ?_⟩
  rw [qf_eq]
  change Qf v0 * _ ≤ Qf v
  set t := ∑ i, v i ^ 2 with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    have : ∀ i, v i = 0 := by
      intro i
      have h1 : v i ^ 2 ≤ t :=
        Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [← h0] at h1
      nlinarith [sq_nonneg (v i)]
    simp [hQf, this]
  · set w : Fin H → ℝ := fun i => v i / Real.sqrt t with hw
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr hpos
    have hwS : w ∈ S := by
      simp only [hS, Set.mem_ofPred_eq, hw, div_pow, hsq]
      rw [← Finset.sum_div, div_self hpos.ne']
    have hvw : ∀ i, v i = Real.sqrt t * w i := fun i => by rw [hw]; field_simp
    have hQv : Qf v = t * Qf w := by
      simp only [hQf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hvw i, hvw j]
      have e : Real.sqrt t * w i * (Real.sqrt t * w j) * gram H i j =
          Real.sqrt t ^ 2 * (w i * w j * gram H i j) := by ring
      rw [e, hsq]
    rw [hQv]
    have := hmin hwS
    simp only [Set.mem_ofPred_eq] at this
    nlinarith

private lemma gpi {κ : Type*} [Fintype κ] (P : MvPolynomial κ ℝ) (r : ℕ) :
    Integrable (fun z => (MvPolynomial.eval z P) ^ r) (stdGauss κ) := by
  have := gauss_poly_integrable (P ^ r); simpa only [map_pow] using this

/-- Cauchy–Schwarz for Gaussian polynomials. -/
private lemma poly_cs {κ : Type*} [Fintype κ] (U V : MvPolynomial κ ℝ) :
    (∫ z, MvPolynomial.eval z U * MvPolynomial.eval z V ∂stdGauss κ) ^ 2 ≤
      (∫ z, (MvPolynomial.eval z U) ^ 2 ∂stdGauss κ) * (∫ z, (MvPolynomial.eval z V) ^ 2 ∂stdGauss κ) := by
  have hUV : Integrable (fun z => MvPolynomial.eval z U * MvPolynomial.eval z V) (stdGauss κ) := by
    have := gauss_poly_integrable (U * V); simpa only [map_mul] using this
  have hquad (t : ℝ) : 0 ≤ (∫ z, (MvPolynomial.eval z U) ^ 2 ∂stdGauss κ) * (t * t) +
      (2 * ∫ z, MvPolynomial.eval z U * MvPolynomial.eval z V ∂stdGauss κ) * t +
      (∫ z, (MvPolynomial.eval z V) ^ 2 ∂stdGauss κ) := by
    have h : 0 ≤ ∫ z, (t * MvPolynomial.eval z U + MvPolynomial.eval z V) ^ 2 ∂stdGauss κ :=
      integral_nonneg fun z => sq_nonneg _
    have he : (fun z => (t * MvPolynomial.eval z U + MvPolynomial.eval z V) ^ 2) = fun z =>
        (t ^ 2 * (MvPolynomial.eval z U) ^ 2 + (2 * t) * (MvPolynomial.eval z U * MvPolynomial.eval z V)) +
          (MvPolynomial.eval z V) ^ 2 := by funext z; ring
    have i1 : Integrable (fun z => t ^ 2 * (MvPolynomial.eval z U) ^ 2) (stdGauss κ) :=
      (gpi U 2).const_mul _
    have i2 : Integrable (fun z => (2 * t) * (MvPolynomial.eval z U * MvPolynomial.eval z V))
      (stdGauss κ) := hUV.const_mul _
    have i12 : Integrable (fun z => t ^ 2 * (MvPolynomial.eval z U) ^ 2 +
      (2 * t) * (MvPolynomial.eval z U * MvPolynomial.eval z V)) (stdGauss κ) := i1.add i2
    rw [he, integral_add i12 (gpi V 2), integral_add i1 i2, integral_const_mul,
      integral_const_mul] at h
    nlinarith only [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

private noncomputable def splitQ {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (b : ℕ) : MvPolynomial ι ℝ :=
  ∑ m ∈ P.support.filter (fun m => m none = b), MvPolynomial.monomial m.some (P.coeff m)

private lemma splitQ_degree {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (s b : ℕ) (hdeg : P.totalDegree ≤ s) :
    (splitQ P b).totalDegree ≤ s - b := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  obtain ⟨hm, hb⟩ := Finset.mem_filter.mp hm
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  have hsum := m.sum_option_index (fun _ k => k) (by simp) (by simp)
  have hle := (MvPolynomial.le_totalDegree hm).trans hdeg
  simp only [hb] at hsum
  simp only [Function.id_def]
  omega

private lemma splitQ_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (s : ℕ) (hdeg : P.totalDegree ≤ s) (z : ι → ℝ) (x : ℝ) :
    MvPolynomial.eval (fun o => o.elim x z) P =
      ∑ b ∈ Finset.range (s + 1), x ^ b * MvPolynomial.eval z (splitQ P b) := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [MvPolynomial.eval_sum]
  have hmono : ∀ m ∈ P.support, MvPolynomial.eval (fun o => o.elim x z)
      (MvPolynomial.monomial m (P.coeff m)) =
        x ^ m none * (P.coeff m * (m.some.prod fun i k => z i ^ k)) := by
    intro m _
    have hp := m.prod_option_index (fun o k => (o.elim x z) ^ k) (by simp) (by simp [pow_add])
    simp only [MvPolynomial.eval_monomial]
    rw [hp]
    simp only [Option.elim_none, Option.elim_some]
    ring
  rw [Finset.sum_congr rfl hmono]
  simp only [splitQ, MvPolynomial.eval_sum, MvPolynomial.eval_monomial, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun m => m none) (t := Finset.range (s + 1))]
  · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m hm => ?_
    rw [(Finset.mem_filter.mp hm).2]
  · intro m hm
    have hsum := m.sum_option_index (fun _ k => k) (by simp) (by simp)
    have hle := (MvPolynomial.le_totalDegree hm).trans hdeg
    rw [Finset.mem_range]
    omega

/-- Fubini on `stdGauss (Option ι) = stdGauss ι ⊗ N(0,1)`. -/
private lemma option_integral {ι : Type*} [Fintype ι] (Q : MvPolynomial (Option ι) ℝ) :
    (∫ z, MvPolynomial.eval z Q ∂stdGauss (Option ι)) =
      ∫ z, ∫ x : ℝ, MvPolynomial.eval (fun o => o.elim x z) Q ∂gaussianReal 0 1 ∂stdGauss ι := by
  let e := (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm
  have hm : ((stdGauss ι).prod (gaussianReal 0 1)).map e = stdGauss (Option ι) :=
    Measure.pi_map_piOptionEquivProd (fun _ => gaussianReal 0 1)
  have hi := gauss_poly_integrable Q
  rw [← hm] at hi ⊢
  have hip := (integrable_map_equiv e _).mp hi
  change Integrable (fun p => MvPolynomial.eval (e p) Q) ((stdGauss ι).prod (gaussianReal 0 1)) at hip
  rw [integral_map_equiv, integral_prod _ hip]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with x
  have he : e (z, x) = (fun o => o.elim x z) := by
    funext i
    cases i <;> rfl
  rw [he]


private lemma pdH (H : ℕ) : ∃ lam : ℝ, 0 < lam ∧ ∀ s ≤ H, ∀ r : ℕ → ℝ,
    lam * ∑ b ∈ Finset.Icc 1 s, r b ^ 2 ≤
      ∫ x, (∑ b ∈ Finset.Icc 1 s, r b * (x ^ b - gm b)) ^ 2 ∂gaussianReal 0 1 := by
  classical
  obtain ⟨lam, hlam, h⟩ := pd1 H
  refine ⟨lam, hlam, fun s hs r => ?_⟩
  set v : Fin H → ℝ := fun i => if i.1 + 1 ≤ s then r (i.1 + 1) else 0 with hv
  have key : ∀ g : ℕ → ℝ, ∑ i : Fin H, (if i.1 + 1 ≤ s then g (i.1 + 1) else 0) =
      ∑ b ∈ Finset.Icc 1 s, g b := by
    intro g
    rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 ≤ s then g (i + 1) else 0)]
    rw [← Finset.sum_filter]
    have : Finset.Icc 1 s = ((Finset.range H).filter (fun i => i + 1 ≤ s)).image (· + 1) := by
      ext b
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨b - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; omega
    rw [this, Finset.sum_image (fun i _ j _ h => by simpa using h)]
  have h1 := h v
  have hsq : ∑ i, v i ^ 2 = ∑ b ∈ Finset.Icc 1 s, r b ^ 2 := by
    rw [← key (fun b => r b ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hv]; split_ifs <;> simp
  have hev : ∀ x, (cpoly H v).eval x = ∑ b ∈ Finset.Icc 1 s, r b * (x ^ b - gm b) := by
    intro x
    rw [← key (fun b => r b * (x ^ b - gm b))]
    simp only [cpoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hv]; split_ifs <;> simp
  rw [hsq] at h1
  simp_rw [hev] at h1
  exact h1

private lemma sum_sq_le_sq_sum {β : Type*} (S : Finset β) (a : β → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    ∑ i ∈ S, a i ^ 2 ≤ (∑ i ∈ S, a i) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => a i * a j) (fun j hj => mul_nonneg (ha i hi) (ha j hj)) hi

private lemma pow4_sum_le {β : Type*} (S : Finset β) (u : β → ℝ) :
    (∑ i ∈ S, u i) ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ S, u i ^ 4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := S) (f := u)
  have h2 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => u i ^ 2)
  have h0 : 0 ≤ (∑ i ∈ S, u i) ^ 2 := sq_nonneg _
  calc (∑ i ∈ S, u i) ^ 4 = ((∑ i ∈ S, u i) ^ 2) ^ 2 := by ring
    _ ≤ ((S.card : ℝ) * ∑ i ∈ S, u i ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (S.card : ℝ) ^ 2 * (∑ i ∈ S, u i ^ 2) ^ 2 := by ring
    _ ≤ (S.card : ℝ) ^ 2 * ((S.card : ℝ) * ∑ i ∈ S, (u i ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by
        rw [← mul_assoc, ← pow_succ]; congr 1
        refine Finset.sum_congr rfl fun i _ => by ring

private lemma option_inner_integrable {ι : Type*} [Fintype ι] (Q : MvPolynomial (Option ι) ℝ) :
    Integrable (fun z => ∫ x : ℝ, MvPolynomial.eval (fun o => o.elim x z) Q ∂gaussianReal 0 1)
      (stdGauss ι) := by
  let e := (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm
  have hm : ((stdGauss ι).prod (gaussianReal 0 1)).map e = stdGauss (Option ι) :=
    Measure.pi_map_piOptionEquivProd (fun _ => gaussianReal 0 1)
  have hi := gauss_poly_integrable Q
  rw [← hm] at hi
  have hip := (integrable_map_equiv e _).mp hi
  change Integrable (fun p => MvPolynomial.eval (e p) Q) ((stdGauss ι).prod (gaussianReal 0 1)) at hip
  have := hip.integral_prod_left
  have he : ∀ z x, e (z, x) = (fun o => o.elim x z) := fun z x => by
    funext i
    cases i <;> rfl
  simp_rw [he] at this
  exact this

private lemma I_add {κ : Type*} [Fintype κ] (Q1 Q2 : MvPolynomial κ ℝ) :
    ∫ z, MvPolynomial.eval z (Q1 + Q2) ∂stdGauss κ =
      (∫ z, MvPolynomial.eval z Q1 ∂stdGauss κ) + ∫ z, MvPolynomial.eval z Q2 ∂stdGauss κ := by
  simp only [map_add]
  exact integral_add (gauss_poly_integrable Q1) (gauss_poly_integrable Q2)

private lemma I_smul {κ : Type*} [Fintype κ] (a : ℝ) (Q : MvPolynomial κ ℝ) :
    ∫ z, MvPolynomial.eval z (MvPolynomial.C a * Q) ∂stdGauss κ =
      a * ∫ z, MvPolynomial.eval z Q ∂stdGauss κ := by
  simp only [map_mul, MvPolynomial.eval_C]
  exact integral_const_mul _ _

private noncomputable def Apol {α : Type*} [DecidableEq α] (P : MvPolynomial (Option α) ℝ) (s : ℕ) :
    MvPolynomial α ℝ :=
  ∑ b ∈ Finset.range (s + 1), MvPolynomial.C (gm b) * splitQ P b

private noncomputable def Bpol {α : Type*} [DecidableEq α] (P : MvPolynomial (Option α) ℝ) (s : ℕ) :
    MvPolynomial (Option α) ℝ :=
  ∑ b ∈ Finset.range (s + 1), (MvPolynomial.X none ^ b - MvPolynomial.C (gm b)) *
    MvPolynomial.rename some (splitQ P b)

private lemma eval_ren {α : Type*} (U : MvPolynomial α ℝ) (x : ℝ) (z : α → ℝ) :
    MvPolynomial.eval (fun o => o.elim x z) (MvPolynomial.rename some U) = MvPolynomial.eval z U := by
  rw [MvPolynomial.eval_rename]; rfl

private lemma evalB {α : Type*} [DecidableEq α] (P : MvPolynomial (Option α) ℝ) (s : ℕ) (x : ℝ)
    (z : α → ℝ) : MvPolynomial.eval (fun o => o.elim x z) (Bpol P s) =
      ∑ b ∈ Finset.range (s + 1), (x ^ b - gm b) * MvPolynomial.eval z (splitQ P b) := by
  simp only [Bpol, map_sum, map_mul, map_sub, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
    eval_ren]
  rfl

private lemma decomp {α : Type*} [Fintype α] [DecidableEq α] (P : MvPolynomial (Option α) ℝ) (s : ℕ)
    (hdeg : P.totalDegree ≤ s) : P = MvPolynomial.rename some (Apol P s) + Bpol P s := by
  apply MvPolynomial.funext
  intro w
  have hw : w = fun o => o.elim (w none) (fun i => w (some i)) := by
    funext o; cases o <;> rfl
  rw [hw, map_add, eval_ren, evalB, splitQ_eval P s hdeg]
  simp only [Apol, map_sum, map_mul, MvPolynomial.eval_C]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma I_ren {α : Type*} [Fintype α] (U : MvPolynomial α ℝ) :
    ∫ z, MvPolynomial.eval z (MvPolynomial.rename some U) ∂stdGauss (Option α) =
      ∫ z, MvPolynomial.eval z U ∂stdGauss α := by
  rw [option_integral]
  simp only [eval_ren, integral_const, probReal_univ, one_smul]

private lemma int_cm (b : ℕ) : ∫ x, (x ^ b - gm b) ∂gaussianReal 0 1 = 0 := by
  rw [integral_sub (int_pow1 b) (integrable_const _), integral_const]
  simp [gm]

private lemma I_orth {α : Type*} [Fintype α] [DecidableEq α] (P : MvPolynomial (Option α) ℝ) (s : ℕ)
    (U : MvPolynomial α ℝ) :
    ∫ z, MvPolynomial.eval z (MvPolynomial.rename some U * Bpol P s) ∂stdGauss (Option α) = 0 := by
  rw [option_integral]
  have : ∀ z : α → ℝ, ∫ x, MvPolynomial.eval (fun o => o.elim x z)
      (MvPolynomial.rename some U * Bpol P s) ∂gaussianReal 0 1 = 0 := by
    intro z
    have e : ∀ x : ℝ, MvPolynomial.eval (fun o => o.elim x z) (MvPolynomial.rename some U * Bpol P s) =
        ∑ b ∈ Finset.range (s + 1),
          (MvPolynomial.eval z U * MvPolynomial.eval z (splitQ P b)) * (x ^ b - gm b) := by
      intro x
      simp only [map_mul, eval_ren, evalB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp only [e]
    have hi : ∀ b ∈ Finset.range (s + 1), Integrable (fun x : ℝ =>
        (MvPolynomial.eval z U * MvPolynomial.eval z (splitQ P b)) * (x ^ b - gm b))
        (gaussianReal 0 1) := fun b _ => ((int_pow1 b).sub (integrable_const (gm b))).const_mul _
    rw [integral_finsetSum _ hi]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [integral_const_mul, int_cm, mul_zero]
  simp only [this, integral_zero]

private lemma gm_zero : gm 0 = 1 := by simp [gm]

private lemma sum_range_Icc (s : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0) :
    ∑ b ∈ Finset.range (s + 1), f b = ∑ b ∈ Finset.Icc 1 s, f b := by
  rw [Finset.sum_range_succ', h0, add_zero]
  have : Finset.Icc 1 s = (Finset.range s).image (· + 1) := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨b - 1, by omega, by omega⟩
    · rintro ⟨i, h1, rfl⟩; omega
  rw [this, Finset.sum_image (fun i _ j _ h => by simpa using h)]

/-- `μ_b = E (x^b − m_b)⁴`. -/
private noncomputable def mu4 (b : ℕ) : ℝ := ∫ x, (x ^ b - gm b) ^ 4 ∂gaussianReal 0 1

private lemma mu4_nonneg (b : ℕ) : 0 ≤ mu4 b := integral_nonneg fun x => by positivity

private lemma mu4_zero : mu4 0 = 0 := by simp [mu4, gm_zero]

private lemma int_cm4 (b : ℕ) : Integrable (fun x : ℝ => (x ^ b - gm b) ^ 4) (gaussianReal 0 1) := by
  have := int_poly1 ((Polynomial.X ^ b - Polynomial.C (gm b)) ^ 4)
  simpa using this

private lemma int_combo (s : ℕ) (r : ℕ → ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => (∑ b ∈ Finset.range (s + 1), (x ^ b - gm b) * r b) ^ k)
      (gaussianReal 0 1) := by
  have := int_poly1 ((∑ b ∈ Finset.range (s + 1),
    (Polynomial.X ^ b - Polynomial.C (gm b)) * Polynomial.C (r b)) ^ k)
  simpa [Polynomial.eval_finsetSum] using this

private lemma B2_lower {α : Type*} [Fintype α] [DecidableEq α] (P : MvPolynomial (Option α) ℝ)
    (s : ℕ) (lam : ℝ)
    (hpd : ∀ r : ℕ → ℝ, lam * ∑ b ∈ Finset.Icc 1 s, r b ^ 2 ≤
      ∫ x, (∑ b ∈ Finset.Icc 1 s, r b * (x ^ b - gm b)) ^ 2 ∂gaussianReal 0 1) :
    lam * ∑ b ∈ Finset.Icc 1 s, ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α ≤
      ∫ z, MvPolynomial.eval z (Bpol P s ^ 2) ∂stdGauss (Option α) := by
  rw [option_integral, ← integral_finsetSum _ (fun b _ => gpi _ 2), ← integral_const_mul]
  refine integral_mono ((integrable_finsetSum _ fun b _ => gpi _ 2).const_mul _)
    (option_inner_integrable _) fun z => ?_
  simp only [map_pow, evalB]
  have e : ∀ x : ℝ, ∑ b ∈ Finset.range (s + 1), (x ^ b - gm b) * MvPolynomial.eval z (splitQ P b) =
      ∑ b ∈ Finset.Icc 1 s, MvPolynomial.eval z (splitQ P b) * (x ^ b - gm b) := by
    intro x
    rw [sum_range_Icc s _ (by simp [gm_zero])]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [e]
  exact hpd (fun b => MvPolynomial.eval z (splitQ P b))

private lemma B4_upper {α : Type*} [Fintype α] [DecidableEq α] (P : MvPolynomial (Option α) ℝ)
    (s : ℕ) (M K : ℝ) (hM : ∀ b ∈ Finset.Icc 1 s, mu4 b ≤ M) (hK : 0 ≤ K)
    (IHb : ∀ b ∈ Finset.Icc 1 s, ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 4 ∂stdGauss α ≤
      K * (∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α) ^ 2) :
    ∫ z, MvPolynomial.eval z (Bpol P s ^ 4) ∂stdGauss (Option α) ≤
      ((s : ℝ) + 1) ^ 3 * M * K *
        (∑ b ∈ Finset.Icc 1 s, ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α) ^ 2 := by
  have hM0 : 0 ≤ M ∨ Finset.Icc 1 s = ∅ := by
    by_cases h : Finset.Icc 1 s = ∅
    · exact Or.inr h
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr h
      exact Or.inl ((mu4_nonneg b).trans (hM b hb))
  rw [option_integral]
  set N : ℝ := (s : ℝ) + 1 with hN
  -- pointwise in z
  have hpt : ∀ z : α → ℝ, ∫ x, MvPolynomial.eval (fun o => o.elim x z) (Bpol P s ^ 4) ∂gaussianReal 0 1 ≤
      N ^ 3 * ∑ b ∈ Finset.range (s + 1), mu4 b * (MvPolynomial.eval z (splitQ P b)) ^ 4 := by
    intro z
    simp only [map_pow, evalB]
    have hcard : ((Finset.range (s + 1)).card : ℝ) = N := by simp [hN]
    have hle : ∀ x : ℝ, (∑ b ∈ Finset.range (s + 1), (x ^ b - gm b) * MvPolynomial.eval z (splitQ P b)) ^ 4 ≤
        N ^ 3 * ∑ b ∈ Finset.range (s + 1),
          (MvPolynomial.eval z (splitQ P b)) ^ 4 * (x ^ b - gm b) ^ 4 := by
      intro x
      have := pow4_sum_le (Finset.range (s + 1)) (fun b => (x ^ b - gm b) * MvPolynomial.eval z (splitQ P b))
      rw [hcard] at this
      refine this.trans (le_of_eq ?_)
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
    have hiR : Integrable (fun x : ℝ => N ^ 3 * ∑ b ∈ Finset.range (s + 1),
        (MvPolynomial.eval z (splitQ P b)) ^ 4 * (x ^ b - gm b) ^ 4) (gaussianReal 0 1) :=
      (integrable_finsetSum _ fun b _ => (int_cm4 b).const_mul _).const_mul _
    refine (integral_mono (int_combo s _ 4) hiR hle).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_finsetSum _ fun b _ => (int_cm4 b).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, mu4]; ring
  have hiR : Integrable (fun z : α → ℝ => N ^ 3 * ∑ b ∈ Finset.range (s + 1),
      mu4 b * (MvPolynomial.eval z (splitQ P b)) ^ 4) (stdGauss α) :=
    (integrable_finsetSum _ fun b _ => (gpi _ 4).const_mul _).const_mul _
  refine (integral_mono (option_inner_integrable _) hiR hpt).trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun b _ => (gpi _ 4).const_mul _]
  simp only [integral_const_mul]
  rw [sum_range_Icc s _ (by simp [mu4_zero])]
  have hJ : ∀ b, 0 ≤ ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α :=
    fun b => integral_nonneg fun _ => sq_nonneg _
  have hsum : ∑ b ∈ Finset.Icc 1 s, mu4 b * ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 4 ∂stdGauss α ≤
      M * K * ∑ b ∈ Finset.Icc 1 s, (∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have h4 : 0 ≤ ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 4 ∂stdGauss α :=
      integral_nonneg fun _ => by positivity
    calc mu4 b * ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 4 ∂stdGauss α
        ≤ M * ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 4 ∂stdGauss α :=
          mul_le_mul_of_nonneg_right (hM b hb) h4
      _ ≤ M * (K * (∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α) ^ 2) := by
          rcases hM0 with hM0 | hM0
          · exact mul_le_mul_of_nonneg_left (IHb b hb) hM0
          · rw [hM0] at hb; simp at hb
      _ = _ := by ring
  have hss := sum_sq_le_sq_sum (Finset.Icc 1 s)
    (fun b => ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α) (fun b _ => hJ b)
  have hN3 : 0 ≤ N ^ 3 := by positivity
  rcases hM0 with hM0 | hM0
  · calc N ^ 3 * ∑ b ∈ Finset.Icc 1 s, mu4 b * ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 4 ∂stdGauss α
        ≤ N ^ 3 * (M * K * ∑ b ∈ Finset.Icc 1 s,
            (∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum hN3
      _ ≤ N ^ 3 * (M * K * (∑ b ∈ Finset.Icc 1 s,
            ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hss (mul_nonneg hM0 hK)) hN3
      _ = _ := by ring
  · simp [hM0]

private lemma I_pow_eq {κ : Type*} [Fintype κ] (Q : MvPolynomial κ ℝ) (r : ℕ) :
    ∫ z, MvPolynomial.eval z (Q ^ r) ∂stdGauss κ = ∫ z, (MvPolynomial.eval z Q) ^ r ∂stdGauss κ := by
  simp only [map_pow]

private lemma mom2 {α : Type*} [Fintype α] [DecidableEq α] (P : MvPolynomial (Option α) ℝ) (s : ℕ)
    (hdeg : P.totalDegree ≤ s) :
    ∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss (Option α) =
      (∫ z, (MvPolynomial.eval z (Apol P s)) ^ 2 ∂stdGauss α) +
        ∫ z, MvPolynomial.eval z (Bpol P s ^ 2) ∂stdGauss (Option α) := by
  set A := MvPolynomial.rename some (Apol P s) with hA
  set B := Bpol P s with hB
  have hP := decomp P s hdeg
  rw [← hA, ← hB] at hP
  have e : P ^ 2 = A ^ 2 + (MvPolynomial.C 2 * (MvPolynomial.rename some (Apol P s) * B) + B ^ 2) := by
    conv_lhs => rw [hP]
    rw [hA, map_ofNat]; ring
  rw [← I_pow_eq, e, I_add, I_add, I_smul, hB, I_orth, hA, ← map_pow, I_ren, I_pow_eq]
  ring

private lemma mom4 {α : Type*} [Fintype α] [DecidableEq α] (P : MvPolynomial (Option α) ℝ) (s : ℕ)
    (hdeg : P.totalDegree ≤ s) :
    ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss (Option α) =
      (∫ z, (MvPolynomial.eval z (Apol P s)) ^ 4 ∂stdGauss α) +
        6 * (∫ z, MvPolynomial.eval z (MvPolynomial.rename some (Apol P s) ^ 2 * Bpol P s ^ 2)
          ∂stdGauss (Option α)) +
        4 * (∫ z, MvPolynomial.eval z (MvPolynomial.rename some (Apol P s) * Bpol P s ^ 3)
          ∂stdGauss (Option α)) +
        ∫ z, MvPolynomial.eval z (Bpol P s ^ 4) ∂stdGauss (Option α) := by
  set A := MvPolynomial.rename some (Apol P s) with hA
  set B := Bpol P s with hB
  have hP := decomp P s hdeg
  rw [← hA, ← hB] at hP
  have e : P ^ 4 = A ^ 4 + (MvPolynomial.C 4 * (MvPolynomial.rename some (Apol P s ^ 3) * B) +
      (MvPolynomial.C 6 * (A ^ 2 * B ^ 2) + (MvPolynomial.C 4 * (A * B ^ 3) + B ^ 4))) := by
    conv_lhs => rw [hP]
    rw [hA, map_pow, map_ofNat, map_ofNat]; ring
  rw [← I_pow_eq, e, I_add, I_add, I_add, I_add, I_smul, I_smul, I_smul, hB, I_orth, hA, ← map_pow,
    I_ren, I_pow_eq]
  ring

private lemma cs_T2 {κ : Type*} [Fintype κ] (A B : MvPolynomial κ ℝ) :
    (∫ z, MvPolynomial.eval z (A ^ 2 * B ^ 2) ∂stdGauss κ) ^ 2 ≤
      (∫ z, MvPolynomial.eval z (A ^ 4) ∂stdGauss κ) * ∫ z, MvPolynomial.eval z (B ^ 4) ∂stdGauss κ := by
  have h := poly_cs (A ^ 2) (B ^ 2)
  simp only [map_mul, map_pow] at h ⊢
  have e1 : ∀ z, (MvPolynomial.eval z A ^ 2) ^ 2 = MvPolynomial.eval z A ^ 4 := fun z => by ring
  have e2 : ∀ z, (MvPolynomial.eval z B ^ 2) ^ 2 = MvPolynomial.eval z B ^ 4 := fun z => by ring
  simp only [e1, e2] at h
  exact h

private lemma cs_T3 {κ : Type*} [Fintype κ] (A B : MvPolynomial κ ℝ) :
    (∫ z, MvPolynomial.eval z (A * B ^ 3) ∂stdGauss κ) ^ 2 ≤
      (∫ z, MvPolynomial.eval z (A ^ 2 * B ^ 2) ∂stdGauss κ) *
        ∫ z, MvPolynomial.eval z (B ^ 4) ∂stdGauss κ := by
  have h := poly_cs (A * B) (B ^ 2)
  simp only [map_mul, map_pow] at h ⊢
  have e1 : ∀ z, MvPolynomial.eval z A * MvPolynomial.eval z B * MvPolynomial.eval z B ^ 2 =
      MvPolynomial.eval z A * MvPolynomial.eval z B ^ 3 := fun z => by ring
  have e2 : ∀ z, (MvPolynomial.eval z A * MvPolynomial.eval z B) ^ 2 =
      MvPolynomial.eval z A ^ 2 * MvPolynomial.eval z B ^ 2 := fun z => by ring
  have e3 : ∀ z, (MvPolynomial.eval z B ^ 2) ^ 2 = MvPolynomial.eval z B ^ 4 := fun z => by ring
  simp only [e1, e2, e3] at h
  exact h

private lemma Apol_degree {α : Type*} [DecidableEq α] (P : MvPolynomial (Option α) ℝ) (s : ℕ)
    (hdeg : P.totalDegree ≤ s) : (Apol P s).totalDegree ≤ s := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro b _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (splitQ_degree P s b hdeg).trans (Nat.sub_le _ _)

/-- The final arithmetic of the induction step. -/
private lemma step_arith (D K A2 B2 A4 B4 T2 T3 : ℝ) (hD : 1 ≤ D) (hK : 0 ≤ K) (hA2 : 0 ≤ A2)
    (hB2 : 0 ≤ B2) (hA4 : A4 ≤ 16 * D * K * A2 ^ 2) (hB4 : B4 ≤ D * K * B2 ^ 2) (_hA40 : 0 ≤ A4)
    (hB40 : 0 ≤ B4) (hT2 : T2 ^ 2 ≤ A4 * B4) (hT20 : 0 ≤ T2) (hT3 : T3 ^ 2 ≤ T2 * B4) :
    A4 + 6 * T2 + 4 * T3 + B4 ≤ 16 * D * K * (A2 + B2) ^ 2 := by
  have hDK : 0 ≤ D * K := mul_nonneg (by linarith) hK
  have h1 : T2 ^ 2 ≤ (4 * D * K * A2 * B2) ^ 2 := by
    calc T2 ^ 2 ≤ A4 * B4 := hT2
      _ ≤ (16 * D * K * A2 ^ 2) * (D * K * B2 ^ 2) := mul_le_mul hA4 hB4 hB40 (by positivity)
      _ = (4 * D * K * A2 * B2) ^ 2 := by ring
  have hT2b : T2 ≤ 4 * D * K * A2 * B2 := (abs_le_of_sq_le_sq' h1 (by positivity)).2
  have h2 : T3 ^ 2 ≤ (D * K * (A2 * B2 + B2 ^ 2)) ^ 2 := by
    calc T3 ^ 2 ≤ T2 * B4 := hT3
      _ ≤ (4 * D * K * A2 * B2) * (D * K * B2 ^ 2) := mul_le_mul hT2b hB4 hB40 (by positivity)
      _ ≤ (D * K * (A2 * B2 + B2 ^ 2)) ^ 2 := by
          have : 0 ≤ (D * K) ^ 2 * (A2 * B2 - B2 ^ 2) ^ 2 := by positivity
          nlinarith
  have hT3b : T3 ≤ D * K * (A2 * B2 + B2 ^ 2) := (abs_le_of_sq_le_sq' h2 (by positivity)).2
  nlinarith [mul_nonneg hDK (mul_nonneg hA2 hB2), mul_nonneg hDK (sq_nonneg A2),
    mul_nonneg hDK (sq_nonneg B2)]

private lemma gauss_rename_integral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (P : MvPolynomial κ ℝ) (r : ℕ) :
    (∫ z, (MvPolynomial.eval z (MvPolynomial.rename e.symm P)) ^ r ∂stdGauss ι) =
      ∫ z, (MvPolynomial.eval z P) ^ r ∂stdGauss κ := by
  simp_rw [MvPolynomial.eval_rename]
  have hh := (measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e).integral_comp'
    (fun z => (MvPolynomial.eval z P) ^ r)
  have he (z : ι → ℝ) : MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e z = z ∘ e.symm := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [MeasurableEquiv.piCongrLeft_apply_apply]
  simpa only [he, stdGauss] using hh

private lemma fm_main (H : ℕ) : ∃ c : ℝ, 1 ≤ c ∧ ∀ (ι : Type) [Fintype ι], ∀ [DecidableEq ι] (s : ℕ),
    s ≤ H → ∀ P : MvPolynomial ι ℝ, P.totalDegree ≤ s →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        c ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 := by
  obtain ⟨lam, hlam, hpd⟩ := pdH H
  set M := ∑ b ∈ Finset.range (H + 1), mu4 b with hM
  set D := max 1 (((H : ℝ) + 1) ^ 3 * M / lam ^ 2) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun b _ => mu4_nonneg b
  have hc1 : (1 : ℝ) ≤ 16 * D := by linarith
  refine ⟨16 * D, hc1, ?_⟩
  apply Fintype.induction_empty_option (P := fun ι => ∀ [DecidableEq ι] (s : ℕ),
    s ≤ H → ∀ P : MvPolynomial ι ℝ, P.totalDegree ≤ s →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        (16 * D) ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2)
  · intro α β instβ e ih instDec s hs P hdeg
    let : Fintype α := Fintype.ofEquiv β e.symm
    classical
    have hh := ih s hs (MvPolynomial.rename e.symm P)
      ((MvPolynomial.totalDegree_rename_le _ _).trans hdeg)
    simpa only [gauss_rename_integral] using hh
  · intro instDec s hs P hdeg
    have hp : P = MvPolynomial.C (P.coeff 0) := by
      ext m
      have hm : m = 0 := Subsingleton.elim _ _
      subst m
      simp
    rw [hp]
    simp only [MvPolynomial.eval_C, integral_const, probReal_univ, one_smul]
    exact le_of_eq (by ring) |>.trans
      (le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hc1))
  · intro α instα ih instDec s hs P hdeg
    classical
    by_cases hs0 : s = 0
    · have hp : P = MvPolynomial.C (P.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by omega)
      rw [hp]
      simp only [MvPolynomial.eval_C, integral_const, probReal_univ, one_smul, hs0, pow_zero, one_mul]
      exact le_of_eq (by ring)
    · have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
      set K := (16 * D) ^ (s - 1) with hKdef
      have hK0 : 0 ≤ K := by positivity
      have hcs : (16 * D) ^ s = 16 * D * K := by
        rw [hKdef, ← pow_succ']; congr 1; omega
      set A := MvPolynomial.rename some (Apol P s) with hA
      set B := Bpol P s with hB
      set A2 := ∫ z, (MvPolynomial.eval z (Apol P s)) ^ 2 ∂stdGauss α with hA2
      set A4 := ∫ z, (MvPolynomial.eval z (Apol P s)) ^ 4 ∂stdGauss α with hA4
      set B2 := ∫ z, MvPolynomial.eval z (B ^ 2) ∂stdGauss (Option α) with hB2
      set B4 := ∫ z, MvPolynomial.eval z (B ^ 4) ∂stdGauss (Option α) with hB4
      set T2 := ∫ z, MvPolynomial.eval z (A ^ 2 * B ^ 2) ∂stdGauss (Option α) with hT2
      set T3 := ∫ z, MvPolynomial.eval z (A * B ^ 3) ∂stdGauss (Option α) with hT3
      rw [mom4 P s hdeg, mom2 P s hdeg, hcs]
      have hA2n : 0 ≤ A2 := integral_nonneg fun _ => sq_nonneg _
      have hB2n : 0 ≤ B2 := integral_nonneg fun z => by simp only [map_pow]; positivity
      have hA4n : 0 ≤ A4 := integral_nonneg fun _ => by positivity
      have hB4n : 0 ≤ B4 := integral_nonneg fun z => by simp only [map_pow]; positivity
      have hT2n : 0 ≤ T2 := integral_nonneg fun z => by simp only [map_mul, map_pow]; positivity
      have hA4b : A4 ≤ 16 * D * K * A2 ^ 2 := by
        rw [← hcs]; exact ih s hs (Apol P s) (Apol_degree P s hdeg)
      have hA4I : ∫ z, MvPolynomial.eval z (A ^ 4) ∂stdGauss (Option α) = A4 := by
        rw [hA, ← map_pow, I_ren, I_pow_eq]
      have hT2b : T2 ^ 2 ≤ A4 * B4 := by
        have := cs_T2 A B
        rwa [hA4I] at this
      have hT3b : T3 ^ 2 ≤ T2 * B4 := cs_T3 A B
      -- the key bound on B4
      set SJ := ∑ b ∈ Finset.Icc 1 s, ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α with hSJ
      have hSJn : 0 ≤ SJ := Finset.sum_nonneg fun b _ => integral_nonneg fun _ => sq_nonneg _
      have hMb : ∀ b ∈ Finset.Icc 1 s, mu4 b ≤ M := by
        intro b hb
        have hbH : b ∈ Finset.range (H + 1) := by
          rw [Finset.mem_Icc] at hb; rw [Finset.mem_range]; omega
        exact Finset.single_le_sum (f := mu4) (fun i _ => mu4_nonneg i) hbH
      have IHb : ∀ b ∈ Finset.Icc 1 s, ∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 4 ∂stdGauss α ≤
          K * (∫ z, (MvPolynomial.eval z (splitQ P b)) ^ 2 ∂stdGauss α) ^ 2 := by
        intro b hb
        rw [Finset.mem_Icc] at hb
        refine (ih (s - b) (by omega) (splitQ P b) (splitQ_degree P s b hdeg)).trans ?_
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by omega)) (sq_nonneg _)
      have hBu := B4_upper P s M K hMb hK0 IHb
      have hBl := B2_lower P s lam (hpd s hs)
      rw [← hSJ] at hBu hBl
      rw [← hB] at hBu hBl
      have hSJb : SJ ≤ B2 / lam := by rw [le_div_iff₀ hlam]; linarith
      have hSJ2 : SJ ^ 2 ≤ (B2 / lam) ^ 2 := pow_le_pow_left₀ hSJn hSJb 2
      have hsH : ((s : ℝ) + 1) ^ 3 ≤ ((H : ℝ) + 1) ^ 3 := by
        have : (s : ℝ) ≤ H := by exact_mod_cast hs
        exact pow_le_pow_left₀ (by positivity) (by linarith) 3
      have hDge : ((H : ℝ) + 1) ^ 3 * M / lam ^ 2 ≤ D := le_max_right _ _
      have hB4b : B4 ≤ D * K * B2 ^ 2 := by
        calc B4 ≤ ((s : ℝ) + 1) ^ 3 * M * K * SJ ^ 2 := hBu
          _ ≤ ((H : ℝ) + 1) ^ 3 * M * K * (B2 / lam) ^ 2 := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsH hM0) hK0)
                hSJ2 (sq_nonneg _) (by positivity)
          _ = (((H : ℝ) + 1) ^ 3 * M / lam ^ 2) * K * B2 ^ 2 := by field_simp
          _ ≤ D * K * B2 ^ 2 := by
              apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDge hK0) (sq_nonneg _)
      exact step_arith D K A2 B2 A4 B4 T2 T3 hD1 hK0 hA2n hB2n hA4b hB4b hA4n hB4n hT2b hT2n hT3b

/-- **Dimension-free fourth moment**: `E P⁴ ≤ K_h (E P²)²` for every real polynomial of total degree
`≤ h` in standard Gaussians, with `K_h` independent of the number of variables. -/
theorem fourth_moment (h : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ), P.totalDegree ≤ h →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        K * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 := by
  obtain ⟨c, hc1, hc⟩ := fm_main h
  refine ⟨c ^ h, by positivity, fun ι _ P hP => ?_⟩
  classical
  exact hc ι h le_rfl P hP

end BstLean.Part48
