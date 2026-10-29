import BstLean.Part48Var
import BstLean.Part62HermK

/-!
# Part 62: an explicit dimension-free fourth moment `κ^{2h}` (omEX-opus-prover, Theorem K route)

Induction on the variables as in `Part48Hyper.fm_main`, but the step splits one variable in the
Hermite basis: `P(x, z) = Σ_b x^b R'_b(z) = Σ_c He_c(x) R_c(z)` with `R_c = Σ_b lap1 b c R'_b`
(`deg R_c ≤ s − c`). For each `z`, `Part62HermK.oneD_weighted` gives
`E_x P⁴ ≤ (Σ_c κ^c c! R_c(z)²)²`; Cauchy–Schwarz on `E_z[R_a² R_c²]` and the induction hypothesis
`E R_c⁴ ≤ κ^{2(s−c)} (E R_c²)²` close the step, since `E P² = Σ_c c! E R_c²`
(`Part62Gram.fischer_sq`).

* `fourth_moment_kappa h κ γ (hK : KCrit h κ γ)`: `E P⁴ ≤ κ^{2h} (E P²)²`.
* `fourth_moment_explicit h`: `E P⁴ ≤ Kexp h (E P²)²`, `Kexp h = kapE h ^ (2h)` (deliverable 1).

The helper lemmas `gpi` … `option_integral`, `option_inner_integrable`, `gauss_rename_integral`
are copied from `Part48Hyper.lean`, where they are private.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part62

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part48 (gauss_poly_integrable)
open BstLean.Part36 (lap1 lap1_eq_zero)

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


private lemma fmK_main (H : ℕ) (κ : ℝ) (γ : ℕ → ℝ) (hK : KCrit H κ γ) :
    ∀ (ι : Type) [Fintype ι], ∀ [DecidableEq ι] (s : ℕ),
    s ≤ H → ∀ P : MvPolynomial ι ℝ, P.totalDegree ≤ s →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        (κ ^ 2) ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 := by
  have hκ5 : 5 ≤ κ := hK.1
  have hk1 : (1 : ℝ) ≤ κ ^ 2 := by nlinarith
  apply Fintype.induction_empty_option (P := fun ι => ∀ [DecidableEq ι] (s : ℕ),
    s ≤ H → ∀ P : MvPolynomial ι ℝ, P.totalDegree ≤ s →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        (κ ^ 2) ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2)
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
      (le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hk1))
  · intro α instα ih instDec s hs P hdeg
    classical
    have hκ0 : 0 ≤ κ := by linarith
    have hκpow : ∀ m : ℕ, κ ^ (2 * m) = (κ ^ 2) ^ m := fun m => pow_mul κ 2 m
    set R : ℕ → MvPolynomial α ℝ := fun c =>
      ∑ b ∈ Finset.range (s + 1), MvPolynomial.C (lap1 b c) * splitQ P b with hR
    have hRdeg : ∀ c, c ≤ s → (R c).totalDegree ≤ s - c := by
      intro c hc
      apply MvPolynomial.totalDegree_finsetSum_le
      intro b hb
      by_cases hbc : b < c
      · rw [lap1_eq_zero (Or.inl hbc)]; simp
      · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact (splitQ_degree P s b hdeg).trans (by omega)
    have hRev : ∀ (z : α → ℝ) c, MvPolynomial.eval z (R c) =
        ∑ b ∈ Finset.range (s + 1), MvPolynomial.eval z (splitQ P b) * lap1 b c := by
      intro z c
      simp only [hR, map_sum, map_mul, MvPolynomial.eval_C]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hPx : ∀ (z : α → ℝ) (x : ℝ), MvPolynomial.eval (fun o => o.elim x z) P =
        ∑ b ∈ Finset.range (s + 1), MvPolynomial.eval z (splitQ P b) * x ^ b := by
      intro z x
      rw [splitQ_eval P s hdeg]
      exact Finset.sum_congr rfl fun b _ => by ring
    set Y2 : ℕ → ℝ := fun c => ∫ z, (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α with hY2
    have hY20 : ∀ c, 0 ≤ Y2 c := fun c => integral_nonneg fun _ => sq_nonneg _
    -- second moment
    have h2 : ∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss (Option α) =
        ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * Y2 c := by
      have h := option_integral (P ^ 2)
      simp only [map_pow] at h
      rw [h]
      have hin : ∀ z : α → ℝ, ∫ x, (MvPolynomial.eval (fun o => o.elim x z) P) ^ 2 ∂gaussianReal 0 1 =
          ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * (MvPolynomial.eval z (R c)) ^ 2 := by
        intro z
        simp_rw [hPx, hRev]
        exact fischer_sq s (fun b => MvPolynomial.eval z (splitQ P b))
      simp_rw [hin]
      rw [integral_finsetSum _ fun c _ => (gpi _ 2).const_mul _]
      exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul]
    -- fourth moment, one variable at a time
    set w : ℕ → ℝ := fun c => κ ^ c * (c.factorial : ℝ) with hw
    have hw0 : ∀ c, 0 ≤ w c := fun c => by simp only [hw]; positivity
    set Q : MvPolynomial α ℝ :=
      (∑ c ∈ Finset.range (s + 1), MvPolynomial.C (w c) * R c ^ 2) ^ 2 with hQ
    have hQev : ∀ z : α → ℝ, MvPolynomial.eval z Q =
        (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2 := by
      intro z; simp [hQ, map_sum]
    have h4 : ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss (Option α) ≤
        ∫ z, (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2 ∂stdGauss α := by
      have h := option_integral (P ^ 4)
      simp only [map_pow] at h
      rw [h]
      have hiQ : Integrable (fun z : α → ℝ =>
          (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2) (stdGauss α) := by
        have := gauss_poly_integrable Q
        simpa only [hQev] using this
      have hiL := option_inner_integrable (P ^ 4)
      simp only [map_pow] at hiL
      refine integral_mono hiL hiQ fun z => ?_
      simp only
      simp_rw [hPx]
      refine (oneD_weighted H s hs κ γ hK (fun b => MvPolynomial.eval z (splitQ P b))).trans
        (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hRev]
    -- pairwise bound
    have hpair : ∀ a ∈ Finset.range (s + 1), ∀ c ∈ Finset.range (s + 1),
        ∫ z, (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α ≤
          (κ ^ (s - a) * Y2 a) * (κ ^ (s - c) * Y2 c) := by
      intro a ha c hc
      have ha' : a ≤ s := by have := Finset.mem_range.mp ha; omega
      have hc' : c ≤ s := by have := Finset.mem_range.mp hc; omega
      have hIa := ih (s - a) (by omega) (R a) (hRdeg a ha')
      have hIc := ih (s - c) (by omega) (R c) (hRdeg c hc')
      have hcs := poly_cs (R a ^ 2) (R c ^ 2)
      simp only [map_pow] at hcs
      have e4 : ∀ (Rr : MvPolynomial α ℝ), (fun z => ((MvPolynomial.eval z) Rr ^ 2) ^ 2) =
          fun z => (MvPolynomial.eval z Rr) ^ 4 := fun Rr => by funext z; ring
      rw [e4, e4] at hcs
      have hsq : (∫ z, (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α) ^ 2
          ≤ ((κ ^ (s - a) * Y2 a) * (κ ^ (s - c) * Y2 c)) ^ 2 := by
        refine hcs.trans ?_
        have h4a : 0 ≤ ∫ z, (MvPolynomial.eval z (R a)) ^ 4 ∂stdGauss α :=
          integral_nonneg fun _ => by positivity
        have e : ((κ ^ (s - a) * Y2 a) * (κ ^ (s - c) * Y2 c)) ^ 2 =
            ((κ ^ 2) ^ (s - a) * Y2 a ^ 2) * ((κ ^ 2) ^ (s - c) * Y2 c ^ 2) := by
          rw [← hκpow, ← hκpow]; ring
        rw [e]
        exact mul_le_mul hIa hIc (integral_nonneg fun _ => by positivity) (by positivity)
      exact (abs_le_of_sq_le_sq' hsq (by have := hY20 a; have := hY20 c; positivity)).2
    -- expand and close
    have hexp : ∫ z, (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2 ∂stdGauss α
        = ∑ a ∈ Finset.range (s + 1), ∑ c ∈ Finset.range (s + 1), (w a * w c) *
          ∫ z, (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α := by
      have e : ∀ z : α → ℝ, (∑ c ∈ Finset.range (s + 1), w c * (MvPolynomial.eval z (R c)) ^ 2) ^ 2 =
          ∑ a ∈ Finset.range (s + 1), ∑ c ∈ Finset.range (s + 1), (w a * w c) *
            ((MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2) := by
        intro z; rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
      have hi : ∀ a c, Integrable (fun z : α → ℝ =>
          (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2) (stdGauss α) := by
        intro a c
        have := gauss_poly_integrable (R a ^ 2 * R c ^ 2)
        simpa only [map_mul, map_pow] using this
      simp_rw [e]
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ => (hi a c).const_mul _]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun c _ => (hi a c).const_mul _]
      exact Finset.sum_congr rfl fun c _ => by rw [integral_const_mul]
    have hbound : ∑ a ∈ Finset.range (s + 1), ∑ c ∈ Finset.range (s + 1), (w a * w c) *
          ∫ z, (MvPolynomial.eval z (R a)) ^ 2 * (MvPolynomial.eval z (R c)) ^ 2 ∂stdGauss α ≤
        (∑ c ∈ Finset.range (s + 1), w c * (κ ^ (s - c) * Y2 c)) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun c hc => ?_
      have := mul_le_mul_of_nonneg_left (hpair a ha c hc) (mul_nonneg (hw0 a) (hw0 c))
      refine this.trans (le_of_eq ?_)
      ring
    have hfold : ∑ c ∈ Finset.range (s + 1), w c * (κ ^ (s - c) * Y2 c) =
        κ ^ s * ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * Y2 c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' : c ≤ s := by have := Finset.mem_range.mp hc; omega
      have : κ ^ c * κ ^ (s - c) = κ ^ s := by rw [← pow_add]; congr 1; omega
      simp only [hw]
      rw [← this]; ring
    rw [h2]
    calc ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss (Option α)
        ≤ _ := h4
      _ = _ := hexp
      _ ≤ _ := hbound
      _ = (κ ^ s * ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * Y2 c) ^ 2 := by rw [hfold]
      _ = (κ ^ 2) ^ s * (∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * Y2 c) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm s 2, hκpow]

/-- **Fourth moment, Theorem K form** with any `κ` satisfying the criterion `KCrit h κ γ`:
`E P⁴ ≤ κ^{2h} (E P²)²`. -/
theorem fourth_moment_kappa (h : ℕ) (κ : ℝ) (γ : ℕ → ℝ) (hK : KCrit h κ γ) :
    ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ), P.totalDegree ≤ h →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        κ ^ (2 * h) * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 := by
  intro ι _ P hP
  classical
  rw [pow_mul]
  exact fmK_main h κ γ hK ι h le_rfl P hP

/-- The explicit constant `Kexp h = kapE h ^ (2h)`, `kapE h = max 5 (2 Σ_{1≤c≤h} √(E He_c⁴)/c!)`. -/
noncomputable def Kexp (h : ℕ) : ℝ := kapE h ^ (2 * h)

lemma Kexp_pos (h : ℕ) : 0 < Kexp h := by
  unfold Kexp; have : (5 : ℝ) ≤ kapE h := le_max_left _ _; positivity

/-- **Explicit dimension-free fourth moment** (deliverable 1): `E P⁴ ≤ Kexp h (E P²)²`. -/
theorem fourth_moment_explicit (h : ℕ) : ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
    P.totalDegree ≤ h →
      ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
        Kexp h * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 :=
  fourth_moment_kappa h (kapE h) _ (kapE_crit h)

end BstLean.Part62
