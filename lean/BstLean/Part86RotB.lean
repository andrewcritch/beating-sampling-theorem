import BstLean.Part86Defs
import BstLean.Part46CharFn_Spectral
import BstLean.Part53Wick
import BstLean.Part56Orth_Projection

/-!
# Part 86, the rotation `Z ↦ (U, W)`: measure preservation and the two-point identity

* `rot_mp`: `Z ↦ (Uof v Z, Wof E Z)` maps the standard Gaussian to the product of standard
  Gaussians.
* `rot_twoPt`: the two-point identity `TwoPt n (JR n d)` (Lemma W of Part 53 on the residual
  coordinates).
-/

namespace BstLean.Part86.XRotB

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono colM IsSymmT Tens)
open BstLean.Part53 (heatA tinner fvA linZ nsq wpair)
open BstLean.Part56 (UnitV phiB kJ ancRK)
open BstLean.Part78 (zv)

variable {n d : ℕ}

/-- The index of the rotated coordinates. -/
abbrev KIdx (n d : ℕ) := (Fin (d + 1) × Fin n) ⊕ (JR n d × Fin n)

/-- The rows on the monomial index. -/
noncomputable def rr (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ) :
    Fin (d + 1) ⊕ JR n d → Mono n d → ℝ :=
  Sum.elim (fun j p => phiB d j v p / Real.sqrt (kJ d j v v)) E

/-- The row index and the output index of a rotated coordinate. -/
def kidx : KIdx n d → (Fin (d + 1) ⊕ JR n d) × Fin n :=
  Sum.elim (fun a => (Sum.inl a.1, a.2)) (fun a => (Sum.inr a.1, a.2))

lemma kidx_inj : Function.Injective (kidx (n := n) (d := d)) := by
  rintro (⟨j, i⟩ | ⟨q, i⟩) (⟨j', i'⟩ | ⟨q', i'⟩) h <;> simp [kidx] at h ⊢ <;> exact h

/-- The basis vectors on the coefficient index. -/
noncomputable def bv (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ) (s : KIdx n d) :
    CoefIdxD n d → ℝ := fun α =>
  rr v E (kidx s).1 ⟨α.1, α.2.1⟩ * if α.2.2 = (kidx s).2 then 1 else 0

lemma sum_coef (f : CoefIdxD n d → ℝ) :
    ∑ α, f α = ∑ p : Mono n d, ∑ a : Fin n, f ⟨p.1, (p.2, a)⟩ := by
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]

lemma rr_orth (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E)
    (s s' : Fin (d + 1) ⊕ JR n d) :
    ∑ p, rr v E s p * rr v E s' p = if s = s' then 1 else 0 := by
  obtain ⟨h1, h2, -⟩ := hE
  rcases s with j | q <;> rcases s' with j' | q'
  · simp only [rr, Sum.elim_inl, Sum.inl.injEq]
    have e : ∀ p, phiB d j v p / Real.sqrt (kJ d j v v) *
        (phiB d j' v p / Real.sqrt (kJ d j' v v)) =
        phiB d j v p * phiB d j' v p / (Real.sqrt (kJ d j v v) * Real.sqrt (kJ d j' v v)) := by
      intro p; ring
    simp only [e]
    rw [← Finset.sum_div]
    by_cases h : j = j'
    · subst h
      have hpos := BstLean.Part56.Orth.block_norm_pos (d := d) v hv j (by have := j.2; omega)
      rw [if_pos rfl, Real.mul_self_sqrt hpos.le]
      have : ∑ p, phiB d j v p * phiB d j v p = kJ d j v v := rfl
      rw [this, div_self hpos.ne']
    · rw [if_neg h, BstLean.Part56.Orth.blocks_orthogonal (d := d) j j' v
        (fun hh => h (Fin.ext hh)), zero_div]
  · simp only [rr, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
    have e : ∀ p, phiB d j v p / Real.sqrt (kJ d j v v) * E q' p =
        E q' p * phiB d j v p / Real.sqrt (kJ d j v v) := by intro p; ring
    simp only [e]
    rw [← Finset.sum_div, h2 q' j (Finset.mem_range.mpr j.2), zero_div]
  · simp only [rr, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
    have e : ∀ p, E q p * (phiB d j' v p / Real.sqrt (kJ d j' v v)) =
        E q p * phiB d j' v p / Real.sqrt (kJ d j' v v) := by intro p; ring
    simp only [e]
    rw [← Finset.sum_div, h2 q j' (Finset.mem_range.mpr j'.2), zero_div]
  · simp only [rr, Sum.elim_inr, Sum.inr.injEq]
    exact h1 q q'

lemma bv_orth (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E)
    (s s' : KIdx n d) :
    ∑ α, bv v E s α * bv v E s' α = if s = s' then 1 else 0 := by
  rw [sum_coef]
  simp only [bv]
  have e : ∀ (p : Mono n d) (a : Fin n),
      rr v E (kidx s).1 p * (if a = (kidx s).2 then 1 else 0) *
        (rr v E (kidx s').1 p * if a = (kidx s').2 then 1 else 0) =
      (rr v E (kidx s).1 p * rr v E (kidx s').1 p) *
        ((if a = (kidx s).2 then (1 : ℝ) else 0) * if a = (kidx s').2 then 1 else 0) := by
    intro p a; ring
  simp only [e]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, rr_orth v hv E hE]
  have hδ : ∑ a : Fin n, ((if a = (kidx s).2 then (1 : ℝ) else 0) *
      if a = (kidx s').2 then 1 else 0) = if (kidx s).2 = (kidx s').2 then 1 else 0 := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hδ]
  by_cases h : s = s'
  · subst h; simp
  · rw [if_neg h]
    have hne : kidx s ≠ kidx s' := fun hh => h (kidx_inj hh)
    by_cases h1 : (kidx s).1 = (kidx s').1
    · have h2 : (kidx s).2 ≠ (kidx s').2 := fun hh => hne (Prod.ext h1 hh)
      simp [h2]
    · simp [h1]

lemma card_JR (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    Fintype.card (JR n d) + (d + 1) = Fintype.card (Mono n d) := by
  obtain ⟨h1, -, h3⟩ := hE
  have ht : ∑ p : Mono n d, (∑ q, E q p * E q p +
      ∑ j ∈ Finset.range (d + 1), phiB d j v p * phiB d j v p / kJ d j v v) =
      (Fintype.card (Mono n d) : ℝ) := by
    simp [h3]
  rw [Finset.sum_add_distrib, Finset.sum_comm] at ht
  have ha : ∑ q : JR n d, ∑ p, E q p * E q p = (Fintype.card (JR n d) : ℝ) := by
    simp [h1]
  have hb : ∑ p : Mono n d, ∑ j ∈ Finset.range (d + 1),
      phiB d j v p * phiB d j v p / kJ d j v v = (d : ℝ) + 1 := by
    rw [Finset.sum_comm]
    have : ∀ j ∈ Finset.range (d + 1),
        ∑ p : Mono n d, phiB d j v p * phiB d j v p / kJ d j v v = 1 := by
      intro j hj
      have hpos := BstLean.Part56.Orth.block_norm_pos (d := d) v hv j
        (by have := Finset.mem_range.mp hj; omega)
      rw [← Finset.sum_div]
      exact div_self hpos.ne'
    rw [Finset.sum_congr rfl this]
    simp
  rw [ha, hb] at ht
  have : ((Fintype.card (JR n d) + (d + 1) : ℕ) : ℝ) = (Fintype.card (Mono n d) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

lemma card_KIdx (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    Fintype.card (KIdx n d) = Fintype.card (CoefIdxD n d) := by
  have h := card_JR v hv E hE
  have hc : Fintype.card (CoefIdxD n d) = Fintype.card (Mono n d) * n := by
    have := Fintype.card_congr (Equiv.sigmaProdDistrib (fun i : Fin (d + 1) => Sym (Fin n) i)
      (Fin n))
    rw [← this, Fintype.card_prod, Fintype.card_fin]
  calc Fintype.card (KIdx n d) = (d + 1) * n + Fintype.card (JR n d) * n := by
        rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin n,
          Fintype.card_fin (d + 1)]
    _ = (Fintype.card (JR n d) + (d + 1)) * n := by ring
    _ = Fintype.card (Mono n d) * n := by rw [h]
    _ = _ := hc.symm

lemma n_pos_of_unit (v : Fin n → ℝ) (hv : UnitV v) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    unfold UnitV at hv
    simp at hv
  · exact h

lemma bv_on (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    Orthonormal ℝ (fun s : KIdx n d =>
      (WithLp.toLp 2 (bv v E s) : EuclideanSpace ℝ (CoefIdxD n d))) := by
  rw [orthonormal_iff_ite]
  intro s s'
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial, dotProduct]
  rw [← bv_orth v hv E hE s s']
  exact Finset.sum_congr rfl fun α _ => mul_comm _ _

/-- The orthonormal basis of the rotation. -/
noncomputable def rotBasis (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ)
    (hE : RotE v E) : OrthonormalBasis (KIdx n d) ℝ (EuclideanSpace ℝ (CoefIdxD n d)) :=
  haveI : Nonempty (KIdx n d) := ⟨Sum.inl (0, ⟨0, n_pos_of_unit v hv⟩)⟩
  OrthonormalBasis.mk (bv_on v hv E hE) (by
    have hc : Fintype.card (KIdx n d) =
        Module.finrank ℝ (EuclideanSpace ℝ (CoefIdxD n d)) := by
      rw [finrank_euclideanSpace]; exact card_KIdx v hv E hE
    have h := (basisOfOrthonormalOfCardEqFinrank (bv_on v hv E hE) hc).span_eq
    rw [coe_basisOfOrthonormalOfCardEqFinrank] at h
    exact h.ge)

lemma rot_coord (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E)
    (Z : CoefIdxD n d → ℝ) (s : KIdx n d) :
    WithLp.ofLp ((rotBasis v hv E hE).repr (WithLp.toLp 2 Z)) s =
      Sum.elim (Uof v Z) (Wof E Z) s := by
  have h0 : WithLp.ofLp ((rotBasis v hv E hE).repr (WithLp.toLp 2 Z)) s =
      (rotBasis v hv E hE).repr (WithLp.toLp 2 Z) s := rfl
  rw [h0, OrthonormalBasis.repr_apply_apply]
  unfold rotBasis
  rw [OrthonormalBasis.coe_mk, EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial, dotProduct]
  rw [sum_coef]
  simp only [bv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases s with ⟨j, i⟩ | ⟨q, i⟩
  · simp only [kidx, Sum.elim_inl, rr, Uof, ancRK, linZ, colM]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    ring
  · simp only [kidx, Sum.elim_inr, rr, Wof, colM]
    apply Finset.sum_congr rfl
    intro p _
    ring

/-- **The rotation preserves the standard Gaussian.** -/
theorem rot_mp (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    MeasurePreserving (fun Z : CoefIdxD n d → ℝ => (Uof v Z, Wof E Z))
      (stdGauss (CoefIdxD n d))
      ((stdGauss (Fin (d + 1) × Fin n)).prod (stdGauss (JR n d × Fin n))) := by
  classical
  have h1 := BstLean.Part46.CharFn.gaussian_basis_preserving (rotBasis v hv E hE)
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : KIdx n d => ℝ))
      (stdGauss (KIdx n d))
      ((stdGauss (Fin (d + 1) × Fin n)).prod (stdGauss (JR n d × Fin n))) :=
    measurePreserving_sumPiEquivProdPi (fun _ : KIdx n d => gaussianReal 0 1)
  have h := h2.comp h1
  have e : (fun Z : CoefIdxD n d → ℝ => (Uof v Z, Wof E Z)) =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : KIdx n d => ℝ)) ∘
        (fun z : CoefIdxD n d → ℝ =>
          WithLp.ofLp ((rotBasis v hv E hE).repr (WithLp.toLp 2 z))) := by
    funext Z
    apply Prod.ext
    · funext a
      simp only [Function.comp_apply, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.coe_mk,
        Equiv.sumPiEquivProdPi_apply]
      rw [rot_coord]; rfl
    · funext a
      simp only [Function.comp_apply, MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.coe_mk,
        Equiv.sumPiEquivProdPi_apply]
      rw [rot_coord]; rfl
  rw [e]
  exact h

/-- The residual coordinates are standard Gaussian. -/
theorem rot_mpW (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    MeasurePreserving (fun Z : CoefIdxD n d → ℝ => Wof E Z)
      (stdGauss (CoefIdxD n d)) (stdGauss (JR n d × Fin n)) :=
  (measurePreserving_snd (μ := stdGauss (Fin (d + 1) × Fin n))
    (ν := stdGauss (JR n d × Fin n))).comp (rot_mp v hv E hE)

lemma cont_fvA (K : ℕ) (A : Tens n) : Continuous (fvA K A) := by
  unfold fvA BstLean.Part41.contr
  fun_prop

/-- **The two-point identity on the residual coordinates.** -/
theorem rot_twoPt (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E) :
    TwoPt n (JR n d) := by
  intro K A A' hA hA' lam p p'
  set ψ : Mono n d → ℝ := fun m => ∑ q, p q * E q m with hψ
  set ψ' : Mono n d → ℝ := fun m => ∑ q, p' q * E q m with hψ'
  have hmp := rot_mpW v hv E hE
  have hlin : ∀ (r : JR n d → ℝ) (Z : CoefIdxD n d → ℝ),
      (fun i => lam * zv (Wof E Z) r i) = lam • linZ Z (fun m => ∑ q, r q * E q m) := by
    intro r Z
    funext i
    simp only [zv, Wof, linZ, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hip : ∀ r r' : JR n d → ℝ,
      ∑ m, (∑ q, r q * E q m) * (∑ q, r' q * E q m) = ∑ q, r q * r' q := by
    intro r r'
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_comm]
    have : ∀ q' : JR n d, ∑ m, r q * E q m * (r' q' * E q' m) =
        r q * r' q' * ∑ m, E q m * E q' m := by
      intro q'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    simp_rw [this, hE.1 q]
    simp
  set G : (JR n d × Fin n → ℝ) → ℝ := fun W =>
    fvA K A (fun i => lam * zv W p i) * fvA K A' (fun i => lam * zv W p' i) with hG
  have hGc : Continuous G := by
    apply Continuous.mul
    · apply (cont_fvA K A).comp
      unfold zv
      fun_prop
    · apply (cont_fvA K A').comp
      unfold zv
      fun_prop
  have hcomp : ∀ Z : CoefIdxD n d → ℝ,
      G (Wof E Z) = fvA K A (lam • linZ Z ψ) * fvA K A' (lam • linZ Z ψ') := by
    intro Z
    simp only [hG]
    rw [hlin p Z, hlin p' Z]
  obtain ⟨hint, hval⟩ := BstLean.Part53.lemmaW53 K n d lam A A' hA hA' ψ ψ'
  have hmeas : AEStronglyMeasurable G (Measure.map (fun Z : CoefIdxD n d → ℝ => Wof E Z)
      (stdGauss (CoefIdxD n d))) := hGc.aestronglyMeasurable
  have hnsq : ∀ r : JR n d → ℝ, nsq (fun m => ∑ q, r q * E q m) = ∑ q, r q ^ 2 := by
    intro r
    unfold nsq
    have := hip r r
    simp only [← pow_two] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [← hmp.map_eq]
    rw [integrable_map_measure hmeas hmp.measurable.aemeasurable]
    have : (G ∘ fun Z : CoefIdxD n d → ℝ => Wof E Z) =
        fun Z => fvA K A (lam • linZ Z ψ) * fvA K A' (lam • linZ Z ψ') := funext hcomp
    rw [this]
    exact hint
  · rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hmeas]
    simp_rw [hcomp]
    rw [hval]
    unfold wpair
    rw [hnsq p, hnsq p', hip p p']

end BstLean.Part86.XRotB

#print axioms BstLean.Part86.XRotB.rot_mp
#print axioms BstLean.Part86.XRotB.rot_twoPt
