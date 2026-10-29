import BstLean.Part152SF

/-!
# Part 152 (file `Op`): the operator norm of a Gaussian matrix (Gordon's bound)

Role: `delegations/statements/p152-spec.md`, optional item 4; the standard fact (G2) of the paper
proof of Theorem 5.

`opN M` is the operator norm of a real `p × q` matrix `M` for the Euclidean norms, written as the
supremum of the bilinear form `u ⬝ᵥ M *ᵥ v` over the unit spheres (it is `0` if `p = 0` or
`q = 0`).

* `mulVec_le_opN`: `|M v| ≤ opN M · |v|`; `opN_le_frob`; `opN_lip`: `opN` is `1`-Lipschitz for the
  Frobenius norm.
* **`opN_mean_le`** (Gordon): for a matrix with independent `N(0, v)` entries (`gaussMat`):
  `E opN ≤ √v·(√p + √q)`.
* **`opN_tail`**: `Pr(opN M ≥ √v·(√p + √q) + t) ≤ exp(−t²/(2v))`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part152

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130

section alg

variable {p q : ℕ}

/-- The values of the bilinear form of `M` on the unit spheres. -/
def opSet (M : Matrix (Fin p) (Fin q) ℝ) : Set ℝ :=
  {x | ∃ u : Fin p → ℝ, ∃ v : Fin q → ℝ, ∑ i, u i ^ 2 = 1 ∧ ∑ j, v j ^ 2 = 1 ∧
    x = u ⬝ᵥ M *ᵥ v}

/-- **The operator norm** of a real matrix for the Euclidean norms. -/
noncomputable def opN (M : Matrix (Fin p) (Fin q) ℝ) : ℝ := sSup (opSet M)

lemma bil_eq (M : Matrix (Fin p) (Fin q) ℝ) (u : Fin p → ℝ) (v : Fin q → ℝ) :
    u ⬝ᵥ M *ᵥ v = ∑ i, ∑ j, M i j * (u i * v j) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bil_le_frob (M : Matrix (Fin p) (Fin q) ℝ) (u : Fin p → ℝ) (v : Fin q → ℝ) :
    |u ⬝ᵥ M *ᵥ v| ≤ √(∑ i, ∑ j, M i j ^ 2) * (√(∑ i, u i ^ 2) * √(∑ j, v j ^ 2)) := by
  rw [bil_eq]
  have e1 : ∑ i, ∑ j, M i j * (u i * v j) =
      ∑ x : Fin p × Fin q, M x.1 x.2 * (u x.1 * v x.2) :=
    (Fintype.sum_prod_type (fun x : Fin p × Fin q => M x.1 x.2 * (u x.1 * v x.2))).symm
  have e2 : ∑ i, ∑ j, M i j ^ 2 = ∑ x : Fin p × Fin q, M x.1 x.2 ^ 2 :=
    (Fintype.sum_prod_type (fun x : Fin p × Fin q => M x.1 x.2 ^ 2)).symm
  have e3 : (∑ i, u i ^ 2) * ∑ j, v j ^ 2 = ∑ x : Fin p × Fin q, (u x.1 * v x.2) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _), e3,
    ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

lemma opSet_bdd (M : Matrix (Fin p) (Fin q) ℝ) : BddAbove (opSet M) := by
  refine ⟨√(∑ i, ∑ j, M i j ^ 2), ?_⟩
  rintro x ⟨u, v, hu, hv, rfl⟩
  have := bil_le_frob M u v
  rw [hu, hv, Real.sqrt_one, mul_one, mul_one] at this
  exact (le_abs_self _).trans this

lemma bil_le_opN (M : Matrix (Fin p) (Fin q) ℝ) {u : Fin p → ℝ} {v : Fin q → ℝ}
    (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ j, v j ^ 2 = 1) : u ⬝ᵥ M *ᵥ v ≤ opN M :=
  le_csSup (opSet_bdd M) ⟨u, v, hu, hv, rfl⟩

lemma opN_nonneg (M : Matrix (Fin p) (Fin q) ℝ) : 0 ≤ opN M := by
  by_cases h : (opSet M).Nonempty
  · obtain ⟨x, u, v, hu, hv, rfl⟩ := h
    have h1 := bil_le_opN M hu hv
    have h2 := bil_le_opN M (u := -u) (by simpa using hu) hv
    rw [neg_dotProduct] at h2
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at h
    unfold opN
    rw [h, Real.sSup_empty]

lemma opN_le_frob (M : Matrix (Fin p) (Fin q) ℝ) : opN M ≤ √(∑ i, ∑ j, M i j ^ 2) := by
  by_cases h : (opSet M).Nonempty
  · refine csSup_le h ?_
    rintro x ⟨u, v, hu, hv, rfl⟩
    have := bil_le_frob M u v
    rw [hu, hv, Real.sqrt_one, mul_one, mul_one] at this
    exact (le_abs_self _).trans this
  · rw [Set.not_nonempty_iff_eq_empty] at h
    unfold opN
    rw [h, Real.sSup_empty]
    exact Real.sqrt_nonneg _

lemma unit_of_ne {d : ℕ} (u : Fin d → ℝ) (h : √(∑ i, u i ^ 2) ≠ 0) :
    ∑ i, ((√(∑ i, u i ^ 2))⁻¹ • u) i ^ 2 = 1 := by
  have h0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, inv_pow, Real.sq_sqrt h0]
  have : ∑ i, u i ^ 2 ≠ 0 := fun h' => h (by rw [h', Real.sqrt_zero])
  exact inv_mul_cancel₀ this

lemma zero_of_norm {d : ℕ} (u : Fin d → ℝ) (h : √(∑ i, u i ^ 2) = 0) : u = 0 := by
  have h0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∑ i, u i ^ 2 = 0 := (Real.sqrt_eq_zero h0).mp h
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (u i)).mp h1 i (Finset.mem_univ i)
  simpa using this

/-- The bilinear form is at most `opN M · |u| · |v|`. -/
lemma bil_le_opN_mul (M : Matrix (Fin p) (Fin q) ℝ) (u : Fin p → ℝ) (v : Fin q → ℝ) :
    u ⬝ᵥ M *ᵥ v ≤ opN M * (√(∑ i, u i ^ 2) * √(∑ j, v j ^ 2)) := by
  by_cases ha : √(∑ i, u i ^ 2) = 0
  · rw [zero_of_norm u ha]
    simp
  by_cases hb : √(∑ j, v j ^ 2) = 0
  · rw [zero_of_norm v hb]
    simp
  have h := bil_le_opN M (unit_of_ne u ha) (unit_of_ne v hb)
  rw [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
  have ha' : 0 < √(∑ i, u i ^ 2) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ha)
  have hb' : 0 < √(∑ j, v j ^ 2) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hb)
  have e : u ⬝ᵥ M *ᵥ v = (√(∑ i, u i ^ 2) * √(∑ j, v j ^ 2)) *
      ((√(∑ i, u i ^ 2))⁻¹ * ((√(∑ j, v j ^ 2))⁻¹ * (u ⬝ᵥ M *ᵥ v))) := by
    field_simp
  rw [e, mul_comm (opN M)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **`|M v| ≤ opN M · |v|`.** -/
theorem mulVec_le_opN (M : Matrix (Fin p) (Fin q) ℝ) (v : Fin q → ℝ) :
    √(∑ i, (M *ᵥ v) i ^ 2) ≤ opN M * √(∑ j, v j ^ 2) := by
  have h := bil_le_opN_mul M (M *ᵥ v) v
  have h0 : 0 ≤ ∑ i, (M *ᵥ v) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : (M *ᵥ v) ⬝ᵥ M *ᵥ v = √(∑ i, (M *ᵥ v) i ^ 2) * √(∑ i, (M *ᵥ v) i ^ 2) := by
    rw [Real.mul_self_sqrt h0]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h
  rcases (Real.sqrt_nonneg (∑ i, (M *ᵥ v) i ^ 2)).eq_or_lt with h1 | h1
  · rw [← h1]
    exact mul_nonneg (opN_nonneg M) (Real.sqrt_nonneg _)
  · have h2 : √(∑ i, (M *ᵥ v) i ^ 2) * √(∑ i, (M *ᵥ v) i ^ 2) ≤
        √(∑ i, (M *ᵥ v) i ^ 2) * (opN M * √(∑ j, v j ^ 2)) := by
      refine h.trans (le_of_eq ?_)
      ring
    exact le_of_mul_le_mul_left h2 h1

lemma opN_le_add (M M' : Matrix (Fin p) (Fin q) ℝ) :
    opN M ≤ opN M' + √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  by_cases h : (opSet M).Nonempty
  · refine csSup_le h ?_
    rintro x ⟨u, v, hu, hv, rfl⟩
    have e : u ⬝ᵥ M *ᵥ v = u ⬝ᵥ M' *ᵥ v + u ⬝ᵥ (M - M') *ᵥ v := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      ring
    have h1 := bil_le_opN M' hu hv
    have h2 := bil_le_frob (M - M') u v
    rw [hu, hv, Real.sqrt_one, mul_one, mul_one] at h2
    simp only [Matrix.sub_apply] at h2
    rw [e]
    linarith [le_abs_self (u ⬝ᵥ (M - M') *ᵥ v)]
  · rw [Set.not_nonempty_iff_eq_empty] at h
    have : opN M = 0 := by unfold opN; rw [h, Real.sSup_empty]
    rw [this]
    exact add_nonneg (opN_nonneg M') (Real.sqrt_nonneg _)

/-- **`opN` is `1`-Lipschitz for the Frobenius norm.** -/
theorem opN_lip (M M' : Matrix (Fin p) (Fin q) ℝ) :
    |opN M - opN M'| ≤ 1 * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  have h1 := opN_le_add M M'
  have h2 := opN_le_add M' M
  have e : ∑ i, ∑ j, (M' i j - M i j) ^ 2 = ∑ i, ∑ j, (M i j - M' i j) ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e] at h2
  rw [one_mul, abs_le]
  constructor <;> linarith

end alg

/-! ## Gordon's bound -/

section gordon

lemma sup_dot_measurable {κ S : Type} [Fintype κ] [Fintype S] [Nonempty S] (c : S → κ → ℝ) :
    Measurable fun ζ : κ → ℝ => Finset.univ.sup' Finset.univ_nonempty (fun s => c s ⬝ᵥ ζ) := by
  have := Finset.measurable_sup' (Finset.univ_nonempty (α := S))
    (f := fun s (ζ : κ → ℝ) => c s ⬝ᵥ ζ) (fun s _ => by
      simp only [dotProduct]; fun_prop)
  convert this using 1
  funext ζ
  simp [Finset.sup'_apply]

lemma sup_dot_integrable {κ S : Type} [Fintype κ] [Fintype S] [Nonempty S] (c : S → κ → ℝ) :
    Integrable (fun ζ : κ → ℝ => Finset.univ.sup' Finset.univ_nonempty (fun s => c s ⬝ᵥ ζ))
      (stdGauss κ) := by
  have hle : ∀ (ζ : κ → ℝ) (s : S), |c s ⬝ᵥ ζ| ≤ ∑ s, |c s ⬝ᵥ ζ| := fun ζ s =>
    Finset.single_le_sum (f := fun s => |c s ⬝ᵥ ζ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  refine Integrable.mono' (g := fun ζ => ∑ s, |c s ⬝ᵥ ζ|)
    (integrable_finsetSum Finset.univ fun s _ => (integrable_dot (c s)).abs)
    (sup_dot_measurable c).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨s0⟩ := ‹Nonempty S›
  constructor
  · have h1 := Finset.le_sup' (fun s => c s ⬝ᵥ ζ) (Finset.mem_univ s0)
    have h2 := neg_abs_le (c s0 ⬝ᵥ ζ)
    have h3 := hle ζ s0
    linarith
  · exact Finset.sup'_le _ _ fun s _ => (le_abs_self _).trans (hle ζ s)

lemma coord_sq {κ : Type} [Fintype κ] (k : κ) :
    Integrable (fun ζ : κ → ℝ => ζ k ^ 2) (stdGauss κ) ∧ ∫ ζ, ζ k ^ 2 ∂stdGauss κ = 1 := by
  have hi : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hs : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
    rw [variance_eq_integral (by fun_prop)] at h
    simpa using h
  unfold stdGauss
  refine ⟨integrable_comp_eval (μ := fun _ : κ => gaussianReal 0 1) (i := k) hi, ?_⟩
  rw [integral_comp_eval (μ := fun _ : κ => gaussianReal 0 1) (i := k) hi.aestronglyMeasurable, hs]

variable {p q : ℕ}

/-- The increments of the tensor family are at most those of the sum family, on the unit
spheres. -/
lemma tensor_inc {u u' : Fin p → ℝ} {v v' : Fin q → ℝ} (hu : ∑ i, u i ^ 2 = 1)
    (hu' : ∑ i, u' i ^ 2 = 1) (hv : ∑ j, v j ^ 2 = 1) (hv' : ∑ j, v' j ^ 2 = 1) :
    ∑ i, ∑ j, (u i * v j - u' i * v' j) ^ 2 ≤ ∑ i, (u i - u' i) ^ 2 + ∑ j, (v j - v' j) ^ 2 := by
  have e1 : ∑ i, (u i - u' i) ^ 2 = 2 - 2 * ∑ i, u i * u' i := by
    have : ∑ i, (u i - u' i) ^ 2 = ∑ i, u i ^ 2 + ∑ i, u' i ^ 2 - 2 * ∑ i, u i * u' i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hu, hu']; ring
  have e2 : ∑ j, (v j - v' j) ^ 2 = 2 - 2 * ∑ j, v j * v' j := by
    have : ∑ j, (v j - v' j) ^ 2 = ∑ j, v j ^ 2 + ∑ j, v' j ^ 2 - 2 * ∑ j, v j * v' j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hv, hv']; ring
  have e3 : ∑ i, ∑ j, (u i * v j - u' i * v' j) ^ 2 =
      2 - 2 * ((∑ i, u i * u' i) * ∑ j, v j * v' j) := by
    have inner : ∀ i, ∑ j, (u i * v j - u' i * v' j) ^ 2 =
        u i ^ 2 + u' i ^ 2 - 2 * (u i * u' i) * ∑ j, v j * v' j := by
      intro i
      have : ∑ j, (u i * v j - u' i * v' j) ^ 2 =
          u i ^ 2 * ∑ j, v j ^ 2 + u' i ^ 2 * ∑ j, v' j ^ 2 -
            2 * (u i * u' i) * ∑ j, v j * v' j := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hv, hv']; ring
    simp_rw [inner]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hu, hu', ← Finset.sum_mul,
      ← Finset.mul_sum]
    ring
  have h1 : 0 ≤ ∑ i, (u i - u' i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ j, (v j - v' j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [e1] at h1
  rw [e2] at h2
  rw [e1, e2, e3]
  nlinarith [mul_nonneg h1 h2]

lemma dot_le_norm {d : ℕ} {u : Fin d → ℝ} (hu : ∑ i, u i ^ 2 = 1) (g : Fin d → ℝ) :
    u ⬝ᵥ g ≤ √(∑ i, g i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u g
  rw [hu, one_mul] at h
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

lemma sqrt_le_half {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) : √x ≤ (x + c) / (2 * √c) := by
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (√x - √c), Real.sq_sqrt hx, Real.sq_sqrt hc.le]

lemma opN_eq_zero (h : p = 0 ∨ q = 0) (M : Matrix (Fin p) (Fin q) ℝ) : opN M = 0 := by
  have : opSet M = ∅ := by
    ext x
    simp only [opSet, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨u, v, hu, hv, -⟩
    rcases h with h | h
    · subst h
      simp at hu
    · subst h
      simp at hv
  unfold opN
  rw [this, Real.sSup_empty]

/-- The finite step of Gordon's bound. -/
lemma gordon_fin {v : ℝ} (hv : 0 ≤ v) (hp : 0 < p) (hq : 0 < q) {N : ℕ}
    (uu : Fin (N + 1) → Fin p → ℝ) (vv : Fin (N + 1) → Fin q → ℝ)
    (hu : ∀ s, ∑ i, uu s i ^ 2 = 1) (hvv : ∀ s, ∑ j, vv s j ^ 2 = 1) :
    ∫ ξ, Finset.univ.sup' Finset.univ_nonempty
        (fun s => (fun x : Fin p × Fin q => √v * (uu s x.1 * vv s x.2)) ⬝ᵥ ξ)
      ∂stdGauss (Fin p × Fin q) ≤ √v * (√p + √q) := by
  set A : Fin (N + 1) → (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ :=
    fun s => Sum.elim (fun x => √v * (uu s x.1 * vv s x.2)) (fun _ => 0) with hA
  set B : Fin (N + 1) → (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ :=
    fun s => Sum.elim (fun _ => 0) (Sum.elim (fun i => √v * uu s i) (fun j => √v * vv s j)) with hB
  set r : ((Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ) → (Fin p × Fin q → ℝ) :=
    fun ζ x => ζ (Sum.inl x) with hr
  have hrp : MeasurePreserving r (stdGauss ((Fin p × Fin q) ⊕ (Fin p ⊕ Fin q)))
      (stdGauss (Fin p × Fin q)) :=
    (measurePreserving_fst (μ := stdGauss (Fin p × Fin q)) (ν := stdGauss (Fin p ⊕ Fin q))).comp
      (measurePreserving_sumPiEquivProdPi
        (fun _ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) => gaussianReal 0 1))
  have hAdot : ∀ s ζ, A s ⬝ᵥ ζ = (fun x : Fin p × Fin q => √v * (uu s x.1 * vv s x.2)) ⬝ᵥ r ζ := by
    intro s ζ
    simp [hA, hr, dotProduct, Fintype.sum_sum_type]
  have hBdot : ∀ s ζ, B s ⬝ᵥ ζ = √v * (uu s ⬝ᵥ (fun i => ζ (Sum.inr (Sum.inl i))) +
      vv s ⬝ᵥ (fun j => ζ (Sum.inr (Sum.inr j)))) := by
    intro s ζ
    simp only [hB, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, zero_add, mul_add, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  rw [← hrp.map_eq, integral_map hrp.measurable.aemeasurable
    (sup_dot_measurable _).aestronglyMeasurable]
  simp only [← hAdot]
  have hSF := sudakovFernique A B (fun s s' => by
      simp [hA, hB, dotProduct, Fintype.sum_sum_type]) (fun s s' => by
      have h := tensor_inc (hu s) (hu s') (hvv s) (hvv s')
      have e1 : ∑ k, (A s k - A s' k) ^ 2 =
          v * ∑ i, ∑ j, (uu s i * vv s j - uu s' i * vv s' j) ^ 2 := by
        simp only [hA, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_sub, mul_pow, Real.sq_sqrt hv]
      have e2 : ∑ k, (B s k - B s' k) ^ 2 =
          v * (∑ i, (uu s i - uu s' i) ^ 2 + ∑ j, (vv s j - vv s' j) ^ 2) := by
        simp only [hB, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add]
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;>
          exact Finset.sum_congr rfl fun i _ => by rw [← mul_sub, mul_pow, Real.sq_sqrt hv]
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h hv)
  refine hSF.trans ?_
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set R : ((Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ) → ℝ := fun ζ =>
    √v * ((∑ i : Fin p, ζ (Sum.inr (Sum.inl i)) ^ 2 + p) / (2 * √p) +
      (∑ j : Fin q, ζ (Sum.inr (Sum.inr j)) ^ 2 + q) / (2 * √q)) with hR
  have i1 : Integrable (fun ζ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ =>
      ∑ i : Fin p, ζ (Sum.inr (Sum.inl i)) ^ 2) (stdGauss _) :=
    integrable_finsetSum _ fun i _ => (coord_sq _).1
  have i2 : Integrable (fun ζ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ =>
      ∑ j : Fin q, ζ (Sum.inr (Sum.inr j)) ^ 2) (stdGauss _) :=
    integrable_finsetSum _ fun i _ => (coord_sq _).1
  have I1 : ∫ ζ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ,
      ∑ i : Fin p, ζ (Sum.inr (Sum.inl i)) ^ 2 ∂stdGauss _ = p := by
    rw [integral_finsetSum _ fun i _ => (coord_sq _).1]
    simp [(coord_sq _).2]
  have I2 : ∫ ζ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ,
      ∑ j : Fin q, ζ (Sum.inr (Sum.inr j)) ^ 2 ∂stdGauss _ = q := by
    rw [integral_finsetSum _ fun i _ => (coord_sq _).1]
    simp [(coord_sq _).2]
  have j1 : Integrable (fun ζ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ =>
      (∑ i : Fin p, ζ (Sum.inr (Sum.inl i)) ^ 2 + p) / (2 * √p)) (stdGauss _) :=
    (i1.add (integrable_const _)).div_const _
  have j2 : Integrable (fun ζ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ =>
      (∑ j : Fin q, ζ (Sum.inr (Sum.inr j)) ^ 2 + q) / (2 * √q)) (stdGauss _) :=
    (i2.add (integrable_const _)).div_const _
  have J1 : ∫ ζ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ,
      (∑ i : Fin p, ζ (Sum.inr (Sum.inl i)) ^ 2 + p) / (2 * √p) ∂stdGauss _ = √p := by
    rw [integral_div, integral_add i1 (integrable_const _), I1, integral_const]
    simp only [probReal_univ, one_smul]
    rw [div_eq_iff (by positivity)]
    nlinarith [Real.sq_sqrt hpR.le]
  have J2 : ∫ ζ : (Fin p × Fin q) ⊕ (Fin p ⊕ Fin q) → ℝ,
      (∑ j : Fin q, ζ (Sum.inr (Sum.inr j)) ^ 2 + q) / (2 * √q) ∂stdGauss _ = √q := by
    rw [integral_div, integral_add i2 (integrable_const _), I2, integral_const]
    simp only [probReal_univ, one_smul]
    rw [div_eq_iff (by positivity)]
    nlinarith [Real.sq_sqrt hqR.le]
  have iR : Integrable R (stdGauss _) := (j1.add j2).const_mul _
  have hRint : ∫ ζ, R ζ ∂stdGauss _ = √v * (√p + √q) := by
    simp only [hR]
    rw [integral_const_mul, integral_add j1 j2, J1, J2]
  rw [← hRint]
  refine integral_mono (sup_dot_integrable B) iR fun ζ => ?_
  refine Finset.sup'_le _ _ fun s _ => ?_
  rw [hBdot]
  simp only [hR]
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Real.sqrt_nonneg v)
  · exact (dot_le_norm (hu s) _).trans
      (sqrt_le_half (Finset.sum_nonneg fun _ _ => sq_nonneg _) hpR)
  · exact (dot_le_norm (hvv s) _).trans
      (sqrt_le_half (Finset.sum_nonneg fun _ _ => sq_nonneg _) hqR)

lemma bil_flat (v : ℝ) (u : Fin p → ℝ) (w : Fin q → ℝ) (ξ : Fin p × Fin q → ℝ) :
    (fun x : Fin p × Fin q => √v * (u x.1 * w x.2)) ⬝ᵥ ξ =
      u ⬝ᵥ (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ) *ᵥ w := by
  rw [bil_eq]
  simp only [dotProduct, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Gordon's bound**, in the standardized entries: `E opN(√v·ξ) ≤ √v·(√p + √q)`. -/
theorem opN_mean_std {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun ξ : Fin p × Fin q → ℝ =>
      opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ))
      (stdGauss (Fin p × Fin q)) ∧
    ∫ ξ : Fin p × Fin q → ℝ, opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ)
      ∂stdGauss (Fin p × Fin q) ≤ √v * (√p + √q) := by
  have hLip : EuLip (fun ξ : Fin p × Fin q → ℝ =>
      opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ)) (√v * 1) :=
    flat_euLip (g := opN) opN_lip hv
  have iop := (gaussConc_mgf_sharp (mul_nonneg (Real.sqrt_nonneg v) zero_le_one) hLip 0).1
  refine ⟨iop, ?_⟩
  have hR0 : 0 ≤ √v * (√(p : ℝ) + √(q : ℝ)) := by positivity
  by_cases hpq : p = 0 ∨ q = 0
  · simp only [opN_eq_zero hpq, integral_zero]
    exact hR0
  push Not at hpq
  have hp : 0 < p := Nat.pos_of_ne_zero hpq.1
  have hq : 0 < q := Nat.pos_of_ne_zero hpq.2
  set K : Set ((Fin p → ℝ) × (Fin q → ℝ)) :=
    {w | ∑ i, w.1 i ^ 2 = 1 ∧ ∑ j, w.2 j ^ 2 = 1} with hK
  have hKne : Nonempty K :=
    ⟨⟨(Pi.single ⟨0, hp⟩ 1, Pi.single ⟨0, hq⟩ 1), by simp [Pi.single_apply],
      by simp [Pi.single_apply]⟩⟩
  set d : ℕ → K := TopologicalSpace.denseSeq K with hd
  have hdd : DenseRange d := TopologicalSpace.denseRange_denseSeq K
  set a0 : ℕ → Fin p × Fin q → ℝ :=
    fun n x => √v * ((d n).1.1 x.1 * (d n).1.2 x.2) with ha0
  set X : ℕ → (Fin p × Fin q → ℝ) → ℝ := fun N ξ =>
    Finset.univ.sup' Finset.univ_nonempty (fun s : Fin (N + 1) => a0 s ⬝ᵥ ξ) with hX
  have ha0le : ∀ n ξ, a0 n ⬝ᵥ ξ ≤
      opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ) := by
    intro n ξ
    simp only [ha0]
    rw [bil_flat]
    exact bil_le_opN _ (d n).2.1 (d n).2.2
  have hXle : ∀ N ξ, X N ξ ≤
      opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ) :=
    fun N ξ => Finset.sup'_le _ _ fun s _ => ha0le s ξ
  have hXmono : ∀ ξ, Monotone fun N => X N ξ := by
    intro ξ N N' hNN
    refine Finset.sup'_le _ _ fun s _ => ?_
    have := Finset.le_sup' (fun s : Fin (N' + 1) => a0 s ⬝ᵥ ξ)
      (Finset.mem_univ (Fin.castLE (Nat.succ_le_succ hNN) s))
    simpa using this
  have hXlub : ∀ ξ, IsLUB (Set.range fun N => X N ξ)
      (opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ)) := by
    intro ξ
    refine ⟨?_, ?_⟩
    · rintro _ ⟨N, rfl⟩
      exact hXle N ξ
    · intro b hb
      by_contra hlt
      push Not at hlt
      set M : Matrix (Fin p) (Fin q) ℝ := Matrix.of fun i j => √v * ξ (i, j) with hM
      have hne : (opSet M).Nonempty :=
        ⟨_, (hKne.some).1.1, (hKne.some).1.2, (hKne.some).2.1, (hKne.some).2.2, rfl⟩
      obtain ⟨x, ⟨u, w, hu, hw, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hne hlt
      have hcont : Continuous fun k : K => k.1.1 ⬝ᵥ M *ᵥ k.1.2 := by
        simp only [bil_eq]
        fun_prop
      have hO : IsOpen {k : K | b < k.1.1 ⬝ᵥ M *ᵥ k.1.2} := isOpen_lt continuous_const hcont
      obtain ⟨n, hn⟩ := hdd.exists_mem_open hO ⟨⟨(u, w), hu, hw⟩, hx⟩
      have h1 : b < a0 n ⬝ᵥ ξ := by
        simp only [ha0]
        rw [bil_flat]
        exact hn
      have h2 : a0 n ⬝ᵥ ξ ≤ X n ξ := by
        have := Finset.le_sup' (fun s : Fin (n + 1) => a0 s ⬝ᵥ ξ) (Finset.mem_univ (Fin.last n))
        simpa using this
      have h3 := hb ⟨n, rfl⟩
      simp only at h3
      linarith
  have hXint : ∀ N, Integrable (X N) (stdGauss (Fin p × Fin q)) := fun N =>
    sup_dot_integrable (fun s : Fin (N + 1) => a0 s)
  have hlim := integral_tendsto_of_tendsto_of_monotone hXint iop (ae_of_all _ hXmono)
    (ae_of_all _ fun ξ => tendsto_atTop_isLUB (hXmono ξ) (hXlub ξ))
  refine le_of_tendsto' hlim fun N => ?_
  exact gordon_fin hv hp hq (fun s : Fin (N + 1) => (d s).1.1) (fun s : Fin (N + 1) => (d s).1.2)
    (fun s => (d s).2.1) (fun s => (d s).2.2)

/-- `opN` is continuous. -/
lemma opN_continuous : Continuous (opN : Matrix (Fin p) (Fin q) ℝ → ℝ) :=
  BstLean.Part148.matLip_continuous opN_lip

/-- **Gordon's bound for the operator norm of a Gaussian matrix**: for a `p × q` matrix `M` with
independent `N(0, v)` entries: `E opN M ≤ √v·(√p + √q)`. -/
theorem opN_mean_le {v : ℝ} (hv : 0 ≤ v) :
    Integrable (opN : Matrix (Fin p) (Fin q) ℝ → ℝ) (gaussMat p q v) ∧
    ∫ M, opN M ∂gaussMat p q v ≤ √v * (√p + √q) := by
  obtain ⟨hi, hm⟩ := opN_mean_std (p := p) (q := q) hv
  have mT : Measurable (fun ξ : Fin p × Fin q → ℝ =>
      (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ)) := measurable_ofFlat _
  constructor
  · exact (integrable_map_measure (μ := stdGauss (Fin p × Fin q))
      opN_continuous.measurable.aestronglyMeasurable mT.aemeasurable).mpr hi
  · have eI : ∫ M, opN M ∂gaussMat p q v = ∫ ξ : Fin p × Fin q → ℝ,
        opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin p) (Fin q) ℝ)
          ∂stdGauss (Fin p × Fin q) := by
      unfold gaussMat
      exact integral_map mT.aemeasurable opN_continuous.measurable.aestronglyMeasurable
    rw [eI]
    exact hm

/-- **The upper tail of the operator norm of a Gaussian matrix**:
`Pr(opN M ≥ √v·(√p + √q) + t) ≤ exp(−t²/(2v))` for `t ≥ 0`. -/
theorem opN_tail {v : ℝ} (hv : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t) :
    (gaussMat p q v).real {M : Matrix (Fin p) (Fin q) ℝ | √v * (√p + √q) + t ≤ opN M} ≤
      Real.exp (-t ^ 2 / (2 * v)) := by
  have h := gaussConc_mat_upper_sharp (g := (opN : Matrix (Fin p) (Fin q) ℝ → ℝ)) zero_le_one
    opN_lip hv ht
  rw [one_pow, mul_one] at h
  refine le_trans (measureReal_mono (fun M hM => ?_)) h
  simp only [mem_ofPred_eq] at hM ⊢
  linarith [(opN_mean_le (p := p) (q := q) hv).2]

/-- The same in the form of the paper: `opN M ≤ √v·(√p + √q + u)` except with probability
`exp(−u²/2)`. -/
theorem opN_tail' {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 ≤ u) :
    (gaussMat p q v).real {M : Matrix (Fin p) (Fin q) ℝ | √v * (√p + √q + u) ≤ opN M} ≤
      Real.exp (-u ^ 2 / 2) := by
  have h := opN_tail (p := p) (q := q) hv.le (t := √v * u) (by positivity)
  have e : -(√v * u) ^ 2 / (2 * v) = -u ^ 2 / 2 := by
    rw [mul_pow, Real.sq_sqrt hv.le]
    field_simp
  rw [e] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext M
  simp only [mem_ofPred_eq]
  constructor <;> intro h <;> linarith

end gordon

end BstLean.Part152

open BstLean.Part152 in
#print axioms opN_mean_le
open BstLean.Part152 in
#print axioms opN_tail'
open BstLean.Part152 in
#print axioms mulVec_le_opN
