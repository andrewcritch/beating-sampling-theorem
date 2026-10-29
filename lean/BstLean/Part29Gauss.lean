import Mathlib

/-!
# Part 29, layer L4 (in part): the Gaussian quadratic-form bound

`proofs/option-m/29-explicit-22-at-100.tex`, Lemma (exact normalization): for standard Gaussian `Z` and the
trace-free matrix `A − (tr A / D) I`, `E T_A² ≤ 2 ‖A‖_F²`. Here the Gaussian moments up to degree four are a
hypothesis (`GaussMoments`); `gaussMoments_std` discharges it for the standard Gaussian product measure.
-/

namespace BstLean.Part29

open MeasureTheory ProbabilityTheory

variable {D : ℕ}

/-- Standard Gaussian moments up to degree four, with integrability. -/
structure GaussMoments (D : ℕ) (ν : Measure (Fin D → ℝ)) : Prop where
  int2 : ∀ i j, Integrable (fun z : Fin D → ℝ => z i * z j) ν
  int4 : ∀ i j k l, Integrable (fun z : Fin D → ℝ => z i * z j * z k * z l) ν
  m2 : ∀ i j, ∫ z, z i * z j ∂ν = if i = j then 1 else 0
  m4 : ∀ i j k l, ∫ z, z i * z j * z k * z l ∂ν =
    (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0)

/-- The quadratic form `zᵀ B z`. -/
def qform (B : Matrix (Fin D) (Fin D) ℝ) (z : Fin D → ℝ) : ℝ := ∑ i, ∑ j, B i j * z i * z j

/-- `E (Zᵀ B Z)² = (tr B)² + 2 ‖B‖_F²` for symmetric `B`. -/
theorem gauss_qform_sq (ν : Measure (Fin D → ℝ)) (hν : GaussMoments D ν)
    (B : Matrix (Fin D) (Fin D) ℝ) (hB : B.IsSymm) :
    ∫ z, qform B z ^ 2 ∂ν = (∑ i, B i i) ^ 2 + 2 * ∑ i, ∑ j, B i j ^ 2 := by
  classical
  have hi (i j k l : Fin D) : Integrable
      (fun z => (B i j * B k l) * (z i * z j * z k * z l)) ν :=
    (hν.int4 i j k l).const_mul _
  have hex (z : Fin D → ℝ) : qform B z ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (B i j * B k l) * (z i * z j * z k * z l) := by
    simp only [qform, pow_two, Finset.sum_mul, Finset.mul_sum]
    congr 1
    ext i
    congr 1
    ext j
    congr 1
    ext k
    congr 1
    ext l
    ring
  have he : (∫ z, qform B z ^ 2 ∂ν) =
      ∑ i, ∑ j, ∑ k, ∑ l, (B i j * B k l) *
        ((if i = j ∧ k = l then 1 else 0) +
         (if i = k ∧ j = l then 1 else 0) +
         (if i = l ∧ j = k then 1 else 0)) := by
    simp_rw [hex]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro k _
          rw [integral_finsetSum]
          · simp_rw [integral_const_mul, hν.m4]
          · intro l _; exact hi i j k l
        · intro k _; exact integrable_finsetSum _ (fun l _ => hi i j k l)
      · intro j _
        exact integrable_finsetSum _ (fun k _ =>
          integrable_finsetSum _ (fun l _ => hi i j k l))
    · intro i _
      exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
        integrable_finsetSum _ (fun l _ => hi i j k l)))
  rw [he]
  simp only [mul_add, Finset.sum_add_distrib]
  simp [ite_and, mul_ite, Finset.mul_sum, Finset.sum_mul, hB.apply, pow_two]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

private lemma center_sum (A : Matrix (Fin D) (Fin D) ℝ) (c : ℝ) :
    (∑ i, ∑ j, (A - c • (1 : Matrix (Fin D) (Fin D) ℝ)) i j ^ 2) =
      (∑ i, ∑ j, A i j ^ 2) - 2 * c * (∑ i, A i i) + D * c ^ 2 := by
  classical
  have hp (i j : Fin D) :
      (A - c • (1 : Matrix (Fin D) (Fin D) ℝ)) i j ^ 2 =
        A i j ^ 2 + if i = j then -2 * c * A i i + c ^ 2 else 0 := by
    by_cases h : i = j
    · subst j
      simp [Matrix.sub_apply, Matrix.smul_apply]
      ring
    · simp [Matrix.sub_apply, Matrix.smul_apply, h]
  simp_rw [hp, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Centring by the trace does not increase the Frobenius norm:
`‖A − (tr A / D) I‖_F² = ‖A‖_F² − (tr A)² / D ≤ ‖A‖_F²`. -/
theorem frob_center_le (hD : 0 < D) (A : Matrix (Fin D) (Fin D) ℝ) :
    ∑ i, ∑ j, (A - ((∑ k, A k k) / D) • (1 : Matrix (Fin D) (Fin D) ℝ)) i j ^ 2 ≤
      ∑ i, ∑ j, A i j ^ 2 := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  rw [center_sum]
  have hpos : 0 ≤ (∑ k, A k k) ^ 2 / (D : ℝ) :=
    div_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le D)
  have hid : -2 * ((∑ k, A k k) / D) * (∑ k, A k k) +
      D * ((∑ k, A k k) / D) ^ 2 = -((∑ k, A k k) ^ 2 / D) := by
    field_simp
    ring
  nlinarith [hid]

/-- **The bound used by part 29:** for symmetric `A` and standard Gaussian moments,
`E (Zᵀ (A − (tr A / D) I) Z)² ≤ 2 ‖A‖_F²`. -/
theorem gauss_centred_sq_le (hD : 0 < D) (ν : Measure (Fin D → ℝ)) (hν : GaussMoments D ν)
    (A : Matrix (Fin D) (Fin D) ℝ) (hA : A.IsSymm) :
    ∫ z, qform (A - ((∑ k, A k k) / D) • (1 : Matrix (Fin D) (Fin D) ℝ)) z ^ 2 ∂ν ≤
      2 * ∑ i, ∑ j, A i j ^ 2 := by
  classical
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hs : (A - ((∑ k, A k k) / D) • (1 : Matrix (Fin D) (Fin D) ℝ)).IsSymm :=
    hA.sub (Matrix.isSymm_one.smul _)
  rw [gauss_qform_sq ν hν _ hs]
  have ht : (∑ i, (A - ((∑ k, A k k) / D) •
      (1 : Matrix (Fin D) (Fin D) ℝ)) i i) = 0 := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [ht]
  have hb := frob_center_le hD A
  nlinarith

section StdGauss

open Real

private noncomputable def gM (n : ℕ) : ℝ := ∫ x, x ^ n ∂(gaussianReal 0 1)

private lemma g_hd (p p' : ℝ → ℝ) (hp : ∀ t, HasDerivAt p (p' t) t) :
    deriv (fun t => p t * rexp (t ^ 2 / 2)) = fun t => (p' t + p t * t) * rexp (t ^ 2 / 2) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    have := (hasDerivAt_pow 2 t).div_const 2
    convert this using 1; ring
  have := (hp t).mul h1.exp
  rw [show (fun t => p t * rexp (t^2/2)) = p * fun x => rexp (x^2/2) from rfl, this.deriv]
  ring

private lemma gM_eq (n : ℕ) : gM n = iteratedDeriv n (fun t => rexp (t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) n
  rw [mgf_fun_id_gaussianReal] at h
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul] at h
  rw [h]; rfl

private lemma hpoly (a b c d e : ℝ) (t : ℝ) :
    HasDerivAt (fun t => a + b * t + c * t ^ 2 + d * t ^ 3 + e * t ^ 4)
      (b + 2 * c * t + 3 * d * t ^ 2 + 4 * e * t ^ 3) t := by
  have h := (((((hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b)).add
    ((hasDerivAt_pow 2 t).const_mul c)).add ((hasDerivAt_pow 3 t).const_mul d)).add
    ((hasDerivAt_pow 4 t).const_mul e))
  convert h using 1
  · funext x; simp
  · push_cast; ring

private lemma step (a b c d e : ℝ) :
    deriv (fun t => (a + b * t + c * t ^ 2 + d * t ^ 3 + e * t ^ 4) * rexp (t ^ 2 / 2)) =
    fun t => (b + (a + 2 * c) * t + (b + 3 * d) * t ^ 2 + (c + 4 * e) * t ^ 3 + d * t ^ 4 + e * t ^ 5) * rexp (t ^ 2 / 2) := by
  rw [g_hd _ _ (hpoly a b c d e)]
  funext t; ring

private noncomputable def gq (a b c d e : ℝ) : ℝ → ℝ :=
  fun t => (a + b * t + c * t ^ 2 + d * t ^ 3 + e * t ^ 4) * rexp (t ^ 2 / 2)

private lemma gstep (a b c d e : ℝ) (he : e = 0) :
    deriv (gq a b c d e) = gq b (a + 2 * c) (b + 3 * d) (c + 4 * e) d := by
  unfold gq; rw [step]; funext t; subst he; ring

private lemma gid : ∀ n : ℕ, n ≤ 4 → iteratedDeriv n (fun t => rexp (t ^ 2 / 2)) =
    gq (if n = 0 then 1 else if n = 2 then 1 else if n = 4 then 3 else 0)
       (if n = 1 then 1 else if n = 3 then 3 else 0)
       (if n = 2 then 1 else if n = 4 then 6 else 0)
       (if n = 3 then 1 else 0) (if n = 4 then 1 else 0) := by
  intro n hn
  induction n with
  | zero => simp only [iteratedDeriv_zero]; unfold gq; funext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih (by omega), gstep _ _ _ _ _ (by simp [show n ≠ 4 by omega])]
    have h3 : n ≤ 3 := by omega
    interval_cases n <;> norm_num

private lemma gM_val (n : ℕ) (hn : n ≤ 4) : gM n =
    if n = 0 then 1 else if n = 2 then 1 else if n = 4 then 3 else 0 := by
  rw [gM_eq, gid n hn]; unfold gq; simp


private lemma g_int (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) n

private lemma pi_mono (c : Fin D → ℕ) :
    Integrable (fun z : Fin D → ℝ => ∏ m, z m ^ c m) (Measure.pi fun _ : Fin D => gaussianReal 0 1) ∧
    ∫ z, ∏ m, z m ^ c m ∂(Measure.pi fun _ : Fin D => gaussianReal 0 1) = ∏ m, gM (c m) :=
  ⟨Integrable.fintype_prod (f := fun m x => x ^ c m) (fun m => g_int (c m)),
   integral_fintype_prod_eq_prod (f := fun m x => x ^ c m)⟩

private def cnt (l : List (Fin D)) (m : Fin D) : ℕ := (l.map fun i => if m = i then 1 else 0).sum

private lemma prod_cnt (l : List (Fin D)) (z : Fin D → ℝ) :
    ∏ m, z m ^ cnt l m = (l.map z).prod := by
  induction l with
  | nil => simp [cnt]
  | cons a l ih =>
    simp only [cnt, List.map_cons, List.sum_cons, pow_add, Finset.prod_mul_distrib] at ih ⊢
    rw [ih]; simp [pow_ite]

private lemma cnt_le (l : List (Fin D)) (m : Fin D) : cnt l m ≤ l.length := by
  induction l with
  | nil => simp [cnt]
  | cons a l ih => simp only [cnt, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; split_ifs <;> omega

private lemma prod_gM (l : List (Fin D)) :
    ∏ m, gM (cnt l m) = ∏ m ∈ l.toFinset, gM (cnt l m) := by
  classical
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro m _ hm
  have : cnt l m = 0 := by
    simp only [List.mem_toFinset] at hm
    unfold cnt
    rw [List.sum_eq_zero]
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [ite_eq_right_iff.mpr]; rintro rfl; exact absurd ha hm
  rw [this, gM_val 0 (by omega)]; simp

private lemma mom (l : List (Fin D)) (hl : l.length ≤ 4) :
    ∫ z, (l.map z).prod ∂(Measure.pi fun _ : Fin D => gaussianReal 0 1) =
      ∏ m ∈ l.toFinset, (if cnt l m = 0 then 1 else if cnt l m = 2 then 1 else if cnt l m = 4 then 3 else 0) := by
  have h := (pi_mono (cnt l)).2
  simp only [prod_cnt] at h
  rw [h, prod_gM]
  apply Finset.prod_congr rfl
  intro m _
  exact gM_val _ ((cnt_le l m).trans hl)

private lemma std_m2 (i j : Fin D) : ∫ z, z i * z j ∂(Measure.pi fun _ : Fin D => gaussianReal 0 1) = if i = j then 1 else 0 := by
  have h := mom [i, j] (by simp)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [h]
  by_cases hij : i = j
  · subst hij; simp [cnt]
  · simp [cnt, hij, Ne.symm hij, Finset.prod_insert]

set_option maxHeartbeats 4000000 in
private lemma std_m4 (i j k l : Fin D) : ∫ z, z i * z j * z k * z l ∂(Measure.pi fun _ : Fin D => gaussianReal 0 1) =
    (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) := by
  have h := mom [i, j, k, l] (by simp)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc] at h
  rw [h]
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    subst_vars <;> (try have := Ne.symm hij) <;> (try have := Ne.symm hik) <;> (try have := Ne.symm hil) <;> (try have := Ne.symm hjk) <;> (try have := Ne.symm hjl) <;> (try have := Ne.symm hkl) <;> (simp_all [cnt, Finset.prod_insert] <;> norm_num)

end StdGauss

/-- Stretch goal: the standard Gaussian product measure has these moments. -/
theorem gaussMoments_std : GaussMoments D (Measure.pi fun _ : Fin D => gaussianReal 0 1) := by
  refine ⟨fun i j => ?_, fun i j k l => ?_, fun i j => std_m2 i j, fun i j k l => std_m4 i j k l⟩
  · have h := (pi_mono (cnt [i, j])).1
    simp only [prod_cnt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    exact h
  · have h := (pi_mono (cnt [i, j, k, l])).1
    simp only [prod_cnt, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ← mul_assoc] at h
    exact h

end BstLean.Part29
