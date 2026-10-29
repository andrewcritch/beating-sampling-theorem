import BstLean.Part162LG

/-!
# Part 162, items 1 and 2 (bridge): the tangential gradient is `(1 − s²)|P_lat ∇Φ|²`

Role: `delegations/statements/p162-spec.md`, items 1 and 2. Do not use `sorry`, `native_decide`
or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:LS` (the lift has
gradient `√(1−s²)P_lat∇φ/|H|`) and Proposition `t7:p07:LG` (`Ψ_φ = (1 − s²)|P_lat ∇_x φ|²`).
This file connects the Lean quantity `tanSq` (used by `ls_lat`, `ls_lat_mom`, `psiA`) to the
paper's `Ψ_φ`, the quantity that Lemma LJ bounds.

* `dirW c e = H(0, e)`, `dirWL`: the direction isometry onto `u^⊥`; `xLatH_split`:
  `xLatH c s v = (s|v|)u + √(1 − s²)W v`.
* **`tanSq_eq`**: `T = (1 − s²)(Σ_j D(W e_j)² − (Σ_j v̂_j D(W e_j))²)`, `D = DΦ(y)`.
* `sum_dirW_sq`: Parseval in the frame `u, W e_1, …, W e_{n−1}`.
* **`tanSq_eq_proj`**: `T = (1 − s²)(|∇Φ(y)|² − ⟨∇Φ(y), u⟩² − ⟨∇Φ(y), W v̂⟩²)`, i.e.
  `(1 − s²)|P_lat ∇Φ(y)|²` with `P_lat` the projection onto `span(u, x)^⊥`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real Filter Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg e0)
open BstLean.Part157
open BstLean.Part161
open BstLean.Part151 (gradSq)
open BstLean.Part53 (unitF53 radF53)

variable {n : ℕ}

/-- The direction map `W e = H(0, e)` (an isometry of `ℝ^{n−1}` onto `u^⊥`). -/
noncomputable def dirW (c : Ret n) (e : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  (hhMat (uHat c)).mulVec (consV 0 e)

lemma consV_zero_add (e e' : Fin (n - 1) → ℝ) :
    consV (n := n) 0 (e + e') = consV 0 e + consV 0 e' := by
  rw [← consV_add]; simp

lemma consV_zero_smul (t : ℝ) (e : Fin (n - 1) → ℝ) :
    consV (n := n) 0 (t • e) = t • consV 0 e := by
  rw [← consV_smul]; simp

/-- `W` as a continuous linear map. -/
noncomputable def dirWL (c : Ret n) : (Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := dirW c
      map_add' := fun e e' => by unfold dirW; rw [consV_zero_add, Matrix.mulVec_add]
      map_smul' := fun t e => by unfold dirW; rw [consV_zero_smul, Matrix.mulVec_smul]; rfl }

lemma dirWL_apply (c : Ret n) (e : Fin (n - 1) → ℝ) : dirWL c e = dirW c e := rfl

/-- `xLatH c s v = (s|v|)·u + √(1 − s²)·W v`. -/
lemma xLatH_split (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) (s : ℝ) (v : Fin (n - 1) → ℝ) :
    xLatH c s v = (s * radF53 v) • uHat c + √(1 - s ^ 2) • dirW c v := by
  unfold xLatH dirW
  have e : consV (n := n) (s * radF53 v) (√(1 - s ^ 2) • v) =
      (s * radF53 v) • e0 n + √(1 - s ^ 2) • consV 0 v := by
    rw [← consV_one_zero, ← consV_smul, ← consV_smul, ← consV_add]
    simp
  rw [e, Matrix.mulVec_add, hh_smul, hh_smul, hh_e0 hn (normSq_uHat hc)]

/-- **The squared tangential gradient in the coordinates of the latitude frame.** For `v ≠ 0`,
`Φ` positively 1-homogeneous and differentiable at `y = xLatH c s v`, with `D = DΦ(y)`,
`h_j = D(W e_j)`, `v̂ = v/|v|`:
`T = (1 − s²)·(Σ_j h_j² − (Σ_j v̂_j h_j)²)`. Here `Σ_j h_j²` is the squared norm of the
projection of `∇Φ(y)` on `u^⊥` and `Σ_j v̂_j h_j = ⟨∇Φ(y), W v̂⟩`, so the bracket is
`|P_lat ∇Φ(y)|²` (the paper's `Ψ_φ = (1 − s²)|P_lat ∇φ|²`). -/
theorem tanSq_eq (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    {Φ : (Fin n → ℝ) → ℝ} (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) (hd : DifferentiableAt ℝ Φ (xLatH c s v)) :
    tanSq Φ c s v = (1 - s ^ 2) *
      (∑ j, (fderiv ℝ Φ (xLatH c s v) (dirW c (Pi.single j 1))) ^ 2 -
        (∑ j, unitF53 v j * fderiv ℝ Φ (xLatH c s v) (dirW c (Pi.single j 1))) ^ 2) := by
  classical
  set y := xLatH c s v with hy
  set Dy := fderiv ℝ Φ y with hDy
  set u := uHat c
  set r := radF53 v with hr
  have rp : 0 < r := radF_pos hv
  set a := √(1 - s ^ 2) with ha
  have ha2 : a ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by linarith)
  set Gu := Dy u
  set h : Fin (n - 1) → ℝ := fun j => Dy (dirW c (Pi.single j 1)) with hh
  -- the derivative of `xLatH c s` at `v`
  have hX : HasFDerivAt (xLatH c s)
      ((s • fderiv ℝ radF53 v).smulRight u + a • dirWL c) v := by
    have e : xLatH c s = fun w => (s * radF53 w) • u + a • dirWL c w := by
      funext w; rw [xLatH_split hn hc, dirWL_apply]
    rw [e]
    have h1 : HasFDerivAt (fun w => s * radF53 w) (s • fderiv ℝ radF53 v) v :=
      ((hasFDerivAt_radF hv).differentiableAt.hasFDerivAt).const_mul s
    have h2 := h1.smul_const u
    have h3 : HasFDerivAt (fun w => a • dirWL c w) (a • dirWL c) v :=
      ((dirWL c).hasFDerivAt).const_smul a
    exact h2.add h3
  have hF : HasFDerivAt (fun w => Φ (xLatH c s w))
      (Dy.comp ((s • fderiv ℝ radF53 v).smulRight u + a • dirWL c)) v :=
    hd.hasFDerivAt.comp v hX
  have hpart : ∀ j, fderiv ℝ (fun w => Φ (xLatH c s w)) v (Pi.single j 1) =
      s * (v j / r) * Gu + a * h j := fun j => by
    rw [hF.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      fderiv_radF_single hv, map_add, map_smul, dirWL_apply, hh]
    ring
  -- Euler at `y` and the value of `Φ` at the point of the sphere
  have hE := euler (H₁ := Φ) hhom hd
  have hyx : y = radF53 v • xLat c s (unitF53 v) := xLatH_eq c s v
  have hW : Dy (dirW c v) = ∑ j, v j * h j := by
    have := clm_apply_sum (Dy.comp (dirWL c)) v
    simpa [dirWL_apply] using this
  have h2a : Dy y = (s * radF53 v) * Dy u + √(1 - s ^ 2) * ∑ j, v j * h j := by
    rw [hy, xLatH_split hn hc, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hW]
  have hsu : ∑ j, unitF53 v j * h j = (∑ j, v j * h j) / radF53 v := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [unitF53, Pi.smul_apply, smul_eq_mul, radF53]
    ring
  have hval : Φ (xLat c s (unitF53 v)) = s * Gu + a * ∑ j, unitF53 v j * h j := by
    have h1 : Φ y = radF53 v * Φ (xLat c s (unitF53 v)) := by rw [hyx]; exact hhom _ _ rp
    have h3 : Φ y = Dy y := hE.symm
    rw [h1, h2a] at h3
    rw [hsu]
    have hr0 : radF53 v ≠ 0 := rp.ne'
    field_simp
    linear_combination h3
  -- assemble
  have hs1 : ∑ j, unitF53 v j ^ 2 = 1 := by
    have := radF_unitF hv
    rw [radF_eq_norm, EuclideanSpace.norm_eq] at this
    have h2 : √(∑ j, ‖(WithLp.toLp 2 (unitF53 v) : EuclideanSpace ℝ (Fin (n - 1))) j‖ ^ 2) ^ 2 = 1 := by
      rw [this]; norm_num
    rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] at h2
    simpa [Real.norm_eq_abs, sq_abs] using h2
  have hu : ∀ j, v j / r = unitF53 v j := fun j => by
    simp only [unitF53, Pi.smul_apply, smul_eq_mul, hr, radF53]; ring
  unfold tanSq gradSq
  simp_rw [hpart, hu]
  rw [hval]
  have e1 : ∑ j, (s * unitF53 v j * Gu + a * h j) ^ 2 =
      s ^ 2 * Gu ^ 2 * ∑ j, unitF53 v j ^ 2 + 2 * s * a * Gu * ∑ j, unitF53 v j * h j +
        a ^ 2 * ∑ j, h j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1, hs1, ha2]
  simp only [hh]
  linear_combination (-(∑ j, unitF53 v j * Dy (dirW c (Pi.single j 1))) ^ 2) * ha2

lemma consV_eq_cons' (k : ℕ) (z : ℝ) (g : Fin k → ℝ) :
    consV (n := k + 1) z g = (Fin.cons z g : Fin (k + 1) → ℝ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consV]
  · simp only [consV, Fin.val_succ, Nat.succ_ne_zero, dite_false, Fin.cons_succ,
      Nat.add_sub_cancel]
    rfl

/-- **Parseval in the latitude frame**: `Σ_j D(W e_j)² = |∇Φ|² − D(u)²` for a linear form `D`
(the frame `u, W e_1, …, W e_{n−1}` is orthonormal). -/
lemma sum_dirW_sq (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) (Dy : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∑ j, (Dy (dirW c (Pi.single j 1))) ^ 2 =
      ∑ i, (Dy (Pi.single i 1)) ^ 2 - (Dy (uHat c)) ^ 2 := by
  classical
  set g : Fin n → ℝ := fun i => Dy (Pi.single i 1) with hg
  set q := (hhMat (uHat c)).mulVec g with hq
  have hD : ∀ z, Dy z = ∑ i, z i * g i := fun z => clm_apply_sum Dy z
  have hHz : ∀ z, Dy ((hhMat (uHat c)).mulVec z) = ∑ k, z k * q k := fun z => by
    rw [hD]
    simp only [hq, Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hh_symm (uHat c) i k]; ring
  have hu : Dy (uHat c) = q ⟨0, by omega⟩ := by
    rw [← hh_e0 hn (normSq_uHat hc), hHz]
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · simp [e0]
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [e0, this]
    · simp
  have hnorm : ∑ i, g i ^ 2 = ∑ i, q i ^ 2 := by
    have := hh_normSq (uHat c) g
    unfold normSq at this
    rw [← this]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hW : ∀ j : Fin k, Dy (dirW c (Pi.single j 1)) = q j.succ := fun j => by
    unfold dirW
    rw [hHz]
    change ∑ i, consV (n := k + 1) 0 (Pi.single j 1) i * q i = q j.succ
    rw [consV_eq_cons', Fin.sum_univ_succ]
    simp only [Fin.cons_zero, zero_mul, Fin.cons_succ, zero_add]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  simp_rw [hW]
  have hg' : ∑ i, Dy (Pi.single i 1) ^ 2 = ∑ i, g i ^ 2 := rfl
  rw [hu, hg', hnorm, Fin.sum_univ_succ]
  simp

/-- **The squared tangential gradient is `(1 − s²)|P_lat ∇Φ|²`**: for `v ≠ 0`, `Φ` positively
1-homogeneous and differentiable at `y = xLatH c s v`, with `g = ∇Φ(y)`, `u` the unit World
centre and `w = W(v/|v|)` (the unit vector of `span(u, x)` orthogonal to `u`):
`T = (1 − s²)·(|g|² − ⟨g, u⟩² − ⟨g, w⟩²)`. -/
theorem tanSq_eq_proj (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    {Φ : (Fin n → ℝ) → ℝ} (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) (hd : DifferentiableAt ℝ Φ (xLatH c s v)) :
    tanSq Φ c s v = (1 - s ^ 2) *
      (∑ i, (fderiv ℝ Φ (xLatH c s v) (Pi.single i 1)) ^ 2 -
        (fderiv ℝ Φ (xLatH c s v) (uHat c)) ^ 2 -
        (fderiv ℝ Φ (xLatH c s v) (dirW c (unitF53 v))) ^ 2) := by
  rw [tanSq_eq hn hc hs hhom hv hd, sum_dirW_sq hn hc]
  have hw : fderiv ℝ Φ (xLatH c s v) (dirW c (unitF53 v)) =
      ∑ j, unitF53 v j * fderiv ℝ Φ (xLatH c s v) (dirW c (Pi.single j 1)) := by
    have := clm_apply_sum ((fderiv ℝ Φ (xLatH c s v)).comp (dirWL c)) (unitF53 v)
    simpa [dirWL_apply] using this
  rw [hw]

end BstLean.Part162

open BstLean.Part162 in
#print axioms tanSq_eq_proj
