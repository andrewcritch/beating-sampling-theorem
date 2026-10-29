import BstLean.Part143HidC

/-!
# Part 143, helper `hidK`, file `HidC2`: the computed centre with the sharper row moment

The conditional variances over `M₂` of `T̂(u)` and of `t|b̂|²` (Parts 137, 140) with the row
bound `E ReLU(a)²ReLU(b)² ≤ v²(|h|²|h′|² + 2⟨h, h′⟩²)/2` (`row_relu_four_le`) in place of
`(3/2)·v²|h|²|h′|²`.

* `rowPair143`, `rows_var_le`, `smooth_row143`, `sq_row143`.
* `That_cond143`: `E_{M₂}(T̂(u) − Ψ)² ≤ (2/m)(α(u)Γ* + 2C²)`, `C = t⟨h₁(u), h̄₁⟩`.
* `bhatNorm_cond143`: `E_{M₂}(t|b̂|² − Ψ_B)² ≤ (2/m)(Γ*² + 2Q²)`, `Q = t|h̄₁|²`.
* `hatFluct143_pt`, `bhatNorm_L2_143`, `Xh_L2_143`, `dist2_L2_143s` (constants `cHat143`,
  `cB143`, `cDst143s`).
* `goodHatExtra143s`, `goodHat_compl143s`: for `n ≥ 16384`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part140 hiding dotp_self

/-! ## Rows -/

/-- One Gaussian row `w = √v·ξ`: `E (ReLU(⟨w, h⟩)ReLU(⟨w, h′⟩))² ≤ v²(|h|²|h′|² + 2⟨h, h′⟩²)/2`. -/
lemma rowPair143 {K : ℕ} {v : ℝ} (hv : 0 ≤ v) (h h' : Fin K → ℝ) :
    Integrable (fun ξ : Fin K → ℝ => (relu (∑ j, (√v • ξ) j * h j) *
      relu (∑ j, (√v • ξ) j * h' j)) ^ 2) (stdGauss (Fin K)) ∧
    ∫ ξ : Fin K → ℝ, (relu (∑ j, (√v • ξ) j * h j) * relu (∑ j, (√v • ξ) j * h' j)) ^ 2
      ∂stdGauss (Fin K) ≤ v ^ 2 * (normSq h * normSq h' + 2 * dotp h h' ^ 2) / 2 := by
  let f : (Fin K → ℝ) → ℝ := fun w => relu (∑ j, w j * h j) * relu (∑ j, w j * h' j)
  have hf : Measurable f :=
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).mul_const _)).mul
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _))
  have key : (fun M : Matrix (Fin 1) (Fin K) ℝ => f (rowOf 0 M) ^ 2) =
      fun M => normSq (reluV (M.mulVec h)) * normSq (reluV (M.mulVec h')) := by
    funext M
    rw [normSq_reluV_one, normSq_reluV_one]
    simp only [f, rowOf]
    rw [mul_pow]
    rfl
  obtain ⟨hRR, hbound⟩ := row_relu_four_le hv h h'
  rw [← key] at hRR hbound
  have hf2 : Integrable (fun ξ => f (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin K)) :=
    (row_integrable_iff (m := 1) v (0 : Fin 1) (hf.pow_const 2)).mp hRR
  have e : ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin K) =
      ∫ M : Matrix (Fin 1) (Fin K) ℝ, f (rowOf 0 M) ^ 2 ∂gaussMat 1 K v :=
    (row_integral (m := 1) v (0 : Fin 1) (hf.pow_const 2)).symm
  exact ⟨hf2, e.trans_le hbound⟩

/-- The variance of a sum of one function of each row, from a bound of the second moment of
one row. -/
lemma rows_var_le {m k : ℕ} (v : ℝ) (f : (Fin k → ℝ) → ℝ) (hf : Measurable f) {c X : ℝ}
    (i1 : Integrable (fun ξ => f (√v • ξ)) (stdGauss (Fin k)))
    (e1 : ∫ ξ, f (√v • ξ) ∂stdGauss (Fin k) = c)
    (i2 : Integrable (fun ξ => f (√v • ξ) ^ 2) (stdGauss (Fin k)))
    (u2 : ∫ ξ, f (√v • ξ) ^ 2 ∂stdGauss (Fin k) ≤ X) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, f (rowOf i M) - (m : ℝ) * c) ^ 2)
      (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (∑ i, f (rowOf i M) - (m : ℝ) * c) ^ 2 ∂gaussMat m k v ≤
      (m : ℝ) * X := by
  have hrow : ∀ i : Fin m, Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => f (rowOf i M))
      (gaussMat m k v) := fun i => (row_integrable_iff (m := m) v i hf).mpr i1
  have iS : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => ∑ i, f (rowOf i M))
      (gaussMat m k v) := integrable_finsetSum _ fun i _ => hrow i
  have eS : ∫ M : Matrix (Fin m) (Fin k) ℝ, ∑ i, f (rowOf i M) ∂gaussMat m k v =
      (m : ℝ) * c := by
    rw [integral_finsetSum _ fun i _ => hrow i]
    simp_rw [row_integral (m := m) v _ hf, e1]
    simp
  obtain ⟨iQ, eQ⟩ := rows_sum_sq (m := m) v f hf i2
  rw [e1] at eQ
  have hexp : (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, f (rowOf i M) - (m : ℝ) * c) ^ 2) =
      fun M => (∑ i, f (rowOf i M)) ^ 2 -
        2 * ((m : ℝ) * c) * (∑ i, f (rowOf i M)) + ((m : ℝ) * c) ^ 2 := by
    funext M
    ring
  have iB : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      2 * ((m : ℝ) * c) * (∑ i, f (rowOf i M))) (gaussMat m k v) := iS.const_mul _
  have iQB : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, f (rowOf i M)) ^ 2 -
      2 * ((m : ℝ) * c) * (∑ i, f (rowOf i M))) (gaussMat m k v) := iQ.sub iB
  refine ⟨by rw [hexp]; exact iQB.add (integrable_const _), ?_⟩
  rw [hexp, integral_add iQB (integrable_const _), integral_sub iQ iB,
    integral_const_mul, eS, eQ]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h3 := mul_le_mul_of_nonneg_left u2 hm0
  have h4 := mul_nonneg hm0 (sq_nonneg c)
  nlinarith

section row

variable {k : ℕ}

/-- **One Gaussian row against the smoothing, sharper second moment.** -/
theorem smooth_row143 {v : ℝ} (hv : 0 < v) (s : ℝ) (g gb : Fin k → ℝ) :
    ∫ ξ : Fin k → ℝ, fS s g gb (√v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      v ^ 2 * (normSq g * (s ^ 2 / v + normSq gb) + 2 * dotp g gb ^ 2) / 2 := by
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  set gP : Fin (k + 1) → ℝ := Fin.cons 0 g with hgP
  set gbP : Fin (k + 1) → ℝ := Fin.cons (s / √v) gb with hgbP
  let H : ℝ × (Fin k → ℝ) → ℝ := fun p =>
    relu (∑ j, (√v • p.2) j * g j) * relu (∑ j, (√v • p.2) j * gb j + s * p.1)
  have key : ∀ ξ : Fin (k + 1) → ℝ,
      relu (∑ j, (√v • ξ) j * gP j) * relu (∑ j, (√v • ξ) j * gbP j) =
        H (ξ 0, fun j => ξ j.succ) := by
    intro ξ
    simp only [H, hgP, hgbP]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, mul_zero, zero_add]
    have e : √v * ξ 0 * (s / √v) = s * ξ 0 := by
      field_simp
    rw [e, add_comm (s * ξ 0)]
  obtain ⟨i2, u2⟩ := rowPair143 hv.le gP gbP
  simp_rw [key] at i2 u2
  have iH2 : Integrable (fun p => H p ^ 2) ((gaussianReal 0 1).prod (stdGauss (Fin k))) :=
    (aug_integrable (fun p => H p ^ 2)).mp i2
  have vH2 : ∫ p, H p ^ 2 ∂((gaussianReal 0 1).prod (stdGauss (Fin k))) ≤
      v ^ 2 * (normSq gP * normSq gbP + 2 * dotp gP gbP ^ 2) / 2 := by
    rw [← aug_integral (fun p => H p ^ 2)]
    exact u2
  have inner2 : ∀ ξ : Fin k → ℝ, fS s g gb (√v • ξ) ^ 2 ≤ ∫ z, H (z, ξ) ^ 2 ∂gaussianReal 0 1 := by
    intro ξ
    simp only [H, fS]
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (psiS_sq_le s _) (sq_nonneg _)
  have hn : normSq gP = normSq g := by
    rw [hgP, normSq_cons]
    simp
  have hnb : normSq gbP = s ^ 2 / v + normSq gb := by
    rw [hgbP, normSq_cons, div_pow, Real.sq_sqrt hv.le]
  have hd : dotp gP gbP = dotp g gb := by
    rw [hgP, hgbP, dotp_cons]
    simp
  have iS2 : Integrable (fun ξ : Fin k → ℝ => ∫ z, H (z, ξ) ^ 2 ∂gaussianReal 0 1)
      (stdGauss (Fin k)) := iH2.integral_prod_right
  obtain ⟨-, -, hI, -⟩ := smooth_row hv s g gb
  calc ∫ ξ : Fin k → ℝ, fS s g gb (√v • ξ) ^ 2 ∂stdGauss (Fin k)
      ≤ ∫ ξ : Fin k → ℝ, (∫ z, H (z, ξ) ^ 2 ∂gaussianReal 0 1) ∂stdGauss (Fin k) :=
        integral_mono hI iS2 inner2
    _ = ∫ p, H p ^ 2 ∂((gaussianReal 0 1).prod (stdGauss (Fin k))) :=
        (integral_prod_symm _ iH2).symm
    _ ≤ v ^ 2 * (normSq gP * normSq gbP + 2 * dotp gP gbP ^ 2) / 2 := vH2
    _ = _ := by rw [hn, hnb, hd]

/-- **One Gaussian row against `ψ_s²`, sharper second moment.** -/
theorem sq_row143 {v : ℝ} (hv : 0 < v) (s : ℝ) (gb : Fin k → ℝ) :
    ∫ ξ : Fin k → ℝ, fQ s gb (√v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      v ^ 2 * ((s ^ 2 / v + normSq gb) ^ 2 + 2 * normSq gb ^ 2) / 2 := by
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  set ν := (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin k))) with hν
  let D : (Fin k → ℝ) → ℝ := fun ξ => ∑ j, (√v • ξ) j * gb j
  let H : ℝ × (ℝ × (Fin k → ℝ)) → ℝ := fun p =>
    relu (D p.2.2 + s * p.1) * relu (D p.2.2 + s * p.2.1)
  have key : ∀ ξ : Fin (k + 1 + 1) → ℝ,
      relu (∑ j, (√v • ξ) j * hP1 v s gb j) * relu (∑ j, (√v • ξ) j * hP2 v s gb j) =
        H (split2 ξ) := by
    intro ξ
    simp only [H, D, split2, hP1, hP2]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, mul_zero, zero_add]
    have e0 : √v * ξ 0 * (s / √v) = s * ξ 0 := by field_simp
    have e1 : √v * ξ (Fin.succ 0) * (s / √v) = s * ξ 1 := by
      have : (Fin.succ 0 : Fin (k + 1 + 1)) = 1 := rfl
      rw [this]
      field_simp
    rw [e0, e1, add_comm (s * ξ 0), add_comm (s * ξ 1)]
  obtain ⟨i2, u2⟩ := rowPair143 hv.le (hP1 v s gb) (hP2 v s gb)
  simp_rw [key] at i2 u2
  have iH2 : Integrable (fun p => H p ^ 2) ν := (aug2_integrable (fun p => H p ^ 2)).mp i2
  have vH2 : ∫ p, H p ^ 2 ∂ν ≤ v ^ 2 * (normSq (hP1 v s gb) * normSq (hP2 v s gb) +
      2 * dotp (hP1 v s gb) (hP2 v s gb) ^ 2) / 2 := by
    rw [hν, ← aug2_integral (fun p => H p ^ 2)]
    exact u2
  rw [normSq_hP1 hv, normSq_hP2 hv, dotp_hP] at vH2
  set M2 : (Fin k → ℝ) → ℝ := fun ξ => ∫ z, relu (D ξ + s * z) ^ 2 ∂gaussianReal 0 1 with hM2
  have in2 : ∀ ξ : Fin k → ℝ,
      ∫ z', (∫ z, H (z, (z', ξ)) ^ 2 ∂gaussianReal 0 1) ∂gaussianReal 0 1 = M2 ξ ^ 2 := by
    intro ξ
    simp only [H, hM2]
    simp_rw [mul_pow, integral_mul_const]
    rw [integral_const_mul, sq]
  obtain ⟨j2, f2⟩ := fub3 iH2
  simp_rw [in2] at j2 f2
  have hle : ∀ ξ : Fin k → ℝ, fQ s gb (√v • ξ) ^ 2 ≤ M2 ξ ^ 2 := by
    intro ξ
    have h := psiS_sq_le s (D ξ)
    have h0 : 0 ≤ psiS s (D ξ) ^ 2 := sq_nonneg _
    change (psiS s (D ξ) ^ 2) ^ 2 ≤ M2 ξ ^ 2
    exact pow_le_pow_left₀ h0 h 2
  obtain ⟨-, -, i4, -⟩ := sq_row hv s gb
  calc ∫ ξ : Fin k → ℝ, fQ s gb (√v • ξ) ^ 2 ∂stdGauss (Fin k)
      ≤ ∫ ξ : Fin k → ℝ, M2 ξ ^ 2 ∂stdGauss (Fin k) := integral_mono i4 j2 hle
    _ = ∫ p, H p ^ 2 ∂ν := f2.symm
    _ ≤ _ := by
        refine vH2.trans (le_of_eq ?_)
        ring

end row

variable {N m : ℕ}

/-! ## Given `M₁` -/

/-- **Given `M₁`, sharper**: `E_{M₂}(T̂(u) − Ψ)² ≤ (2/m)·(α(u)·Γ* + 2·C²)`,
`C = t⟨h₁(u), h̄₁⟩`. -/
theorem That_cond143 (hN : 1 ≤ N) (hm : 1 ≤ m) (M₁ : Matrix (Fin m) (Fin N) ℝ) (u : Fin N → ℝ) :
    ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, (That N m u (M₁, M₂) - PsiM M₁ u) ^ 2
      ∂gaussMat m m (2 / (m : ℝ)) ≤ 2 / (m : ℝ) * (alphaU M₁ u * GamS M₁ +
        2 * (2 / (m : ℝ) * dotp (reluV (M₁.mulVec u)) (h1bar M₁)) ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set v : ℝ := 2 / (m : ℝ) with hvdef
  set g : Fin m → ℝ := reluV (M₁.mulVec u) with hg
  set gb : Fin m → ℝ := h1bar M₁ with hgb
  set s : ℝ := sS M₁ with hs
  obtain ⟨i1, e1, i2, -⟩ := smooth_row hv s g gb
  obtain ⟨-, u2⟩ := rows_var_le (m := m) v (fS s g gb) (measurable_fS s g gb) i1 e1 i2
    (smooth_row143 hv s g gb)
  have hT : ∀ M₂ : Matrix (Fin m) (Fin m) ℝ, That N m u (M₁, M₂) - PsiM M₁ u =
      v * (∑ i, fS s g gb (rowOf i M₂) - (m : ℝ) * cS v s g gb) := by
    intro M₂
    have e : That N m u (M₁, M₂) =
        v * dotp (reluV (M₂.mulVec g)) (fun i => psiS s ((M₂.mulVec gb) i)) := rfl
    have e' : PsiM M₁ u = v * ((m : ℝ) * cS v s g gb) := by
      unfold PsiM cS
      rw [← hvdef, ← hg, ← hgb, ← hs]
      rw [hvdef]
      field_simp
    have e'' : dotp (reluV (M₂.mulVec g)) (fun i => psiS s ((M₂.mulVec gb) i)) =
        ∑ i, fS s g gb (rowOf i M₂) := rfl
    rw [e, e', e'']
    ring
  simp_rw [hT, mul_pow]
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left u2 (sq_nonneg v)).trans (le_of_eq ?_)
  have hG : s ^ 2 / v + normSq gb = GamS M₁ / v := by
    rw [hs, sS_sq hN, ← hvdef, ← hgb]
    field_simp
    ring
  rw [hG]
  unfold alphaU
  rw [← hvdef, ← hg, hvdef]
  field_simp

/-- **Given `M₁`, sharper**: `E_{M₂}(t|b̂|² − Ψ_B)² ≤ (2/m)·(Γ*² + 2·Q²)`, `Q = t|h̄₁|²`. -/
theorem bhatNorm_cond143 (hN : 1 ≤ N) (hm : 1 ≤ m) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, (Bh N m (M₁, M₂) - PsiB M₁) ^ 2
      ∂gaussMat m m (2 / (m : ℝ)) ≤ 2 / (m : ℝ) * (GamS M₁ ^ 2 +
        2 * (2 / (m : ℝ) * normSq (h1bar M₁)) ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set v : ℝ := 2 / (m : ℝ) with hvdef
  set gb : Fin m → ℝ := h1bar M₁ with hgb
  set s : ℝ := sS M₁ with hs
  obtain ⟨i1, e1, i2, -⟩ := sq_row hv s gb
  obtain ⟨-, u2⟩ := rows_var_le (m := m) v (fQ s gb) (measurable_fQ s gb) i1 e1 i2
    (sq_row143 hv s gb)
  have hT : ∀ M₂ : Matrix (Fin m) (Fin m) ℝ, Bh N m (M₁, M₂) - PsiB M₁ =
      v * (∑ i, fQ s gb (rowOf i M₂) - (m : ℝ) * cQ v s gb) := by
    intro M₂
    have e : Bh N m (M₁, M₂) = v * normSq (fun i => psiS s ((M₂.mulVec gb) i)) := rfl
    have e' : PsiB M₁ = v * ((m : ℝ) * cQ v s gb) := by
      unfold PsiB cQ
      rw [← hvdef, ← hgb, ← hs]
      rw [hvdef]
      field_simp
    have e'' : normSq (fun i => psiS s ((M₂.mulVec gb) i)) = ∑ i, fQ s gb (rowOf i M₂) := rfl
    rw [e, e', e'']
    ring
  simp_rw [hT, mul_pow]
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left u2 (sq_nonneg v)).trans (le_of_eq ?_)
  have hG : s ^ 2 / v + normSq gb = GamS M₁ / v := by
    rw [hs, sS_sq hN, ← hvdef, ← hgb]
    field_simp
    ring
  rw [hG, hvdef]
  field_simp

/-! ## Over `M₁` and `M₂` -/

/-- The sharper constant of H2(b). -/
noncomputable def cHat143 (N m : ℕ) : ℝ :=
  √((2 * (1 + 5 / (m : ℝ)) + 4 * (√((1 + 2 / (N : ℝ)) / (2 * m)) + q1 (e0 N)) ^ 2) / (m : ℝ) +
    (kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 / (m : ℝ))

/-- The sharper constant of the squared length of the computed centre. -/
noncomputable def cB143 (N m : ℕ) : ℝ :=
  √((2 * (1 + 5 / (m : ℝ)) + 4 * (√((1 + 2 / (N : ℝ)) / (2 * m)) + q1 (e0 N)) ^ 2) / (m : ℝ) +
    (kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 / (m : ℝ))

lemma cHat143_nonneg (N m : ℕ) : 0 ≤ cHat143 N m := Real.sqrt_nonneg _

lemma cB143_nonneg (N m : ℕ) : 0 ≤ cB143 N m := Real.sqrt_nonneg _

/-- From an `L²` bound of `f − c` to an `L²` bound of `f`, `c ≥ 0`. -/
lemma L2le_of_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {a c : ℝ} (h : L2le μ (fun ω => f ω - c) a) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    L2le μ f (a + c) := by
  have h2 := h.add' (L2le.const (μ := μ) c) ha (abs_nonneg c)
  rw [abs_of_nonneg hc] at h2
  exact h2.congr_fun fun ω => by ring

/-- **Lemma H2(b), sharper**, every `N, m ≥ 1`: for a unit vector `u₀`,
`‖T̂(u₀) − γ·κ(q₁)‖_{L²(θ)} ≤ γ·cHat143 N m`. -/
theorem hatFluct143_pt (hN : 1 ≤ N) (hm : 1 ≤ m) {u0 : Fin N → ℝ} (hu0 : normSq u0 = 1) :
    L2le (hidGauss N m)
      (fun θ => That N m u0 θ - 2 / (N : ℝ) * kappa (q1 u0)) (2 / (N : ℝ) * cHat143 N m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hγ : (0 : ℝ) < 2 / (N : ℝ) := by positivity
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  obtain ⟨hq0, hq1⟩ := q1_mem hN hu0
  obtain ⟨hA1, hA2⟩ := alpha_L2 (m := m) hN hm hu0
  obtain ⟨-, hG2⟩ := GamS_L2 (N := N) (m := m) hN hm
  have hG1 := GamS_L2x (N := N) (m := m) hN hm
  have hC := cov_L2x (m := m) hN hm hu0
  set aG : ℝ := 2 / (N : ℝ) * √(2 / ((N : ℝ) * m)) with haGd
  set aC : ℝ := 2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m)) with haCd
  have haG : 0 ≤ aG := by rw [haGd]; positivity
  have haC : 0 ≤ aC := by rw [haCd]; positivity
  have hTm : Measurable (That N m u0) := (measurable_That hN).of_uncurry_left
  -- the conditional mean is measurable
  have hPm : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiM M₁ u0) := by
    have e : (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiM M₁ u0) = fun M₁ =>
        ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, That N m u0 (M₁, M₂) ∂gaussMat m m (2 / (m : ℝ)) := by
      funext M₁
      obtain ⟨i1, e1, -, -⟩ := That_cond hN hm M₁ u0
      have i0 : Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ => That N m u0 (M₁, M₂))
          (gaussMat m m (2 / (m : ℝ))) := by
        have := i1.add (integrable_const (PsiM M₁ u0))
        refine this.congr (Filter.Eventually.of_forall fun M₂ => ?_)
        simp
      rw [integral_sub i0 (integrable_const _)] at e1
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at e1
      linarith
    rw [e]
    exact (hTm.stronglyMeasurable.integral_prod_right').measurable
  -- `B`: the conditional mean minus the constant
  have hB : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiM M₁ u0 - 2 / (N : ℝ) * kappa (q1 u0))
      (kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + aG) + aC) := by
    have habs : ∀ {f : Matrix (Fin m) (Fin N) ℝ → ℝ} {a : ℝ},
        L2le (gaussMat m N (2 / (N : ℝ))) f a →
        L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ => |f M₁|) a := fun {f a} h =>
      L2le.of_abs_le (continuous_abs.comp_aestronglyMeasurable h.aesm) h
        (fun ω => le_of_eq (abs_abs _))
    have hsum := (((habs hA1).add' (habs hG1) (by positivity) haG).const_mul_nonneg
      hk0).add' (habs hC) (mul_nonneg hk0 (add_nonneg (by positivity) haG)) haC
    refine L2le.of_abs_le (hPm.sub_const _).aestronglyMeasurable hsum fun M₁ => ?_
    rw [abs_of_nonneg (add_nonneg (mul_nonneg hk0 (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      (abs_nonneg _))]
    set gP : Fin (m + 1) → ℝ := Fin.cons 0 (reluV (M₁.mulVec u0)) with hgP
    set gbP : Fin (m + 1) → ℝ := Fin.cons (sS M₁ / √(2 / (m : ℝ))) (h1bar M₁) with hgbP
    have hpb : (0 : ℝ) ≤ 2 / (N : ℝ) / (2 / (m : ℝ)) := by positivity
    have hp := psi_abs_sub kGood_kappa gP gbP hpb
      (show |q1 u0| ≤ 1 by rw [abs_of_nonneg hq0]; exact hq1)
    have hn1 : normSq gP = normSq (reluV (M₁.mulVec u0)) := by
      rw [hgP, normSq_cons]
      simp
    have hn2 : normSq gbP = GamS M₁ / (2 / (m : ℝ)) := by
      rw [hgbP, normSq_cons, div_pow, Real.sq_sqrt hv.le, sS_sq hN]
      field_simp
      ring
    have hd : dotp gP gbP = dotp (reluV (M₁.mulVec u0)) (h1bar M₁) := by
      rw [hgP, hgbP, dotp_cons]
      simp
    have hnr : 2 / (m : ℝ) * (nrm gP * nrm gbP) = √(alphaU M₁ u0) * √(GamS M₁) := by
      unfold nrm
      rw [hn1, hn2]
      have e1 : alphaU M₁ u0 = 2 / (m : ℝ) * normSq (reluV (M₁.mulVec u0)) := rfl
      have e2 : GamS M₁ = 2 / (m : ℝ) * (GamS M₁ / (2 / (m : ℝ))) := by
        field_simp
      rw [e1]
      conv_rhs => rw [e2]
      rw [Real.sqrt_mul hv.le, Real.sqrt_mul hv.le]
      have := Real.mul_self_sqrt hv.le
      calc 2 / (m : ℝ) * (√(normSq (reluV (M₁.mulVec u0))) * √(GamS M₁ / (2 / (m : ℝ))))
          = (√(2 / (m : ℝ)) * √(2 / (m : ℝ))) * (√(normSq (reluV (M₁.mulVec u0))) *
              √(GamS M₁ / (2 / (m : ℝ)))) := by rw [this]
        _ = _ := by ring
    have hPsi : PsiM M₁ u0 = 2 / (m : ℝ) * psi kappa gP gbP := rfl
    have hsq := sqrt_mul_sub (g := 2 / (N : ℝ)) (alphaU_nonneg M₁ u0) (GamS_nonneg M₁)
    have e3 : PsiM M₁ u0 - 2 / (N : ℝ) * kappa (q1 u0) =
        2 / (m : ℝ) * (psi kappa gP gbP - 2 / (N : ℝ) / (2 / (m : ℝ)) * kappa (q1 u0)) := by
      rw [hPsi]
      field_simp
    have e4 : √(alphaU M₁ u0) * √(GamS M₁) - 2 / (N : ℝ) =
        2 / (m : ℝ) * (nrm gP * nrm gbP - 2 / (N : ℝ) / (2 / (m : ℝ))) := by
      rw [← hnr]
      field_simp
    have e5 : 2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁) - 2 / (N : ℝ) * q1 u0 =
        2 / (m : ℝ) * (dotp gP gbP - 2 / (N : ℝ) / (2 / (m : ℝ)) * q1 u0) := by
      rw [hd]
      field_simp
    rw [e3, abs_mul, abs_of_pos hv, e5, abs_mul, abs_of_pos hv]
    have h6 : |√(alphaU M₁ u0) * √(GamS M₁) - 2 / (N : ℝ)| =
        2 / (m : ℝ) * |nrm gP * nrm gbP - 2 / (N : ℝ) / (2 / (m : ℝ))| := by
      rw [e4, abs_mul, abs_of_pos hv]
    have h7 := mul_le_mul_of_nonneg_left hp hv.le
    have h8 : kappa 0 * (2 / (m : ℝ) * |nrm gP * nrm gbP - 2 / (N : ℝ) / (2 / (m : ℝ))|) ≤
        kappa 0 * (|alphaU M₁ u0 - 2 / (N : ℝ)| + |GamS M₁ - 2 / (N : ℝ)|) := by
      rw [← h6]
      exact mul_le_mul_of_nonneg_left hsq hk0
    nlinarith [h7, h8]
  -- `g`: the conditional standard deviation
  have hCf := L2le_of_sub hC haC (mul_nonneg hγ.le hq0)
  have hmα : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => alphaU M₁ u0) :=
    (continuous_const.mul (continuous_normSq.comp (continuous_h1_M u0))).measurable
  have hmC : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁)) :=
    (measurable_dotp_comp (continuous_h1_M u0).measurable (measurable_h1bar hN)).const_mul _
  have hG0 : ∀ M₁ : Matrix (Fin m) (Fin N) ℝ, 0 ≤ 2 / (m : ℝ) * (alphaU M₁ u0 * GamS M₁ +
      2 * (2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁)) ^ 2) := fun M₁ =>
    mul_nonneg hv.le (add_nonneg (mul_nonneg (alphaU_nonneg M₁ u0) (GamS_nonneg M₁))
      (by positivity))
  have hA0 : 0 ≤ 2 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) +
      2 * (aC + 2 / (N : ℝ) * q1 u0) ^ 2) := by positivity
  have hg : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => √(2 / (m : ℝ) * (alphaU M₁ u0 * GamS M₁ +
        2 * (2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁)) ^ 2)))
      (√(2 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) +
        2 * (aC + 2 / (N : ℝ) * q1 u0) ^ 2))) := by
    have iG : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
        2 / (m : ℝ) * ((alphaU M₁ u0 ^ 2 + GamS M₁ ^ 2) / 2 +
          2 * (2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁)) ^ 2))
        (gaussMat m N (2 / (N : ℝ))) :=
      (((hA2.int_sq.add hG2.int_sq).div_const 2).add (hCf.int_sq.const_mul 2)).const_mul _
    refine L2le.of_sq_le
      (G := fun M₁ => 2 / (m : ℝ) * ((alphaU M₁ u0 ^ 2 + GamS M₁ ^ 2) / 2 +
          2 * (2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁)) ^ 2))
      ((((hmα.mul (measurable_GamS hN)).add ((hmC.pow_const 2).const_mul 2)).const_mul
        _).sqrt.aestronglyMeasurable) iG (fun M₁ => ?_) ?_
    · rw [Real.sq_sqrt (hG0 M₁)]
      have : alphaU M₁ u0 * GamS M₁ ≤ (alphaU M₁ u0 ^ 2 + GamS M₁ ^ 2) / 2 := by
        nlinarith [sq_nonneg (alphaU M₁ u0 - GamS M₁)]
      exact mul_le_mul_of_nonneg_left (by linarith) hv.le
    · have iAG : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
          (alphaU M₁ u0 ^ 2 + GamS M₁ ^ 2) / 2) (gaussMat m N (2 / (N : ℝ))) :=
        (hA2.int_sq.add hG2.int_sq).div_const 2
      have iC2 : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
          2 * (2 / (m : ℝ) * dotp (reluV (M₁.mulVec u0)) (h1bar M₁)) ^ 2)
          (gaussMat m N (2 / (N : ℝ))) := hCf.int_sq.const_mul 2
      rw [Real.sq_sqrt hA0, integral_const_mul, integral_add iAG iC2,
        integral_div, integral_add hA2.int_sq hG2.int_sq, integral_const_mul]
      have a1 := hA2.le
      have a2 := hG2.le
      have a3 := hCf.le
      rw [mul_pow, Real.sq_sqrt (by positivity)] at a1 a2
      refine mul_le_mul_of_nonneg_left ?_ hv.le
      linarith
  have hRm : Measurable (fun z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      That N m u0 z - PsiM z.1 u0) := hTm.sub (hPm.comp measurable_fst)
  have key := L2le.prod_orth (μ := gaussMat m N (2 / (N : ℝ))) (ν := gaussMat m m (2 / (m : ℝ)))
    hRm.aestronglyMeasurable hB hg (fun M₁ => by
      obtain ⟨i1, e1, i2, -⟩ := That_cond hN hm M₁ u0
      refine ⟨i1, e1, i2, (That_cond143 hN hm M₁ u0).trans (le_of_eq ?_)⟩
      rw [Real.sq_sqrt (hG0 M₁)])
  have key' : L2le (hidGauss N m) (fun z : HidParam N m => That N m u0 z - PsiM z.1 u0 +
      (PsiM z.1 u0 - 2 / (N : ℝ) * kappa (q1 u0))) _ := key
  refine (key'.congr_fun fun θ => by ring).congr_bound ?_
  rw [Real.sq_sqrt hA0, q1_eq hN hu0]
  unfold cHat143
  have r1 : √(5 / (m : ℝ)) = √5 / √(m : ℝ) := Real.sqrt_div (by norm_num) _
  have r2 : √(2 / ((N : ℝ) * m)) = √(2 / (N : ℝ)) / √(m : ℝ) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have r3 : √((1 + 2 / (N : ℝ)) / (2 * m)) = √((1 + 2 / (N : ℝ)) / 2) / √(m : ℝ) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have hs2 := Real.sq_sqrt hm'.le
  have e5 : kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + aG) + aC =
      2 / (N : ℝ) * ((kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) / √(m : ℝ)) := by
    rw [haGd, haCd, r1, r2, r3]
    ring
  have e6 : 2 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) +
        2 * (aC + 2 / (N : ℝ) * q1 (e0 N)) ^ 2) +
      (kappa 0 * (2 / (N : ℝ) * √(5 / (m : ℝ)) + aG) + aC) ^ 2 =
      (2 / (N : ℝ)) ^ 2 * ((2 * (1 + 5 / (m : ℝ)) +
        4 * (√((1 + 2 / (N : ℝ)) / (2 * m)) + q1 (e0 N)) ^ 2) / (m : ℝ) +
        (kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 / (m : ℝ)) := by
    rw [e5]
    calc 2 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) +
          2 * (aC + 2 / (N : ℝ) * q1 (e0 N)) ^ 2) +
          (2 / (N : ℝ) * ((kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) /
            √(m : ℝ))) ^ 2
        = (2 / (N : ℝ)) ^ 2 * ((2 * (1 + 5 / (m : ℝ)) +
            4 * (√((1 + 2 / (N : ℝ)) / (2 * m)) + q1 (e0 N)) ^ 2) / (m : ℝ) +
            (kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 /
              √(m : ℝ) ^ 2) := by rw [haCd]; ring
      _ = _ := by rw [hs2]
  rw [e6, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hγ.le]

/-- **The squared length of the computed centre, sharper**:
`‖t|b̂|² − γ·κ(q₁)‖_{L²(θ)} ≤ γ·cB143 N m`, every `N, m ≥ 1`. -/
theorem bhatNorm_L2_143 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => Bh N m θ - 2 / (N : ℝ) * kap1 N)
      (2 / (N : ℝ) * cB143 N m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  have hγ : (0 : ℝ) < 2 / (N : ℝ) := by positivity
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  obtain ⟨hq0, hq1⟩ := q1_mem hN (Part137.normSq_e0 hN)
  obtain ⟨-, hG2⟩ := GamS_L2 (N := N) (m := m) hN hm
  have hG1 := GamS_L2x (N := N) (m := m) hN hm
  have hC := h1bar_L2 (m := m) hN hm
  set aG : ℝ := 2 / (N : ℝ) * √(2 / ((N : ℝ) * m)) with haG
  set aC : ℝ := 2 / (N : ℝ) * √((1 + 2 / (N : ℝ)) / (2 * m)) with haC
  have haG0 : 0 ≤ aG := by rw [haG]; positivity
  have haC0 : 0 ≤ aC := by rw [haC]; positivity
  have hTm : Measurable (Bh N m) := measurable_Bh hN
  have hPm : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiB M₁) := by
    have e : (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiB M₁) = fun M₁ =>
        ∫ M₂ : Matrix (Fin m) (Fin m) ℝ, Bh N m (M₁, M₂) ∂gaussMat m m (2 / (m : ℝ)) := by
      funext M₁
      obtain ⟨i1, e1, -, -⟩ := bhatNorm_cond hN hm M₁
      have i0 : Integrable (fun M₂ : Matrix (Fin m) (Fin m) ℝ => Bh N m (M₁, M₂))
          (gaussMat m m (2 / (m : ℝ))) := by
        have := i1.add (integrable_const (PsiB M₁))
        refine this.congr (Filter.Eventually.of_forall fun M₂ => ?_)
        simp
      rw [integral_sub i0 (integrable_const _)] at e1
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at e1
      linarith
    rw [e]
    exact (hTm.stronglyMeasurable.integral_prod_right').measurable
  have hB : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => PsiB M₁ - 2 / (N : ℝ) * kap1 N)
      (kappa 0 * aG + aC) := by
    have habs : ∀ {f : Matrix (Fin m) (Fin N) ℝ → ℝ} {a : ℝ},
        L2le (gaussMat m N (2 / (N : ℝ))) f a →
        L2le (gaussMat m N (2 / (N : ℝ))) (fun M₁ => |f M₁|) a := fun {f a} h =>
      L2le.of_abs_le (continuous_abs.comp_aestronglyMeasurable h.aesm) h
        (fun ω => le_of_eq (abs_abs _))
    have hsum := ((habs hG1).const_mul_nonneg hk0).add' (habs hC) (mul_nonneg hk0 haG0) haC0
    refine L2le.of_abs_le (hPm.sub_const _).aestronglyMeasurable hsum fun M₁ => ?_
    rw [abs_of_nonneg (add_nonneg (mul_nonneg hk0 (abs_nonneg _)) (abs_nonneg _))]
    set gP := hP1 (2 / (m : ℝ)) (sS M₁) (h1bar M₁) with hgP
    set gbP := hP2 (2 / (m : ℝ)) (sS M₁) (h1bar M₁) with hgbP
    have hpb : (0 : ℝ) ≤ 2 / (N : ℝ) / (2 / (m : ℝ)) := by positivity
    have hp := psi_abs_sub kGood_kappa gP gbP hpb
      (show |q1 (e0 N)| ≤ 1 by rw [abs_of_nonneg hq0]; exact hq1)
    have hGv : sS M₁ ^ 2 / (2 / (m : ℝ)) + normSq (h1bar M₁) = GamS M₁ / (2 / (m : ℝ)) := by
      rw [sS_sq hN]
      field_simp
      ring
    have hn1 : normSq gP = GamS M₁ / (2 / (m : ℝ)) := by rw [hgP, normSq_hP1 hv, hGv]
    have hn2 : normSq gbP = GamS M₁ / (2 / (m : ℝ)) := by rw [hgbP, normSq_hP2 hv, hGv]
    have hd : dotp gP gbP = normSq (h1bar M₁) := dotp_hP _ _ _
    have hnr : nrm gP * nrm gbP = GamS M₁ / (2 / (m : ℝ)) := by
      unfold nrm
      rw [hn1, hn2]
      exact Real.mul_self_sqrt (div_nonneg (GamS_nonneg M₁) hv.le)
    have hPsi : PsiB M₁ = 2 / (m : ℝ) * psi kappa gP gbP := rfl
    rw [hnr, hd] at hp
    have e3 : PsiB M₁ - 2 / (N : ℝ) * kap1 N =
        2 / (m : ℝ) * (psi kappa gP gbP - 2 / (N : ℝ) / (2 / (m : ℝ)) * kappa (q1 (e0 N))) := by
      rw [hPsi]
      unfold kap1
      field_simp
    have e4 : GamS M₁ - 2 / (N : ℝ) =
        2 / (m : ℝ) * (GamS M₁ / (2 / (m : ℝ)) - 2 / (N : ℝ) / (2 / (m : ℝ))) := by
      field_simp
    have e5 : 2 / (m : ℝ) * normSq (h1bar M₁) - 2 / (N : ℝ) * q1 (e0 N) =
        2 / (m : ℝ) * (normSq (h1bar M₁) - 2 / (N : ℝ) / (2 / (m : ℝ)) * q1 (e0 N)) := by
      field_simp
    rw [e3, abs_mul, abs_of_pos hv, e4, abs_mul, abs_of_pos hv, e5, abs_mul, abs_of_pos hv]
    have h7 := mul_le_mul_of_nonneg_left hp hv.le
    linarith
  -- the conditional standard deviation
  have hQf := L2le_of_sub hC haC0 (mul_nonneg hγ.le hq0)
  have hmQ : Measurable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
      2 / (m : ℝ) * normSq (h1bar M₁)) :=
    (measurable_normSq.comp (measurable_h1bar hN)).const_mul _
  have hA0 : 0 ≤ 2 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) +
      2 * (aC + 2 / (N : ℝ) * q1 (e0 N)) ^ 2) := by positivity
  have hg : L2le (gaussMat m N (2 / (N : ℝ)))
      (fun M₁ : Matrix (Fin m) (Fin N) ℝ => √(2 / (m : ℝ) * (GamS M₁ ^ 2 +
        2 * (2 / (m : ℝ) * normSq (h1bar M₁)) ^ 2)))
      (√(2 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) +
        2 * (aC + 2 / (N : ℝ) * q1 (e0 N)) ^ 2))) := by
    have iQ2 : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
        2 * (2 / (m : ℝ) * normSq (h1bar M₁)) ^ 2) (gaussMat m N (2 / (N : ℝ))) :=
      hQf.int_sq.const_mul 2
    have iG : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ =>
        2 / (m : ℝ) * (GamS M₁ ^ 2 + 2 * (2 / (m : ℝ) * normSq (h1bar M₁)) ^ 2))
        (gaussMat m N (2 / (N : ℝ))) := (hG2.int_sq.add iQ2).const_mul _
    refine L2le.of_sq_le
      (G := fun M₁ => 2 / (m : ℝ) * (GamS M₁ ^ 2 + 2 * (2 / (m : ℝ) * normSq (h1bar M₁)) ^ 2))
      (((((measurable_GamS hN).pow_const 2).add ((hmQ.pow_const 2).const_mul 2)).const_mul
        _).sqrt.aestronglyMeasurable) iG (fun M₁ => ?_) ?_
    · rw [Real.sq_sqrt (by positivity)]
    · rw [Real.sq_sqrt hA0, integral_const_mul, integral_add hG2.int_sq iQ2, integral_const_mul]
      have a2 := hG2.le
      have a3 := hQf.le
      rw [mul_pow, Real.sq_sqrt (by positivity)] at a2
      refine mul_le_mul_of_nonneg_left ?_ hv.le
      linarith
  have hRm : Measurable (fun z : Matrix (Fin m) (Fin N) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      Bh N m z - PsiB z.1) := hTm.sub (hPm.comp measurable_fst)
  have key := L2le.prod_orth (μ := gaussMat m N (2 / (N : ℝ))) (ν := gaussMat m m (2 / (m : ℝ)))
    hRm.aestronglyMeasurable hB hg (fun M₁ => by
      obtain ⟨i1, e1, i2, -⟩ := bhatNorm_cond hN hm M₁
      refine ⟨i1, e1, i2, (bhatNorm_cond143 hN hm M₁).trans (le_of_eq ?_)⟩
      rw [Real.sq_sqrt (by positivity)])
  have key' : L2le (hidGauss N m) (fun z : HidParam N m => Bh N m z - PsiB z.1 +
      (PsiB z.1 - 2 / (N : ℝ) * kap1 N)) _ := key
  refine (key'.congr_fun fun θ => by ring).congr_bound ?_
  rw [Real.sq_sqrt hA0]
  unfold cB143
  have r2 : √(2 / ((N : ℝ) * m)) = √(2 / (N : ℝ)) / √(m : ℝ) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have r3 : √((1 + 2 / (N : ℝ)) / (2 * m)) = √((1 + 2 / (N : ℝ)) / 2) / √(m : ℝ) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  have hs2 := Real.sq_sqrt hm'.le
  have e5 : kappa 0 * aG + aC =
      2 / (N : ℝ) * ((kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) / √(m : ℝ)) := by
    rw [haG, haC, r2, r3]
    ring
  have e6 : 2 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) +
        2 * (aC + 2 / (N : ℝ) * q1 (e0 N)) ^ 2) + (kappa 0 * aG + aC) ^ 2 =
      (2 / (N : ℝ)) ^ 2 * ((2 * (1 + 5 / (m : ℝ)) +
        4 * (√((1 + 2 / (N : ℝ)) / (2 * m)) + q1 (e0 N)) ^ 2) / (m : ℝ) +
        (kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 / (m : ℝ)) := by
    rw [e5]
    calc 2 / (m : ℝ) * ((2 / (N : ℝ)) ^ 2 * (1 + 5 / (m : ℝ)) +
          2 * (aC + 2 / (N : ℝ) * q1 (e0 N)) ^ 2) +
          (2 / (N : ℝ) * ((kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) /
            √(m : ℝ))) ^ 2
        = (2 / (N : ℝ)) ^ 2 * ((2 * (1 + 5 / (m : ℝ)) +
            4 * (√((1 + 2 / (N : ℝ)) / (2 * m)) + q1 (e0 N)) ^ 2) / (m : ℝ) +
            (kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 /
              √(m : ℝ) ^ 2) := by rw [haC]; ring
      _ = _ := by rw [hs2]
  rw [e6, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hγ.le]

/-- **Lemma H2(b), over the input and `θ`, sharper**. -/
theorem hatFluct143_joint (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun p : (Fin N → ℝ) × HidParam N m =>
        (That N m p.1 p.2 - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2)
        ((uniformSphere N).prod (hidGauss N m)) ∧
      ∫ p, (That N m p.1 p.2 - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2
          ∂((uniformSphere N).prod (hidGauss N m)) ≤ (2 / (N : ℝ) * cHat143 N m) ^ 2 := by
  have h := hatFluct143_pt (m := m) hN hm (Part137.normSq_e0 hN)
  have hYm : Measurable (Function.uncurry fun (u : Fin N → ℝ) (θ : HidParam N m) =>
      (That N m u θ - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2) :=
    ((measurable_That hN).sub_const _).pow_const 2
  have hY : Exch (fun (u : Fin N → ℝ) (θ : HidParam N m) =>
      (That N m u θ - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2) :=
    exch_That.comp fun x => (x - 2 / (N : ℝ) * kappa (q1 (e0 N))) ^ 2
  obtain ⟨h1, h2⟩ := exch_avg hN hYm hY (Part137.normSq_e0 hN) h.int_sq
  exact ⟨h1, h2.trans_le h.le⟩

/-- `‖t⟨h̄, b̂⟩ − γκ(q₁)‖_{L²(θ)} ≤ γ·cHat143 N m`. -/
theorem Xh_L2_143 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => Xh N m θ - 2 / (N : ℝ) * kap1 N)
      (2 / (N : ℝ) * cHat143 N m) := by
  have := uniformSphere_isProbability N hN
  obtain ⟨h1, h2⟩ := hatFluct143_joint (m := m) hN hm
  have hj : L2le ((uniformSphere N).prod (hidGauss N m))
      (fun p : (Fin N → ℝ) × HidParam N m =>
        That N m p.1 p.2 - 2 / (N : ℝ) * kappa (q1 (e0 N))) (2 / (N : ℝ) * cHat143 N m) :=
    ⟨(((measurable_That hN).sub_const _ :)).aestronglyMeasurable, h1, h2⟩
  refine hj.integral_left.congr_fun fun θ => ?_
  rw [integral_sub (sphere_cont_integrable hN (continuous_That_u θ)) (integrable_const _),
    That_mean hN]
  simp [kap1]

/-- The constant of the distance, sharper: `cB143 + 2·cHat143 + cH143`. -/
noncomputable def cDst143s (N m : ℕ) : ℝ := cB143 N m + 2 * cHat143 N m + cH143 N m

lemma cDst143s_nonneg (N m : ℕ) : 0 ≤ cDst143s N m := by
  have := cB143_nonneg N m
  have := cHat143_nonneg N m
  have := cH143_nonneg N m
  unfold cDst143s
  linarith

/-- **The distance in `L²(θ)`, sharper**:
`‖t|b̂ − h̄|² − γ(q_N − κ(q₁))‖₂ ≤ γ·cDst143s N m`. -/
theorem dist2_L2_143s (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => dist2 N m θ - 2 / (N : ℝ) * (qN N - kap1 N))
      (2 / (N : ℝ) * cDst143s N m) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have hB := bhatNorm_L2_143 (m := m) hN hm
  have hX := (Xh_L2_143 (m := m) hN hm).const_mul (-2)
  have hH := Hh_L2_143 (m := m) hN hm
  have e2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [e2] at hX
  have h1 := hB.add' hX (mul_nonneg hγ (cB143_nonneg N m))
    (mul_nonneg (by norm_num) (mul_nonneg hγ (cHat143_nonneg N m)))
  have h2 := h1.add' hH
    (add_nonneg (mul_nonneg hγ (cB143_nonneg N m))
      (mul_nonneg (by norm_num) (mul_nonneg hγ (cHat143_nonneg N m))))
    (mul_nonneg hγ (cH143_nonneg N m))
  refine (h2.congr_fun fun θ => ?_).congr_bound ?_
  · rw [dist2_eq]
    ring
  · unfold cDst143s
    ring

theorem errT_mean143 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (errT (N := N) (m := m)) (hidGauss N m) ∧
      ∫ θ, errT θ ∂hidGauss N m ≤ (2 / (N : ℝ) * cHat143 N m) ^ 2 := by
  have := uniformSphere_isProbability N hN
  obtain ⟨h1, h2⟩ := hatFluct143_joint (m := m) hN hm
  refine ⟨h1.integral_prod_right, ?_⟩
  have e := integral_prod_symm _ h1
  unfold errT kap1
  rw [← e]
  exact h2

/-- Markov for `errT`, sharper constant. -/
theorem errT_bad143 (hN : 1 ≤ N) (hm : 1 ≤ m) {B : ℝ} (hB : 0 < B) :
    (hidGauss N m).real {θ | B < errT θ} ≤ (2 / (N : ℝ) * cHat143 N m) ^ 2 / B := by
  obtain ⟨hi, hle⟩ := errT_mean143 (m := m) hN hm
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := hidGauss N m) (f := errT)
    (Filter.Eventually.of_forall errT_nonneg) hi B
  have hsub : {θ : HidParam N m | B < errT θ} ⊆ {θ | B ≤ errT θ} :=
    fun θ (hθ : B < errT θ) => (le_of_lt hθ : B ≤ errT θ)
  have hmono := measureReal_mono (μ := hidGauss N m) hsub (measure_ne_top _ _)
  rw [le_div_iff₀ hB, mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono hB.le).trans (hmk.trans hle)

/-! ## The numbers -/

/-- `q₁(e₀) ≤ κ(0) + 1/√N`. -/
lemma q1e_le (hN : 1 ≤ N) : q1 (e0 N) ≤ kappa 0 + 1 / √(N : ℝ) := by
  have := uniformSphere_isProbability N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hN'
  have hsm : √(N : ℝ) ^ 2 = N := Real.sq_sqrt hN'.le
  have ic : Integrable (fun u : Fin N → ℝ => dotp (e0 N) u ^ 2) (uniformSphere N) :=
    sphere_cont_integrable hN ((continuous_dotp_e0 N).pow 2)
  have iR : Integrable (fun u : Fin N → ℝ => kappa 0 + 1 / √(N : ℝ) / 2 +
      √(N : ℝ) / 2 * dotp (e0 N) u ^ 2) (uniformSphere N) :=
    (integrable_const _).add (ic.const_mul _)
  have h : q1 (e0 N) ≤ ∫ u, (kappa 0 + 1 / √(N : ℝ) / 2 +
      √(N : ℝ) / 2 * dotp (e0 N) u ^ 2) ∂uniformSphere N := by
    unfold q1
    refine integral_mono_ae (sphere_cont_integrable hN (continuous_kappa_dot (e0 N))) iR ?_
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    have ht := dotp_unit_mem' (Part137.normSq_e0 hN) (show normSq u = 1 from hu)
    set t := dotp (e0 N) u with htd
    have hk1 : kappa t ≤ kappa 0 + |t| := by
      rcases le_total 0 t with h0 | h0
      · have := (kappa_lipschitz (by norm_num : (-1 : ℝ) ≤ 0) h0 ht.2).2
        rw [abs_of_nonneg h0]; linarith
      · have := (kappa_lipschitz ht.1 h0 (by norm_num : (0 : ℝ) ≤ 1)).1
        have := abs_nonneg t
        linarith
    have habs : 2 * |t| ≤ √(N : ℝ) * t ^ 2 + 1 / √(N : ℝ) := by
      have e : √(N : ℝ) * t ^ 2 + 1 / √(N : ℝ) - 2 * |t| =
          (√(N : ℝ) * |t| - 1) ^ 2 / √(N : ℝ) := by
        rw [← sq_abs t]
        field_simp
        ring
      have : 0 ≤ (√(N : ℝ) * |t| - 1) ^ 2 / √(N : ℝ) := by positivity
      linarith
    change kappa t ≤ kappa 0 + 1 / √(N : ℝ) / 2 + √(N : ℝ) / 2 * t ^ 2
    linarith
  rw [integral_add (integrable_const _) (ic.const_mul _), integral_const_mul,
    int_dotp_e0_sq hN] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have e : √(N : ℝ) / 2 * (1 / (N : ℝ)) = 1 / √(N : ℝ) / 2 := by
    field_simp
    linarith [hsm]
  rw [e] at h
  linarith

/-- The common part of `cHat143²` and `cB143²`. -/
lemma first143_le (hN : 8192 ≤ N) (hm : 1000000 ≤ m) :
    2 * (1 + 5 / (m : ℝ)) + 4 * (√((1 + 2 / (N : ℝ)) / (2 * m)) + q1 (e0 N)) ^ 2 ≤
      24368 / 10000 := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (8192 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < m := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by omega
  have hq0 := (q1_mem hN1 (Part137.normSq_e0 hN1)).1
  have hs : (90 : ℝ) ≤ √(N : ℝ) := Real.le_sqrt' (by norm_num) |>.mpr (by linarith)
  have his : 1 / √(N : ℝ) ≤ 1 / 90 := one_div_le_one_div_of_le (by norm_num) hs
  have hq := q1e_le hN1
  have k1 := kappa_zero_le
  have hNle : 2 / (N : ℝ) ≤ 2 / 8192 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have hr : √((1 + 2 / (N : ℝ)) / (2 * m)) ≤ 1 / 1000 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hr0 : 0 ≤ √((1 + 2 / (N : ℝ)) / (2 * m)) := Real.sqrt_nonneg _
  have h1 : 5 / (m : ℝ) ≤ 5 / 1000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
  have h2 := pow_le_pow_left₀ (add_nonneg hr0 hq0)
    (by linarith : √((1 + 2 / (N : ℝ)) / (2 * m)) + q1 (e0 N) ≤
      1 / 1000 + (31831 / 100000 + 1 / 90)) 2
  have h2' : ((1 : ℝ) / 1000 + (31831 / 100000 + 1 / 90)) ^ 2 ≤ 10918 / 100000 := by norm_num
  linarith [h2.trans h2']

lemma cHat143_sq_le (hN : 8192 ≤ N) (hm : 1000000 ≤ m) :
    cHat143 N m ^ 2 ≤ 4465 / 1000 / (m : ℝ) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (8192 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < m := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have k1 := kappa_zero_le
  have k0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have s5 : √(5 : ℝ) ≤ 22361 / 10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have s50 : 0 ≤ √(5 : ℝ) := Real.sqrt_nonneg _
  have hNle : 2 / (N : ℝ) ≤ 2 / 8192 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have sN : √(2 / (N : ℝ)) ≤ 1 / 64 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have sN0 : 0 ≤ √(2 / (N : ℝ)) := Real.sqrt_nonneg _
  have sH : √((1 + 2 / (N : ℝ)) / 2) ≤ 7072 / 10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have sH0 : 0 ≤ √((1 + 2 / (N : ℝ)) / 2) := Real.sqrt_nonneg _
  have hf := first143_le hN hm
  unfold cHat143
  rw [Real.sq_sqrt (by positivity)]
  have h3 : kappa 0 * (√5 + √(2 / (N : ℝ))) ≤ 31831 / 100000 * (22361 / 10000 + 1 / 64) :=
    mul_le_mul k1 (by linarith) (by positivity) (by norm_num)
  have h2 : (kappa 0 * (√5 + √(2 / (N : ℝ))) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 ≤
      (31831 / 100000 * (22361 / 10000 + 1 / 64) + 7072 / 10000) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2' : ((31831 : ℝ) / 100000 * (22361 / 10000 + 1 / 64) + 7072 / 10000) ^ 2 ≤
      20277 / 10000 := by norm_num
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hm0.le
  linarith [h2.trans h2']

lemma cB143_sq_le (hN : 8192 ≤ N) (hm : 1000000 ≤ m) :
    cB143 N m ^ 2 ≤ 2944 / 1000 / (m : ℝ) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (8192 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < m := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have k1 := kappa_zero_le
  have k0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have hNle : 2 / (N : ℝ) ≤ 2 / 8192 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have sN : √(2 / (N : ℝ)) ≤ 1 / 64 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have sN0 : 0 ≤ √(2 / (N : ℝ)) := Real.sqrt_nonneg _
  have sH : √((1 + 2 / (N : ℝ)) / 2) ≤ 7072 / 10000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have sH0 : 0 ≤ √((1 + 2 / (N : ℝ)) / 2) := Real.sqrt_nonneg _
  have hf := first143_le hN hm
  unfold cB143
  rw [Real.sq_sqrt (by positivity)]
  have h3 : kappa 0 * √(2 / (N : ℝ)) ≤ 31831 / 100000 * (1 / 64) :=
    mul_le_mul k1 sN sN0 (by norm_num)
  have h2 : (kappa 0 * √(2 / (N : ℝ)) + √((1 + 2 / (N : ℝ)) / 2)) ^ 2 ≤
      (31831 / 100000 * (1 / 64) + 7072 / 10000) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2' : ((31831 : ℝ) / 100000 * (1 / 64) + 7072 / 10000) ^ 2 ≤ 5072 / 10000 := by norm_num
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hm0.le
  linarith [h2.trans h2']

/-- `cDst143s² ≤ 77.94/m` at the widths of the Focus. -/
lemma cDst143s_sq_le {n : ℕ} (hn : 4096 ≤ n) :
    cDst143s (2 * n) (mW n) ^ 2 ≤ 7794 / 100 / (mW n : ℝ) := by
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have a1 := mul_sqrt_le hmpos (cB143_nonneg (2 * n) (mW n))
    (cB143_sq_le (N := 2 * n) (by omega) hmM) (by norm_num : (0 : ℝ) ≤ 1716 / 1000) (by norm_num)
  have a2 := mul_sqrt_le hmpos (cHat143_nonneg (2 * n) (mW n))
    (cHat143_sq_le (N := 2 * n) (by omega) hmM) (by norm_num : (0 : ℝ) ≤ 2114 / 1000)
    (by norm_num)
  have a3 := mul_sqrt_le hmpos (cH143_nonneg (2 * n) (mW n))
    (cH143_sq_le (N := 2 * n) (by omega) hmM) (by norm_num : (0 : ℝ) ≤ 2884 / 1000)
    (by norm_num)
  have hs : 0 < √(mW n : ℝ) := Real.sqrt_pos.mpr hmpos
  have h0 := cDst143s_nonneg (2 * n) (mW n)
  have h1 : cDst143s (2 * n) (mW n) * √(mW n : ℝ) ≤ 8828 / 1000 := by
    unfold cDst143s
    nlinarith
  have h2 : (cDst143s (2 * n) (mW n) * √(mW n : ℝ)) ^ 2 ≤ (8828 / 1000) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h0 hs.le) h1 2
  rw [mul_pow, Real.sq_sqrt hmpos.le] at h2
  rw [le_div_iff₀ hmpos]
  nlinarith

/-- `Pr(t|b̂ − h̄|² > γ·Xc/N) ≤ 311.76·(n²/m_W)/(Xc − 8/25)²`. -/
theorem goodDist_prob143s {n : ℕ} (hn : 4096 ≤ n) {Xc : ℝ} (hXc : 8 / 25 < Xc) :
    (hidGauss (2 * n) (mW n)).real (goodDist n Xc)ᶜ ≤
      31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (Xc - 8 / 25) ^ 2 := by
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hX0 : 0 < Xc - 8 / 25 := by linarith
  have e : (goodDist n Xc)ᶜ = {θ | 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) <
      dist2 (2 * n) (mW n) θ} := by
    ext θ
    simp [goodDist, not_le]
  rw [e]
  refine (distBad_of_L2 (N := 2 * n) (m := mW n) (by omega)
    (dist2_L2_143s (by omega) hm) hXc).trans ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [hNcast, mul_pow]
  have a := mul_le_mul_of_nonneg_left (cDst143s_sq_le hn) (sq_nonneg (2 * (n : ℝ)))
  have e1 : (2 * (n : ℝ)) ^ 2 * (7794 / 100 / (mW n : ℝ)) =
      31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by ring
  rw [e1] at a
  exact a

/-- `Pr(goodT n dT fails) ≤ 4.465·(n²/m_W)/(n·dT)`. -/
theorem goodT_prob143 {n : ℕ} (hn : 4096 ≤ n) {dT : ℝ} (hdT : 0 < dT) :
    (hidGauss (2 * n) (mW n)).real (goodT n dT)ᶜ ≤
      4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * dT) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  set B : ℝ := (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT / (n : ℝ) with hB
  have hBpos : 0 < B := by rw [hB, hNcast]; positivity
  have hsub : (goodT n dT)ᶜ ⊆ {θ | B < errT θ} := by
    intro θ hθ
    have h1 : ¬ (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT := hθ
    rw [not_le] at h1
    change B < errT θ
    rw [hB, div_lt_iff₀ hnpos]
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (errT_bad143 (N := 2 * n) (m := mW n) hN hm hBpos).trans ?_
  have hc := cHat143_sq_le (N := 2 * n) (m := mW n) (by omega) hmM
  have e : (2 / ((2 * n : ℕ) : ℝ) * cHat143 (2 * n) (mW n)) ^ 2 / B =
      (n : ℝ) * cHat143 (2 * n) (mW n) ^ 2 / dT := by
    rw [hB, hNcast]
    field_simp
  rw [e]
  have h2 : (n : ℝ) * cHat143 (2 * n) (mW n) ^ 2 ≤ (n : ℝ) * (4465 / 1000 / (mW n : ℝ)) :=
    mul_le_mul_of_nonneg_left hc hnpos.le
  have h3 : (n : ℝ) * (4465 / 1000 / (mW n : ℝ)) / dT =
      4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * dT) := by
    field_simp
  rw [← h3]
  exact div_le_div_of_nonneg_right h2 hdT.le

/-- The constant of the two events of the computed centre, sharper, `n ≥ 16384`. -/
noncomputable def cExtra143s : ℝ := 1404 / 100

/-- **The two events of the computed centre, sharper**, `n ≥ 16384`:
`Pr(goodDist n (3/4) fails) + Pr(goodT n (1/400000) fails) ≤ 14.04/n`. -/
theorem goodHatExtra143s {n : ℕ} (hn : 16384 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodDist n (3 / 4))ᶜ +
      (hidGauss (2 * n) (mW n)).real (goodT n (1 / 400000))ᶜ ≤ cExtra143s / (n : ℝ) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hρ := nsq_div_mW_le128 hn
  have h2 := goodDist_prob143s hn4 (Xc := 3 / 4) (by norm_num)
  have h3 := goodT_prob143 hn4 (dT := 1 / 400000) (by norm_num)
  have e1 : (1 : ℝ) / (128 * (n : ℝ)) = 1 / 128 / (n : ℝ) := by field_simp
  rw [e1] at hρ
  have b2 : 31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (3 / 4 - 8 / 25) ^ 2 ≤
      1318 / 100 / (n : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 31176 / 100)
    refine this.trans ?_
    have e4 : (31176 : ℝ) / 100 * (1 / 128 / (n : ℝ)) = 31176 / 100 / 128 / (n : ℝ) := by ring
    have e5 : (1318 : ℝ) / 100 / (n : ℝ) * (3 / 4 - 8 / 25) ^ 2 =
        1318 / 100 * (3 / 4 - 8 / 25) ^ 2 / (n : ℝ) := by ring
    rw [e4, e5]
    refine div_le_div_of_nonneg_right ?_ hnpos.le
    norm_num
  have b3 : 4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * (1 / 400000)) ≤
      86 / 100 / (n : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hnpos]
    have := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 4465 / 1000)
    have h5 : 4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) * (n : ℝ) ≤ 4465 / 1000 * (1 / 128) := by
      have := mul_le_mul_of_nonneg_right this hnpos.le
      refine this.trans (le_of_eq ?_)
      field_simp
    refine h5.trans ?_
    nlinarith
  unfold cExtra143s
  have e3 : (1404 : ℝ) / 100 / (n : ℝ) = 1318 / 100 / (n : ℝ) + 86 / 100 / (n : ℝ) := by ring
  rw [e3]
  exact add_le_add (h2.trans b2) (h3.trans b3)

/-- **The good hidden event for the computed centre, sharper**, `n ≥ 16384`:
`Pr(goodHat n fails) ≤ P143 + cExtra143s/n = 0.000775 + 14.04/n`. -/
theorem goodHat_compl143s {n : ℕ} (hn : 16384 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ P143 + cExtra143s / (n : ℝ) := by
  have h1 := good136_prob143 (n := n) (by omega)
  have h23 := goodHatExtra143s hn
  have hsub : (goodHat n)ᶜ ⊆
      ((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ) ∪ (goodT n (1 / 400000))ᶜ := by
    intro θ hθ
    simp only [goodHat, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have h4 := (measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  linarith

end BstLean.Part143

open BstLean.Part143 in
#print axioms hatFluct143_pt
open BstLean.Part143 in
#print axioms bhatNorm_L2_143
open BstLean.Part143 in
#print axioms dist2_L2_143s
open BstLean.Part143 in
#print axioms goodHatExtra143s
open BstLean.Part143 in
#print axioms goodHat_compl143s
