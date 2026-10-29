import BstLean.Part150CDefs

/-!
# Part 150, item 3: the finite centre against the oracle centre (deterministic form)

Role: `delegations/statements/p150-spec.md`, item 3. Paper source: `onW45-opus-prover.md` §3
(Proposition P45 (i), (ii)) and §1 (`s̃² ≥ 0`).

The replacement bounds enter as HYPOTHESES (`Part150All` instantiates them):
* `hα : ∀ a s, 0 ≤ s → |binMean J (relu(a + s·)) − ψ_s(a)| ≤ α·s`;
* `hβ : ∀ a s, 0 ≤ s → |binMean J (relu(a + s·)²) − E relu(a + sZ)²| ≤ β·s²`;
* `hφ : ∀ s s' x, |ψ_s(x) − ψ_{s'}(x)| ≤ cφ·|s − s'|`.

Results (every one is a deterministic inequality, for every matrix and every `(c, τ ≥ 0)`):
* `c_binW_sum`, `c_binMean_var_nonneg`: total weight `1`; the binomial variance is `≥ 0`.
* `hT_sub_hO`, `hT_sub_hO_sq`: `|h̃_i − h̄_i| ≤ α·s_i`, `|h̃ − h̄|² ≤ α²τ²‖A₁‖²_F`.
* `sT2_eq_var`, `sT2_nonneg`: `s̃² = t·Σ_i Var_binomial ≥ 0` for every input.
* `sT2_le`: `s̃² ≤ t·τ²‖A₁‖²_F`, given `E Z_J² ≤ 1`.
* `gT_sub_gO`: `|γ̃_Γ − γ_Γ| ≤ β·t·τ²‖A₁‖²_F`.
* `sT2_sub_sO2`: `|s̃² − s²| ≤ β tτ²‖A₁‖²_F + t(2ατ‖A₁‖_F·|h̄| + α²τ²‖A₁‖²_F)` (the cross term).
* `secondLayer_coord`: `|binMean J₂ (relu(ã + s̃·)) − ψ_s(a)| ≤ α₂ s̃ + cφ|s̃ − s| + |ã − a|`.
* `bT_sub_bO`: the same for the two centres, coordinate by coordinate.
* `bT_sub_bO_nrm`: the norm form (Proposition P45 (i)):
  `|b̃′ − b′| ≤ √m·(α₂ s̃ + cφ|s̃ − s|) + |A₂(h̃ − h̄)|`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Finset
open BstLean.Part130 BstLean.Part137 BstLean.Part141
open BstLean.Part132 (nrm nrm_sq)

section

variable {n m : ℕ}

/-- The binomial weights have sum `1`. -/
lemma c_binW_sum (J : ℕ) : ∑ j ∈ range (J + 1), binW J j = 1 := by
  unfold binW
  rw [← sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  simp

/-- The variance of `f(Z_J)` is nonnegative: `E f(Z_J)² − (E f(Z_J))² ≥ 0`. -/
lemma c_binMean_var_nonneg (J : ℕ) (f : ℝ → ℝ) :
    0 ≤ binMean J (fun z => f z ^ 2) - binMean J f ^ 2 := by
  have h : binMean J (fun z => f z ^ 2) - binMean J f ^ 2 =
      ∑ j ∈ range (J + 1), binW J j * (f (binAtom J j) - binMean J f) ^ 2 := by
    have e : ∀ j, binW J j * (f (binAtom J j) - binMean J f) ^ 2 =
        binW J j * f (binAtom J j) ^ 2 - 2 * binMean J f * (binW J j * f (binAtom J j)) +
          binMean J f ^ 2 * binW J j := fun j => by ring
    simp_rw [e]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, c_binW_sum]
    have e1 : ∑ j ∈ range (J + 1), binW J j * f (binAtom J j) ^ 2 =
        binMean J (fun z => f z ^ 2) := rfl
    have e2 : ∑ j ∈ range (J + 1), binW J j * f (binAtom J j) = binMean J f := rfl
    rw [e1, e2]
    ring
  rw [h]
  exact sum_nonneg fun j _ => mul_nonneg (binW_nonneg J j) (sq_nonneg _)

lemma sRow_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (i : Fin m) :
    0 ≤ sRow A₁ τ i := mul_nonneg hτ (Real.sqrt_nonneg _)

lemma sRow_sq (A₁ : Matrix (Fin m) (Fin n) ℝ) (τ : ℝ) (i : Fin m) :
    sRow A₁ τ i ^ 2 = τ ^ 2 * ∑ j, A₁ i j ^ 2 := by
  unfold sRow
  rw [mul_pow, Real.sq_sqrt (sum_nonneg fun j _ => sq_nonneg _)]

lemma sum_sRow_sq (A₁ : Matrix (Fin m) (Fin n) ℝ) (τ : ℝ) :
    ∑ i, sRow A₁ τ i ^ 2 = τ ^ 2 * froSq A₁ := by
  simp_rw [sRow_sq]
  rw [← mul_sum]
  rfl

lemma froSq_nonneg (A₁ : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ froSq A₁ :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- **(a)** `|h̃_i − h̄_i| ≤ α·s_i`. -/
theorem hT_sub_hO {J₁ : ℕ} {α : ℝ}
    (hα : ∀ a s : ℝ, 0 ≤ s → |binMean J₁ (fun z => relu (a + s * z)) - psiS s a| ≤ α * s)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (i : Fin m) :
    |hT J₁ A₁ c τ i - hO A₁ c τ i| ≤ α * sRow A₁ τ i :=
  hα _ _ (sRow_nonneg A₁ hτ i)

/-- **(a)** `|h̃ − h̄|² ≤ α²·τ²·‖A₁‖²_F`. -/
theorem hT_sub_hO_sq {J₁ : ℕ} {α : ℝ}
    (hα : ∀ a s : ℝ, 0 ≤ s → |binMean J₁ (fun z => relu (a + s * z)) - psiS s a| ≤ α * s)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∑ i, (hT J₁ A₁ c τ i - hO A₁ c τ i) ^ 2 ≤ α ^ 2 * τ ^ 2 * froSq A₁ := by
  calc ∑ i, (hT J₁ A₁ c τ i - hO A₁ c τ i) ^ 2 ≤ ∑ i, α ^ 2 * sRow A₁ τ i ^ 2 := by
        refine sum_le_sum fun i _ => ?_
        have h := hT_sub_hO hα A₁ c hτ i
        rw [← mul_pow]
        exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    _ = α ^ 2 * τ ^ 2 * froSq A₁ := by rw [← mul_sum, sum_sRow_sq]; ring

/-- **(b)** `s̃² = t·Σ_i (E relu(m_i + s_i Z_J)² − (E relu(m_i + s_i Z_J))²)`. -/
theorem sT2_eq_var (J₁ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    sT2 J₁ A₁ c τ = 2 / (m : ℝ) * ∑ i,
      (binMean J₁ (fun z => relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2) -
        binMean J₁ (fun z => relu (mRow A₁ c i + sRow A₁ τ i * z)) ^ 2) := by
  unfold sT2 gT hT
  rw [sum_sub_distrib, mul_sub]

/-- **(b)** `s̃² ≥ 0` for every input (the two moments use the same weights). -/
theorem sT2_nonneg (J₁ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    0 ≤ sT2 J₁ A₁ c τ := by
  rw [sT2_eq_var]
  exact mul_nonneg (by positivity) (sum_nonneg fun i _ => c_binMean_var_nonneg J₁ _)

/-- **(c)** `|γ̃_Γ − γ_Γ| ≤ β·t·τ²·‖A₁‖²_F`. -/
theorem gT_sub_gO {J₁ : ℕ} {β : ℝ}
    (hβ : ∀ a s : ℝ, 0 ≤ s → |binMean J₁ (fun z => relu (a + s * z) ^ 2) -
      ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤ β * s ^ 2)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    |gT J₁ A₁ c τ - gO A₁ c τ| ≤ β * (2 / (m : ℝ)) * τ ^ 2 * froSq A₁ := by
  have ht : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  unfold gT gO
  rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_nonneg ht]
  calc 2 / (m : ℝ) * |∑ i, (binMean J₁ (fun z => relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2) -
        ∫ z, relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2 ∂gaussianReal 0 1)|
      ≤ 2 / (m : ℝ) * ∑ i, β * sRow A₁ τ i ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ ht
        exact (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun i _ => hβ _ _ (sRow_nonneg A₁ hτ i))
    _ = β * (2 / (m : ℝ)) * τ ^ 2 * froSq A₁ := by rw [← mul_sum, sum_sRow_sq]; ring

/-- **(ii), the scale**: `|s̃² − s²| ≤ β tτ²‖A₁‖²_F + t(2ατ‖A₁‖_F·|h̄| + α²τ²‖A₁‖²_F)`. The middle
term is the cross term `2t⟨e, h̄⟩` of the paper (`e = h̃ − h̄`), of first order in `α`. -/
theorem sT2_sub_sO2 {J₁ : ℕ} {α β : ℝ} (hα0 : 0 ≤ α)
    (hα : ∀ a s : ℝ, 0 ≤ s → |binMean J₁ (fun z => relu (a + s * z)) - psiS s a| ≤ α * s)
    (hβ : ∀ a s : ℝ, 0 ≤ s → |binMean J₁ (fun z => relu (a + s * z) ^ 2) -
      ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤ β * s ^ 2)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    |sT2 J₁ A₁ c τ - sO2 A₁ c τ| ≤ β * (2 / (m : ℝ)) * τ ^ 2 * froSq A₁ +
      2 / (m : ℝ) * (2 * (α * τ * √(froSq A₁)) * √(∑ i, hO A₁ c τ i ^ 2) +
        α ^ 2 * τ ^ 2 * froSq A₁) := by
  have ht : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hE := hT_sub_hO_sq hα A₁ c hτ
  set e : Fin m → ℝ := fun i => hT J₁ A₁ c τ i - hO A₁ c τ i with he
  have hE' : ∑ i, e i ^ 2 ≤ α ^ 2 * τ ^ 2 * froSq A₁ := hE
  have hE0 : 0 ≤ ∑ i, e i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hH0 : 0 ≤ ∑ i, hO A₁ c τ i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hcs : |∑ i, e i * hO A₁ c τ i| ≤ α * τ * √(froSq A₁) * √(∑ i, hO A₁ c τ i ^ 2) := by
    have h1 : (∑ i, e i * hO A₁ c τ i) ^ 2 ≤ (∑ i, e i ^ 2) * ∑ i, hO A₁ c τ i ^ 2 :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    have h2 : |∑ i, e i * hO A₁ c τ i| ≤ √((∑ i, e i ^ 2) * ∑ i, hO A₁ c τ i ^ 2) :=
      Real.abs_le_sqrt h1
    rw [Real.sqrt_mul hE0] at h2
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    calc √(∑ i, e i ^ 2) ≤ √(α ^ 2 * τ ^ 2 * froSq A₁) := Real.sqrt_le_sqrt hE'
      _ = α * τ * √(froSq A₁) := by
          rw [← mul_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hα0 hτ)]
  have hsq : ∑ i, hT J₁ A₁ c τ i ^ 2 - ∑ i, hO A₁ c τ i ^ 2 =
      2 * ∑ i, e i * hO A₁ c τ i + ∑ i, e i ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [he]
    ring
  have hd : sT2 J₁ A₁ c τ - sO2 A₁ c τ = (gT J₁ A₁ c τ - gO A₁ c τ) -
      2 / (m : ℝ) * (2 * ∑ i, e i * hO A₁ c τ i + ∑ i, e i ^ 2) := by
    rw [← hsq]
    unfold sT2 sO2
    ring
  rw [hd]
  have hg := gT_sub_gO hβ A₁ c hτ
  have h3 : |2 * ∑ i, e i * hO A₁ c τ i + ∑ i, e i ^ 2| ≤
      2 * (α * τ * √(froSq A₁)) * √(∑ i, hO A₁ c τ i ^ 2) + α ^ 2 * τ ^ 2 * froSq A₁ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hE0]
    nlinarith [hcs, hE']
  calc |gT J₁ A₁ c τ - gO A₁ c τ - 2 / (m : ℝ) * (2 * ∑ i, e i * hO A₁ c τ i + ∑ i, e i ^ 2)|
      ≤ |gT J₁ A₁ c τ - gO A₁ c τ| +
        |2 / (m : ℝ) * (2 * ∑ i, e i * hO A₁ c τ i + ∑ i, e i ^ 2)| := abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg ht]
        exact add_le_add hg (mul_le_mul_of_nonneg_left h3 ht)

/-- **(d)** The second-layer inequality for one coordinate:
`|E relu(ã + s̃ Z_J) − ψ_s(a)| ≤ α₂·s̃ + cφ·|s̃ − s| + |ã − a|`. -/
theorem secondLayer_coord {J₂ : ℕ} {α₂ cφ : ℝ}
    (hα : ∀ a s : ℝ, 0 ≤ s → |binMean J₂ (fun z => relu (a + s * z)) - psiS s a| ≤ α₂ * s)
    (hφ : ∀ s s' x : ℝ, |psiS s x - psiS s' x| ≤ cφ * |s - s'|)
    (at' a : ℝ) {st : ℝ} (hst : 0 ≤ st) (s : ℝ) :
    |binMean J₂ (fun z => relu (at' + st * z)) - psiS s a| ≤
      α₂ * st + cφ * |st - s| + |at' - a| := by
  have h1 := hα at' st hst
  have h2 := hφ st s at'
  have h3 := psiS_lip_x s at' a
  have e : binMean J₂ (fun z => relu (at' + st * z)) - psiS s a =
      (binMean J₂ (fun z => relu (at' + st * z)) - psiS st at') +
        (psiS st at' - psiS s at') + (psiS s at' - psiS s a) := by ring
  rw [e]
  exact (abs_add_three _ _ _).trans (add_le_add (add_le_add h1 h2) h3)

/-- **(d)** The two centres, coordinate by coordinate:
`|b̃′_j − b′_j| ≤ α₂·s̃ + cφ·|s̃ − s| + |(A₂(h̃ − h̄))_j|`. -/
theorem bT_sub_bO {J₂ : ℕ} {α₂ cφ : ℝ}
    (hα : ∀ a s : ℝ, 0 ≤ s → |binMean J₂ (fun z => relu (a + s * z)) - psiS s a| ≤ α₂ * s)
    (hφ : ∀ s s' x : ℝ, |psiS s x - psiS s' x| ≤ cφ * |s - s'|)
    (J₁ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (j : Fin m) :
    |bT J₁ J₂ A₁ A₂ c τ j - bO A₁ A₂ c τ j| ≤
      α₂ * sT J₁ A₁ c τ + cφ * |sT J₁ A₁ c τ - sO A₁ c τ| +
        |(A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ)) j| := by
  have h := secondLayer_coord hα hφ ((A₂.mulVec (hT J₁ A₁ c τ)) j) ((A₂.mulVec (hO A₁ c τ)) j)
    (Real.sqrt_nonneg (sT2 J₁ A₁ c τ)) (sO A₁ c τ)
  rw [Matrix.mulVec_sub]
  exact h

/-- A norm bound from a coordinate bound: if `|x_j| ≤ K + |y_j|` for every `j`, then
`|x| ≤ √m·K + |y|`. -/
lemma nrm_le_of_coord {x y : Fin m → ℝ} {K : ℝ} (hK : 0 ≤ K) (h : ∀ j, |x j| ≤ K + |y j|) :
    nrm x ≤ √(m : ℝ) * K + nrm y := by
  have hy0 : 0 ≤ nrm y := Real.sqrt_nonneg _
  have h1 : ∑ j, |y j| ≤ √(m : ℝ) * nrm y := by
    have hc : (∑ j : Fin m, 1 * |y j|) ^ 2 ≤ (∑ _j : Fin m, (1 : ℝ) ^ 2) * ∑ j, |y j| ^ 2 :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      sq_abs] at hc
    have h2 := Real.abs_le_sqrt hc
    rw [Real.sqrt_mul (Nat.cast_nonneg m)] at h2
    exact (le_abs_self _).trans h2
  have h3 : normSq x ≤ (√(m : ℝ) * K + nrm y) ^ 2 := by
    calc normSq x = ∑ j, |x j| ^ 2 := by simp only [normSq, sq_abs]
      _ ≤ ∑ j, (K + |y j|) ^ 2 :=
          sum_le_sum fun j _ => pow_le_pow_left₀ (abs_nonneg _) (h j) 2
      _ = (m : ℝ) * K ^ 2 + 2 * K * ∑ j, |y j| + normSq y := by
          simp only [add_sq, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
            nsmul_eq_mul, sq_abs, normSq, ← mul_sum]
      _ ≤ (m : ℝ) * K ^ 2 + 2 * K * (√(m : ℝ) * nrm y) + normSq y := by
          gcongr
      _ = (√(m : ℝ) * K + nrm y) ^ 2 := by
          rw [add_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), nrm_sq]
          ring
  calc nrm x = √(normSq x) := rfl
    _ ≤ √((√(m : ℝ) * K + nrm y) ^ 2) := Real.sqrt_le_sqrt h3
    _ = √(m : ℝ) * K + nrm y :=
        Real.sqrt_sq (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK) hy0)

/-- **(d), the norm form (Proposition P45 (i))**:
`|b̃′ − b′| ≤ √m·(α₂·s̃ + cφ·|s̃ − s|) + |A₂(h̃ − h̄)|`. Multiply by `√t = √(2/m)` for the form of
the paper: `√t|b̃′ − b′| ≤ √2·α₂ s̃ + √2·cφ|s̃ − s| + √t|A₂ e|`. -/
theorem bT_sub_bO_nrm {J₂ : ℕ} {α₂ cφ : ℝ} (hα0 : 0 ≤ α₂) (hφ0 : 0 ≤ cφ)
    (hα : ∀ a s : ℝ, 0 ≤ s → |binMean J₂ (fun z => relu (a + s * z)) - psiS s a| ≤ α₂ * s)
    (hφ : ∀ s s' x : ℝ, |psiS s x - psiS s' x| ≤ cφ * |s - s'|)
    (J₁ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) :
    nrm (bT J₁ J₂ A₁ A₂ c τ - bO A₁ A₂ c τ) ≤
      √(m : ℝ) * (α₂ * sT J₁ A₁ c τ + cφ * |sT J₁ A₁ c τ - sO A₁ c τ|) +
        nrm (A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ)) :=
  nrm_le_of_coord
    (add_nonneg (mul_nonneg hα0 (Real.sqrt_nonneg _)) (mul_nonneg hφ0 (abs_nonneg _)))
    (fun j => bT_sub_bO hα hφ J₁ A₁ A₂ c τ j)

/-- The variance of `f(Z_J)` is at most the mean square about any constant `a`. -/
lemma c_binMean_var_le (J : ℕ) (f : ℝ → ℝ) (a : ℝ) :
    binMean J (fun z => f z ^ 2) - binMean J f ^ 2 ≤ binMean J (fun z => (f z - a) ^ 2) := by
  have h : binMean J (fun z => (f z - a) ^ 2) =
      binMean J (fun z => f z ^ 2) - 2 * a * binMean J f + a ^ 2 := by
    have e : ∀ j, binW J j * (f (binAtom J j) - a) ^ 2 =
        binW J j * f (binAtom J j) ^ 2 - 2 * a * (binW J j * f (binAtom J j)) +
          a ^ 2 * binW J j := fun j => by ring
    unfold binMean
    simp_rw [e]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, c_binW_sum, mul_one]
  rw [h]
  nlinarith [sq_nonneg (binMean J f - a)]

/-- **(b), upper side**: `s̃² ≤ t·τ²·‖A₁‖²_F`, given `E Z_J² ≤ 1` (`relu` is 1-Lipschitz). -/
theorem sT2_le {J₁ : ℕ} (h2 : binMean J₁ (fun z => z ^ 2) ≤ 1)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    sT2 J₁ A₁ c τ ≤ 2 / (m : ℝ) * (τ ^ 2 * froSq A₁) := by
  rw [sT2_eq_var, ← sum_sRow_sq]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => ?_) (by positivity)
  refine (c_binMean_var_le J₁ _ (relu (mRow A₁ c i))).trans ?_
  calc binMean J₁ (fun z => (relu (mRow A₁ c i + sRow A₁ τ i * z) - relu (mRow A₁ c i)) ^ 2)
      ≤ binMean J₁ (fun z => sRow A₁ τ i ^ 2 * z ^ 2) := by
        unfold binMean
        refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (binW_nonneg _ _)
        have h := relu_lip (mRow A₁ c i + sRow A₁ τ i * binAtom J₁ j) (mRow A₁ c i)
        rw [add_sub_cancel_left] at h
        change _ ^ 2 ≤ sRow A₁ τ i ^ 2 * binAtom J₁ j ^ 2
        rw [← mul_pow]
        exact sq_le_sq.mpr h
    _ = sRow A₁ τ i ^ 2 * binMean J₁ (fun z => z ^ 2) := by
        unfold binMean
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        ring
    _ ≤ sRow A₁ τ i ^ 2 := by nlinarith [sq_nonneg (sRow A₁ τ i)]

end

end BstLean.Part150
