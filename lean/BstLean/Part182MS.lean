import BstLean.Part182Def

/-!
# Part 182 (file `MS`): mode separation for the two-input Jacobian product

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:MS`.
For unit inputs `x`, `x'` with `c = x·x'`, `c² < 1`: `e = eTan x x' = (x' − cx)/√(1−c²)`,
`e' = eTan x' x`, `P_E = PEm x x' = I − xxᵀ − eeᵀ` (the projection on `span(x, x')^⊥`; also
`I − x'x'ᵀ − e'e'ᵀ`, `PEm_alt`).

* `ms_two`: the 2×2 bound `kE A A' + ko(AB' + BA') + ks BB' ≤ λ√(A²+B²)√(A'²+B'²)`,
  `λ = (kE+ks)/2 + √(((kE−ks)/2)² + ko²)`, nonnegative entries.
* `ms_opN`: from the three pair bounds (`‖P_E JᵀJ'P_E‖ ≤ K_E`, `|P_E JᵀJ'e'|, |P_E J'ᵀJe| ≤ K_O`,
  `|⟨Je, J'e'⟩| ≤ K_S`), `‖(JΠ_x)ᵀ(J'Π_{x'})‖_op ≤ λ(K_E, K_O, K_S)`.
* `ms_opN_n`: the same with `K = n k`, conclusion `n λ(k_E, k_o, k_s)`; with `J = jac A₁ A₂ x`
  the left side is the operator norm in `pairBad` (file `Def`), since `jacT = jac * projT`.
-/

namespace BstLean.Part182

open Real Matrix
open BstLean.Part130 BstLean.Part152
open BstLean.Part153 (nrm projT abs_dot_le_nrm)

lemma ms_quad_up {p q ko : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p * q = ko ^ 2) (z1 z2 : ℝ) :
    0 ≤ p * z1 ^ 2 - 2 * ko * z1 * z2 + q * z2 ^ 2 := by
  rcases hp.lt_or_eq with hp' | hp'
  · have h : p * (p * z1 ^ 2 - 2 * ko * z1 * z2 + q * z2 ^ 2) = (p * z1 - ko * z2) ^ 2 := by
      have : p * (q * z2 ^ 2) = ko ^ 2 * z2 ^ 2 := by rw [← mul_assoc, hpq]
      nlinarith
    exact (mul_nonneg_iff_of_pos_left hp').mp (h ▸ sq_nonneg _)
  · have hko : ko = 0 := by
      have : ko ^ 2 = 0 := by rw [← hpq, ← hp']; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    rw [hko, ← hp']; nlinarith [mul_nonneg hq (sq_nonneg z2)]

lemma ms_quad_lo {kE ko ks lam : ℝ} (hE : 0 ≤ kE) (ho : 0 ≤ ko) (hs : 0 ≤ ks) (hl : ko ≤ lam)
    (z1 z2 : ℝ) : -(lam * (z1 ^ 2 + z2 ^ 2)) ≤ kE * z1 ^ 2 + 2 * ko * z1 * z2 + ks * z2 ^ 2 := by
  nlinarith [mul_nonneg ho (sq_nonneg (z1 + z2)), mul_nonneg hE (sq_nonneg z1),
    mul_nonneg hs (sq_nonneg z2), mul_nonneg (sub_nonneg.mpr hl) (add_nonneg (sq_nonneg z1) (sq_nonneg z2))]

lemma ms_pol {kE ko ks lam : ℝ}
    (Qup : ∀ z1 z2 : ℝ, kE * z1 ^ 2 + 2 * ko * z1 * z2 + ks * z2 ^ 2 ≤ lam * (z1 ^ 2 + z2 ^ 2))
    (Qlo : ∀ z1 z2 : ℝ, -(lam * (z1 ^ 2 + z2 ^ 2)) ≤ kE * z1 ^ 2 + 2 * ko * z1 * z2 + ks * z2 ^ 2)
    (x1 x2 y1 y2 : ℝ) : 4 * (kE * x1 * y1 + ko * (x1 * y2 + x2 * y1) + ks * x2 * y2) ≤
      2 * lam * ((x1 ^ 2 + x2 ^ 2) + (y1 ^ 2 + y2 ^ 2)) := by
  have h1 := Qup (x1 + y1) (x2 + y2)
  have h2 := Qlo (x1 - y1) (x2 - y2)
  nlinarith

lemma ms_scale {kE ko ks lam : ℝ}
    (pol : ∀ x1 x2 y1 y2 : ℝ, 4 * (kE * x1 * y1 + ko * (x1 * y2 + x2 * y1) + ks * x2 * y2) ≤
      2 * lam * ((x1 ^ 2 + x2 ^ 2) + (y1 ^ 2 + y2 ^ 2))) (A B A' B' : ℝ) :
    kE * A * A' + ko * (A * B' + B * A') + ks * B * B' ≤
      lam * (√(A ^ 2 + B ^ 2) * √(A' ^ 2 + B' ^ 2)) := by
  obtain ⟨N, hNd⟩ : ∃ N, N = √(A ^ 2 + B ^ 2) := ⟨_, rfl⟩
  obtain ⟨N', hNd'⟩ : ∃ N', N' = √(A' ^ 2 + B' ^ 2) := ⟨_, rfl⟩
  rw [← hNd, ← hNd']
  have hN : N ^ 2 = A ^ 2 + B ^ 2 := by rw [hNd]; exact Real.sq_sqrt (by positivity)
  have hN' : N' ^ 2 = A' ^ 2 + B' ^ 2 := by rw [hNd']; exact Real.sq_sqrt (by positivity)
  have hN0 : 0 ≤ N := by rw [hNd]; exact Real.sqrt_nonneg _
  have hN0' : 0 ≤ N' := by rw [hNd']; exact Real.sqrt_nonneg _
  have key := pol (N' * A) (N' * B) (N * A') (N * B')
  have e1 : (N' * A) ^ 2 + (N' * B) ^ 2 = N ^ 2 * N' ^ 2 := by rw [hN]; ring
  have e2 : (N * A') ^ 2 + (N * B') ^ 2 = N ^ 2 * N' ^ 2 := by rw [hN']; ring
  rw [e1, e2] at key
  have e3 : kE * (N' * A) * (N * A') + ko * (N' * A * (N * B') + N' * B * (N * A')) +
      ks * (N' * B) * (N * B') = (N * N') * (kE * A * A' + ko * (A * B' + B * A') + ks * B * B') := by
    ring
  rw [e3] at key
  have key2 : (N * N') * (kE * A * A' + ko * (A * B' + B * A') + ks * B * B') ≤
      (N * N') * (lam * (N * N')) := by nlinarith
  rcases (mul_nonneg hN0 hN0').lt_or_eq with hpos | hz
  · exact le_of_mul_le_mul_left key2 hpos
  · rcases mul_eq_zero.mp hz.symm with h | h
    · have : A ^ 2 + B ^ 2 = 0 := by rw [← hN, h]; ring
      have hA : A = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
      have hB : B = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
      rw [hA, hB, ← hz]; simp
    · have : A' ^ 2 + B' ^ 2 = 0 := by rw [← hN', h]; ring
      have hA : A' = 0 := by nlinarith [sq_nonneg A', sq_nonneg B']
      have hB : B' = 0 := by nlinarith [sq_nonneg A', sq_nonneg B']
      rw [hA, hB, ← hz]; simp

/-- **The 2×2 bilinear bound of mode separation**: for `M = [[kE, ko], [ko, ks]]` with
nonnegative entries and `λ = (kE+ks)/2 + √(((kE−ks)/2)² + ko²)`,
`kE A A' + ko(A B' + B A') + ks B B' ≤ λ √(A²+B²) √(A'²+B'²)`. -/
theorem ms_two {kE ko ks : ℝ} (hE : 0 ≤ kE) (ho : 0 ≤ ko) (hs : 0 ≤ ks) (A B A' B' : ℝ) :
    kE * A * A' + ko * (A * B' + B * A') + ks * B * B' ≤
      ((kE + ks) / 2 + √(((kE - ks) / 2) ^ 2 + ko ^ 2)) *
        (√(A ^ 2 + B ^ 2) * √(A' ^ 2 + B' ^ 2)) := by
  obtain ⟨R, hRd⟩ : ∃ R, R = √(((kE - ks) / 2) ^ 2 + ko ^ 2) := ⟨_, rfl⟩
  rw [← hRd]
  have hR0 : 0 ≤ R := by rw [hRd]; exact Real.sqrt_nonneg _
  have hR2 : R ^ 2 = ((kE - ks) / 2) ^ 2 + ko ^ 2 := by rw [hRd]; exact Real.sq_sqrt (by positivity)
  have hRd1 : |(kE - ks) / 2| ≤ R := by
    rw [hRd, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hRo : ko ≤ R := by nlinarith
  have hab := abs_le.mp hRd1
  have hpq : ((kE + ks) / 2 + R - kE) * ((kE + ks) / 2 + R - ks) = ko ^ 2 := by
    have : ((kE + ks) / 2 + R - kE) * ((kE + ks) / 2 + R - ks) = R ^ 2 - ((kE - ks) / 2) ^ 2 := by
      ring
    rw [this, hR2]; ring
  have Qup : ∀ z1 z2 : ℝ, kE * z1 ^ 2 + 2 * ko * z1 * z2 + ks * z2 ^ 2 ≤
      ((kE + ks) / 2 + R) * (z1 ^ 2 + z2 ^ 2) := by
    intro z1 z2
    have := ms_quad_up (by linarith) (by linarith) hpq z1 z2
    nlinarith
  have Qlo : ∀ z1 z2 : ℝ, -(((kE + ks) / 2 + R) * (z1 ^ 2 + z2 ^ 2)) ≤
      kE * z1 ^ 2 + 2 * ko * z1 * z2 + ks * z2 ^ 2 :=
    ms_quad_lo hE ho hs (by linarith)
  exact ms_scale (ms_pol Qup Qlo) A B A' B'


/-! ## The pair decomposition -/

variable {n m : ℕ}

/-- The tangent direction `e = (x' − c x)/√(1 − c²)`, `c = x·x'`. -/
noncomputable def eTan (x x' : Fin n → ℝ) : Fin n → ℝ :=
  (√(1 - (x ⬝ᵥ x') ^ 2))⁻¹ • (x' - (x ⬝ᵥ x') • x)

/-- The projection `P_E = I − x xᵀ − e eᵀ` on `span(x, x')^⊥`. -/
noncomputable def PEm (x x' : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - vecMulVec x x - vecMulVec (eTan x x') (eTan x x')

lemma PEm_mulVec (x x' w : Fin n → ℝ) :
    PEm x x' *ᵥ w = w - (x ⬝ᵥ w) • x - (eTan x x' ⬝ᵥ w) • eTan x x' := by
  unfold PEm
  rw [sub_mulVec, sub_mulVec, one_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    op_smul_eq_smul]

lemma ms_dot_self (x : Fin n → ℝ) : x ⬝ᵥ x = normSq x := by
  unfold normSq dotProduct; simp [sq]

section unit
variable {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
  (hc : (x ⬝ᵥ x') ^ 2 < 1)
include hx hx' hc

lemma eTan_dot_x : eTan x x' ⬝ᵥ x = 0 := by
  unfold eTan
  rw [smul_dotProduct, sub_dotProduct, smul_dotProduct, ms_dot_self, hx, dotProduct_comm x' x]
  simp

lemma eTan_dot_self : eTan x x' ⬝ᵥ eTan x x' = 1 := by
  unfold eTan
  rw [smul_dotProduct, dotProduct_smul]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    ms_dot_self, hx, hx', dotProduct_comm x' x]
  have h1 : 0 < 1 - (x ⬝ᵥ x') ^ 2 := by linarith
  have hs := Real.sq_sqrt h1.le
  have hs0 : √(1 - (x ⬝ᵥ x') ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  field_simp
  nlinarith [hs]

lemma PEm_idem (w : Fin n → ℝ) : PEm x x' *ᵥ (PEm x x' *ᵥ w) = PEm x x' *ᵥ w := by
  have h1 := eTan_dot_x hx hx' hc
  have h2 := eTan_dot_self hx hx' hc
  have hxx : x ⬝ᵥ x = 1 := by rw [ms_dot_self, hx]
  have hxe : x ⬝ᵥ eTan x x' = 0 := by rw [dotProduct_comm]; exact h1
  conv_lhs => rw [PEm_mulVec x x' (PEm x x' *ᵥ w)]
  have a1 : x ⬝ᵥ (PEm x x' *ᵥ w) = 0 := by
    rw [PEm_mulVec]; simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, hxx, hxe]; ring
  have a2 : eTan x x' ⬝ᵥ (PEm x x' *ᵥ w) = 0 := by
    rw [PEm_mulVec]; simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, h1, h2]; ring
  rw [a1, a2]; simp

/-- `P_E = I − x'x'ᵀ − e'e'ᵀ` as well. -/
lemma PEm_alt (w : Fin n → ℝ) :
    PEm x x' *ᵥ w = w - (x' ⬝ᵥ w) • x' - (eTan x' x ⬝ᵥ w) • eTan x' x := by
  rw [PEm_mulVec]
  have h1 : 0 < 1 - (x ⬝ᵥ x') ^ 2 := by linarith
  have hs := Real.sq_sqrt h1.le
  have hs0 : √(1 - (x ⬝ᵥ x') ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  have hcomm : x' ⬝ᵥ x = x ⬝ᵥ x' := dotProduct_comm _ _
  unfold eTan
  rw [hcomm]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, smul_dotProduct, sub_dotProduct]
  generalize x ⬝ᵥ x' = c at h1 hs hs0
  generalize √(1 - c ^ 2) = σ at hs hs0
  field_simp
  rw [hs]
  ring

end unit

lemma PEm_symm (x x' a b : Fin n → ℝ) : (PEm x x' *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (PEm x x' *ᵥ b) := by
  rw [PEm_mulVec, PEm_mulVec]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm b x, dotProduct_comm b (eTan x x'), dotProduct_comm x a,
    dotProduct_comm (eTan x x') a]
  ring

lemma ms_opN_le_of_bil {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u v, u ⬝ᵥ M *ᵥ v ≤ C * (nrm u * nrm v)) : opN M ≤ C := by
  by_cases hne : (opSet M).Nonempty
  · refine csSup_le hne ?_
    rintro y ⟨u, v, hu, hv, rfl⟩
    have hu' : nrm u = 1 := by unfold nrm normSq; rw [hu, Real.sqrt_one]
    have hv' : nrm v = 1 := by unfold nrm normSq; rw [hv, Real.sqrt_one]
    have := h u v
    rwa [hu', hv', mul_one, mul_one] at this
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold opN
    rw [hne, Real.sSup_empty]
    exact hC

lemma ms_abs_bil_le_opN {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (u : Fin p → ℝ) (v : Fin q → ℝ) :
    |u ⬝ᵥ M *ᵥ v| ≤ opN M * (nrm u * nrm v) := by
  have h1 := bil_le_opN_mul M u v
  have h2 := bil_le_opN_mul M (-u) v
  have e : √(∑ i, (-u) i ^ 2) = √(∑ i, u i ^ 2) := by simp
  rw [e, neg_dotProduct] at h2
  exact abs_le.mpr ⟨by unfold nrm normSq; linarith, by unfold nrm normSq; linarith⟩


lemma ms_bil {p q : ℕ} (J : Matrix (Fin m) (Fin p) ℝ) (J' : Matrix (Fin m) (Fin q) ℝ)
    (a : Fin p → ℝ) (b : Fin q → ℝ) : (J *ᵥ a) ⬝ᵥ (J' *ᵥ b) = a ⬝ᵥ (Jᵀ * J') *ᵥ b := by
  rw [← mulVec_mulVec, dotProduct_mulVec a, vecMul_transpose]

lemma ms_PE_dot_x (x x' w : Fin n → ℝ) (hx : normSq x = 1) (h1 : eTan x x' ⬝ᵥ x = 0) :
    x ⬝ᵥ (PEm x x' *ᵥ w) = 0 := by
  have hxx : x ⬝ᵥ x = 1 := by rw [ms_dot_self, hx]
  have hxe : x ⬝ᵥ eTan x x' = 0 := by rw [dotProduct_comm]; exact h1
  rw [PEm_mulVec]; simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, hxx, hxe]; ring

lemma ms_PE_dot_e (x x' w : Fin n → ℝ) (h1 : eTan x x' ⬝ᵥ x = 0) (h2 : eTan x x' ⬝ᵥ eTan x x' = 1) :
    eTan x x' ⬝ᵥ (PEm x x' *ᵥ w) = 0 := by
  rw [PEm_mulVec]; simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, h1, h2]; ring

lemma ms_pyth (α e : Fin n → ℝ) (β : ℝ) (h0 : e ⬝ᵥ α = 0) (h1 : e ⬝ᵥ e = 1) :
    normSq (α + β • e) = normSq α + β ^ 2 := by
  rw [← ms_dot_self, ← ms_dot_self]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm α e, h0, h1]
  ring

lemma ms_normSq_projT_le {x : Fin n → ℝ} (hx : normSq x = 1) (u : Fin n → ℝ) :
    normSq (projT x *ᵥ u) ≤ normSq u ∧ x ⬝ᵥ (projT x *ᵥ u) = 0 := by
  rw [BstLean.Part153.projT_mulVec_sj]
  have hxx : x ⬝ᵥ x = 1 := by rw [ms_dot_self, hx]
  constructor
  · rw [← ms_dot_self, ← ms_dot_self]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm u x, hxx]
    nlinarith [sq_nonneg (x ⬝ᵥ u)]
  · simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, hxx]; ring

/-- Real-number combination of the four pair terms. -/
lemma ms_comb {KE KO KS t1 t2 t3 t4 A A' β β' : ℝ} (hE0 : 0 ≤ KE) (hO0 : 0 ≤ KO) (hS0 : 0 ≤ KS)
    (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (T1 : |t1| ≤ KE * (A * A')) (T2 : |t2| ≤ A * KO) (T3 : |t3| ≤ A' * KO) (T4 : |t4| ≤ KS) :
    t1 + β' * t2 + β * t3 + β * β' * t4 ≤
      ((KE + KS) / 2 + √(((KE - KS) / 2) ^ 2 + KO ^ 2)) *
        (√(A ^ 2 + β ^ 2) * √(A' ^ 2 + β' ^ 2)) := by
  have hm := ms_two hE0 hO0 hS0 A |β| A' |β'|
  rw [sq_abs, sq_abs] at hm
  refine le_trans ?_ hm
  have a1 : β' * t2 ≤ |β'| * (A * KO) := by
    calc _ ≤ |β' * t2| := le_abs_self _
      _ = |β'| * |t2| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left T2 (abs_nonneg _)
  have a2 : β * t3 ≤ |β| * (A' * KO) := by
    calc _ ≤ |β * t3| := le_abs_self _
      _ = |β| * |t3| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left T3 (abs_nonneg _)
  have a3 : β * β' * t4 ≤ |β| * |β'| * KS := by
    calc _ ≤ |β * β' * t4| := le_abs_self _
      _ = |β| * |β'| * |t4| := by rw [abs_mul, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left T4 (by positivity)
  have a0 := (abs_le.mp T1).2
  nlinarith

/-- The pair bound for tangent vectors `f ⊥ x`, `f' ⊥ x'`. -/
lemma ms_core {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (J J' : Matrix (Fin m) (Fin n) ℝ) {KE KO KS : ℝ}
    (hE0 : 0 ≤ KE) (hO0 : 0 ≤ KO) (hS0 : 0 ≤ KS)
    (hE : opN (PEm x x' * (Jᵀ * J') * PEm x x') ≤ KE)
    (hO1 : nrm (PEm x x' *ᵥ ((Jᵀ * J') *ᵥ eTan x' x)) ≤ KO)
    (hO2 : nrm (PEm x x' *ᵥ ((J'ᵀ * J) *ᵥ eTan x x')) ≤ KO)
    (hS : |(J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)| ≤ KS)
    {f f' : Fin n → ℝ} (hxf : x ⬝ᵥ f = 0) (hxf' : x' ⬝ᵥ f' = 0) :
    (J *ᵥ f) ⬝ᵥ (J' *ᵥ f') ≤ ((KE + KS) / 2 + √(((KE - KS) / 2) ^ 2 + KO ^ 2)) *
      (√(normSq f) * √(normSq f')) := by
  have hc' : (x' ⬝ᵥ x) ^ 2 < 1 := by rw [dotProduct_comm]; exact hc
  have e1 := eTan_dot_x hx hx' hc
  have e2 := eTan_dot_self hx hx' hc
  have e1' := eTan_dot_x hx' hx hc'
  have e2' := eTan_dot_self hx' hx hc'
  have hf : f = PEm x x' *ᵥ f + (eTan x x' ⬝ᵥ f) • eTan x x' := by
    rw [PEm_mulVec, hxf]; simp
  have hf' : f' = PEm x x' *ᵥ f' + (eTan x' x ⬝ᵥ f') • eTan x' x := by
    rw [PEm_alt hx hx' hc, hxf']; simp
  have hPe' : eTan x' x ⬝ᵥ (PEm x x' *ᵥ f') = 0 := by
    rw [PEm_alt hx hx' hc]
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, e1', e2']; ring
  have hPe : eTan x x' ⬝ᵥ (PEm x x' *ᵥ f) = 0 := ms_PE_dot_e x x' f e1 e2
  have hN : normSq f = normSq (PEm x x' *ᵥ f) + (eTan x x' ⬝ᵥ f) ^ 2 := by
    rw [← ms_pyth _ _ _ hPe e2, ← hf]
  have hN' : normSq f' = normSq (PEm x x' *ᵥ f') + (eTan x' x ⬝ᵥ f') ^ 2 := by
    rw [← ms_pyth _ _ _ hPe' e2', ← hf']
  have hPα : PEm x x' *ᵥ (PEm x x' *ᵥ f) = PEm x x' *ᵥ f := PEm_idem hx hx' hc f
  have hPα' : PEm x x' *ᵥ (PEm x x' *ᵥ f') = PEm x x' *ᵥ f' := PEm_idem hx hx' hc f'
  generalize PEm x x' *ᵥ f = α at hf hN hPe hPα
  generalize PEm x x' *ᵥ f' = α' at hf' hN' hPe' hPα'
  have T1 : |(J *ᵥ α) ⬝ᵥ (J' *ᵥ α')| ≤ KE * (nrm α * nrm α') := by
    rw [ms_bil]
    have : α ⬝ᵥ (Jᵀ * J') *ᵥ α' = α ⬝ᵥ (PEm x x' * (Jᵀ * J') * PEm x x') *ᵥ α' := by
      rw [show (PEm x x' * (Jᵀ * J') * PEm x x') *ᵥ α' =
          PEm x x' *ᵥ ((Jᵀ * J') *ᵥ (PEm x x' *ᵥ α')) by rw [mulVec_mulVec, mulVec_mulVec],
        hPα', ← PEm_symm, hPα]
    rw [this]
    exact (ms_abs_bil_le_opN _ _ _).trans (mul_le_mul_of_nonneg_right hE (by unfold nrm; positivity))
  have T2 : |(J *ᵥ α) ⬝ᵥ (J' *ᵥ eTan x' x)| ≤ nrm α * KO := by
    rw [ms_bil, ← hPα, PEm_symm, hPα]
    exact (abs_dot_le_nrm _ _).trans (mul_le_mul_of_nonneg_left hO1 (by unfold nrm; positivity))
  have T3 : |(J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ α')| ≤ nrm α' * KO := by
    rw [dotProduct_comm, ms_bil, ← hPα', PEm_symm, hPα']
    exact (abs_dot_le_nrm _ _).trans (mul_le_mul_of_nonneg_left hO2 (by unfold nrm; positivity))
  have hexp : (J *ᵥ f) ⬝ᵥ (J' *ᵥ f') = (J *ᵥ α) ⬝ᵥ (J' *ᵥ α') + (eTan x' x ⬝ᵥ f') *
      ((J *ᵥ α) ⬝ᵥ (J' *ᵥ eTan x' x)) + (eTan x x' ⬝ᵥ f) * ((J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ α')) +
      (eTan x x' ⬝ᵥ f) * (eTan x' x ⬝ᵥ f') * ((J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)) := by
    conv_lhs => rw [hf, hf']
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  have hsq : nrm α ^ 2 = normSq α := by unfold nrm; exact Real.sq_sqrt (normSq_nonneg _)
  have hsq' : nrm α' ^ 2 = normSq α' := by unfold nrm; exact Real.sq_sqrt (normSq_nonneg _)
  rw [hexp, hN, hN', ← hsq, ← hsq']
  exact ms_comb hE0 hO0 hS0 (by unfold nrm; positivity) (by unfold nrm; positivity) T1 T2 T3 hS

/-- **Mode separation** (paper: Lemma `t7:p04:MS`, operator form). For unit inputs `x`, `x'`
with `c = x·x'`, `c² < 1`, tangent directions `e = eTan x x'`, `e' = eTan x' x`, and
`P_E = PEm x x'`: if `‖P_E JᵀJ' P_E‖ ≤ K_E`, `|P_E JᵀJ' e'| ≤ K_O`, `|P_E J'ᵀJ e| ≤ K_O`,
`|⟨Je, J'e'⟩| ≤ K_S`, then
`‖(JΠ_x)ᵀ(J'Π_{x'})‖ ≤ (K_E+K_S)/2 + √(((K_E−K_S)/2)² + K_O²)`. -/
theorem ms_opN {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (J J' : Matrix (Fin m) (Fin n) ℝ) {KE KO KS : ℝ}
    (hE0 : 0 ≤ KE) (hO0 : 0 ≤ KO) (hS0 : 0 ≤ KS)
    (hE : opN (PEm x x' * (Jᵀ * J') * PEm x x') ≤ KE)
    (hO1 : nrm (PEm x x' *ᵥ ((Jᵀ * J') *ᵥ eTan x' x)) ≤ KO)
    (hO2 : nrm (PEm x x' *ᵥ ((J'ᵀ * J) *ᵥ eTan x x')) ≤ KO)
    (hS : |(J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)| ≤ KS) :
    opN ((J * projT x)ᵀ * (J' * projT x')) ≤
      (KE + KS) / 2 + √(((KE - KS) / 2) ^ 2 + KO ^ 2) := by
  have hlam0 : 0 ≤ (KE + KS) / 2 + √(((KE - KS) / 2) ^ 2 + KO ^ 2) := by positivity
  refine ms_opN_le_of_bil _ hlam0 fun u v => ?_
  obtain ⟨hfu, hxf⟩ := ms_normSq_projT_le hx u
  obtain ⟨hfv, hxf'⟩ := ms_normSq_projT_le hx' v
  have hbil : u ⬝ᵥ ((J * projT x)ᵀ * (J' * projT x')) *ᵥ v =
      (J *ᵥ (projT x *ᵥ u)) ⬝ᵥ (J' *ᵥ (projT x' *ᵥ v)) := by
    rw [mulVec_mulVec, mulVec_mulVec, ms_bil]
  rw [hbil]
  refine (ms_core hx hx' hc J J' hE0 hO0 hS0 hE hO1 hO2 hS hxf hxf').trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)) hlam0
  · exact Real.sqrt_le_sqrt hfu
  · exact Real.sqrt_le_sqrt hfv

/-- The same with the factor `n`: pair constants `n k_E`, `n k_o`, `n k_s` give `n λ`. -/
theorem ms_opN_n {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (J J' : Matrix (Fin m) (Fin n) ℝ) {kE ko ks : ℝ}
    (hE0 : 0 ≤ kE) (hO0 : 0 ≤ ko) (hS0 : 0 ≤ ks)
    (hE : opN (PEm x x' * (Jᵀ * J') * PEm x x') ≤ n * kE)
    (hO1 : nrm (PEm x x' *ᵥ ((Jᵀ * J') *ᵥ eTan x' x)) ≤ n * ko)
    (hO2 : nrm (PEm x x' *ᵥ ((J'ᵀ * J) *ᵥ eTan x x')) ≤ n * ko)
    (hS : |(J *ᵥ eTan x x') ⬝ᵥ (J' *ᵥ eTan x' x)| ≤ n * ks) :
    opN ((J * projT x)ᵀ * (J' * projT x')) ≤
      n * ((kE + ks) / 2 + √(((kE - ks) / 2) ^ 2 + ko ^ 2)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine (ms_opN hx hx' hc J J' (mul_nonneg hn hE0) (mul_nonneg hn hO0) (mul_nonneg hn hS0)
    hE hO1 hO2 hS).trans (le_of_eq ?_)
  have e : ((n * kE - n * ks) / 2) ^ 2 + (n * ko) ^ 2 =
      (n : ℝ) ^ 2 * (((kE - ks) / 2) ^ 2 + ko ^ 2) := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hn]
  ring

end BstLean.Part182

open BstLean.Part182 in
#print axioms ms_two
open BstLean.Part182 in
#print axioms ms_opN
open BstLean.Part182 in
#print axioms ms_opN_n
