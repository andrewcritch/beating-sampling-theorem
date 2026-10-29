import BstLean.Part86Defs
import BstLean.Part84Scale
import BstLean.Part84Rep
import BstLean.Part84Poly

/-!
# Part 86, `Scale`: the pointwise scale comparison in the abstract model

`scale86 : Scale86 M k` for `n ≥ 100`, `n ≥ 4 k⁴`, given the two-point identity `TwoPt n J`.
-/

namespace BstLean.Part86

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (frob IsSymmT Tens)
open BstLean.Part53 (heatA tinner fvA)
open BstLean.Part59 (tensOf)
open BstLean.Part78 (zv)
open BstLean.Part84 (hmean en scaleIface)
open BstLean.Part84.Rep (cOf polyEval_cOf unitT unitT_symm fvA_unitT heat_unitT_zero
  heat_unitT_pos tinner_zero_order)

set_option linter.unusedSectionVars false

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

namespace ScaleAux

/-- The polynomial `z ↦ P(b, z)`. -/
noncomputable def Px (b : I → ℝ) (P : MvPolynomial (I ⊕ Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval (Sum.elim (fun j => MvPolynomial.C (b j)) MvPolynomial.X) P

lemma Px_deg (b : I → ℝ) (P : MvPolynomial (I ⊕ Fin n) ℝ) :
    (Px b P).totalDegree ≤ P.totalDegree := by
  apply BstLean.Part84.deg_aeval
  intro i
  cases i with
  | inl j => simp
  | inr i => simp [MvPolynomial.totalDegree_X]

lemma Px_eval (b : I → ℝ) (P : MvPolynomial (I ⊕ Fin n) ℝ) (y : Fin n → ℝ) :
    MvPolynomial.eval y (Px b P) = MvPolynomial.eval (Sum.elim b y) P := by
  unfold Px
  rw [BstLean.Part84.eval_aeval']
  have : (fun i => MvPolynomial.eval y
      (Sum.elim (fun j => MvPolynomial.C (b j)) MvPolynomial.X i)) = Sum.elim b y := by
    funext i
    cases i <;> simp
  rw [this]

lemma tinner_self {c : ℕ} (a : (Fin c → Fin n) → ℝ) : tinner a a = frob a := by
  unfold tinner frob
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The one-point and variance formulas. -/
lemma rep (hT : TwoPt n J) (k : ℕ) (A : Tens n) (hA : ∀ j, IsSymmT (A j)) (lam : ℝ)
    (p : J → ℝ) :
    ∫ W : J × Fin n → ℝ, fvA k A (fun i => lam * zv W p i) ∂stdGauss (J × Fin n) =
      hmean k (lam ^ 2 * ∑ q, p q ^ 2) A ∧
    ∫ W : J × Fin n → ℝ, (fvA k A (fun i => lam * zv W p i) -
        hmean k (lam ^ 2 * ∑ q, p q ^ 2) A) ^ 2 ∂stdGauss (J × Fin n) =
      en k (lam ^ 2 * ∑ q, p q ^ 2) A := by
  obtain ⟨hint1, heq1⟩ := hT k A (unitT n) hA unitT_symm lam p p
  simp only [fvA_unitT, mul_one] at hint1 heq1
  have h1 : ∫ W : J × Fin n → ℝ, fvA k A (fun i => lam * zv W p i) ∂stdGauss (J × Fin n) =
      hmean k (lam ^ 2 * (∑ q, p q ^ 2)) A := by
    rw [heq1, Finset.sum_eq_single 0]
    · rw [tinner_zero_order, heat_unitT_zero]
      simp [hmean]
    · intro c _ hc
      rw [heat_unitT_pos k _ c hc]
      simp [tinner]
    · simp
  refine ⟨h1, ?_⟩
  obtain ⟨hint2, heq2⟩ := hT k A A hA hA lam p p
  have hint2' : Integrable (fun W : J × Fin n → ℝ => fvA k A (fun i => lam * zv W p i) ^ 2)
      (stdGauss (J × Fin n)) := by
    simpa [pow_two] using hint2
  have hexp : ∀ W : J × Fin n → ℝ, (fvA k A (fun i => lam * zv W p i) -
      hmean k (lam ^ 2 * (∑ q, p q ^ 2)) A) ^ 2 = fvA k A (fun i => lam * zv W p i) ^ 2 -
        2 * hmean k (lam ^ 2 * (∑ q, p q ^ 2)) A * fvA k A (fun i => lam * zv W p i) +
        hmean k (lam ^ 2 * (∑ q, p q ^ 2)) A ^ 2 := fun W => by ring
  have hprob : IsProbabilityMeasure (stdGauss (J × Fin n)) := by
    unfold stdGauss; infer_instance
  simp_rw [hexp]
  rw [integral_add (show Integrable (fun W : J × Fin n → ℝ =>
      fvA k A (fun i => lam * zv W p i) ^ 2 - 2 * hmean k (lam ^ 2 * (∑ q, p q ^ 2)) A *
        fvA k A (fun i => lam * zv W p i)) (stdGauss (J × Fin n)) from
      hint2'.sub (hint1.const_mul _)) (integrable_const _),
    integral_sub hint2' (hint1.const_mul _), integral_const_mul, h1, integral_const]
  have h2 : ∫ W : J × Fin n → ℝ, fvA k A (fun i => lam * zv W p i) ^ 2 ∂stdGauss (J × Fin n) =
      ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) * lam ^ (2 * c) *
        tinner (heatA k (lam ^ 2 * (∑ q, p q ^ 2)) A c) (heatA k (lam ^ 2 * (∑ q, p q ^ 2)) A c) * (∑ q, p q * p q) ^ c := by
    rw [← heq2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun W => by simp [pow_two])
  rw [h2, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h0 : tinner (heatA k (lam ^ 2 * (∑ q, p q ^ 2)) A 0) (heatA k (lam ^ 2 * (∑ q, p q ^ 2)) A 0) =
      hmean k (lam ^ 2 * (∑ q, p q ^ 2)) A ^ 2 := by
    rw [tinner_zero_order]; unfold hmean; ring
  rw [h0]
  have hI : Finset.Ico (0 + 1) (k + 1) = Finset.Icc 1 k := by
    ext c; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [hI]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, Nat.factorial_zero, Nat.cast_one, mul_zero,
    pow_zero, one_mul, mul_one]
  unfold en
  have hterm : ∀ c ∈ Finset.Icc 1 k, (c.factorial : ℝ) * lam ^ (2 * c) *
      tinner (heatA k (lam ^ 2 * (∑ q, p q ^ 2)) A c) (heatA k (lam ^ 2 * (∑ q, p q ^ 2)) A c) * (∑ q, p q * p q) ^ c =
      (c.factorial : ℝ) * (lam ^ 2 * (∑ q, p q ^ 2)) ^ c * frob (heatA k (lam ^ 2 * (∑ q, p q ^ 2)) A c) := by
    intro c _
    have : (∑ q, p q * p q) = (∑ q, p q ^ 2) := by
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [this, tinner_self, mul_pow, ← pow_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  ring

/-- The numeric step. -/
lemma numeric (k : ℕ) (hk : 1 ≤ k) (hn : 100 ≤ n) (hnk : 4 * k ^ 4 ≤ n) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t ≤ 100 / 99 / Real.sqrt n) :
    t ^ 2 * (1 + k * t) ^ k ≤ 2 / (n : ℝ) := by
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set u := Real.sqrt n with hu
  have hu2 : u ^ 2 = n := Real.sq_sqrt hn0.le
  have hu0 : 0 < u := Real.sqrt_pos.mpr hn0
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnkR : 4 * (k : ℝ) ^ 4 ≤ n := by exact_mod_cast hnk
  have huk : 2 * (k : ℝ) ^ 2 ≤ u := by
    by_contra h
    push_neg at h
    have : u ^ 2 < (2 * (k : ℝ) ^ 2) ^ 2 := by nlinarith
    nlinarith
  have hkt : (k : ℝ) * t ≤ 50 / 99 / k := by
    have h1 : (k : ℝ) * t ≤ k * (100 / 99 / u) := mul_le_mul_of_nonneg_left ht (by linarith)
    have h2 : (k : ℝ) * (100 / 99 / u) ≤ 50 / 99 / k := by
      have hk0 : (0 : ℝ) < k := by linarith
      rw [show (k : ℝ) * (100 / 99 / u) = (100 / 99 * k) / u by ring,
        div_le_div_iff₀ hu0 hk0]
      nlinarith
    linarith
  have hpow : (1 + (k : ℝ) * t) ^ k ≤ (99 / 74 : ℝ) ^ 2 := by
    have h1 : 1 + (k : ℝ) * t ≤ Real.exp (50 / 99 / k) :=
      le_trans (by linarith) (Real.add_one_le_exp _)
    have h2 : (1 + (k : ℝ) * t) ^ k ≤ Real.exp (50 / 99 / k) ^ k :=
      pow_le_pow_left₀ (by positivity) h1 k
    have h3 : Real.exp (50 / 99 / k) ^ k = Real.exp (50 / 99) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    have h4 : Real.exp (25 / 99) ≤ 99 / 74 := by
      have h := Real.add_one_le_exp (-(25 / 99 : ℝ))
      rw [Real.exp_neg] at h
      have hp : 0 < Real.exp (25 / 99) := Real.exp_pos _
      rw [le_div_iff₀ (by norm_num)]
      have : (74 / 99 : ℝ) ≤ (Real.exp (25 / 99))⁻¹ := by linarith
      have := mul_le_mul_of_nonneg_right this hp.le
      rw [inv_mul_cancel₀ hp.ne'] at this
      linarith
    have h5 : Real.exp (50 / 99) = Real.exp (25 / 99) ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h3, h5] at h2
    exact h2.trans (pow_le_pow_left₀ (Real.exp_pos _).le h4 2)
  have ht2 : t ^ 2 ≤ (100 / 99) ^ 2 / n := by
    have := pow_le_pow_left₀ ht0 ht 2
    rwa [div_pow, hu2] at this
  calc t ^ 2 * (1 + k * t) ^ k ≤ (100 / 99) ^ 2 / n * (99 / 74 : ℝ) ^ 2 :=
        mul_le_mul ht2 hpow (by positivity) (by positivity)
    _ ≤ 2 / n := by
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hn0.le
        norm_num

end ScaleAux

open ScaleAux in
/-- **Scale comparison, pointwise.** -/
theorem scale86 (M : Mod n I J S G) (k : ℕ) (hk : 1 ≤ k) (hT : TwoPt n J) (hn : 100 ≤ n)
    (hnk : 4 * k ^ 4 ≤ n) : Scale86 M k := by
  intro P hP lam hlam x
  have : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set Q := Px (M.b x) P with hQ
  have hQd : Q.totalDegree ≤ k := (Px_deg _ _).trans hP
  set A : Tens n := tensOf k (cOf k Q) with hAdef
  have hA : ∀ j, IsSymmT (A j) := BstLean.Part59.tensOf_symm59x n k (cOf k Q)
  have hF : ∀ (l : ℝ) (W : J × Fin n → ℝ),
      Fm M P l W x = fvA k A (fun i => l * zv W (M.ps x) i) := by
    intro l W
    rw [hAdef, BstLean.Part59.fvA_tensOf59x, polyEval_cOf k Q hQd, hQ, Px_eval]
    rfl
  set κ := ∑ q, M.ps x q ^ 2 with hκ
  have hκ0 : 0 ≤ κ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hPhi : ∀ l : ℝ, Phi M P l x = hmean k (l ^ 2 * κ) A := by
    intro l
    unfold Phi
    simp_rw [hF]
    exact (rep hT k A hA l (M.ps x)).1
  have hVar : ∫ W : J × Fin n → ℝ, (Fm M P lam W x - Phi M P lam x) ^ 2
      ∂stdGauss (J × Fin n) = en k (lam ^ 2 * κ) A := by
    rw [hPhi]
    simp_rw [hF]
    exact (rep hT k A hA lam (M.ps x)).2
  rw [hVar, hPhi, hPhi]
  have hen : 0 ≤ en k (lam ^ 2 * κ) A :=
    Finset.sum_nonneg fun c _ => mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (mul_nonneg (sq_nonneg _) hκ0) _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rcases hκ0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp only [mul_zero, sub_self]
    rw [← h0, mul_zero] at hen
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]; positivity
  have hinv : 1 / (n : ℝ) ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hnR
  have hl := abs_le.mp hlam
  set e := 1 - 1 / (n : ℝ) with he
  have he0 : 99 / 100 ≤ e := by rw [he]; linarith
  have hs0 : 0 < κ * e := mul_pos hpos (by linarith)
  have h1 : κ * e ≤ lam ^ 2 * κ := by nlinarith
  have h2 : κ * e ≤ 1 ^ 2 * κ := by nlinarith
  obtain ⟨hsc, -⟩ := scaleIface n k A hA (lam ^ 2 * κ) (1 ^ 2 * κ) (κ * e) hs0 h1 h2
  set t := |1 ^ 2 * κ - lam ^ 2 * κ| * Real.sqrt n / (κ * e) with ht
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htle : t ≤ 100 / 99 / Real.sqrt n := by
    have habs : |1 ^ 2 * κ - lam ^ 2 * κ| = |lam ^ 2 - 1| * κ := by
      rw [show (1 : ℝ) ^ 2 * κ - lam ^ 2 * κ = -((lam ^ 2 - 1) * κ) by ring, abs_neg, abs_mul,
        abs_of_pos hpos]
    rw [ht, habs, div_le_div_iff₀ hs0 hsq]
    have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have hb : |lam ^ 2 - 1| * (n : ℝ) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hlam hn0.le
      rwa [one_div, inv_mul_cancel₀ hn0.ne'] at this
    calc |lam ^ 2 - 1| * κ * Real.sqrt n * Real.sqrt n
        = (|lam ^ 2 - 1| * n) * κ := by rw [mul_assoc, hss]; ring
      _ ≤ 1 * κ := mul_le_mul_of_nonneg_right hb hpos.le
      _ ≤ 100 / 99 * (κ * e) := by nlinarith
  have hnum := numeric k hk hn hnk t ht0 htle
  have hsym : (hmean k (lam ^ 2 * κ) A - hmean k (1 ^ 2 * κ) A) ^ 2 =
      (hmean k (1 ^ 2 * κ) A - hmean k (lam ^ 2 * κ) A) ^ 2 := by ring
  rw [hsym]
  calc (hmean k (1 ^ 2 * κ) A - hmean k (lam ^ 2 * κ) A) ^ 2
      ≤ t ^ 2 * (1 + k * t) ^ k * en k (lam ^ 2 * κ) A := hsc
    _ ≤ 2 / (n : ℝ) * en k (lam ^ 2 * κ) A := mul_le_mul_of_nonneg_right hnum hen

end BstLean.Part86

#print axioms BstLean.Part86.scale86
