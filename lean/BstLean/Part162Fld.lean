import BstLean.Part162LS
import BstLean.Part161All
import BstLean.Part151FStage
import BstLean.Part153SJ

/-!
# Part 162, item 1 (instances): Lemma LS for the Agent fields `λ` and `σ`

Role: `delegations/statements/p162-spec.md`, item 1. Do not use `sorry`, `native_decide` or
`axiom`.

* `lamX_hom`, `sigX_hom`: `λ(x)`, `σ(x)` are positively 1-homogeneous in the input.
* `lamX_euLip`, `sigX_euLip`: they are Lipschitz, with constants `lipLam`, `lipSig`
  (`√(‖A₂‖_F²‖A₁‖_F²)/|b|` and `√(2/m_A)·√(‖A₂‖_F²‖A₁‖_F²)`).
* **`ls_lamX`, `ls_sigX`**: Lemma LS (`p = 1`) on every latitude sphere for `λ` and `σ`.
* `abs_lA_le`, `abs_sgA_le`: `|λ| ≤ lipLam`, `|σ| ≤ lipSig` on the input sphere (used for
  integrability).
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg hid2)
open BstLean.Part134 (lam res sig)
open BstLean.Part148 (EuLip)
open BstLean.Part157
open BstLean.Part161
open BstLean.Part53 (unitF53)

section fields

variable {m : ℕ}

lemma lam_sub (b h h' : Fin m → ℝ) : lam b (h - h') = lam b h - lam b h' := by
  unfold lam
  rw [← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [sub_mul]

lemma lam_smul (b h : Fin m → ℝ) (t : ℝ) : lam b (t • h) = t * lam b h := by
  unfold lam
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]

lemma res_sub (b h h' : Fin m → ℝ) : res b (h - h') = res b h - res b h' := by
  unfold res; rw [lam_sub, sub_smul]; abel

lemma res_smul (b h : Fin m → ℝ) (t : ℝ) : res b (t • h) = t • res b h := by
  unfold res; rw [lam_smul, smul_sub, smul_smul]

lemma abs_lam_le (b w : Fin m → ℝ) : |lam b w| ≤ √(normSq w) * (√(normSq b))⁻¹ := by
  unfold lam
  by_cases hb : normSq b = 0
  · rw [hb, div_zero, abs_zero]; positivity
  · have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg b) (Ne.symm hb)
    have hcs : (∑ j, w j * b j) ^ 2 ≤ normSq w * normSq b := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h1 : |∑ j, w j * b j| ≤ √(normSq w) * √(normSq b) := by
      rw [← Real.sqrt_mul (normSq_nonneg w), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hcs
    rw [abs_div, abs_of_pos hb0]
    have hs : 0 < √(normSq b) := Real.sqrt_pos.mpr hb0
    rw [div_le_iff₀ hb0]
    calc |∑ j, w j * b j| ≤ √(normSq w) * √(normSq b) := h1
      _ = √(normSq w) * (√(normSq b))⁻¹ * (√(normSq b) * √(normSq b)) := by
          field_simp
      _ = √(normSq w) * (√(normSq b))⁻¹ * normSq b := by
          rw [Real.mul_self_sqrt hb0.le]

lemma normSq_res_le (b w : Fin m → ℝ) : normSq (res b w) ≤ normSq w := by
  by_cases hb : normSq b = 0
  · unfold res lam; rw [hb, div_zero, zero_smul, sub_zero]
  · have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg b) (Ne.symm hb)
    have e : normSq (res b w) = normSq w - (∑ j, w j * b j) ^ 2 / normSq b := by
      unfold res lam normSq
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have : ∀ j, (w j - (∑ i, w i * b i) / (∑ i, b i ^ 2) * b j) ^ 2 =
          w j ^ 2 - 2 * ((∑ i, w i * b i) / (∑ i, b i ^ 2)) * (w j * b j) +
            ((∑ i, w i * b i) / (∑ i, b i ^ 2)) ^ 2 * b j ^ 2 := fun j => by ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hb' : (∑ i, b i ^ 2) ≠ 0 := hb
      field_simp
      ring
    rw [e]
    have : 0 ≤ (∑ j, w j * b j) ^ 2 / normSq b := div_nonneg (sq_nonneg _) hb0.le
    linarith

lemma sqrt_normSq_sub_le (x y : Fin m → ℝ) :
    |√(normSq x) - √(normSq y)| ≤ √(normSq (x - y)) := by
  have e : ∀ z : Fin m → ℝ, √(normSq z) = BstLean.Part53.radF53 z := fun z => rfl
  rw [e, e, e]
  have h := radF_lip x y
  refine h.trans (le_of_eq ?_)
  rfl

end fields

variable {n : ℕ}

/-- `λ(x)` is positively 1-homogeneous in the input. -/
lemma lamX_hom (D : Design n) (c : Ret n) (t : ℝ) (x : Fin n → ℝ) (ht : 0 < t) :
    lamX D c (t • x) = t * lamX D c x := by
  unfold lamX
  rw [BstLean.Part153.hid2_smul _ _ ht.le, lam_smul]

/-- `σ(x)` is positively 1-homogeneous in the input. -/
lemma sigX_hom (D : Design n) (c : Ret n) (t : ℝ) (x : Fin n → ℝ) (ht : 0 < t) :
    sigX D c (t • x) = t * sigX D c x := by
  unfold sigX sig
  rw [BstLean.Part153.hid2_smul _ _ ht.le, res_smul]
  have : normSq (t • res (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 x)) =
      t ^ 2 * normSq (res (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 x)) := by
    unfold normSq
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finset.mul_sum]
  rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  ring

/-- The Lipschitz constant of `λ` in the input: `√(‖A₂‖_F² ‖A₁‖_F²)/|b|`. -/
noncomputable def lipLam (D : Design n) (c : Ret n) : ℝ :=
  √(BstLean.Part131.frob c.2.1.1.2 * BstLean.Part131.frob c.2.1.1.1) *
    (√(normSq (D.bA c.1 c.2.1.1)))⁻¹

/-- The Lipschitz constant of `σ` in the input: `√(2/m_A)·√(‖A₂‖_F² ‖A₁‖_F²)`. -/
noncomputable def lipSig (D : Design n) (c : Ret n) : ℝ :=
  √(2 / (BstLean.Part130.mA n : ℝ)) * √(BstLean.Part131.frob c.2.1.1.2 * BstLean.Part131.frob c.2.1.1.1)

lemma lipLam_nonneg (D : Design n) (c : Ret n) : 0 ≤ lipLam D c := by unfold lipLam; positivity
lemma lipSig_nonneg (D : Design n) (c : Ret n) : 0 ≤ lipSig D c := by unfold lipSig; positivity

lemma hid2_dist (D : Design n) (c : Ret n) (x y : Fin n → ℝ) :
    √(normSq (hid2 c.2.1.1.1 c.2.1.1.2 x - hid2 c.2.1.1.1 c.2.1.1.2 y)) ≤
      √(BstLean.Part131.frob c.2.1.1.2 * BstLean.Part131.frob c.2.1.1.1) *
        √(∑ i, (x i - y i) ^ 2) := by
  have h := BstLean.Part151.hid2_lip c.2.1.1.1 c.2.1.1.2 x y
  rw [← Real.sqrt_mul (by unfold BstLean.Part131.frob; positivity)]
  refine Real.sqrt_le_sqrt (h.trans (le_of_eq ?_))
  unfold normSq
  simp only [Pi.sub_apply]
  ring

lemma lamX_euLip (D : Design n) (c : Ret n) : EuLip (lamX D c) (lipLam D c) := by
  intro x y
  unfold lamX
  rw [← lam_sub]
  refine (abs_lam_le _ _).trans ?_
  unfold lipLam
  have h := hid2_dist D c x y
  calc √(normSq (hid2 c.2.1.1.1 c.2.1.1.2 x - hid2 c.2.1.1.1 c.2.1.1.2 y)) *
        (√(normSq (D.bA c.1 c.2.1.1)))⁻¹ ≤
        (√(BstLean.Part131.frob c.2.1.1.2 * BstLean.Part131.frob c.2.1.1.1) *
          √(∑ i, (x i - y i) ^ 2)) * (√(normSq (D.bA c.1 c.2.1.1)))⁻¹ :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by ring

lemma sigX_euLip (D : Design n) (c : Ret n) : EuLip (sigX D c) (lipSig D c) := by
  intro x y
  unfold sigX sig lipSig
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (sqrt_normSq_sub_le _ _).trans ?_
  rw [← res_sub]
  exact (Real.sqrt_le_sqrt (normSq_res_le _ _)).trans (hid2_dist D c x y)

open BstLean.Part151 (gradSq) in
/-- **Lemma LS (`p = 1`) for `λ` on a latitude sphere.** -/
theorem ls_lamX (hn : 2 ≤ n) (D : Design n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    ((n : ℝ) - 2) * ∫ v, (lamX D c (xLat c s (unitF53 v)) -
        ∫ w, lamX D c (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 ∂stdGauss (Fin (n - 1)) ≤
      ∫ v, (gradSq (fun w => lamX D c (xLatH c s w)) v - lamX D c (xLat c s (unitF53 v)) ^ 2)
        ∂stdGauss (Fin (n - 1)) :=
  ls_lat hn c hs (lipLam_nonneg D c) (lamX_euLip D c) (fun t x ht => lamX_hom D c t x ht)

open BstLean.Part151 (gradSq) in
/-- **Lemma LS (`p = 1`) for `σ` on a latitude sphere.** -/
theorem ls_sigX (hn : 2 ≤ n) (D : Design n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    ((n : ℝ) - 2) * ∫ v, (sigX D c (xLat c s (unitF53 v)) -
        ∫ w, sigX D c (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 ∂stdGauss (Fin (n - 1)) ≤
      ∫ v, (gradSq (fun w => sigX D c (xLatH c s w)) v - sigX D c (xLat c s (unitF53 v)) ^ 2)
        ∂stdGauss (Fin (n - 1)) :=
  ls_lat hn c hs (lipSig_nonneg D c) (sigX_euLip D c) (fun t x ht => sigX_hom D c t x ht)


/-! ## Bounds of the fields on the input sphere -/

lemma latitude_sq_le (a τ : ℝ) (z : ℝ × (Fin (n - 1) → ℝ)) : latitude a τ z ^ 2 ≤ 1 := by
  unfold latitude
  set p := a + τ * z.1
  have hq : 0 ≤ τ ^ 2 * normSq z.2 := mul_nonneg (sq_nonneg _) (normSq_nonneg _)
  rw [div_pow, Real.sq_sqrt (by positivity)]
  rcases (show 0 ≤ p ^ 2 + τ ^ 2 * normSq z.2 by positivity).eq_or_lt with h | h
  · rw [← h, div_zero]; norm_num
  · rw [div_le_one h]; linarith

lemma latC_sq_le (D : Design n) (c : Ret n) (a : Ix n) : latC D c a ^ 2 ≤ 1 :=
  latitude_sq_le _ _ _

lemma normSq_xLat_le (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) (v : Fin (n - 1) → ℝ) :
    normSq (xLat c s (unitF53 v)) ≤ 1 := by
  unfold xLat
  rw [hh_normSq, normSq_consV hn]
  have h1 : normSq (√(1 - s ^ 2) • unitF53 v) = (1 - s ^ 2) * normSq (unitF53 v) := by
    unfold normSq
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Real.sq_sqrt (by linarith), Finset.mul_sum]
  have h2 : normSq (unitF53 v) ≤ 1 := by
    have h := radF_unitF_le v
    have h3 : normSq (unitF53 v) = BstLean.Part53.radF53 (unitF53 v) ^ 2 := (radF_sq _).symm
    rw [h3]
    have := radF_nonneg (unitF53 v)
    nlinarith
  rw [h1]
  nlinarith

lemma abs_hom_le {Φ : (Fin n → ℝ) → ℝ} {L : ℝ} (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) (x : Fin n → ℝ) :
    |Φ x| ≤ L * √(normSq x) := by
  have h0 : Φ 0 = 0 := hom_zero hhom
  have h := hL x 0
  rw [h0, sub_zero] at h
  simpa [normSq] using h

lemma abs_lA_le (hn : 1 ≤ n) (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    |lA D c a v| ≤ lipLam D c := by
  refine (abs_hom_le (lamX_euLip D c) (fun t x ht => lamX_hom D c t x ht) _).trans ?_
  have h := normSq_xLat_le hn c (latC_sq_le D c a) v
  calc lipLam D c * √(normSq (xLat c (latC D c a) (unitF53 v))) ≤ lipLam D c * √1 :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (lipLam_nonneg D c)
    _ = lipLam D c := by simp

/-- `σ(x)` at the pair `(a, v)`. -/
noncomputable def sgA (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) : ℝ :=
  sigX D c (xLat c (latC D c a) (unitF53 v))

lemma sA_eq (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    sA D c a v = sgA D c a v ^ 2 := rfl

lemma sgA_nonneg (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    0 ≤ sgA D c a v := by
  unfold sgA sigX sig; positivity

lemma abs_sgA_le (hn : 1 ≤ n) (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    |sgA D c a v| ≤ lipSig D c := by
  refine (abs_hom_le (sigX_euLip D c) (fun t x ht => sigX_hom D c t x ht) _).trans ?_
  have h := normSq_xLat_le hn c (latC_sq_le D c a) v
  calc lipSig D c * √(normSq (xLat c (latC D c a) (unitF53 v))) ≤ lipSig D c * √1 :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (lipSig_nonneg D c)
    _ = lipSig D c := by simp

lemma measurable_sgA (D : Design n) (c : Ret n) :
    Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => sgA D c p.1 p.2) :=
  (measurable_sigX D c).comp (measurable_xA D c)

end BstLean.Part162

open BstLean.Part162 in
#print axioms ls_lamX
open BstLean.Part162 in
#print axioms ls_sigX
