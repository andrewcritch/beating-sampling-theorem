import BstLean.Part90Defs
import BstLean.Part90Mink
import BstLean.Part90Kernel

/-!
# Part 90: the slice oscillation hypothesis for the instance `modRK m 3 t v E`

`instOsc`: from the slice moments of the anchor features and of the residual kernel (`SliceMom`)
and the anchor bounds, the oscillation hypothesis `SliceOscM` at the level `R_p²`.

In a slice, `mu x = mū + Δ`, `Δ = (b₂ − β₂) A₂ + (b₃ − β₃) A₃`, and
* `H_x − H̄ = 3 T[Δ]`,
* `A_x − Ā = 2 H̄ Δ + 3 T[Δ, Δ] + 3 c² (τ − k̄) tr T`,
with `H̄ = H + 3 T[mū]`, `Ā = ∇f(mū) + 3 c² k̄ tr T`. Minkowski in `L⁴` of the slice does the rest.

No `sorry`, no `native_decide`, no `axiom`.
-/

namespace BstLean.Part90

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (Mono)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV kJ tauR KR polarPoint perpDir axialR axialS axialMeasure polarState)
open BstLean.Part78 (nsq frobH zv)
open BstLean.Part80 (kA)
open BstLean.Part82 (T3 SymT frobT trT aU3 HU3)
open BstLean.Part86

namespace OscAux

/-! ## Finite sums -/

section sums
variable {ι : Type*} [Fintype ι]

lemma dot_le (u w : ι → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : ∑ i, u i ^ 2 ≤ a ^ 2) (hw : ∑ i, w i ^ 2 ≤ b ^ 2) : ∑ i, u i * w i ≤ a * b := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
  have h0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : (∑ i, u i * w i) ^ 2 ≤ (a * b) ^ 2 := by
    rw [mul_pow]
    exact h.trans (mul_le_mul hu hw (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg a))
  exact (abs_le_of_sq_le_sq' h2 (mul_nonneg ha hb)).2

/-- The triangle inequality for two terms. -/
lemma tri2 (u w : ι → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : ∑ i, u i ^ 2 ≤ a ^ 2) (hw : ∑ i, w i ^ 2 ≤ b ^ 2) :
    ∑ i, (u i + w i) ^ 2 ≤ (a + b) ^ 2 := by
  have e : ∑ i, (u i + w i) ^ 2 = ∑ i, u i ^ 2 + 2 * ∑ i, u i * w i + ∑ i, w i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have := dot_le u w a b ha hb hu hw
  rw [e]
  nlinarith

/-- The triangle inequality for three terms. -/
lemma tri3 (u w y : ι → ℝ) (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu : ∑ i, u i ^ 2 ≤ a ^ 2) (hw : ∑ i, w i ^ 2 ≤ b ^ 2) (hy : ∑ i, y i ^ 2 ≤ c ^ 2) :
    ∑ i, (u i + w i + y i) ^ 2 ≤ (a + b + c) ^ 2 :=
  tri2 (fun i => u i + w i) y (a + b) c (add_nonneg ha hb) hc (tri2 u w a b ha hb hu hw) hy

/-- A combination of two vectors of squared norm at most `s²`. -/
lemma comb2 (u w : ι → ℝ) (p q s : ℝ) (hs : 0 ≤ s)
    (hu : ∑ i, u i ^ 2 ≤ s ^ 2) (hw : ∑ i, w i ^ 2 ≤ s ^ 2) :
    ∑ i, (p * u i + q * w i) ^ 2 ≤ ((|p| + |q|) * s) ^ 2 := by
  have h1 : ∑ i, (p * u i) ^ 2 ≤ (|p| * s) ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, sq_abs]
    exact mul_le_mul_of_nonneg_left hu (sq_nonneg p)
  have h2 : ∑ i, (q * w i) ^ 2 ≤ (|q| * s) ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, sq_abs]
    exact mul_le_mul_of_nonneg_left hw (sq_nonneg q)
  have := tri2 (fun i => p * u i) (fun i => q * w i) (|p| * s) (|q| * s)
    (mul_nonneg (abs_nonneg p) hs) (mul_nonneg (abs_nonneg q) hs) h1 h2
  rwa [← add_mul] at this

end sums

/-! ## Pointwise algebra of the cubic -/

section alg
variable {n : ℕ}

lemma frobH_prod (M : Matrix (Fin n) (Fin n) ℝ) :
    frobH M = ∑ a : Fin n × Fin n, M a.1 a.2 ^ 2 := by
  unfold frobH
  rw [Fintype.sum_prod_type]

lemma frobH_nonneg (M : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobH M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

lemma frobT_nonneg (T : T3 n) : 0 ≤ frobT T :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => sq_nonneg _

lemma nsq_nonneg (a : Fin n → ℝ) : 0 ≤ nsq a := Finset.sum_nonneg fun i _ => sq_nonneg _

/-- `‖M Δ‖² ≤ ‖M‖_F² ‖Δ‖²`. -/
lemma mulVec_le (M : Matrix (Fin n) (Fin n) ℝ) (Δ : Fin n → ℝ) :
    ∑ i, (∑ j, M i j * Δ j) ^ 2 ≤ frobH M * nsq Δ := by
  unfold frobH nsq
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

/-- `‖tr T‖² ≤ n ‖T‖_F²`. -/
lemma trT_le (T : T3 n) : nsq (trT T) ≤ (n : ℝ) * frobT T := by
  unfold nsq trT frobT
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : (∑ j, T i j j) ^ 2 ≤ (n : ℝ) * ∑ j, T i j j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun j => T i j j)
    simpa using this
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  refine Finset.sum_le_sum fun j _ => ?_
  exact Finset.single_le_sum (f := fun k => T i j k ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ j)

/-- `T[Δ]` for `Δ = p A₂ + q A₃`. -/
lemma TA_comb (T : T3 n) (A2 A3 : Fin n → ℝ) (p q : ℝ) (i l : Fin n) :
    TA T (fun k => p * A2 k + q * A3 k) i l = p * TA T A2 i l + q * TA T A3 i l := by
  unfold TA
  simp only [Matrix.of_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma frobH_TA_comb (T : T3 n) (A2 A3 : Fin n → ℝ) (p q sK : ℝ) (hsK : 0 ≤ sK)
    (h2 : frobH (TA T A2) ≤ sK ^ 2) (h3 : frobH (TA T A3) ≤ sK ^ 2) :
    frobH (TA T (fun k => p * A2 k + q * A3 k)) ≤ ((|p| + |q|) * sK) ^ 2 := by
  rw [frobH_prod] at h2 h3 ⊢
  simp only [TA_comb]
  exact comb2 (fun a : Fin n × Fin n => TA T A2 a.1 a.2) (fun a => TA T A3 a.1 a.2) p q sK hsK
    h2 h3

/-- `H_x − H̄ = 3 T[Δ]`. -/
lemma hess_le (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (mb A2 A3 : Fin n → ℝ) (p q sK : ℝ)
    (hsK : 0 ≤ sK) (h2 : frobH (TA T A2) ≤ sK ^ 2) (h3 : frobH (TA T A3) ≤ sK ^ 2) :
    frobH (HU3 H T (fun l => mb l + (p * A2 l + q * A3 l)) - HU3 H T mb) ≤
      9 * ((|p| + |q|) * sK) ^ 2 := by
  have e : frobH (HU3 H T (fun l => mb l + (p * A2 l + q * A3 l)) - HU3 H T mb) =
      9 * frobH (TA T (fun k => p * A2 k + q * A3 k)) := by
    unfold frobH
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (HU3 H T (fun l => mb l + (p * A2 l + q * A3 l)) - HU3 H T mb) i j =
        3 * TA T (fun k => p * A2 k + q * A3 k) i j := by
      unfold HU3 TA
      simp only [Matrix.sub_apply, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
      ring
    rw [this]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (frobH_TA_comb T A2 A3 p q sK hsK h2 h3) (by norm_num)

/-- `A_x − Ā = 2 H̄ Δ + 3 T[Δ, Δ] + 3 (k − k') tr T`. -/
lemma grad_id (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (hT : SymT T)
    (mb Δ : Fin n → ℝ) (k k' : ℝ) (i : Fin n) :
    aU3 ℓ H T (fun l => mb l + Δ l) i + 3 * k * trT T i -
        (aU3 ℓ H T mb i + 3 * k' * trT T i) =
      2 * ∑ j, HU3 H T mb i j * Δ j + 3 * ∑ j, TA T Δ i j * Δ j + 3 * (k - k') * trT T i := by
  have hsw : ∑ j, ∑ l, T i j l * mb j * Δ l = ∑ j, ∑ l, T i j l * Δ j * mb l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [(hT i l j).2]; ring
  have e1 : ∑ j, H i j * (mb j + Δ j) = ∑ j, H i j * mb j + ∑ j, H i j * Δ j := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, ∑ l, T i j l * (mb j + Δ j) * (mb l + Δ l) =
      ∑ j, ∑ l, T i j l * mb j * mb l + ∑ j, ∑ l, T i j l * mb j * Δ l +
        ∑ j, ∑ l, T i j l * Δ j * mb l + ∑ j, ∑ l, T i j l * Δ j * Δ l := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have e3 : ∑ j, HU3 H T mb i j * Δ j =
      ∑ j, H i j * Δ j + 3 * ∑ j, ∑ l, T i j l * Δ j * mb l := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : HU3 H T mb i j = H i j + 3 * ∑ l, T i j l * mb l := rfl
    rw [this, add_mul, mul_assoc, Finset.sum_mul]
    congr 2
    exact Finset.sum_congr rfl fun l _ => by ring
  have e4 : ∑ j, TA T Δ i j * Δ j = ∑ j, ∑ l, T i j l * Δ j * Δ l := by
    unfold TA
    simp only [Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  unfold aU3
  rw [e1, e2, e3, e4, hsw]
  ring

/-- The pointwise bound of `‖A_x − Ā‖`. -/
lemma grad_le (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (hT : SymT T)
    (mb A2 A3 : Fin n → ℝ) (p q k k' sH sN sK sT : ℝ)
    (hsH : 0 ≤ sH) (hsN : 0 ≤ sN) (hsK : 0 ≤ sK) (hsT : 0 ≤ sT)
    (hH : frobH (HU3 H T mb) ≤ sH ^ 2)
    (hA2 : nsq A2 ≤ sN ^ 2) (hA3 : nsq A3 ≤ sN ^ 2)
    (h2 : frobH (TA T A2) ≤ sK ^ 2) (h3 : frobH (TA T A3) ≤ sK ^ 2)
    (hTr : (n : ℝ) * frobT T ≤ sT ^ 2) :
    nsq (fun i => aU3 ℓ H T (fun l => mb l + (p * A2 l + q * A3 l)) i + 3 * k * trT T i -
        (aU3 ℓ H T mb i + 3 * k' * trT T i)) ≤
      (2 * (|p| + |q|) * sH * sN + 3 * (|p| + |q|) ^ 2 * sK * sN + 3 * |k - k'| * sT) ^ 2 := by
  set δ := |p| + |q| with hδ
  have hδ0 : 0 ≤ δ := add_nonneg (abs_nonneg p) (abs_nonneg q)
  set Δ : Fin n → ℝ := fun l => p * A2 l + q * A3 l with hΔ
  have hΔn : nsq Δ ≤ (δ * sN) ^ 2 := comb2 A2 A3 p q sN hsN hA2 hA3
  have hTΔ : frobH (TA T Δ) ≤ (δ * sK) ^ 2 := frobH_TA_comb T A2 A3 p q sK hsK h2 h3
  have e : ∀ i, aU3 ℓ H T (fun l => mb l + (p * A2 l + q * A3 l)) i + 3 * k * trT T i -
        (aU3 ℓ H T mb i + 3 * k' * trT T i) =
      2 * ∑ j, HU3 H T mb i j * Δ j + 3 * ∑ j, TA T Δ i j * Δ j + 3 * (k - k') * trT T i :=
    fun i => grad_id ℓ H T hT mb Δ k k' i
  unfold nsq
  simp only [e]
  refine tri3 _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
  · have h := mulVec_le (HU3 H T mb) Δ
    have h' : frobH (HU3 H T mb) * nsq Δ ≤ sH ^ 2 * (δ * sN) ^ 2 :=
      mul_le_mul hH hΔn (nsq_nonneg _) (sq_nonneg _)
    simp only [mul_pow, ← Finset.mul_sum]
    nlinarith
  · have h := mulVec_le (TA T Δ) Δ
    have h' : frobH (TA T Δ) * nsq Δ ≤ (δ * sK) ^ 2 * (δ * sN) ^ 2 :=
      mul_le_mul hTΔ hΔn (nsq_nonneg _) (sq_nonneg _)
    simp only [mul_pow, ← Finset.mul_sum]
    nlinarith
  · have h := trT_le T
    unfold nsq at h
    simp only [mul_pow, ← Finset.mul_sum, sq_abs]
    have h' : ∑ i, trT T i ^ 2 ≤ sT ^ 2 := h.trans hTr
    have := mul_le_mul_of_nonneg_left h' (by positivity : 0 ≤ 3 ^ 2 * (k - k') ^ 2)
    linarith

end alg

/-! ## The analytic core: Minkowski in `L⁴` of a slice -/

lemma abs_pow4 (a : ℝ) : |a| ^ 4 = a ^ 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]

lemma sqrt_pow4 (a : ℝ) (ha : 0 ≤ a) : Real.sqrt a ^ 4 = a ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ha]

set_option maxHeartbeats 800000 in
lemma core {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    (δ κ NA NH : G → ℝ) (hδm : Measurable δ) (hκm : Measurable κ) (hδ0 : ∀ g, 0 ≤ δ g)
    (hi4 : Integrable (fun g => δ g ^ 4) μ) (hi8 : Integrable (fun g => δ g ^ 8) μ)
    (hiK : Integrable (fun g => κ g ^ 4) μ)
    (m C4 C8 CK R c sH sF qN qK sT n1 FT : ℝ) (hm : 0 < m) (hC4 : 0 ≤ C4) (hC8 : 0 ≤ C8)
    (hCK : 0 ≤ CK) (hR : 0 ≤ R) (hsH : 0 ≤ sH) (hsF : 0 ≤ sF) (hqN : 0 ≤ qN) (hqK : 0 ≤ qK)
    (hsT : 0 ≤ sT) (hn1 : 0 ≤ n1) (hFT : 0 ≤ FT) (hsT2 : sT ^ 2 = n1 * FT)
    (I4 : ∫ g, δ g ^ 4 ∂μ ≤ (C4 * R) ^ 4 / m ^ 2)
    (I8 : ∫ g, δ g ^ 8 ∂μ ≤ (C8 * R) ^ 8 / m ^ 4)
    (IK : R ^ 4 * ∫ g, κ g ^ 4 ∂μ ≤ CK ^ 4 / m ^ 2)
    (hNA0 : ∀ g, 0 ≤ NA g) (hNH0 : ∀ g, 0 ≤ NH g)
    (hNA : ∀ g, NA g ≤ (2 * δ g * sH * (qN * |c|) + 3 * δ g ^ 2 * (qK * |c| * sF) * (qN * |c|) +
      3 * |c ^ 2 * κ g| * sT) ^ 2)
    (hNH : ∀ g, NH g ≤ 9 * (δ g * (qK * |c| * sF)) ^ 2)
    (e1 e2 e4 e3 : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he4 : 0 ≤ e4)
    (h1 : 2 * C4 * (qN / Real.sqrt m) ≤ e1)
    (h2 : 3 * C8 ^ 2 * (qK * qN) / m ≤ e2)
    (h4 : 3 * C4 * qK / Real.sqrt m ≤ e4)
    (h3 : 9 * CK ^ 2 * n1 / m ≤ e3 ^ 2) :
    ∃ z : ℝ, 0 ≤ z ∧ c ^ 2 * R ^ 2 * z ^ 2 ≤ e3 ^ 2 * (c ^ 2) ^ 3 * FT ∧
      ∫ g, NA g ^ 2 ∂μ ≤ (e1 * (|c| * R) * sH + e2 * (c ^ 2 * R ^ 2) * sF + z) ^ 4 ∧
      ∫ g, NH g ^ 2 ∂μ ≤ (e4 * (|c| * R) * sF) ^ 4 := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsm2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have hsm4 : Real.sqrt m ^ 4 = m ^ 2 := sqrt_pow4 m hm.le
  have hca : 0 ≤ |c| := abs_nonneg c
  have hcc : |c| ^ 2 = c ^ 2 := sq_abs c
  set J := ∫ g, κ g ^ 4 ∂μ with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun g => by positivity
  set z := 3 * c ^ 2 * sT * Real.sqrt (Real.sqrt J) with hz
  have hz0 : 0 ≤ z := by positivity
  have hz2 : z ^ 2 = 9 * (c ^ 2) ^ 2 * sT ^ 2 * Real.sqrt J := by
    rw [hz, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg J)]; norm_num
  have hz4 : z ^ 4 = 81 * c ^ 8 * sT ^ 4 * J := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hz2, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt hJ0]
    ring
  -- `R² √J ≤ CK²/m`
  have hRJ : R ^ 2 * Real.sqrt J ≤ CK ^ 2 / m := by
    have h : (R ^ 2 * Real.sqrt J) ^ 2 ≤ (CK ^ 2 / m) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hJ0, div_pow, ← pow_mul, ← pow_mul]
      exact IK
    exact (abs_le_of_sq_le_sq' h (by positivity)).2
  refine ⟨z, hz0, ?_, ?_, ?_⟩
  · have e : c ^ 2 * R ^ 2 * z ^ 2 = (c ^ 2) ^ 3 * FT * (9 * n1 * (R ^ 2 * Real.sqrt J)) := by
      rw [hz2, hsT2]; ring
    rw [e]
    have h : 9 * n1 * (R ^ 2 * Real.sqrt J) ≤ e3 ^ 2 := by
      refine le_trans ?_ h3
      have := mul_le_mul_of_nonneg_left hRJ (by positivity : 0 ≤ 9 * n1)
      refine this.trans (le_of_eq ?_)
      ring
    have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (c ^ 2) ^ 3 * FT)
    linarith
  · -- Minkowski for the three terms
    set a1 := 2 * sH * (qN * |c|) * (C4 * R) / Real.sqrt m with ha1
    set a2 := 3 * (qK * |c| * sF) * (qN * |c|) * (C8 * R) ^ 2 / m with ha2
    have ha10 : 0 ≤ a1 := by positivity
    have ha20 : 0 ≤ a2 := by positivity
    have ef1 : (fun g => (2 * δ g * sH * (qN * |c|)) ^ 4) =
        fun g => (2 * sH * (qN * |c|)) ^ 4 * δ g ^ 4 := by funext g; ring
    have ef2 : (fun g => (3 * δ g ^ 2 * (qK * |c| * sF) * (qN * |c|)) ^ 4) =
        fun g => (3 * (qK * |c| * sF) * (qN * |c|)) ^ 4 * δ g ^ 8 := by funext g; ring
    have ef3 : (fun g => (3 * |c ^ 2 * κ g| * sT) ^ 4) =
        fun g => (81 * c ^ 8 * sT ^ 4) * κ g ^ 4 := by
      funext g
      rw [mul_pow, mul_pow, abs_pow4]; ring
    have b1 : ∫ g, (2 * δ g * sH * (qN * |c|)) ^ 4 ∂μ ≤ a1 ^ 4 := by
      rw [ef1, integral_const_mul]
      have := mul_le_mul_of_nonneg_left I4 (by positivity : 0 ≤ (2 * sH * (qN * |c|)) ^ 4)
      refine this.trans (le_of_eq ?_)
      rw [ha1, div_pow, mul_pow _ (C4 * R), hsm4]; ring
    have b2 : ∫ g, (3 * δ g ^ 2 * (qK * |c| * sF) * (qN * |c|)) ^ 4 ∂μ ≤ a2 ^ 4 := by
      rw [ef2, integral_const_mul]
      have := mul_le_mul_of_nonneg_left I8
        (by positivity : 0 ≤ (3 * (qK * |c| * sF) * (qN * |c|)) ^ 4)
      refine this.trans (le_of_eq ?_)
      rw [ha2, div_pow, mul_pow _ ((C8 * R) ^ 2), ← pow_mul]; ring
    have b3 : ∫ g, (3 * |c ^ 2 * κ g| * sT) ^ 4 ∂μ ≤ z ^ 4 := by
      rw [ef3, integral_const_mul, hz4]
    obtain ⟨i3, m3⟩ := mink3 (μ := μ) 4 (by norm_num)
      (fun g => 2 * δ g * sH * (qN * |c|))
      (fun g => 3 * δ g ^ 2 * (qK * |c| * sF) * (qN * |c|))
      (fun g => 3 * |c ^ 2 * κ g| * sT)
      (fun g => by have := hδ0 g; positivity) (fun g => by have := hδ0 g; positivity)
      (fun g => by positivity)
      (by fun_prop) (by fun_prop) (by fun_prop)
      (by rw [ef1]; exact hi4.const_mul _) (by rw [ef2]; exact hi8.const_mul _)
      (by rw [ef3]; exact hiK.const_mul _)
      a1 a2 z ha10 ha20 hz0 b1 b2 b3
    have hmono : ∫ g, NA g ^ 2 ∂μ ≤
        ∫ g, (2 * δ g * sH * (qN * |c|) + 3 * δ g ^ 2 * (qK * |c| * sF) * (qN * |c|) +
          3 * |c ^ 2 * κ g| * sT) ^ 4 ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => sq_nonneg _) i3
        (Filter.Eventually.of_forall fun g => ?_)
      have := pow_le_pow_left₀ (hNA0 g) (hNA g) 2
      rw [← pow_mul] at this
      exact this
    refine hmono.trans (m3.trans (pow_le_pow_left₀ (by positivity) ?_ 4))
    have k1 : a1 ≤ e1 * (|c| * R) * sH := by
      have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ |c| * R * sH)
      refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by ring)))
      rw [ha1]; ring
    have k2 : a2 ≤ e2 * (c ^ 2 * R ^ 2) * sF := by
      have := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ c ^ 2 * R ^ 2 * sF)
      refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by ring)))
      rw [ha2, ← hcc]; ring
    linarith
  · have hi : Integrable (fun g => 81 * (qK * |c| * sF) ^ 4 * δ g ^ 4) μ := hi4.const_mul _
    have hmono : ∫ g, NH g ^ 2 ∂μ ≤ ∫ g, 81 * (qK * |c| * sF) ^ 4 * δ g ^ 4 ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => sq_nonneg _) hi
        (Filter.Eventually.of_forall fun g => ?_)
      have := pow_le_pow_left₀ (hNH0 g) (hNH g) 2
      refine this.trans (le_of_eq ?_)
      ring
    refine hmono.trans ?_
    rw [integral_const_mul]
    have := mul_le_mul_of_nonneg_left I4 (by positivity : 0 ≤ 81 * (qK * |c| * sF) ^ 4)
    refine this.trans ?_
    have e : 81 * (qK * |c| * sF) ^ 4 * ((C4 * R) ^ 4 / m ^ 2) =
        (3 * C4 * qK / Real.sqrt m * (|c| * R * sF)) ^ 4 := by
      rw [mul_pow (3 * C4 * qK / Real.sqrt m), div_pow, hsm4]; ring
    rw [e]
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    have := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ |c| * R * sF)
    exact this.trans (le_of_eq (by ring))

/-! ## The slice of the instance -/

section slice
variable {m : ℕ}

lemma compact_sph (n : ℕ) : IsCompact {w : Fin n → ℝ | ∑ i, w i ^ 2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
    intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hw' : ∑ j, w j ^ 2 = 1 := hw
    have h1 : w i ^ 2 ≤ ∑ j, w j ^ 2 :=
      Finset.single_le_sum (f := fun j => w j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

lemma slice_meas (v : Fin (m + 1) → ℝ) (a r : ℝ) (F : (Fin (m + 1) → ℝ) → ℝ)
    (hF : Continuous F) : Measurable (fun g => F (polarPoint v (perpDir v g) a r)) := by
  have h1 : Measurable (perpDir v) := by unfold perpDir; fun_prop
  have h2 : Continuous (fun w : Fin (m + 1) → ℝ => polarPoint v w a r) := by
    unfold polarPoint; fun_prop
  exact (hF.comp h2).measurable.comp h1

lemma slice_int (hm : 1 ≤ m) (v : Fin (m + 1) → ℝ) (hv : UnitV v) (a r : ℝ)
    (F : (Fin (m + 1) → ℝ) → ℝ) (hF : Continuous F) :
    Integrable (fun g => F (polarPoint v (perpDir v g) a r)) (stdGauss (Fin (m + 1))) := by
  have h2 : Continuous (fun w : Fin (m + 1) → ℝ => polarPoint v w a r) := by
    unfold polarPoint; fun_prop
  obtain ⟨C, hC⟩ := (compact_sph (m + 1)).exists_bound_of_continuousOn (hF.comp h2).continuousOn
  refine Integrable.of_bound (slice_meas v a r F hF).aestronglyMeasurable C ?_
  filter_upwards [BstLean.Part89.perp_unit hm v hv] with g hg
  exact hC _ hg

lemma dot_pp (v : Fin (m + 1) → ℝ) (hv : UnitV v) (a r : ℝ) (g : Fin (m + 1) → ℝ) :
    ∑ i, polarPoint v (perpDir v g) a r i * v i = axialS a r := by
  have e : polarPoint v (perpDir v g) a r = axialS a r • v + axialR a r • perpDir v g := rfl
  have h1 : ∑ i, v i ^ 2 = 1 := hv
  have h2 := BstLean.Part56.perpDir_orth56 v g hv
  have h3 : ∑ i, polarPoint v (perpDir v g) a r i * v i =
      axialS a r * ∑ i, v i ^ 2 + axialR a r * ∑ i, v i * perpDir v g i := by
    rw [e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h3, h1, h2]
  ring

variable (t : ℝ) (v : Fin (m + 1) → ℝ) (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ)

lemma b_eq (x : Fin (m + 1) → ℝ) (j : Fin (3 + 1)) :
    (modRK m 3 t v E).b x j = bF v j x := XIdent.eval_bPE v x j

lemma b_zero (x : Fin (m + 1) → ℝ) : (modRK m 3 t v E).b x 0 = 1 := by
  rw [b_eq]
  unfold bF
  have h := (closedForms (m + 1)).1
  simp [(h x v).1, (h v v).1]

lemma b_one (hv : UnitV v) (x : Fin (m + 1) → ℝ) :
    (modRK m 3 t v E).b x 1 = ∑ i, x i * v i := by
  rw [b_eq]
  unfold bF
  have h := (closedForms (m + 1)).1
  have h1 : ∑ i, v i * v i = 1 := by
    have : ∑ i, v i ^ 2 = 1 := hv
    simpa [sq] using this
  have e : ((1 : Fin (3 + 1)) : ℕ) = 1 := rfl
  rw [e, (h x v).2.1, (h v v).2.1, h1, Real.sqrt_one, div_one]

lemma cont_bF (j : Fin (3 + 1)) : Continuous (bF v (j : ℕ)) := by
  have e : bF v (j : ℕ) = fun x => MvPolynomial.eval x (bPE 3 v j) := by
    funext x; exact (XIdent.eval_bPE v x j).symm
  rw [e]
  exact MvPolynomial.continuous_eval _

lemma tau_eq (hv : UnitV v) (hE : RotE v E) (x : Fin (m + 1) → ℝ) :
    tauR 3 v x = ∑ q, MvPolynomial.eval x (psPE E q) * MvPolynomial.eval x (psPE E q) :=
  (rot_KR v hv E hE x x).symm

lemma cont_tau (hv : UnitV v) (hE : RotE v E) : Continuous (tauR 3 v) := by
  have e : tauR 3 v = fun x => ∑ q, MvPolynomial.eval x (psPE E q) *
      MvPolynomial.eval x (psPE E q) := by
    funext x; exact tau_eq v E hv hE x
  rw [e]
  refine continuous_finset_sum _ fun q _ => ?_
  exact (MvPolynomial.continuous_eval _).mul (MvPolynomial.continuous_eval _)

lemma kA_eq (hv : UnitV v) (hE : RotE v E) (c : ℝ) (x : Fin (m + 1) → ℝ) :
    kA (psM (modRK m 3 t v E) c) x = c ^ 2 * tauR 3 v x := by
  rw [tau_eq v E hv hE x, Finset.mul_sum]
  unfold kA psM
  refine Finset.sum_congr rfl fun q _ => ?_
  have : (modRK m 3 t v E).ps x q = MvPolynomial.eval x (psPE E q) := rfl
  rw [this]; ring

end slice

end OscAux

open OscAux in
/-- **The slice oscillation hypothesis** for the instance `modRK m 3 t v E` at the level `R_p²`. -/
theorem instOsc (m : ℕ) (hm : 5000 ≤ m) (C4 C8 CK : ℝ) (hC4 : 0 ≤ C4) (hC8 : 0 ≤ C8)
    (hCK : 0 ≤ CK) (hMom : SliceMom m C4 C8 CK)
    (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E)
    (ℓ : Fin (m + 1) → ℝ) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hHs : H.IsSymm)
    (T : T3 (m + 1)) (hTs : SymT T)
    (Mk e1 e2 e4 e3 : ℝ) (hMk : 0 ≤ Mk) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he4 : 0 ≤ e4)
    (he3 : 0 ≤ e3)
    (h1 : 2 * C4 * Real.sqrt (9 / 8 * ((m : ℝ) + 1) / m) ≤ e1)
    (h2 : 3 * C8 ^ 2 * Real.sqrt (103 / 100 * Mk * (9 / 8) * ((m : ℝ) + 1)) / m ≤ e2)
    (h4 : 3 * C4 * Real.sqrt (103 / 100 * Mk) / Real.sqrt m ≤ e4)
    (h3 : 9 * CK ^ 2 * ((m : ℝ) + 1) / m ≤ e3 ^ 2)
    (A : Fin (3 + 1) → Fin (m + 1) → ℝ) (c : ℝ)
    (hA2 : nsq (A 2) ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2)
    (hA3 : nsq (A 3) ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2)
    (hT2 : frobH (TA T (A 2)) ≤ 103 / 100 * Mk * c ^ 2 * frobT T)
    (hT3 : frobH (TA T (A 3)) ≤ 103 / 100 * Mk * c ^ 2 * frobT T) :
    SliceOscM (modRK m 3 t v E) ℓ H T A c (fun p => axialR p.1 (radF53 p.2) ^ 2)
      (fun p => axialR p.1 (radF53 p.2)) e1 e2 e4 (e3 ^ 2 * (c ^ 2) ^ 3 * frobT T) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hFT := frobT_nonneg T
  -- the constants
  obtain ⟨qN, hqN⟩ : ∃ qN : ℝ, qN = Real.sqrt (9 / 8 * ((m : ℝ) + 1)) := ⟨_, rfl⟩
  obtain ⟨qK, hqK⟩ : ∃ qK : ℝ, qK = Real.sqrt (103 / 100 * Mk) := ⟨_, rfl⟩
  obtain ⟨sT, hsT⟩ : ∃ sT : ℝ, sT = Real.sqrt (((m : ℝ) + 1) * frobT T) := ⟨_, rfl⟩
  have hqN0 : 0 ≤ qN := hqN ▸ Real.sqrt_nonneg _
  have hqK0 : 0 ≤ qK := hqK ▸ Real.sqrt_nonneg _
  have hsT0 : 0 ≤ sT := hsT ▸ Real.sqrt_nonneg _
  have hsF0 : 0 ≤ Real.sqrt (frobT T) := Real.sqrt_nonneg _
  have hqN2 : qN ^ 2 = 9 / 8 * ((m : ℝ) + 1) := by rw [hqN, Real.sq_sqrt (by positivity)]
  have hqK2 : qK ^ 2 = 103 / 100 * Mk := by rw [hqK, Real.sq_sqrt (by positivity)]
  have hsT2 : sT ^ 2 = ((m : ℝ) + 1) * frobT T := by rw [hsT, Real.sq_sqrt (by positivity)]
  have hsF2 : Real.sqrt (frobT T) ^ 2 = frobT T := Real.sq_sqrt hFT
  have hsN : ∀ a : Fin (m + 1) → ℝ, nsq a ≤ 9 / 8 * ((m : ℝ) + 1) * c ^ 2 →
      nsq a ≤ (qN * |c|) ^ 2 := by
    intro a ha; rw [mul_pow, hqN2, sq_abs]; exact ha
  have hsK : ∀ a : Fin (m + 1) → ℝ, frobH (TA T a) ≤ 103 / 100 * Mk * c ^ 2 * frobT T →
      frobH (TA T a) ≤ (qK * |c| * Real.sqrt (frobT T)) ^ 2 := by
    intro a ha; rw [mul_pow, mul_pow, hqK2, sq_abs, hsF2]; exact ha
  have hTr : (((m + 1 : ℕ) : ℝ)) * frobT T ≤ sT ^ 2 := by
    rw [hsT2]; push_cast; exact le_rfl
  have h1' : 2 * C4 * (qN / Real.sqrt m) ≤ e1 := by
    rw [hqN, ← Real.sqrt_div (by positivity)]; exact h1
  have h2' : 3 * C8 ^ 2 * (qK * qN) / m ≤ e2 := by
    rw [hqN, hqK, ← Real.sqrt_mul (by positivity)]
    have e : 103 / 100 * Mk * (9 / 8 * ((m : ℝ) + 1)) = 103 / 100 * Mk * (9 / 8) * ((m : ℝ) + 1) := by
      ring
    rw [e]; exact h2
  have h4' : 3 * C4 * qK / Real.sqrt m ≤ e4 := by rw [hqK]; exact h4
  unfold SliceOscM
  change ∀ᵐ p ∂axialMeasure t v, _
  filter_upwards [BstLean.Part89.axial_ne_zero t v] with p hp
  have hr0 : 0 ≤ radF53 p.2 := by unfold radF53; positivity
  have hR0 : 0 ≤ axialR p.1 (radF53 p.2) := by unfold axialR; positivity
  obtain ⟨β2, β3, kb, -, -, I4, I8, IK⟩ := hMom v hv p.1 (radF53 p.2) hp hr0
  -- the constants of the slice
  obtain ⟨mb, hmb⟩ : ∃ mb : Fin (m + 1) → ℝ, mb = fun i =>
      A 0 i + axialS p.1 (radF53 p.2) * A 1 i + β2 * A 2 i + β3 * A 3 i := ⟨_, rfl⟩
  have hsH0 : 0 ≤ Real.sqrt (frobH (HU3 H T mb)) := Real.sqrt_nonneg _
  have hsH2 : frobH (HU3 H T mb) ≤ Real.sqrt (frobH (HU3 H T mb)) ^ 2 :=
    le_of_eq (Real.sq_sqrt (frobH_nonneg _)).symm
  -- the mean field on the slice
  have hmu : ∀ g : Fin (m + 1) → ℝ,
      muM (modRK m 3 t v E) A (polarPoint v (perpDir v g) p.1 (radF53 p.2)) = fun l => mb l +
        ((bF v 2 (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - β2) * A 2 l +
          (bF v 3 (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - β3) * A 3 l) := by
    intro g
    funext l
    unfold muM
    rw [Fin.sum_univ_four, b_zero, b_one t v E hv, dot_pp v hv, b_eq t v E _ 2, b_eq t v E _ 3,
      hmb]
    have e2 : ((2 : Fin (3 + 1)) : ℕ) = 2 := rfl
    have e3 : ((3 : Fin (3 + 1)) : ℕ) = 3 := rfl
    rw [e2, e3]
    ring
  have c2 : Continuous (bF v 2) := cont_bF v (2 : Fin (3 + 1))
  have c3 : Continuous (bF v 3) := cont_bF v (3 : Fin (3 + 1))
  have cτ : Continuous (tauR 3 v) := cont_tau v E hv hE
  have cδ : Continuous (fun x => |bF v 2 x - β2| + |bF v 3 x - β3|) :=
    (c2.sub continuous_const).abs.add (c3.sub continuous_const).abs
  have cκ : Continuous (fun x => tauR 3 v x - kb) := cτ.sub continuous_const
  obtain ⟨z, hz0, hz, hA, hH⟩ := core (stdGauss (Fin (m + 1)))
    (fun g => |bF v 2 (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - β2| +
      |bF v 3 (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - β3|)
    (fun g => tauR 3 v (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - kb)
    (fun g => nsq (fun i => AxC ℓ H T (muM (modRK m 3 t v E) A) (psM (modRK m 3 t v E) c)
      (polarPoint v (perpDir v g) p.1 (radF53 p.2)) i -
        (aU3 ℓ H T mb i + 3 * (c ^ 2 * kb) * trT T i)))
    (fun g => frobH (HxC H T (muM (modRK m 3 t v E) A)
      (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - HU3 H T mb))
    (slice_meas v _ _ _ cδ) (slice_meas v _ _ _ cκ)
    (fun g => add_nonneg (abs_nonneg _) (abs_nonneg _))
    (slice_int (by omega) v hv _ _ _ (cδ.pow 4)) (slice_int (by omega) v hv _ _ _ (cδ.pow 8))
    (slice_int (by omega) v hv _ _ _ (cκ.pow 4))
    (m : ℝ) C4 C8 CK (axialR p.1 (radF53 p.2)) c (Real.sqrt (frobH (HU3 H T mb)))
    (Real.sqrt (frobT T)) qN qK sT ((m : ℝ) + 1) (frobT T) hm0 hC4 hC8 hCK hR0 hsH0 hsF0 hqN0
    hqK0 hsT0 hm1 hFT hsT2 I4 I8 IK (fun g => nsq_nonneg _) (fun g => frobH_nonneg _)
    (by
      intro g
      have hg := grad_le ℓ H T hTs mb (A 2) (A 3)
        (bF v 2 (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - β2)
        (bF v 3 (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - β3)
        (c ^ 2 * tauR 3 v (polarPoint v (perpDir v g) p.1 (radF53 p.2))) (c ^ 2 * kb)
        (Real.sqrt (frobH (HU3 H T mb))) (qN * |c|) (qK * |c| * Real.sqrt (frobT T)) sT
        hsH0 (by positivity) (by positivity) hsT0 hsH2 (hsN _ hA2) (hsN _ hA3) (hsK _ hT2)
        (hsK _ hT3) hTr
      rw [← mul_sub] at hg
      refine le_trans (le_of_eq ?_) hg
      congr 1
      funext i
      unfold AxC
      rw [hmu g, kA_eq t v E hv hE])
    (by
      intro g
      have hg := hess_le H T mb (A 2) (A 3)
        (bF v 2 (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - β2)
        (bF v 3 (polarPoint v (perpDir v g) p.1 (radF53 p.2)) - β3)
        (qK * |c| * Real.sqrt (frobT T)) (by positivity) (hsK _ hT2) (hsK _ hT3)
      refine le_trans (le_of_eq ?_) hg
      unfold HxC
      rw [hmu g])
    e1 e2 e4 e3 he1 he2 he4 h1' h2' h4' h3
  exact ⟨fun i => aU3 ℓ H T mb i + 3 * (c ^ 2 * kb) * trT T i, HU3 H T mb, z, hz0, hz, hA, hH⟩

end BstLean.Part90

#print axioms BstLean.Part90.instOsc
