import BstLean.Part184Core
import BstLean.Part162Gm

/-!
# Part 184 (file `BF1`): the location fluctuation as a sum of independent rows

No proof is left open; no `native_decide` or `axiom` is used.
-/

namespace BstLean.Part184

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part170
open BstLean.Part134 (res)
open BstLean.Part167 (perp)
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part148 (EuLip)

lemma gmom4_eq' : gmom 4 = 3 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, BstLean.Part162.gmom_even]
  simp [Finset.prod_range_succ]; norm_num

lemma gmom6_eq' : gmom 6 = 15 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, BstLean.Part162.gmom_even]
  simp [Finset.prod_range_succ]; norm_num

lemma gmom8_eq' : gmom 8 = 105 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, BstLean.Part162.gmom_even]
  simp [Finset.prod_range_succ]; norm_num

/-- The polynomial closure of the location moment expansion. -/
lemma poly_bf {S2 S4 S6 S8 P W4 W6 W8 : ℝ} (h2 : 0 ≤ S2) (h4 : 0 ≤ S4)
    (hP : 0 ≤ P) (hW4 : 0 ≤ W4) (hW6 : 0 ≤ W6) (hW8 : 0 ≤ W8)
    (hS2 : S2 ≤ P) (hS4 : S4 ≤ (π / 2) ^ 4 * gmom 4 * W4) (hS6 : S6 ≤ (π / 2) ^ 6 * gmom 6 * W6)
    (hS8 : S8 ≤ (π / 2) ^ 8 * gmom 8 * W8) (h46 : W6 ≤ P * W4) (h48 : W8 ≤ P ^ 2 * W4)
    (h44 : W4 ≤ P ^ 2) :
    105 * S2 ^ 4 + 490 * S2 ^ 2 * S4 + 63 * S4 ^ 2 + 56 * S2 * S6 + S8 ≤
      105 * P ^ 4 + 46600 * (P ^ 2 * W4) := by
  rw [gmom4_eq'] at hS4
  rw [gmom6_eq'] at hS6
  rw [gmom8_eq'] at hS8
  have hpi : π < 3.1416 := Real.pi_lt_d4
  have hpi0 : 0 < π := Real.pi_pos
  have p2 : π / 2 ≤ 1.5708 := by linarith
  have p4 : (π / 2) ^ 4 ≤ 1.5708 ^ 4 := pow_le_pow_left₀ (by positivity) p2 4
  have p6 : (π / 2) ^ 6 ≤ 1.5708 ^ 6 := pow_le_pow_left₀ (by positivity) p2 6
  have p8 : (π / 2) ^ 8 ≤ 1.5708 ^ 8 := pow_le_pow_left₀ (by positivity) p2 8
  have hPW : 0 ≤ P ^ 2 * W4 := by positivity
  have c4 : S4 ≤ 1827 / 100 * W4 := by
    have h1 : (π / 2) ^ 4 * 3 * W4 ≤ 1.5708 ^ 4 * 3 * W4 := by gcongr
    have h2 : (1.5708 : ℝ) ^ 4 * 3 * W4 ≤ 1827 / 100 * W4 := by
      have : (1.5708 : ℝ) ^ 4 * 3 ≤ 1827 / 100 := by norm_num
      exact mul_le_mul_of_nonneg_right this hW4
    linarith
  have c6 : S6 ≤ 2255 / 10 * (P * W4) := by
    have h1 : (π / 2) ^ 6 * 15 * W6 ≤ 1.5708 ^ 6 * 15 * W6 := by gcongr
    have h2 : (1.5708 : ℝ) ^ 6 * 15 * W6 ≤ 2255 / 10 * W6 := by
      have : (1.5708 : ℝ) ^ 6 * 15 ≤ 2255 / 10 := by norm_num
      exact mul_le_mul_of_nonneg_right this hW6
    have h3 : 2255 / 10 * W6 ≤ 2255 / 10 * (P * W4) := by linarith
    linarith
  have c8 : S8 ≤ 3990 * (P ^ 2 * W4) := by
    have h1 : (π / 2) ^ 8 * 105 * W8 ≤ 1.5708 ^ 8 * 105 * W8 := by gcongr
    have h2 : (1.5708 : ℝ) ^ 8 * 105 * W8 ≤ 3990 * W8 := by
      have : (1.5708 : ℝ) ^ 8 * 105 ≤ 3990 := by norm_num
      exact mul_le_mul_of_nonneg_right this hW8
    have h3 : 3990 * W8 ≤ 3990 * (P ^ 2 * W4) := by linarith
    linarith
  have t1 : S2 ^ 4 ≤ P ^ 4 := pow_le_pow_left₀ h2 hS2 4
  have t2 : S2 ^ 2 * S4 ≤ P ^ 2 * (1827 / 100 * W4) :=
    mul_le_mul (pow_le_pow_left₀ h2 hS2 2) c4 h4 (by positivity)
  have t3 : S4 ^ 2 ≤ (1827 / 100 * W4) ^ 2 := pow_le_pow_left₀ h4 c4 2
  have t3' : (1827 / 100 * W4) ^ 2 ≤ (1827 / 100) ^ 2 * (P ^ 2 * W4) := by
    have : W4 * W4 ≤ P ^ 2 * W4 := mul_le_mul_of_nonneg_right h44 hW4
    nlinarith
  have t4 : S2 * S6 ≤ P * (2255 / 10 * (P * W4)) := by
    rcases le_total 0 S6 with h6 | h6
    · exact mul_le_mul hS2 c6 h6 hP
    · have : S2 * S6 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 h6
      have : 0 ≤ P * (2255 / 10 * (P * W4)) := by positivity
      linarith
  have e4 : P * (2255 / 10 * (P * W4)) = 2255 / 10 * (P ^ 2 * W4) := by ring
  have fin : 490 * (1827 / 100) + 63 * (1827 / 100) ^ 2 + 56 * (2255 / 10) + 3990 ≤ (46600 : ℝ) := by
    norm_num
  nlinarith


/-- `(f − Ef)^{2p}` is integrable for a Euclidean-Lipschitz `f` of a standard Gaussian vector. -/
lemma euLip_dev_pow_int {ι : Type} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : EuLip f L) (p : ℕ) :
    Integrable (fun x => (f x - ∫ y, f y ∂stdGauss ι) ^ (2 * p)) (stdGauss ι) := by
  have hLn : EuLip (fun x => -f x) L := by
    intro x y
    have := hL x y
    rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
    exact this
  obtain ⟨i1, -⟩ := BstLean.Part152.gaussConc_moment hL0 hL p
  obtain ⟨i2, -⟩ := BstLean.Part152.gaussConc_moment hL0 hLn p
  have hc := hL.continuous hL0
  refine Integrable.mono' (i1.add i2) ((hc.measurable.sub_const _).pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [integral_neg] at *
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [pow_mul]; positivity)]
  set d := f x - ∫ y, f y ∂stdGauss ι
  have e : -f x - -∫ y, f y ∂stdGauss ι = -d := by simp only [d]; ring
  rw [e]
  rcases le_total 0 d with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -d ≤ 0)]
    simp [pow_mul]
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -d)]
    rw [pow_mul, pow_mul, pow_mul, neg_sq]
    simp

section core
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

/-- The location row function `ν ↦ E_v ReLU(c(v) + √t ν·w(v))`. -/
noncomputable def rowF (μ : Measure V) (c : V → ℝ) (w : V → Fin m → ℝ) (t : ℝ)
    (ν : Fin m → ℝ) : ℝ :=
  ∫ v, relu (c v + √t * (ν ⬝ᵥ w v)) ∂μ

lemma rowF_eq (a : V → Fin m → ℝ) (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) (t : ℝ)
    (j : Fin m) (y : Fin m → Fin m → ℝ) :
    rowF μ (fun v => (M₀ *ᵥ a v) j) (fun v => BstLean.Part183.wT μ a h (a v)) t (y j) =
      ∫ v, relu ((M₀ *ᵥ a v) j + (matOf t (Function.uncurry y) *ᵥ
        perp (res h (vmean μ a)) (perp h (a v))) j) ∂μ := by
  simp only [rowF, matOf_uncurry_mulVec]
  rfl

/-- **The location row function is `√(tΛ)/2`-Lipschitz.** -/
lemma rowF_lip {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) {t : ℝ} (ht : 0 ≤ t) (j : Fin m) :
    EuLip (rowF μ (fun v => (M₀ *ᵥ a v) j) (fun v => BstLean.Part183.wT μ a h (a v)) t)
      (√(t * Λ) / 2) := by
  intro ν ν'
  have hd := flY_diff ha hK hΛ0 hΛ h M₀ (matOf t (Function.uncurry fun _ : Fin m => ν))
    (matOf t (Function.uncurry fun _ : Fin m => ν')) j
  have e1 := rowF_eq (μ := μ) a h M₀ t j (fun _ => ν)
  have e2 := rowF_eq (μ := μ) a h M₀ t j (fun _ => ν')
  rw [e1, e2]
  refine hd.trans (le_of_eq ?_)
  have hn : normSq (fun k => matOf t (Function.uncurry fun _ : Fin m => ν) j k -
      matOf t (Function.uncurry fun _ : Fin m => ν') j k) = t * ∑ k, (ν k - ν' k) ^ 2 := by
    unfold normSq matOf
    simp only [Matrix.of_apply, Function.uncurry_apply_pair]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_sub, mul_pow, Real.sq_sqrt ht]
  rw [hn, ← mul_assoc, mul_comm Λ t, Real.sqrt_mul (by positivity)]
  ring

/-- **The location fluctuation by the row moment expansion** (generic): with
`ℓ_j = (κ b_j)²·tΛ/4`, `E(E − EE)⁸ ≤ 105(Σℓ)⁴ + 46600(Σℓ)²Σℓ²`. -/
theorem flE_rows8 {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) (b ψ : Fin m → ℝ) (κ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ ζ, ENNReal.ofReal (|flE μ a h M₀ b ψ κ (matOf t ζ) -
        ∫ ζ', flE μ a h M₀ b ψ κ (matOf t ζ') ∂stdGauss (Fin m × Fin m)| ^ 8)
        ∂stdGauss (Fin m × Fin m) ≤
      ENNReal.ofReal (105 * (∑ j, (κ * b j) ^ 2 * (t * Λ / 4)) ^ 4 +
        46600 * ((∑ j, (κ * b j) ^ 2 * (t * Λ / 4)) ^ 2 *
          ∑ j, ((κ * b j) ^ 2 * (t * Λ / 4)) ^ 2)) := by
  set ρ := stdGauss (Fin m) with hρ
  set P := Measure.pi fun _ : Fin m => ρ with hP
  set G : Fin m → (Fin m → ℝ) → ℝ := fun j =>
    rowF μ (fun v => (M₀ *ᵥ a v) j) (fun v => BstLean.Part183.wT μ a h (a v)) t with hGd
  set f : Fin m → (Fin m → ℝ) → ℝ := fun j ν => κ * b j * G j ν with hfd
  set L : Fin m → ℝ := fun j => |κ * b j| * (√(t * Λ) / 2) with hLd
  have hL0 : ∀ j, 0 ≤ L j := fun j => by positivity
  have hL : ∀ j, EuLip (f j) (L j) := fun j => by
    intro x y
    have := rowF_lip ha hK hΛ0 hΛ h M₀ ht j x y
    simp only [f, L, G]
    rw [← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have cf : ∀ j, Continuous (f j) := fun j => (hL j).continuous (hL0 j)
  have if1 : ∀ j, Integrable (f j) ρ := fun j => BstLean.Part170.euLip_integrable (hL0 j) (hL j)
  set φ : Fin m → (Fin m → ℝ) → ℝ := fun j ν => f j ν - ∫ ν', f j ν' ∂ρ with hφd
  have mφ : ∀ j, Measurable (φ j) := fun j => (cf j).measurable.sub_const _
  have iφ8 : ∀ j, Integrable (fun ν => φ j ν ^ 8) ρ := fun j =>
    euLip_dev_pow_int (hL0 j) (hL j) 4
  have hφ0 : ∀ j, ∫ ν, φ j ν ∂ρ = 0 := fun j => by
    simp only [φ]; rw [integral_sub (if1 j) (integrable_const _)]; simp
  -- the row identities
  have hF : ∀ y : Fin m → Fin m → ℝ, flE μ a h M₀ b ψ κ (matOf t (Function.uncurry y)) =
      ∑ j, (f j (y j) - κ * b j * ψ j) := by
    intro y
    unfold flE
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e := rowF_eq (μ := μ) a h M₀ t j y
    simp only [f, G]
    rw [e]; ring
  have hcomp : ∀ j {g : (Fin m → ℝ) → ℝ}, AEStronglyMeasurable g ρ →
      ∫ y, g (y j) ∂P = ∫ ν, g ν ∂ρ := fun j g hg => integral_comp_eval hg
  have icomp : ∀ j {g : (Fin m → ℝ) → ℝ}, Integrable g ρ →
      Integrable (fun y : Fin m → Fin m → ℝ => g (y j)) P :=
    fun j g hg => (measurePreserving_eval (fun _ : Fin m => ρ) j).integrable_comp_of_integrable hg
  have hQ : ∫ ζ, flE μ a h M₀ b ψ κ (matOf t ζ) ∂stdGauss (Fin m × Fin m) =
      ∑ j, (∫ ν, f j ν ∂ρ - κ * b j * ψ j) := by
    rw [integral_uncurry]
    simp_rw [hF]
    rw [integral_finset_sum]
    swap
    · intro j _; exact (icomp j (if1 j)).sub (integrable_const _)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_sub (icomp j (if1 j)) (integrable_const _), hcomp j (if1 j).aestronglyMeasurable]
    simp
  have step1 : ∫⁻ ζ, ENNReal.ofReal (|flE μ a h M₀ b ψ κ (matOf t ζ) -
        ∫ ζ', flE μ a h M₀ b ψ κ (matOf t ζ') ∂stdGauss (Fin m × Fin m)| ^ 8)
        ∂stdGauss (Fin m × Fin m) = ∫⁻ y, ENNReal.ofReal ((∑ j, φ j (y j)) ^ 8) ∂P := by
    rw [lintegral_uncurry]
    refine lintegral_congr fun y => ?_
    rw [hF, hQ, ← Finset.sum_sub_distrib, Even.pow_abs ⟨4, rfl⟩]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [φ]; ring
  rw [step1]
  refine (mom8_pi_lint ρ φ mφ iφ8 hφ0).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the moments
  set ℓ : Fin m → ℝ := fun j => (κ * b j) ^ 2 * (t * Λ / 4) with hℓd
  have hℓ0 : ∀ j, 0 ≤ ℓ j := fun j => by positivity
  have hLℓ : ∀ j, L j ^ 2 = ℓ j := fun j => by
    simp only [L, ℓ]
    rw [mul_pow, sq_abs, div_pow, Real.sq_sqrt (by positivity)]; ring
  have hmomk : ∀ k, 1 ≤ k → ∀ j, ∫ ν, |φ j ν| ^ k ∂ρ ≤ (π / 2) ^ k * gmom k * L j ^ k := by
    intro k hk j
    have hp := BstLean.Part162.poincare_p (hL0 j) (hL j) hk
    refine hp.trans ?_
    have hg : ∫ x, √(BstLean.Part151.gradSq (f j) x) ^ k ∂ρ ≤ L j ^ k := by
      have hpt : ∀ x, √(BstLean.Part151.gradSq (f j) x) ^ k ≤ L j ^ k := fun x => by
        refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ k
        rw [Real.sqrt_le_left (hL0 j)]
        exact BstLean.Part151.gradSq_le (hL0 j) (hL j) x
      calc _ ≤ ∫ _x, L j ^ k ∂ρ :=
            integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
              (integrable_const _) (Eventually.of_forall hpt)
        _ = L j ^ k := by simp
    have := gmom_nonneg k
    have h2 : 0 ≤ (π / 2) ^ k := by positivity
    calc (π / 2) ^ k * (gmom k * ∫ x, √(BstLean.Part151.gradSq (f j) x) ^ k ∂ρ)
        ≤ (π / 2) ^ k * (gmom k * L j ^ k) := by gcongr
      _ = _ := by ring
  have hS2 : Smom ρ φ 2 ≤ ∑ j, ℓ j := by
    unfold Smom
    refine Finset.sum_le_sum fun j _ => ?_
    have := BstLean.Part151.poincare_lip_L (hL0 j) (hL j)
    rw [← hLℓ j]
    simpa [φ, sq_abs] using this
  have hSk : ∀ p : ℕ, 1 ≤ p → Smom ρ φ (2 * p) ≤ (π / 2) ^ (2 * p) * gmom (2 * p) * ∑ j, ℓ j ^ p := by
    intro p hp
    unfold Smom
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (hmomk (2 * p) (by omega) j).trans (le_of_eq ?_)
    rw [show L j ^ (2 * p) = (L j ^ 2) ^ p by rw [pow_mul], hLℓ j]
  have h4 := hSk 2 (by norm_num)
  have h6 := hSk 3 (by norm_num)
  have h8 := hSk 4 (by norm_num)
  norm_num only at h4 h6 h8
  have hPs : ∀ j, ℓ j ≤ ∑ i, ℓ i := fun j =>
    Finset.single_le_sum (fun i _ => hℓ0 i) (Finset.mem_univ j)
  set Pℓ := ∑ i, ℓ i with hPℓ
  have hP0 : 0 ≤ Pℓ := Finset.sum_nonneg fun i _ => hℓ0 i
  have h46 : ∑ j, ℓ j ^ 3 ≤ Pℓ * ∑ j, ℓ j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := mul_le_mul_of_nonneg_right (hPs j) (sq_nonneg (ℓ j))
    nlinarith
  have h48 : ∑ j, ℓ j ^ 4 ≤ Pℓ ^ 2 * ∑ j, ℓ j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := pow_le_pow_left₀ (hℓ0 j) (hPs j) 2
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg (ℓ j))
    nlinarith
  have h44 : ∑ j, ℓ j ^ 2 ≤ Pℓ ^ 2 := by
    rw [sq Pℓ, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hPs j) (hℓ0 j)
  exact poly_bf (Smom_nonneg ρ φ 2) (Smom_nonneg ρ φ 4) hP0
    (Finset.sum_nonneg fun j _ => pow_nonneg (hℓ0 j) 2)
    (Finset.sum_nonneg fun j _ => pow_nonneg (hℓ0 j) 3)
    (Finset.sum_nonneg fun j _ => pow_nonneg (hℓ0 j) 4) hS2 h4 h6 h8 h46 h48 h44

end core

end BstLean.Part184
