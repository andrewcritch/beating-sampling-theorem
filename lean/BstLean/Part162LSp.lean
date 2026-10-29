import BstLean.Part162Pq
import BstLean.Part161Six

/-!
# Part 162, item 1: Lemma LS for the moments of order `2q`

Role: `delegations/statements/p162-spec.md`, item 1. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:LS` (all `p`).
Route: the Gaussian `L^p` Poincaré inequality (`poincare_p`) applied to the Lipschitz function
`H = H₁ − m|v|` (as in `ls_var`); radius and direction are independent, so
`‖H‖_p = ‖|Z|‖_p ‖G − m‖_p`; `|∇H| ≤ |G − m| + √T` and Minkowski (`mink4` of Part 161).

* **`ls_mom`**: `‖|Z|‖_p·‖G − EG‖_p ≤ c(‖G − EG‖_p + ‖√T‖_p)`, `c = (π/2)(E|g|^p)^{1/p}`.
* `sqrt_card_le_momN_radF`: `√k ≤ ‖|Z|‖_{2q}`.
* `cLS q = (π/2)(E|g|^{2q})^{1/(2q)}`; **`ls_mom_sqrt`**: `(√k − c_q)‖G − EG‖_{2q} ≤ c_q‖√T‖_{2q}`.
* **`ls_lat_mom`**: the same on a latitude sphere, `k = n − 1`, for a Lipschitz positively
  1-homogeneous `Φ` (such as `λ`, `σ`).
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq gradSq_integrable gradSq_nonneg gradSq_le measurable_gradSq)
open BstLean.Part161 (momN momN_nonneg momN_pow mink4)

variable {ι : Type} [Fintype ι] {H₁ : (ι → ℝ) → ℝ} {L : ℝ}

/-- **Lemma LS for the moment of order `p` (sphere form).** For a Lipschitz positively
1-homogeneous `H₁` on `ℝ^k`, `G = H₁(Z/|Z|)`, `T = |∇H₁|² − G²` (the squared tangential
gradient), `c = (π/2)(E|g|^p)^{1/p}` and `R = ‖|Z|‖_p`:
`R·‖G − EG‖_p ≤ c·(‖G − EG‖_p + ‖√T‖_p)`, i.e. `‖G − EG‖_p ≤ c‖√T‖_p/(R − c)` when `R > c`. -/
theorem ls_mom [DecidableEq ι] [Nonempty ι] (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {p : ℕ} (hp : 1 ≤ p) :
    momN (stdGauss ι) p radF53 *
        momN (stdGauss ι) p (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι) ≤
      π / 2 * gmom p ^ ((p : ℝ)⁻¹) *
        (momN (stdGauss ι) p (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι) +
          momN (stdGauss ι) p (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2))) := by
  set γ := stdGauss ι
  have hp0 : p ≠ 0 := by omega
  have hc := hL.continuous hL0
  set G : (ι → ℝ) → ℝ := fun v => H₁ (unitF53 v) with hGd
  have mG : Measurable G := hc.measurable.comp measurable_unitF
  have bG : ∀ v, |G v| ≤ L := hom_unit_bound hL0 hL hhom
  have iG : Integrable G γ := Integrable.of_bound mG.aestronglyMeasurable L
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact bG v)
  set m := ∫ v, G v ∂γ with hm
  have hmL : |m| ≤ L := by
    rw [hm]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |G v| ∂γ ≤ ∫ _v, L ∂γ :=
          integral_mono iG.abs (integrable_const _) bG
      _ = L := by simp
  set H : (ι → ℝ) → ℝ := fun w => H₁ w - m * radF53 w with hHd
  have hHL : EuLip H (L + |m|) := by
    intro x y
    have h1 := hL x y
    have h2 := radF_lip x y
    have e : H x - H y = (H₁ x - H₁ y) - m * (radF53 x - radF53 y) := by simp only [hHd]; ring
    rw [e]
    calc |(H₁ x - H₁ y) - m * (radF53 x - radF53 y)| ≤ |H₁ x - H₁ y| + |m * (radF53 x - radF53 y)| :=
          abs_sub _ _
      _ = |H₁ x - H₁ y| + |m| * |radF53 x - radF53 y| := by rw [abs_mul]
      _ ≤ L * √(∑ i, (x i - y i) ^ 2) + |m| * √(∑ i, (x i - y i) ^ 2) := by gcongr
      _ = (L + |m|) * √(∑ i, (x i - y i) ^ 2) := by ring
  have hHeq : ∀ v, H v = (G v - m) * radF53 v := fun v => by
    simp only [hHd, hGd]; rw [hom_rad hhom v]; ring
  have hH0 : ∫ v, H v ∂γ = 0 := by
    simp_rw [hHeq]
    rw [polar_integral_mul (fun u => H₁ u - m) (fun r => r) (hc.measurable.sub_const m) measurable_id]
    have : ∫ Z, (H₁ (unitF53 Z) - m) ∂γ = 0 := by
      rw [integral_sub iG (integrable_const m)]
      simp [hm, G]
    rw [this, zero_mul]
  -- Poincaré in `L^p` for `H`
  have hP := poincare_p (add_nonneg hL0 (abs_nonneg m)) hHL hp
  rw [hH0] at hP
  simp only [sub_zero] at hP
  -- left side: `E|H|^p = E|G − m|^p · E|Z|^p`
  have hLHS : ∫ v, |H v| ^ p ∂γ = (∫ v, |G v - m| ^ p ∂γ) * ∫ v, |radF53 v| ^ p ∂γ := by
    have e : ∀ v, |H v| ^ p = |H₁ (unitF53 v) - m| ^ p * |radF53 v| ^ p := fun v => by
      rw [hHeq, abs_mul, mul_pow]
    simp_rw [e]
    exact polar_integral_mul (fun u => |H₁ u - m| ^ p) (fun r => |r| ^ p)
      ((hc.measurable.sub_const m).abs.pow_const p) (measurable_id.abs.pow_const p)
  -- the gradient of `H`
  set T : (ι → ℝ) → ℝ := fun v => gradSq H₁ v - G v ^ 2 with hTd
  have hnz : ∀ᵐ v ∂γ, v ≠ 0 := by
    have h0 : γ {(0 : ι → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton (0 : ι → ℝ))
    rw [ae_iff]
    simpa using h0
  have hgr : ∀ᵐ v ∂γ, √(gradSq H v) ≤ |G v - m| + √(T v) := by
    filter_upwards [hnz, hL.ae_diff hL0] with v hv hd
    have e := gradSq_sub_rad hhom m hv hd
    have e2 : gradSq H v = (G v - m) ^ 2 + T v := by
      simp only [hTd]; rw [show gradSq H v = gradSq (fun w => H₁ w - m * radF53 w) v from rfl, e]
      simp only [hGd]; ring
    rw [e2]
    have hT : T v ≤ √(T v) ^ 2 := by
      by_cases h : 0 ≤ T v
      · rw [Real.sq_sqrt h]
      · push_neg at h; exact h.le.trans (sq_nonneg _)
    rw [show |G v - m| + √(T v) = √((|G v - m| + √(T v)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [sq_abs (G v - m), abs_nonneg (G v - m), Real.sqrt_nonneg (T v)]
  -- Minkowski for `|G − m| + √T`
  set X := momN γ p (fun v => G v - m)
  set Y := momN γ p (fun v => √(T v))
  have bT : ∀ v, √(T v) ≤ L := fun v => by
    rw [show L = √(L ^ 2) from (Real.sqrt_sq hL0).symm]
    refine Real.sqrt_le_sqrt ?_
    have := gradSq_le hL0 hL v
    nlinarith [sq_nonneg (G v)]
  have mT : Measurable (fun v => √(T v)) := ((measurable_gradSq H₁).sub (mG.pow_const 2)).sqrt
  have hmk := mink4 γ p (g1 := fun v => |G v - m|) (g2 := fun v => √(T v)) (g3 := fun _ => 0)
    (g4 := fun _ => 0) (mG.sub_const m).abs mT measurable_const measurable_const
    (fun v => abs_nonneg _) (fun v => Real.sqrt_nonneg _) (fun _ => le_rfl) (fun _ => le_rfl)
    (M := 2 * L) (fun v => (abs_sub _ _).trans (by linarith [bG v]))
    (fun v => by linarith [bT v]) (fun _ => by positivity) (fun _ => by positivity)
    (b1 := X) (b2 := Y) (b3 := 0) (b4 := 0) (momN_nonneg _ _ _) (momN_nonneg _ _ _) le_rfl le_rfl
    (by rw [momN_pow γ hp0])
    (by rw [momN_pow γ hp0]; simp_rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact le_rfl)
    (by simp [zero_pow hp0]) (by simp [zero_pow hp0])
  simp only [add_zero] at hmk
  -- combine
  have igr : Integrable (fun v => √(gradSq H v) ^ p) γ := by
    refine Integrable.of_bound ((measurable_gradSq H).sqrt.pow_const p).aestronglyMeasurable
      ((L + |m|) ^ p) (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
    refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ p
    rw [show L + |m| = √((L + |m|) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (gradSq_le (add_nonneg hL0 (abs_nonneg m)) hHL v)
  have isum : Integrable (fun v => (|G v - m| + √(T v)) ^ p) γ := by
    refine Integrable.of_bound (((mG.sub_const m).abs.add mT).pow_const p).aestronglyMeasurable
      ((2 * L + L) ^ p) (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity)
      (add_le_add ((abs_sub _ _).trans (by linarith [bG v])) (bT v)) p
  have hgrp : ∫ v, √(gradSq H v) ^ p ∂γ ≤ (X + Y) ^ p :=
    (integral_mono_ae igr isum (hgr.mono fun v hv =>
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hv p)).trans hmk
  set R := momN γ p radF53
  set c := π / 2 * gmom p ^ ((p : ℝ)⁻¹)
  have hX0 : 0 ≤ X := momN_nonneg _ _ _
  have hY0 : 0 ≤ Y := momN_nonneg _ _ _
  have hR0 : 0 ≤ R := momN_nonneg _ _ _
  have hc0 : 0 ≤ c := by have := gmom_nonneg p; positivity
  have hXp : X ^ p = ∫ v, |G v - m| ^ p ∂γ := momN_pow γ hp0 _
  have hRp : R ^ p = ∫ v, |radF53 v| ^ p ∂γ := momN_pow γ hp0 _
  have hcp : c ^ p = (π / 2) ^ p * gmom p := by
    rw [mul_pow, Real.rpow_inv_natCast_pow (gmom_nonneg p) hp0]
  have key : (R * X) ^ p ≤ (c * (X + Y)) ^ p := by
    rw [mul_pow, mul_pow, hXp, hRp, hcp, mul_comm (∫ v, |radF53 v| ^ p ∂γ), ← hLHS, mul_assoc]
    refine hP.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgrp (gmom_nonneg p))
      (by positivity)
  exact le_of_pow_le_pow_left₀ hp0 (by positivity) key

/-- `√k ≤ ‖|Z|‖_{2q}` for a standard Gaussian vector in `ℝ^k` (Lyapunov). -/
lemma sqrt_card_le_momN_radF [Nonempty ι] {q : ℕ} (hq : 1 ≤ q) :
    √(Fintype.card ι : ℝ) ≤ momN (stdGauss ι) (2 * q) radF53 := by
  set γ := stdGauss ι
  have hrad2 : ∫ Z, radF53 Z ^ 2 ∂γ = Fintype.card ι := by
    classical
    simp_rw [radF_sq]
    rw [integral_finset_sum _ fun i _ => by
      simpa [sq] using BstLean.Part107.gauss_pair_integrable107 (ι := ι) i i]
    have : ∀ i : ι, ∫ Z, Z i ^ 2 ∂γ = 1 := fun i => by
      have := BstLean.Part107.gauss_pair107 (ι := ι) i i
      simpa [sq] using this
    simp [this]
  have i2 : Integrable (fun Z => radF53 Z ^ 2) γ := by
    classical
    have : (fun Z => radF53 Z ^ 2) = fun Z : ι → ℝ => ∑ i, Z i * Z i := by
      funext Z; rw [radF_sq]; exact Finset.sum_congr rfl fun i _ => sq _
    rw [this]
    exact integrable_finset_sum _ fun i _ => BstLean.Part107.gauss_pair_integrable107 i i
  have hJ : (∫ Z, radF53 Z ^ 2 ∂γ) ^ q ≤ ∫ Z, (radF53 Z ^ 2) ^ q ∂γ := by
    by_cases hint : Integrable (fun Z => (radF53 Z ^ 2) ^ q) γ
    · exact (convexOn_pow q).map_integral_le (μ := γ) (f := fun Z => radF53 Z ^ 2)
        (continuous_pow q).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun Z => Set.mem_Ici.mpr (sq_nonneg _)) i2 hint
    · -- the moment is finite (Gaussian norms have all moments)
      exfalso
      apply hint
      classical
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      have hb : ∀ Z : ι → ℝ, (radF53 Z ^ 2) ^ (r + 1) ≤ (Fintype.card ι : ℝ) ^ r *
          ∑ i, (Z i ^ 2) ^ (r + 1) := fun Z => by
        rw [radF_sq]
        have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset ι))
          (f := fun i => Z i ^ 2) (fun i _ => sq_nonneg _) r
        rw [Finset.card_univ] at h
        have hc : (0 : ℝ) < (Fintype.card ι : ℝ) ^ r := by
          have : 0 < Fintype.card ι := Fintype.card_pos
          positivity
        rw [div_le_iff₀ hc] at h
        linarith
      have ip : Integrable (fun Z : ι → ℝ => ∑ i, (Z i ^ 2) ^ (r + 1)) γ := by
        refine integrable_finsetSum _ fun i _ => ?_
        have := BstLean.Part35.stdGauss_prod_integrable (ι := ι) (2 * (r + 1)) (fun _ => i)
        simpa [Finset.prod_const, ← pow_mul] using this
      refine (ip.const_mul ((Fintype.card ι : ℝ) ^ r)).mono'
        ((measurable_radF.pow_const 2).pow_const (r + 1)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun Z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
      exact hb Z
  rw [hrad2] at hJ
  unfold momN
  have hp : (2 * q : ℕ) ≠ 0 := by omega
  have e : ∫ v, |radF53 v| ^ (2 * q) ∂γ = ∫ Z, (radF53 Z ^ 2) ^ q ∂γ := by
    congr 1; funext v; rw [abs_of_nonneg (radF_nonneg v), ← pow_mul]
  rw [e]
  have h0 : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  calc √(Fintype.card ι : ℝ) = ((Fintype.card ι : ℝ) ^ q) ^ (((2 * q : ℕ) : ℝ)⁻¹) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0, Real.sqrt_eq_rpow]
        congr 1
        push_cast
        field_simp
    _ ≤ (∫ Z, (radF53 Z ^ 2) ^ q ∂γ) ^ (((2 * q : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg h0 _) hJ (by positivity)

/-- `c_q = (π/2)(E|g|^{2q})^{1/(2q)}` (the paper's `c_p = (π/2)ν_{2p}`). -/
noncomputable def cLS (q : ℕ) : ℝ := π / 2 * gmom (2 * q) ^ (((2 * q : ℕ) : ℝ)⁻¹)

lemma cLS_nonneg (q : ℕ) : 0 ≤ cLS q := by unfold cLS; have := gmom_nonneg (2 * q); positivity

/-- **Lemma LS, moments of order `2q`, sphere form**: `(√k − c_q)·‖G − EG‖_{2q} ≤ c_q·‖√T‖_{2q}`. -/
theorem ls_mom_sqrt [DecidableEq ι] [Nonempty ι] (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {q : ℕ} (hq : 1 ≤ q) :
    (√(Fintype.card ι : ℝ) - cLS q) *
        momN (stdGauss ι) (2 * q) (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι) ≤
      cLS q * momN (stdGauss ι) (2 * q) (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) := by
  have h := ls_mom hL0 hL hhom (p := 2 * q) (by omega)
  have hR := sqrt_card_le_momN_radF (ι := ι) hq
  have hX := momN_nonneg (stdGauss ι) (2 * q)
    (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι)
  have h2 := mul_le_mul_of_nonneg_right hR hX
  unfold cLS
  nlinarith [h, h2]

open BstLean.Part161 (xLat) in
open BstLean.Part157 (Ret) in
/-- **Lemma LS, moments of order `2q`, on a latitude sphere** (Lemma `t7:p07:LS`, all `p`):
for a Lipschitz positively 1-homogeneous `Φ` on `ℝⁿ`,
`(√(n−1) − c_q)·‖Φ(x) − E(Φ | s)‖_{2q} ≤ c_q·‖√T‖_{2q}`, `T` the squared tangential gradient of
the lift `Φ ∘ xLatH c s`. (Paper: `‖φ − E(φ|s)‖_{2p} ≤ c_p (∏(n−1−2j))^{−1/(2p)}‖√Ψ‖_{2p}`.) -/
theorem ls_lat_mom {n : ℕ} (hn : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1)
    {Φ : (Fin n → ℝ) → ℝ} (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) {q : ℕ} (hq : 1 ≤ q) :
    (√((n : ℝ) - 1) - cLS q) * momN (stdGauss (Fin (n - 1))) (2 * q)
        (fun v => Φ (xLat c s (unitF53 v)) - ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) ≤
      cLS q * momN (stdGauss (Fin (n - 1))) (2 * q)
        (fun v => √(gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLat c s (unitF53 v)) ^ 2)) := by
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  set H₁ : (Fin (n - 1) → ℝ) → ℝ := fun w => Φ (xLatH c s w) with hH₁
  have hHL : EuLip H₁ L := by
    intro v w
    refine (hL _ _).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hL0)
    exact xLatH_dist (by omega) c hs v w
  have hHh : ∀ (t : ℝ) (v : Fin (n - 1) → ℝ), 0 < t → H₁ (t • v) = t * H₁ v := fun t v ht => by
    simp only [hH₁]; rw [xLatH_smul c s ht, hhom _ _ ht]
  have h := ls_mom_sqrt hL0 hHL hHh hq
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton (0 : Fin (n - 1) → ℝ))
    rw [ae_iff]
    simpa using h0
  have hG : ∀ᵐ v ∂stdGauss (Fin (n - 1)), H₁ (unitF53 v) = Φ (xLat c s (unitF53 v)) := by
    filter_upwards [hnz] with v hv
    simp only [hH₁]
    rw [xLatH_eq, radF_unitF hv, unitF_unitF hv, one_smul]
  have hm : ∫ w, H₁ (unitF53 w) ∂stdGauss (Fin (n - 1)) =
      ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1)) := integral_congr_ae hG
  have e1 : momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss (Fin (n - 1))) =
      momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => Φ (xLat c s (unitF53 v)) - ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) := by
    unfold momN; rw [hm]
    congr 1
    exact integral_congr_ae (hG.mono fun v hv => by beta_reduce; rw [hv])
  have e2 : momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) =
      momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => √(gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLat c s (unitF53 v)) ^ 2)) := by
    unfold momN
    congr 1
    exact integral_congr_ae (hG.mono fun v hv => by beta_reduce; rw [hv])
  have hc : (Fintype.card (Fin (n - 1)) : ℝ) = (n : ℝ) - 1 := by
    rw [Fintype.card_fin, Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1, e2, hc] at h
  exact h

end BstLean.Part162

open BstLean.Part162 in
#print axioms ls_mom
open BstLean.Part162 in
#print axioms ls_lat_mom
