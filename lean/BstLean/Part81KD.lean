import BstLean.Part81KDElem
import BstLean.Part78Sphere
import BstLean.Part78Mean

/-!
# Part 81 (KD): sphere constants of the degree-`d` kernel `κ(x,y) = Σ_q p_q(x) p_q(y)`

On the sphere `κ(x,x) = Σ_{j=1}^{d} h_j(x²)`, hence `e_d ≤ κ(x,x) ≤ d` and
`κ(x,x) − e_d ≤ Cδ d · Σ x_i⁴` with `Cδ d = d − 1` (natural subtraction).
-/

namespace BstLean.Part81

/-- The constant of the refined diagonal bound: `Cδ d = d − 1` (natural subtraction, so
`Cδ 0 = 0`). -/
def Cδ (d : ℕ) : ℝ := ((d - 1 : ℕ) : ℝ)

lemma Cδ_nonneg (d : ℕ) : 0 ≤ Cδ d := Nat.cast_nonneg _

lemma Cδ_eq (d : ℕ) (hd : 1 ≤ d) : Cδ d = (d : ℝ) - 1 := by
  unfold Cδ; rw [Nat.cast_sub hd]; simp

end BstLean.Part81

namespace BstLean.Part81.KD

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM phiSq)
open BstLean.Part53 (hS53 c0)
open BstLean.Part78 (q4 sph_int)

variable {n d : ℕ}

/-! ## The diagonal as a sum of complete homogeneous symmetric polynomials -/

lemma sumJJ (g : Mono n d → ℝ) : ∑ q : JJ n d, g q.1 = ∑ p, g p - g default := by
  classical
  have h : ∑ q : JJ n d, g q.1
      = ∑ p ∈ Finset.univ.filter (fun p : Mono n d => p ≠ default), g p := by
    rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  rw [h, Finset.filter_ne' Finset.univ (default : Mono n d),
    Finset.sum_erase_eq_sub (Finset.mem_univ _)]

lemma phiM_default (x : Fin n → ℝ) : phiM x (default : Mono n d) = 1 := by
  simp [phiM, monoVal, default]

lemma kap_diag_phiSq (x : Fin n → ℝ) : kap d x x = phiSq d x - 1 := by
  unfold kap pf
  rw [sumJJ (fun p => phiM x p * phiM x p), phiM_default, mul_one]
  unfold phiSq
  congr 1
  exact Finset.sum_congr rfl (fun p _ => (sq _).symm)

lemma kap_diag_hS (x : Fin n → ℝ) :
    kap d x x = ∑ j ∈ Finset.range d, hS53 (fun i => x i ^ 2) (j + 1) := by
  rw [kap_diag_phiSq, phiSq_hS,
    Fin.sum_univ_eq_sum_range (fun i => hS53 (fun i => x i ^ 2) i) (d + 1),
    Finset.sum_range_succ', hSZero53]
  ring

lemma eD_eq (d : ℕ) : eD d = ∑ j ∈ Finset.range d, 1 / ((j + 1).factorial : ℝ) := by
  unfold eD c0
  rw [Finset.sum_range_succ']
  simp

lemma sum_range_le (t : ℕ → ℝ) (Q : ℝ) (_hQ : 0 ≤ Q) (h0 : t 0 ≤ 0) (ht : ∀ j, t j ≤ Q) (d : ℕ) :
    ∑ j ∈ Finset.range d, t j ≤ ((d - 1 : ℕ) : ℝ) * Q := by
  induction d with
  | zero => simp
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa using h0
    · rw [Finset.sum_range_succ]
      have e : ((d + 1 - 1 : ℕ) : ℝ) = ((d - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.add_sub_cancel, Nat.cast_sub hd]; simp
      rw [e]
      nlinarith [ht d]

lemma q4_eq (x : Fin n → ℝ) : ∑ i, (fun i => x i ^ 2) i ^ 2 = ∑ i, x i ^ 4 :=
  Finset.sum_congr rfl (fun i _ => by show (x i ^ 2) ^ 2 = x i ^ 4; ring)

/-! ## The smoothing constant -/

lemma eD_mono {d e : ℕ} (h : d ≤ e) : eD d ≤ eD e := by
  rw [eD_eq, eD_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun j _ _ => by positivity)

lemma two_pow_le_fact (j : ℕ) : (2 : ℝ) ^ j ≤ ((j + 1).factorial : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ, mul_comm]
    have h2 : (2 : ℝ) ≤ ((j + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    exact mul_le_mul h2 ih (by positivity) (by positivity)

lemma fact_ge (j : ℕ) : 24 * (5 : ℝ) ^ j ≤ ((j + 4).factorial : ℝ) := by
  induction j with
  | zero => norm_num [Nat.factorial]
  | succ j ih =>
    rw [show j + 1 + 4 = (j + 4) + 1 by ring, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h5 : (5 : ℝ) ≤ ((j + 4 + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    nlinarith [mul_le_mul h5 ih (by positivity) (by positivity : (0:ℝ) ≤ ((j + 4 + 1 : ℕ) : ℝ))]

lemma geom5 (d : ℕ) : ∑ j ∈ Finset.range d, (1 / 5 : ℝ) ^ j = 5 / 4 - 5 / 4 * (1 / 5) ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

end BstLean.Part81.KD

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM phiSq)
open BstLean.Part53 (hS53 c0)
open BstLean.Part78 (q4 sph_int)
open BstLean.Part81.KD

variable {n d : ℕ}

theorem one_le_eD (d : ℕ) (hd : 1 ≤ d) : 1 ≤ eD d := by
  refine le_trans ?_ (eD_mono hd)
  rw [eD_eq]; simp

theorem three_halves_le_eD (d : ℕ) (hd : 2 ≤ d) : 3 / 2 ≤ eD d := by
  refine le_trans ?_ (eD_mono hd)
  rw [eD_eq]; norm_num [Finset.sum_range_succ, Nat.factorial]

theorem five_thirds_le_eD (d : ℕ) (hd : 3 ≤ d) : 5 / 3 ≤ eD d := by
  refine le_trans ?_ (eD_mono hd)
  rw [eD_eq]; norm_num [Finset.sum_range_succ, Nat.factorial]

theorem eD_le (d : ℕ) : eD d ≤ 1719 / 1000 := by
  refine le_trans (eD_mono (Nat.le_add_right d 3)) ?_
  rw [eD_eq, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∑ j ∈ Finset.range d, 1 / ((j + 1 + 1 + 1 + 1).factorial : ℝ)
      ≤ ∑ j ∈ Finset.range d, 1 / 24 * (1 / 5 : ℝ) ^ j := by
    apply Finset.sum_le_sum; intro j _
    have := fact_ge j
    rw [show 1 / 24 * (1 / 5 : ℝ) ^ j = 1 / (24 * 5 ^ j) by rw [one_div_pow]; ring]
    exact one_div_le_one_div_of_le (by positivity) this
  rw [← Finset.mul_sum, geom5] at h
  have hp : (0 : ℝ) ≤ (1 / 5) ^ d := by positivity
  norm_num [Nat.factorial] at h ⊢
  linarith

theorem eD_le_two (d : ℕ) : eD d ≤ 2 := le_trans (eD_le d) (by norm_num)

/-! ## Pointwise bounds on the diagonal -/

theorem kap_diag_lower (n d : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : eD d ≤ kap d x x := by
  rw [kap_diag_hS, eD_eq]
  exact Finset.sum_le_sum fun j _ => (hSBounds53 _ (fun i => sq_nonneg _) hx (j + 1)).1

theorem kap_diag_upper (n d : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : kap d x x ≤ d := by
  rw [kap_diag_hS]
  calc ∑ j ∈ Finset.range d, hS53 (fun i => x i ^ 2) (j + 1)
      ≤ ∑ _j ∈ Finset.range d, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => hSLeOne53 _ (fun i => sq_nonneg _) hx (j + 1)
    _ = d := by simp

theorem kap_diag_refined (n d : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    kap d x x - eD d ≤ Cδ d * ∑ i, x i ^ 4 := by
  rw [kap_diag_hS, eD_eq, ← Finset.sum_sub_distrib]
  unfold Cδ
  apply sum_range_le (fun j => hS53 (fun i => x i ^ 2) (j + 1) - 1 / ((j + 1).factorial : ℝ))
  · exact Finset.sum_nonneg fun i _ => by positivity
  · have := hSLeOne53 _ (fun i => sq_nonneg (x i)) hx 1
    simpa using this
  · intro j
    have := (hSBounds53 _ (fun i => sq_nonneg (x i)) hx (j + 1)).2
    rw [q4_eq] at this
    show hS53 (fun i => x i ^ 2) (j + 1) - 1 / ((j + 1).factorial : ℝ) ≤ _
    linarith

end BstLean.Part81

namespace BstLean.Part81.KD

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM phiSq)
open BstLean.Part78 (q4 sph_int)

variable {n d : ℕ}

/-! ## The inner integral -/

lemma cont_pf (q : JJ n d) : Continuous (fun x : Fin n → ℝ => pf x q) := by
  unfold pf phiM monoVal
  exact continuous_multiset_prod _ (fun _ _ => continuous_apply _)

lemma cont_kap_diag : Continuous (fun x : Fin n → ℝ => kap d x x) := by
  unfold kap
  exact continuous_finsetSum _ (fun q _ => (cont_pf q).mul (cont_pf q))

/-- `μ_q = E p_q`. -/
noncomputable def mu (n d : ℕ) (q : JJ n d) : ℝ := ∫ y, pf y q ∂uniformSphere n

lemma inner_eq (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∫ y, kap d x y ∂uniformSphere n = ∑ q : JJ n d, pf x q * mu n d q := by
  unfold kap
  rw [integral_finsetSum _ (fun q _ => (sph_int hn (cont_pf q)).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

lemma term_nonneg (hn : 1 ≤ n) (x : Fin n → ℝ) (q : JJ n d) : 0 ≤ pf x q * mu n d q := by
  by_cases h : ∃ i, ¬ Even (q.1.2.1.count i)
  · have : mu n d q = 0 := mom_odd hn _ h
    rw [this, mul_zero]
  · simp only [not_exists, not_not] at h
    refine mul_nonneg ?_ (mom_nonneg hn _)
    show 0 ≤ monoVal x q.1.2.1
    unfold monoVal
    rw [prodMapUniv]
    exact Finset.prod_nonneg fun i _ => (h i).pow_nonneg _

lemma mm1_eq (hn : 1 ≤ n) : mm1 n d = ∑ q : JJ n d, mu n d q ^ 2 := by
  unfold mm1
  simp_rw [inner_eq hn]
  rw [integral_finsetSum _ (fun q _ => (sph_int hn (cont_pf q)).mul_const _)]
  simp_rw [integral_mul_const]
  exact Finset.sum_congr rfl (fun q _ => (sq _).symm)

lemma inner_sq_le (hn : 1 ≤ n) (x : Fin n → ℝ) :
    (∫ y, kap d x y ∂uniformSphere n) ^ 2 ≤ kap d x x * mm1 n d := by
  rw [inner_eq hn, mm1_eq hn]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun q : JJ n d => pf x q) (mu n d)
  have e : kap d x x = ∑ q : JJ n d, pf x q ^ 2 := by
    unfold kap; exact Finset.sum_congr rfl (fun q _ => (sq _).symm)
  rw [e]; exact h

end BstLean.Part81.KD

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part78 (q4 sph_int)
open BstLean.Part81.KD

variable {n d : ℕ}

theorem inner_kap_nonneg (n d : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) :
    0 ≤ ∫ y, kap d x y ∂uniformSphere n := by
  rw [inner_eq hn]
  exact Finset.sum_nonneg fun q _ => term_nonneg hn x q

theorem tG_lower (n d : ℕ) (hn : 1 ≤ n) : eD d ≤ tG n d := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hc : ∫ _x : Fin n → ℝ, eD d ∂uniformSphere n = eD d := by simp
  rw [← hc]
  unfold tG
  apply integral_mono_ae (integrable_const _) (sph_int hn cont_kap_diag)
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  exact kap_diag_lower n d x hx

theorem tG_upper (n d : ℕ) (hn : 1 ≤ n) : tG n d - eD d ≤ 3 * Cδ d / n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have iQ : Integrable (fun x : Fin n → ℝ => q4 x) (uniformSphere n) :=
    sph_int hn BstLean.Part78.q4_cont
  have hc : ∫ _x : Fin n → ℝ, eD d ∂uniformSphere n = eD d := by simp
  have h : tG n d ≤ ∫ x, (eD d + Cδ d * q4 x) ∂uniformSphere n := by
    unfold tG
    apply integral_mono_ae (sph_int hn cont_kap_diag) ((integrable_const _).add (iQ.const_mul _))
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    have := kap_diag_refined n d x hx
    show kap d x x ≤ eD d + Cδ d * q4 x
    unfold q4; linarith
  rw [integral_add (integrable_const _) (iQ.const_mul _), integral_const_mul, hc,
    BstLean.Part78.integral_q4 hn] at h
  have h3 : 3 / ((n : ℝ) + 2) ≤ 3 / n := by
    rw [div_le_div_iff₀ (by positivity) hnR]; nlinarith
  have := mul_le_mul_of_nonneg_left h3 (Cδ_nonneg d)
  have e : 3 * Cδ d / n = Cδ d * (3 / n) := by ring
  rw [e]; linarith

theorem kk2_upper (n d : ℕ) (hn : 1 ≤ n) : kk2 n d - tG n d ^ 2 ≤ 3 * Cδ d ^ 2 / n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have iQ : Integrable (fun x : Fin n → ℝ => q4 x) (uniformSphere n) :=
    sph_int hn BstLean.Part78.q4_cont
  have iK : Integrable (fun x : Fin n → ℝ => kap d x x) (uniformSphere n) :=
    sph_int hn cont_kap_diag
  have iK2 : Integrable (fun x : Fin n → ℝ => kap d x x ^ 2) (uniformSphere n) :=
    sph_int hn (cont_kap_diag.pow 2)
  have ex : ∫ x, (kap d x x - eD d) ^ 2 ∂uniformSphere n
      = kk2 n d - 2 * eD d * tG n d + eD d ^ 2 := by
    have e : ∀ x : Fin n → ℝ, (kap d x x - eD d) ^ 2
        = kap d x x ^ 2 - 2 * eD d * kap d x x + eD d ^ 2 := fun x => by ring
    simp_rw [e]
    have hA : ∫ x, (kap d x x ^ 2 - 2 * eD d * kap d x x + eD d ^ 2) ∂uniformSphere n
        = ∫ x, (kap d x x ^ 2 - 2 * eD d * kap d x x) ∂uniformSphere n
          + ∫ _x : Fin n → ℝ, eD d ^ 2 ∂uniformSphere n :=
      integral_add (iK2.sub (iK.const_mul _)) (integrable_const _)
    have hB : ∫ x, (kap d x x ^ 2 - 2 * eD d * kap d x x) ∂uniformSphere n
        = ∫ x, kap d x x ^ 2 ∂uniformSphere n - ∫ x, 2 * eD d * kap d x x ∂uniformSphere n :=
      integral_sub iK2 (iK.const_mul _)
    rw [hA, hB, integral_const_mul]
    simp [kk2, tG]
  have hle : ∫ x, (kap d x x - eD d) ^ 2 ∂uniformSphere n
      ≤ ∫ x, Cδ d ^ 2 * q4 x ∂uniformSphere n := by
    apply integral_mono_ae
      (sph_int hn ((cont_kap_diag.sub continuous_const).pow 2)) (iQ.const_mul _)
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    have h0 : 0 ≤ kap d x x - eD d := by linarith [kap_diag_lower n d x hx]
    have h1 : kap d x x - eD d ≤ Cδ d * q4 x := kap_diag_refined n d x hx
    have hq0 := BstLean.Part78.q4_nonneg x
    have hq1 := BstLean.Part78.q4_le_one x hx
    show (kap d x x - eD d) ^ 2 ≤ Cδ d ^ 2 * q4 x
    calc (kap d x x - eD d) ^ 2 ≤ (Cδ d * q4 x) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = Cδ d ^ 2 * (q4 x * q4 x) := by ring
      _ ≤ Cδ d ^ 2 * q4 x := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  rw [integral_const_mul, BstLean.Part78.integral_q4 hn, ex] at hle
  have h3 : 3 / ((n : ℝ) + 2) ≤ 3 / n := by
    rw [div_le_div_iff₀ (by positivity) hnR]; nlinarith
  have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (Cδ d))
  have e : 3 * Cδ d ^ 2 / n = Cδ d ^ 2 * (3 / n) := by ring
  rw [e]
  nlinarith [sq_nonneg (tG n d - eD d)]

theorem inner_kap_le (n d : ℕ) (hd : 1 ≤ d) (hn : d + 1 ≤ n) (hK : KerGen n d)
    (hF : FeatOp n d ((d : ℝ) + 1)) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    ∫ y, kap d x y ∂uniformSphere n ≤ kap d x x := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨hm0, -, -, hgen⟩ := hK
  obtain ⟨hm, -⟩ := hgen ((d : ℝ) + 1) (by positivity) hF
  have hm1 : mm1 n d ≤ 1 := by
    refine le_trans hm ?_
    rw [div_le_one hnR]; exact_mod_cast hn
  have hk1 : 1 ≤ kap d x x := le_trans (one_le_eD d hd) (kap_diag_lower n d x hx)
  have hsq := inner_sq_le (d := d) hn1 x
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hm1 (by linarith : (0 : ℝ) ≤ kap d x x)]

/-- **Sphere constants of the degree-`d` kernel**, `Cδ d = d − 1`. -/
theorem sphCGen (n d : ℕ) (hd : 1 ≤ d) (hn : d + 1 ≤ n) (hK : KerGen n d)
    (hF : FeatOp n d ((d : ℝ) + 1)) :
    SphC n d ((d : ℝ) + 1) (((d : ℝ) + 1) * (eD d + 3 * Cδ d / n)) (3 * Cδ d) (3 * Cδ d ^ 2) d := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hK' := hK
  obtain ⟨hm0, hs0, hk, hgen⟩ := hK
  obtain ⟨hm, hs⟩ := hgen ((d : ℝ) + 1) (by positivity) hF
  have htu := tG_upper n d hn1
  refine ⟨tG_lower n d hn1, htu, hm0, hm, hs0, ?_, hk, kk2_upper n d hn1, ?_⟩
  · refine le_trans hs ?_
    have hpos : (0 : ℝ) ≤ ((d : ℝ) + 1) / n := by positivity
    have := mul_le_mul_of_nonneg_left (by linarith : tG n d ≤ eD d + 3 * Cδ d / n) hpos
    refine le_trans this (le_of_eq ?_)
    ring
  · intro x hx
    exact ⟨kap_diag_lower n d x hx, kap_diag_upper n d x hx, inner_kap_nonneg n d hn1 x,
      inner_kap_le n d hd hn hK' hF x hx⟩

end BstLean.Part81

#print axioms BstLean.Part81.kap_diag_lower
#print axioms BstLean.Part81.kap_diag_upper
#print axioms BstLean.Part81.kap_diag_refined
#print axioms BstLean.Part81.inner_kap_nonneg
#print axioms BstLean.Part81.sphCGen
#print axioms BstLean.Part81.eD_le
#print axioms BstLean.Part81.one_le_eD
#print axioms BstLean.Part81.three_halves_le_eD
#print axioms BstLean.Part81.five_thirds_le_eD
