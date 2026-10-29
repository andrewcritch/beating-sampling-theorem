import BstLean.Part58Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

/-! Derivative identities for the complete homogeneous polynomials in `κ`. -/

namespace BstLean.Part58.Kappa

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def mon (s : Multiset ι) : MvPolynomial ι ℝ :=
  (s.map (X : ι → MvPolynomial ι ℝ)).prod

@[simp] lemma mon_zero : mon (0 : Multiset ι) = 1 := by simp [mon]

@[simp] lemma mon_cons (a : ι) (s : Multiset ι) : mon (a ::ₘ s) = X a * mon s := by
  simp [mon]

lemma X_mul_pderiv_mon (i : ι) (s : Multiset ι) :
    X i * pderiv i (mon s) = (s.count i : ℝ) • mon s := by
  induction s using Multiset.induction_on with
  | empty => simp [mon]
  | @cons a s ih =>
    rw [mon_cons, Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases ha : a = i
    · subst a
      simp only [pderiv_X_self, one_mul, Multiset.count_cons_self, Nat.cast_add,
        Nat.cast_one, smul_eq_C_mul] at *
      rw [mul_add]
      have hm := congrArg (fun p => X i * p) ih
      rw [hm]
      simp only [map_add, map_one]
      ring
    · simp only [pderiv_X_of_ne ha, zero_mul, zero_add,
        Multiset.count_cons_of_ne (Ne.symm ha)]
      calc
        _ = X a * (X i * pderiv i (mon s)) := by ring
        _ = X a * ((s.count i : ℝ) • mon s) := by rw [ih]
        _ = _ := by simp only [smul_eq_C_mul]; ring

lemma pderiv_mon_of_mem (i : ι) (s : Multiset ι) (hi : i ∈ s) :
    pderiv i (mon s) = (s.count i : ℝ) • mon (s.erase i) := by
  have hm : mon s = X i * mon (s.erase i) := by
    conv_lhs => rw [← Multiset.cons_erase hi, mon_cons]
  apply mul_left_cancel₀ (show (X i : MvPolynomial ι ℝ) ≠ 0 by exact X_ne_zero i)
  rw [X_mul_pderiv_mon, hm]
  simp only [smul_eq_C_mul]
  ring

lemma pderiv_mon_of_not_mem (i : ι) (s : Multiset ι) (hi : i ∉ s) :
    pderiv i (mon s) = 0 := by
  apply mul_left_cancel₀ (show (X i : MvPolynomial ι ℝ) ≠ 0 by exact X_ne_zero i)
  rw [X_mul_pderiv_mon, Multiset.count_eq_zero.mpr hi]
  simp

/-- Remove one occurrence of a fixed variable from a homogeneous monomial. -/
noncomputable def consEquiv (i : ι) (j : ℕ) :
    Sym ι j ≃ {s : Sym ι (j + 1) // i ∈ s} where
  toFun s := ⟨Sym.cons i s, Sym.mem_cons_self _ _⟩
  invFun s := s.val.erase i s.property
  left_inv s := Sym.erase_cons_head s i
  right_inv s := Subtype.ext (Sym.cons_erase s.property)

/-- The derivative recurrence avoids expanding the full monomial support. -/
theorem pderiv_hsymm_succ (i : ι) (j : ℕ) :
    pderiv i (hsymm ι ℝ (j + 1)) =
      hsymm ι ℝ j + X i * pderiv i (hsymm ι ℝ j) := by
  classical
  have hs : pderiv i (hsymm ι ℝ (j + 1)) =
      ∑ s : {s : Sym ι (j + 1) // i ∈ s},
        (s.val.val.count i : ℝ) • mon (s.val.val.erase i) := by
    unfold hsymm
    rw [map_sum]
    change (∑ s : Sym ι (j + 1), pderiv i (mon s.val)) = _
    rw [← Fintype.sum_subtype_add_sum_subtype (p := fun s : Sym ι (j + 1) => i ∈ s)]
    have hz : (∑ s : {s : Sym ι (j + 1) // ¬ i ∈ s}, pderiv i (mon s.val.val)) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      exact pderiv_mon_of_not_mem i s.val.val s.property
    rw [hz, add_zero]
    · apply Finset.sum_congr rfl
      intro s hs
      exact pderiv_mon_of_mem i s.val s.property
  rw [hs, ← (consEquiv i j).sum_comp]
  change (∑ s : Sym ι j, ((i ::ₘ s.val).count i : ℝ) •
    mon ((i ::ₘ s.val).erase i)) = _
  simp only [consEquiv, Multiset.count_cons_self, Multiset.erase_cons_head,
    Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  rw [Finset.sum_add_distrib]
  have hp : (∑ s : Sym ι j, (s.val.count i : ℝ) • mon s.val) =
      X i * pderiv i (hsymm ι ℝ j) := by
    simp only [hsymm, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact (X_mul_pderiv_mon i s.val).symm
  rw [hp]
  exact add_comm _ _

noncomputable def hval (j : ℕ) (u : ι → ℝ) : ℝ := eval u (hsymm ι ℝ j)

lemma hval_eq (j : ℕ) (u : ι → ℝ) :
    hval j u = ∑ s : Sym ι j, (s.val.map u).prod := by
  simp [hval, hsymm, map_multiset_prod, Multiset.map_map]

private lemma enum_exists {j : ℕ} (s : Sym ι j) :
    ∃ w : Fin j → ι, Finset.univ.val.map w = s.val := by
  have he (s : Multiset ι) : ∃ (r : ℕ) (w : Fin r → ι),
      r = s.card ∧ Finset.univ.val.map w = s := by
    induction s using Quot.inductionOn with
    | h a => exact ⟨a.length, a.get, rfl, by simp [Fin.univ_val_map]⟩
  obtain ⟨r, w, hr, hw⟩ := he s.val
  have hj : r = j := hr.trans s.property
  clear hr
  subst r
  exact ⟨w, hw⟩

private noncomputable def enum {j : ℕ} (s : Sym ι j) : Fin j → ι :=
  Classical.choose (enum_exists s)

private lemma enum_spec {j : ℕ} (s : Sym ι j) :
    Finset.univ.val.map (enum s) = s.val := Classical.choose_spec (enum_exists s)

private lemma enum_injective {j : ℕ} : Function.Injective (enum : Sym ι j → Fin j → ι) := by
  intro s t h
  apply Subtype.ext
  rw [← enum_spec s, ← enum_spec t, h]

theorem hval_bounds (j : ℕ) (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i ≤ 1) : 0 ≤ hval j u ∧ hval j u ≤ 1 := by
  classical
  rw [hval_eq]
  constructor
  · exact Finset.sum_nonneg fun s _ => Multiset.prod_nonneg
      (by intro a ha; obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha; exact hu i)
  · have hm (s : Sym ι j) : (s.val.map u).prod = ∏ t, u (enum s t) := by
      rw [← enum_spec s, Multiset.map_map]
      rfl
    simp_rw [hm]
    calc
      _ = ∑ w ∈ Finset.univ.image (enum : Sym ι j → Fin j → ι), ∏ t, u (w t) := by
        rw [Finset.sum_image (fun s _ t _ h => enum_injective h)]
      _ ≤ ∑ w : Fin j → ι, ∏ t, u (w t) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun w _ _ => Finset.prod_nonneg (fun t _ => hu _))
      _ = ∏ _ : Fin j, ∑ i, u i := (Fintype.prod_sum (fun (_ : Fin j) i => u i)).symm
      _ ≤ 1 := by
        exact Finset.prod_le_one₀ (fun _ _ => Finset.sum_nonneg fun i _ => hu i)
          (fun _ _ => hs)

theorem pderiv_hval_bounds (j : ℕ) (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i ≤ 1) (i : ι) :
    0 ≤ eval u (pderiv i (hsymm ι ℝ j)) ∧
      eval u (pderiv i (hsymm ι ℝ j)) ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pderiv_hsymm_succ]
    simp only [map_add, map_mul, eval_X, Nat.cast_add, Nat.cast_one]
    obtain ⟨hlo, hhi⟩ := hval_bounds j u hu hs
    have hui : u i ≤ 1 := (Finset.single_le_sum (fun l _ => hu l)
      (Finset.mem_univ i)).trans hs
    constructor
    · exact add_nonneg hlo (mul_nonneg (hu i) ih.1)
    · change hval j u + u i * eval u (pderiv i (hsymm ι ℝ j)) ≤ (j : ℝ) + 1
      nlinarith [mul_le_mul_of_nonneg_right hui ih.1]

noncomputable def Hpoly (d : ℕ) : MvPolynomial ι ℝ :=
  ∑ j ∈ Finset.range (d + 1), hsymm ι ℝ j

noncomputable def Hval (d : ℕ) (u : ι → ℝ) : ℝ := eval u (Hpoly d)

noncomputable def common (d : ℕ) (u : ι → ℝ) : ℝ :=
  ∑ j ∈ Finset.range d, hval j u

theorem pderiv_Hpoly (d : ℕ) (u : ι → ℝ) (i : ι) :
    eval u (pderiv i (Hpoly d)) - common d u =
      u i * ∑ j ∈ Finset.range d, eval u (pderiv i (hsymm ι ℝ j)) := by
  unfold Hpoly common
  rw [map_sum, map_sum]
  rw [Finset.sum_range_succ']
  simp only [hsymm_zero, pderiv_one, map_zero, add_zero,
    pderiv_hsymm_succ, map_add, map_mul, eval_X]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hval]
  ring

theorem pderiv_Hpoly_centered_bounds (d : ℕ) (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i ≤ 1) (i : ι) :
    0 ≤ eval u (pderiv i (Hpoly d)) - common d u ∧
      eval u (pderiv i (Hpoly d)) - common d u ≤
        u i * ((d : ℝ) * ((d : ℝ) - 1) / 2) := by
  rw [pderiv_Hpoly]
  have hb : (∑ j ∈ Finset.range d, eval u (pderiv i (hsymm ι ℝ j))) ≤
      (d : ℝ) * ((d : ℝ) - 1) / 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range d, (j : ℝ) :=
        Finset.sum_le_sum (fun j hj => (pderiv_hval_bounds j u hu hs i).2)
      _ = _ := by
        induction d with
        | zero => simp
        | succ d ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  constructor
  · exact mul_nonneg (hu i) (Finset.sum_nonneg fun j _ =>
      (pderiv_hval_bounds j u hu hs i).1)
  · exact mul_le_mul_of_nonneg_left hb (hu i)

theorem eval_hasDerivAt (p : MvPolynomial ι ℝ) (u : ℝ → ι → ℝ) (du : ι → ℝ)
    (t : ℝ) (hu : ∀ i, HasDerivAt (fun t => u t i) (du i) t) :
    HasDerivAt (fun t => eval (u t) p)
      (∑ i, eval (u t) (pderiv i p) * du i) t := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const t c
  | add p q hp hq =>
    simpa only [map_add, add_mul, Finset.sum_add_distrib, Pi.add_def] using hp.add hq
  | mul_X p i hp =>
    convert hp.mul (hu i) using 1
    · funext s
      simp
    · simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, eval_X,
        pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero,
        add_mul, Finset.sum_add_distrib]
      simp only [mul_ite, one_mul, mul_one, mul_zero, zero_mul, ite_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      have hs : (∑ j, u t i * eval (u t) (pderiv j p) * du j) =
          (∑ j, eval (u t) (pderiv j p) * du j) * u t i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hs]
      ring

theorem Hval_deriv_sq_bound (d : ℕ) (u w : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i ≤ 1) (hw : ∑ i, w i = 0) :
    (∑ i, eval u (pderiv i (Hpoly d)) * w i) ^ 2 ≤
      ((d : ℝ) * ((d : ℝ) - 1) / 2) ^ 2 * ∑ i, w i ^ 2 := by
  let B : ℝ := (d : ℝ) * ((d : ℝ) - 1) / 2
  have hB : 0 ≤ B := by
    cases d with
    | zero => simp [B]
    | succ d => dsimp [B]; push_cast; simp only [add_sub_cancel_right]; positivity
  let a : ι → ℝ := fun i => eval u (pderiv i (Hpoly d)) - common d u
  have ha : ∀ i, 0 ≤ a i ∧ a i ≤ u i * B :=
    fun i => pderiv_Hpoly_centered_bounds d u hu hs i
  have hui : ∀ i, u i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun l _ => hu l) (Finset.mem_univ i)).trans hs
  have ha2 : (∑ i, a i ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ ∑ i, (u i * B) ^ 2 := Finset.sum_le_sum fun i _ =>
        (sq_le_sq₀ (ha i).1 (mul_nonneg (hu i) hB)).mpr (ha i).2
      _ = B ^ 2 * ∑ i, u i ^ 2 := by simp only [mul_pow, Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ B ^ 2 * ∑ i, u i := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => by nlinarith [hu i, hui i]) (sq_nonneg B)
      _ ≤ B ^ 2 := by simpa using mul_le_mul_of_nonneg_left hs (sq_nonneg B)
  have he : (∑ i, eval u (pderiv i (Hpoly d)) * w i) = ∑ i, a i * w i := by
    simp only [a, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, mul_zero, sub_zero]
  rw [he]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a w).trans
    (mul_le_mul_of_nonneg_right ha2 (Finset.sum_nonneg fun i _ => sq_nonneg _))

/-- `κ`, viewed as a function of squared coordinates, is Lipschitz on the probability simplex. -/
theorem Hval_sub_sq_le (d : ℕ) (u z : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hz : ∀ i, 0 ≤ z i)
    (hsu : ∑ i, u i = 1) (hsz : ∑ i, z i = 1) :
    (Hval d u - Hval d z) ^ 2 ≤
      ((d : ℝ) * ((d : ℝ) - 1) / 2) ^ 2 * ∑ i, (u i - z i) ^ 2 := by
  let U : ℝ → ι → ℝ := fun t i => z i + t * (u i - z i)
  let V : ℝ → ℝ := fun t => Hval d (U t)
  let D : ℝ → ℝ := fun t => ∑ i, eval (U t) (pderiv i (Hpoly d)) * (u i - z i)
  let C : ℝ := Real.sqrt (((d : ℝ) * ((d : ℝ) - 1) / 2) ^ 2 *
    ∑ i, (u i - z i) ^ 2)
  have hC : C ^ 2 = ((d : ℝ) * ((d : ℝ) - 1) / 2) ^ 2 *
      ∑ i, (u i - z i) ^ 2 := Real.sq_sqrt (by positivity)
  have hd : ∀ t, HasDerivAt V (D t) t := by
    intro t
    apply eval_hasDerivAt
    intro i
    convert (hasDerivAt_const t (z i)).add
      ((hasDerivAt_id t).mul_const (u i - z i)) using 1 <;> simp [U, Pi.add_def]
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t‖ ≤ C := by
    intro t ht
    have hU : ∀ i, 0 ≤ U t i := by
      intro i
      have : U t i = (1 - t) * z i + t * u i := by dsimp [U]; ring
      rw [this]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hz i))
        (mul_nonneg ht.1 (hu i))
    have hsum : ∑ i, U t i = 1 := by
      simp only [U, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_sub_distrib, hsu, hsz]
      ring
    have hw : (∑ i, (u i - z i)) = 0 := by rw [Finset.sum_sub_distrib, hsu, hsz]; ring
    have h := Hval_deriv_sq_bound d (U t) (fun i => u i - z i) hU hsum.le hw
    change D t ^ 2 ≤ _ at h
    rw [← hC] at h
    rw [Real.norm_eq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by simpa only [sq_abs] using h)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
  have hV0 : V 0 = Hval d z := by
    change Hval d (U 0) = Hval d z
    have hU : U 0 = z := by funext i; simp [U]
    rw [hU]
  have hV1 : V 1 = Hval d u := by
    change Hval d (U 1) = Hval d u
    have hU : U 1 = u := by funext i; simp [U]
    rw [hU]
  rw [hV0, hV1] at h
  norm_num only [sub_zero, norm_one, mul_one, Real.norm_eq_abs] at h
  have hh := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr h
  rw [sq_abs] at hh
  exact hh.trans_eq hC

theorem Hval_eq_kap {n : ℕ} (d : ℕ) (x : Fin n → ℝ) :
    Hval d (fun i => x i ^ 2) = BstLean.Part58.kap d x := by
  classical
  unfold Hval Hpoly BstLean.Part58.kap BstLean.Part41.phiSq BstLean.Part41.phiM
  rw [map_sum, Fintype.sum_sigma]
  change (∑ j ∈ Finset.range (d + 1), hval j (fun i => x i ^ 2)) =
    ∑ j : Fin (d + 1), ∑ s : Sym (Fin n) j.val, BstLean.Part36.monoVal x s.val ^ 2
  calc
    _ = ∑ j : Fin (d + 1), hval j.val (fun i => x i ^ 2) :=
      (Fin.sum_univ_eq_sum_range _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hval_eq]
      apply Finset.sum_congr rfl
      intro s hs
      exact Multiset.prod_map_pow

theorem Hval_bounds (d : ℕ) (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hs : ∑ i, u i ≤ 1) : 0 ≤ Hval d u ∧ Hval d u ≤ (d : ℝ) + 1 := by
  unfold Hval Hpoly
  rw [map_sum]
  constructor
  · exact Finset.sum_nonneg fun j hj => (hval_bounds j u hu hs).1
  · calc
      _ ≤ ∑ j ∈ Finset.range (d + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun j hj => (hval_bounds j u hu hs).2
      _ = _ := by simp

noncomputable def mix (u a : ι → ℝ) (y : ℝ) : ι → ℝ := fun i => y * u i + (1 - y) * a i

theorem mix_nonneg (u a : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (ha : ∀ i, 0 ≤ a i)
    (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) : ∀ i, 0 ≤ mix u a y i := by
  intro i
  exact add_nonneg (mul_nonneg hy.1 (hu i)) (mul_nonneg (sub_nonneg.mpr hy.2) (ha i))

theorem mix_sum (u a : ι → ℝ) (hu : ∑ i, u i = 1) (ha : ∑ i, a i = 1) (y : ℝ) :
    ∑ i, mix u a y i = 1 := by
  simp only [mix, Finset.sum_add_distrib, ← Finset.mul_sum, hu, ha]
  ring

theorem simplex_distance_sq_le_two (u a : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (ha : ∀ i, 0 ≤ a i)
    (hsu : ∑ i, u i = 1) (hsa : ∑ i, a i = 1) :
    (∑ i, (u i - a i) ^ 2) ≤ 2 := by
  have hu1 : ∀ i, u i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun j _ => hu j) (Finset.mem_univ i)).trans_eq hsu
  have ha1 : ∀ i, a i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)).trans_eq hsa
  calc
    _ ≤ ∑ i, (u i + a i) := Finset.sum_le_sum fun i _ => by
      nlinarith [hu i, ha i, hu1 i, ha1 i, mul_nonneg (hu i) (ha i)]
    _ = 2 := by rw [Finset.sum_add_distrib, hsu, hsa]; norm_num

theorem Hval_mix_sub_sq_le (d : ℕ) (u a : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (ha : ∀ i, 0 ≤ a i)
    (hsu : ∑ i, u i = 1) (hsa : ∑ i, a i = 1)
    (y z : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    (Hval d (mix u a y) - Hval d (mix u a z)) ^ 2 ≤
      (2 * ((d : ℝ) * ((d : ℝ) - 1) / 2) ^ 2) * (y - z) ^ 2 := by
  have h := Hval_sub_sq_le d (mix u a y) (mix u a z)
    (mix_nonneg u a hu ha y hy) (mix_nonneg u a hu ha z hz)
    (mix_sum u a hsu hsa y) (mix_sum u a hsu hsa z)
  have he : (∑ i, (mix u a y i - mix u a z i) ^ 2) =
      (y - z) ^ 2 * ∑ i, (u i - a i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [mix]
    ring
  rw [he] at h
  have hb := mul_le_mul_of_nonneg_left (simplex_distance_sq_le_two u a hu ha hsu hsa)
    (sq_nonneg (y - z))
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ((d : ℝ) * ((d : ℝ) - 1) / 2))
  exact h.trans (by nlinarith [hh])

end BstLean.Part58.Kappa
