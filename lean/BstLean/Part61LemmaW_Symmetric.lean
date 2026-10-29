import BstLean.Part61Defs
import BstLean.Part58Kappa_Symmetric

/-! Signed complete homogeneous polynomials on the unit ℓ¹ ball.
The derivative recurrence separates a coordinate-independent term. This term vanishes
along directions with coordinate sum zero. Euler's identity gives the factorial lower bound.
-/

namespace BstLean.Part61.W
open MvPolynomial BstLean.Part58.Kappa
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hval_abs_bound (j : ℕ) (u : ι → ℝ) (hu : ∑ i, |u i| ≤ 1) :
    |hval j u| ≤ 1 := by
  rw [hval_eq]
  calc
    _ ≤ ∑ s : Sym ι j, |(s.val.map u).prod| := Finset.abs_sum_le_sum_abs _ _
    _ = hval j (fun i => |u i|) := by
      rw [hval_eq]
      apply Finset.sum_congr rfl
      intro s hs
      induction s.val using Multiset.induction_on with
      | empty => simp
      | @cons a s ih => simp only [Multiset.map_cons, Multiset.prod_cons, abs_mul, ih]
    _ ≤ 1 := (hval_bounds j _ (fun i => abs_nonneg _) hu).2

lemma pderiv_abs_bound (j : ℕ) (u : ι → ℝ) (hu : ∑ i, |u i| ≤ 1) (i : ι) :
    |eval u (pderiv i (hsymm ι ℝ j))| ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pderiv_hsymm_succ]
    simp only [map_add, map_mul, eval_X, Nat.cast_add, Nat.cast_one]
    have hui : |u i| ≤ 1 := (Finset.single_le_sum (fun l _ => abs_nonneg (u l))
      (Finset.mem_univ i)).trans hu
    calc
      _ ≤ |hval j u| + |u i| * |eval u (pderiv i (hsymm ι ℝ j))| := by
        simpa only [hval, abs_mul] using abs_add_le (eval u (hsymm ι ℝ j))
          (u i * eval u (pderiv i (hsymm ι ℝ j)))
      _ ≤ 1 + 1 * j := add_le_add (hval_abs_bound j u hu)
        (mul_le_mul hui ih (abs_nonneg _) zero_le_one)
      _ = _ := by ring

lemma deriv_centered_bound (j : ℕ) (u w : ι → ℝ) (hu : ∑ i, |u i| ≤ 1)
    (hw : ∑ i, w i = 0) :
    (∑ i, eval u (pderiv i (hsymm ι ℝ j)) * w i) ^ 2 ≤
      (j : ℝ) ^ 2 * ∑ i, w i ^ 2 := by
  cases j with
  | zero => simp
  | succ j =>
    let a : ι → ℝ := fun i => u i * eval u (pderiv i (hsymm ι ℝ j))
    have ha : ∀ i, |a i| ≤ |u i| * j := fun i => by
      dsimp [a]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (pderiv_abs_bound j u hu i) (abs_nonneg _)
    have hs2 : (∑ i, u i ^ 2) ≤ 1 := by
      have hi : ∀ i, |u i| ≤ 1 := fun i =>
        (Finset.single_le_sum (fun l _ => abs_nonneg (u l)) (Finset.mem_univ i)).trans hu
      exact (Finset.sum_le_sum (fun i _ => by nlinarith [sq_abs (u i), abs_nonneg (u i), hi i])).trans hu
    have ha2 : (∑ i, a i ^ 2) ≤ (j : ℝ) ^ 2 := by
      calc
        _ ≤ ∑ i, (|u i| * j) ^ 2 := Finset.sum_le_sum fun i _ => by
          have h := pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2
          simpa only [sq_abs] using h
        _ = (j : ℝ) ^ 2 * ∑ i, u i ^ 2 := by
          simp only [mul_pow, sq_abs, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ (j : ℝ) ^ 2 := by simpa using mul_le_mul_of_nonneg_left hs2 (sq_nonneg (j : ℝ))
    have he : (∑ i, eval u (pderiv i (hsymm ι ℝ (j + 1))) * w i) = ∑ i, a i * w i := by
      simp only [pderiv_hsymm_succ, map_add, map_mul, eval_X, add_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, hw, mul_zero, zero_add, a]
    rw [he]
    refine (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a w).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    exact ha2.trans (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) j])

lemma hval_sub_sq_bound (j : ℕ) (u z : ι → ℝ)
    (hu : ∑ i, |u i| ≤ 1) (hz : ∑ i, |z i| ≤ 1)
    (hs : ∑ i, u i = ∑ i, z i) :
    (hval j u - hval j z) ^ 2 ≤ (j : ℝ) ^ 2 * ∑ i, (u i - z i) ^ 2 := by
  let U : ℝ → ι → ℝ := fun t i => z i + t * (u i - z i)
  let V : ℝ → ℝ := fun t => hval j (U t)
  let D : ℝ → ℝ := fun t => ∑ i, eval (U t) (pderiv i (hsymm ι ℝ j)) * (u i - z i)
  let C : ℝ := Real.sqrt ((j : ℝ) ^ 2 * ∑ i, (u i - z i) ^ 2)
  have hC : C ^ 2 = (j : ℝ) ^ 2 * ∑ i, (u i - z i) ^ 2 := Real.sq_sqrt (by positivity)
  have hd : ∀ t, HasDerivAt V (D t) t := by
    intro t
    apply eval_hasDerivAt
    intro i
    convert (hasDerivAt_const t (z i)).add
      ((hasDerivAt_id t).mul_const (u i - z i)) using 1 <;> simp [U, Pi.add_def]
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t‖ ≤ C := by
    intro t ht
    have hU : ∑ i, |U t i| ≤ 1 := by
      calc
        _ ≤ ∑ i, ((1-t) * |z i| + t * |u i|) := Finset.sum_le_sum fun i _ => by
          have he : U t i = (1-t) * z i + t * u i := by dsimp [U]; ring
          rw [he]
          simpa only [abs_mul, abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2)]
            using abs_add_le ((1-t)*z i) (t*u i)
        _ = (1-t) * ∑ i, |z i| + t * ∑ i, |u i| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ (1-t) * 1 + t * 1 := add_le_add
          (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left hu ht.1)
        _ = 1 := by ring
    have hw : (∑ i, (u i - z i)) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
    have h := deriv_centered_bound j (U t) (fun i => u i - z i) hU hw
    change D t ^ 2 ≤ _ at h
    rw [← hC] at h
    rw [Real.norm_eq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by simpa only [sq_abs] using h)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
  have hV0 : V 0 = hval j z := by simp [V, U]
  have hV1 : V 1 = hval j u := by simp [V, U]
  rw [hV0, hV1] at h
  norm_num only [sub_zero, norm_one, mul_one, Real.norm_eq_abs] at h
  have hh := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr h
  rw [sq_abs] at hh
  exact hh.trans_eq hC

lemma hval_smul (j : ℕ) (u : ι → ℝ) (s : ℝ) :
    hval j (s • u) = s ^ j * hval j u := by
  rw [hval_eq, hval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hm (m : Multiset ι) : (m.map (s • u)).prod = s ^ m.card * (m.map u).prod := by
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons i m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.map_cons,
        Multiset.prod_cons, Multiset.card_cons, pow_succ]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  rw [hm, a.property]

lemma hval_euler (j : ℕ) (u : ι → ℝ) :
    (∑ i, u i * eval u (pderiv i (hsymm ι ℝ j))) = (j : ℝ) * hval j u := by
  have hp : (∑ i : ι, X i * pderiv i (hsymm ι ℝ j)) = (j : ℝ) • hsymm ι ℝ j := by
    simp only [hsymm, map_sum, Finset.mul_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    change (∑ i, X i * pderiv i (mon s.val)) = (j : ℝ) • mon s.val
    simp_rw [X_mul_pderiv_mon]
    rw [← Finset.sum_smul, ← Nat.cast_sum]
    congr 1
    exact_mod_cast (Multiset.sum_count_eq_card (fun a ha => Finset.mem_univ a)).trans s.property
  have he := congrArg (eval u) hp
  simpa only [map_sum, map_mul, eval_X, smul_eq_C_mul, eval_C, hval] using he

lemma hval_lower (j : ℕ) (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    1 ≤ (j.factorial : ℝ) * hval j u := by
  induction j with
  | zero => simp [hval]
  | succ j ih =>
    have hd : ∀ i, hval j u ≤ eval u (pderiv i (hsymm ι ℝ (j+1))) := by
      intro i
      rw [pderiv_hsymm_succ]
      simp only [map_add, map_mul, eval_X]
      exact le_add_of_nonneg_right (mul_nonneg (hu i) (pderiv_hval_bounds j u hu hs.le i).1)
    have hh : hval j u ≤ (j+1 : ℕ) * hval (j+1) u := by
      calc
        _ = ∑ i, u i * hval j u := by rw [← Finset.sum_mul, hs, one_mul]
        _ ≤ ∑ i, u i * eval u (pderiv i (hsymm ι ℝ (j+1))) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hd i) (hu i)
        _ = _ := hval_euler (j+1) u
    have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) j.factorial)
    calc
      1 ≤ (j.factorial : ℝ) * hval j u := ih
      _ ≤ (j.factorial : ℝ) * ((j+1 : ℕ) * hval (j+1) u) := hm
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul]; ring

end BstLean.Part61.W
