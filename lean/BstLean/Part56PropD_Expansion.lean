import BstLean.Part56PropD_Kernel

/-! The polynomial homogeneous block expansion used in Prop D. -/
namespace BstLean.Part56

open BstLean.Part41 (Mono phiM)
open BstLean.Part36 (monoVal)

variable {n : ℕ}

noncomputable def linearProduct (a w : Fin n → ℝ) (s : Multiset (Fin n)) : Polynomial ℝ :=
  (s.map fun l => Polynomial.C (a l) + Polynomial.X * Polynomial.C (w l)).prod

theorem linearProduct_degree (a w : Fin n → ℝ) (s : Multiset (Fin n)) :
    (linearProduct a w s).natDegree ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp [linearProduct]
  | @cons l s ih =>
    have hl : (Polynomial.C (a l) + Polynomial.X * Polynomial.C (w l)).natDegree ≤ 1 := by
      apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)
    simpa only [linearProduct, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
      Nat.add_comm] using Polynomial.natDegree_mul_le_of_le hl ih

theorem linearProduct_eval (a w : Fin n → ℝ) (s : Multiset (Fin n)) (r : ℝ) :
    (linearProduct a w s).eval r = monoVal (a + r • w) s := by
  simp only [linearProduct, Polynomial.eval_multiset_prod, Multiset.map_map,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
    monoVal, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_def]

theorem linearProduct_zero (a w : Fin n → ℝ) (s : Multiset (Fin n)) :
    (linearProduct a w s).coeff 0 = monoVal a s := by
  rw [Polynomial.coeff_zero_eq_eval_zero, linearProduct_eval]
  simp

theorem monoVal_smul (v : Fin n → ℝ) (s : Multiset (Fin n)) (r : ℝ) :
    monoVal (r • v) s = r ^ s.card * monoVal v s := by
  unfold monoVal
  simp only [Pi.smul_apply, smul_eq_mul, Multiset.prod_map_mul]
  congr 1
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons l s ih => simp [ih, pow_succ, mul_comm]

/-- The full block is its finite homogeneous expansion in the perpendicular radius. -/
theorem phiB_expansion (d j : ℕ) (a w : Fin n → ℝ) (r : ℝ) (p : Mono n d) :
    phiB d j (a + r • w) p =
      ∑ i ∈ Finset.range (j + 1), PhiJI d j i a w p * r ^ i := by
  classical
  by_cases hp : (p.1 : ℕ) = j
  · have hd : (linearProduct a w p.2.1).natDegree < j + 1 := by
      have h := linearProduct_degree a w p.2.1
      exact lt_of_le_of_lt (h.trans_eq (p.2.2.trans hp)) (Nat.lt_succ_self j)
    simp only [phiB, PhiJI, hp, ite_true, phiM]
    exact (linearProduct_eval a w p.2.1 r).symm.trans
      (Polynomial.eval_eq_sum_range' hd r)
  · simp [phiB, PhiJI, hp]

theorem PhiJI_zero (d j : ℕ) (a w : Fin n → ℝ) (p : Mono n d) :
    PhiJI d j 0 a w p = phiB d j a p := by
  classical
  by_cases hp : (p.1 : ℕ) = j
  · simp only [PhiJI, phiB, hp, ite_true, phiM]
    exact linearProduct_zero a w p.2.1
  · simp [PhiJI, phiB, hp]

theorem phiB_smul (d j : ℕ) (v : Fin n → ℝ) (s : ℝ) :
    phiB d j (s • v) = s ^ j • phiB d j v := by
  classical
  ext p
  by_cases hp : (p.1 : ℕ) = j
  · simp only [phiB, hp, ite_true, phiM, Pi.smul_apply, smul_eq_mul,
      monoVal_smul, p.2.2, hp]
  · simp [phiB, hp]

noncomputable def psiHat (d j : ℕ) (s r : ℝ) (v w : Fin n → ℝ) : Mono n d → ℝ :=
  ∑ i ∈ Finset.range j, r ^ i • (fun p => PhiJI d j (i + 1) (s • v) w p)

/-- Dividing the nonconstant part by the perpendicular radius leaves a polynomial. -/
theorem phiB_polar_expansion (d j : ℕ) (s r : ℝ) (v w : Fin n → ℝ) :
    phiB d j (s • v + r • w) = s ^ j • phiB d j v + r • psiHat d j s r v w := by
  classical
  ext p
  rw [phiB_expansion, Finset.sum_range_succ']
  simp only [pow_zero, mul_one, PhiJI_zero, phiB_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, psiHat, Finset.sum_apply]
  rw [add_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

section
variable {ι : Type*} [Fintype ι]

theorem projectOff_self (u : ι → ℝ) : projectOff u u = 0 := by
  classical
  by_cases hz : (∑ i, u i ^ 2) = 0
  · have hu : ∀ i, u i = 0 :=
      fun i => ((Finset.sum_sq_eq_zero_iff Finset.univ u).mp hz) i (Finset.mem_univ i)
    ext i
    simp [projectOff, hu]
  · ext i
    simp [projectOff, ← pow_two, div_self hz]

theorem projectOff_smul (u a : ι → ℝ) (c : ℝ) :
    projectOff u (c • a) = c • projectOff u a := by
  classical
  have hs : (∑ i, (c * a i) * u i) = c * ∑ i, a i * u i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  ext i
  simp only [projectOff, Pi.smul_apply, smul_eq_mul, hs, div_eq_mul_inv]
  ring

theorem projectOff_add (u a a' : ι → ℝ) :
    projectOff u (a + a') = projectOff u a + projectOff u a' := by
  ext i
  simp only [projectOff, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]
  ring

end

theorem residualB_polar (d j : ℕ) (s r : ℝ) (v w : Fin n → ℝ) :
    residualB d j v (s • v + r • w) =
      r • projectOff (phiB d j v) (psiHat d j s r v w) := by
  have he (x : Fin n → ℝ) : residualB d j v x = projectOff (phiB d j v) (phiB d j x) := by
    ext p
    simp only [residualB, projectOff, betaJ, kJ, pow_two]
  rw [he, phiB_polar_expansion, projectOff_add, projectOff_smul,
    projectOff_self, smul_zero, zero_add, projectOff_smul]

private lemma linearProduct_cons (a w : Fin n → ℝ) (l : Fin n) (s : Multiset (Fin n)) :
    linearProduct a w (l ::ₘ s) = Polynomial.C (a l) * linearProduct a w s +
      Polynomial.X * (Polynomial.C (w l) * linearProduct a w s) := by
  simp only [linearProduct, Multiset.map_cons, Multiset.prod_cons]
  ring

theorem linearProduct_coeff_zero_cons (a w : Fin n → ℝ) (l : Fin n) (s : Multiset (Fin n)) :
    (linearProduct a w (l ::ₘ s)).coeff 0 = a l * (linearProduct a w s).coeff 0 := by
  rw [linearProduct_cons]
  simp

theorem linearProduct_coeff_succ_cons (a w : Fin n → ℝ) (l : Fin n)
    (s : Multiset (Fin n)) (i : ℕ) :
    (linearProduct a w (l ::ₘ s)).coeff (i + 1) =
      a l * (linearProduct a w s).coeff (i + 1) +
        w l * (linearProduct a w s).coeff i := by
  rw [linearProduct_cons, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]

/-- A dimension-free coordinate bound for every homogeneous coefficient. -/
theorem linearProduct_coeff_bound (a w : Fin n → ℝ) (ha : ∀ l, |a l| ≤ 1)
    (hw : ∀ l, |w l| ≤ 1) (s : Multiset (Fin n)) (i : ℕ) :
    |(linearProduct a w s).coeff i| ≤ (2 : ℝ) ^ s.card := by
  induction s using Multiset.induction_on generalizing i with
  | empty =>
    simp only [linearProduct, Multiset.map_zero, Multiset.prod_zero, Polynomial.coeff_one,
      Multiset.card_zero, pow_zero]
    split_ifs <;> norm_num
  | @cons l s ih =>
    rw [Multiset.card_cons, pow_succ]
    cases i with
    | zero =>
      rw [linearProduct_coeff_zero_cons, abs_mul]
      have ht := mul_le_mul (ha l) (ih 0) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hc : 0 ≤ (2 : ℝ) ^ s.card := by positivity
      nlinarith
    | succ i =>
      rw [linearProduct_coeff_succ_cons]
      calc
        _ ≤ |a l * (linearProduct a w s).coeff (i + 1)| +
          |w l * (linearProduct a w s).coeff i| := abs_add_le _ _
        _ ≤ 1 * (2 : ℝ) ^ s.card + 1 * (2 : ℝ) ^ s.card := by
          simp only [abs_mul]
          exact add_le_add
            (mul_le_mul (ha l) (ih (i + 1)) (abs_nonneg _) (by norm_num))
            (mul_le_mul (hw l) (ih i) (abs_nonneg _) (by norm_num))
        _ = _ := by ring

theorem continuous_linearProduct_coeff (s : Multiset (Fin n)) (i : ℕ) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (linearProduct p.1 p.2 s).coeff i) := by
  induction s using Multiset.induction_on generalizing i with
  | empty => simpa only [linearProduct, Multiset.map_zero, Multiset.prod_zero] using
      (continuous_const : Continuous (fun _ : (Fin n → ℝ) × (Fin n → ℝ) =>
        (1 : Polynomial ℝ).coeff i))
  | @cons l s ih =>
    cases i with
    | zero =>
      simp_rw [linearProduct_coeff_zero_cons]
      exact ((continuous_apply l).comp continuous_fst).mul (ih 0)
    | succ i =>
      simp_rw [linearProduct_coeff_succ_cons]
      exact (((continuous_apply l).comp continuous_fst).mul (ih (i + 1))).add
        (((continuous_apply l).comp continuous_snd).mul (ih i))

theorem psiHat_dot_expansion (d j : ℕ) (s r s' r' : ℝ) (v w w' : Fin n → ℝ) :
    (∑ p : Mono n d, psiHat d j s r v w p * psiHat d j s' r' v w' p) =
      ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j,
        (r ^ i * r' ^ i') * ∑ p : Mono n d,
          PhiJI d j (i + 1) (s • v) w p * PhiJI d j (i' + 1) (s' • v) w' p := by
  classical
  simp only [psiHat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem psiHat_dot_sq_le (d j : ℕ) (s r s' r' : ℝ) (v w w' : Fin n → ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr'0 : 0 ≤ r') (hr'1 : r' ≤ 1) :
    (∑ p : Mono n d, psiHat d j s r v w p * psiHat d j s' r' v w' p) ^ 2 ≤
      (j : ℝ) ^ 2 * ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j,
        (∑ p : Mono n d, PhiJI d j (i + 1) (s • v) w p *
          PhiJI d j (i' + 1) (s' • v) w' p) ^ 2 := by
  classical
  let S := (Finset.range j).product (Finset.range j)
  let Q (q : ℕ × ℕ) := ∑ p : Mono n d,
    PhiJI d j (q.1 + 1) (s • v) w p * PhiJI d j (q.2 + 1) (s' • v) w' p
  let L (q : ℕ × ℕ) := r ^ q.1 * r' ^ q.2
  have hL : ∀ q ∈ S, L q ^ 2 ≤ 1 := by
    intro q _
    have h0 : 0 ≤ L q := mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hr'0 _)
    have h1 : L q ≤ 1 := (mul_le_mul (pow_le_one₀ hr0 hr1) (pow_le_one₀ hr'0 hr'1)
      (pow_nonneg hr'0 _) (by norm_num)).trans_eq (one_mul _)
    exact pow_le_one₀ h0 h1
  have hs : (∑ q ∈ S, L q ^ 2) ≤ (j : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _q ∈ S, (1 : ℝ) := Finset.sum_le_sum hL
      _ = _ := by simp [S, Finset.card_product, pow_two]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S L Q
  have ht := hc.trans (mul_le_mul_of_nonneg_right hs
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  rw [psiHat_dot_expansion]
  have he : (∑ q ∈ S, L q * Q q) =
      ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, (r ^ i * r' ^ i') * Q (i, i') :=
    Finset.sum_product' _ _ (fun i i' => (r ^ i * r' ^ i') * Q (i, i'))
  have he' : (∑ q ∈ S, Q q ^ 2) =
      ∑ i ∈ Finset.range j, ∑ i' ∈ Finset.range j, Q (i, i') ^ 2 :=
    Finset.sum_product' _ _ (fun i i' => Q (i, i') ^ 2)
  simpa only [he, he', Q] using ht

end BstLean.Part56
