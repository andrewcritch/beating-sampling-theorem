import BstLean.Part81F3Row

/-!
# Part 81 (F3): the sharp feature operator bound at map degree 3

`featOp3 : FeatOp n 3 (1 + 3/(n+2))`, that is
`E (c·p(x))² ≤ (1 + 3/(n+2))/n · ‖c‖²` for the non-constant raw monomials of degree `≤ 3` under
the uniform distribution on the sphere.

Proof. Split `P = P₁ + P₂ + P₃` by degree. Parity gives `E P₂P₁ = E P₂P₃ = 0`. The Schur test
on each degree block gives `E P₁² ≤ ‖c₁‖²/n`, `E P₂² ≤ ‖c₂‖²/n`, `E P₃² ≤ 3‖c₃‖²/(n(n+2))`.
With `θ = 3/(n+2)`: `(P₁+P₃)² ≤ (1+θ)P₁² + (1+1/θ)P₃²`, and `(1+1/θ)·3/(n(n+2)) = (1+θ)/n`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part81.F3

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM)

variable {n d : ℕ}

/-! ## Pointwise bounds for `|x^p| · oddP_p(x)` on the sphere -/

lemma abs_le_one_of_sphere {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (j : Fin n) : |x j| ≤ 1 := by
  have := Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  rw [hx] at this
  exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)

lemma prod_le_one_factor (f : Fin n → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) (i : Fin n) :
    ∏ j, f j ≤ f i := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i, f j ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (hf j).1) (fun j _ => (hf j).2)
  have h0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j := Finset.prod_nonneg fun j _ => (hf j).1
  nlinarith [(hf i).1]

lemma prod_le_two_factor (f : Fin n → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) (i k : Fin n)
    (hik : i ≠ k) : ∏ j, f j ≤ f i * f k := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _
      (Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ k⟩)]
  have h1 : ∏ j ∈ (Finset.univ.erase i).erase k, f j ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (hf j).1) (fun j _ => (hf j).2)
  have h0 : 0 ≤ f i * f k := mul_nonneg (hf i).1 (hf k).1
  calc f i * (f k * ∏ j ∈ (Finset.univ.erase i).erase k, f j)
      = (f i * f k) * ∏ j ∈ (Finset.univ.erase i).erase k, f j := by ring
    _ ≤ (f i * f k) * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = f i * f k := mul_one _

/-- `|x^u| · oddP_u(x) = ∏ |x_j|^{c_j + c_j mod 2}`. -/
lemma prod_form (u : Multiset (Fin n)) (x : Fin n → ℝ) :
    |monoVal x u| * oddP u x = ∏ j, |x j| ^ (u.count j + u.count j % 2) := by
  classical
  unfold monoVal oddP
  rw [prodMapUniv, Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro j _
  rw [abs_pow, pow_add]

lemma fac_bounds {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (u : Multiset (Fin n)) (j : Fin n) :
    0 ≤ |x j| ^ (u.count j + u.count j % 2) ∧ |x j| ^ (u.count j + u.count j % 2) ≤ 1 :=
  ⟨pow_nonneg (abs_nonneg _) _, pow_le_one₀ (abs_nonneg _) (abs_le_one_of_sphere hx j)⟩

lemma fac_le_sq {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (u : Multiset (Fin n)) (i : Fin n)
    (hi : i ∈ u) : |x i| ^ (u.count i + u.count i % 2) ≤ x i ^ 2 := by
  classical
  have h1 := Multiset.count_pos.mpr hi
  calc |x i| ^ (u.count i + u.count i % 2) ≤ |x i| ^ 2 :=
        pow_le_pow_of_le_one (abs_nonneg _) (abs_le_one_of_sphere hx i) (by omega)
    _ = x i ^ 2 := sq_abs _

lemma pt_one {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (u : Multiset (Fin n)) (i : Fin n)
    (hi : i ∈ u) : |monoVal x u| * oddP u x ≤ x i ^ 2 := by
  rw [prod_form]
  exact (prod_le_one_factor _ (fac_bounds hx u) i).trans (fac_le_sq hx u i hi)

lemma pt_two {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (u : Multiset (Fin n)) (i k : Fin n)
    (hik : i ≠ k) (hi : i ∈ u) (hk : k ∈ u) :
    |monoVal x u| * oddP u x ≤ x i ^ 2 * x k ^ 2 := by
  rw [prod_form]
  exact (prod_le_two_factor _ (fac_bounds hx u) i k hik).trans
    (mul_le_mul (fac_le_sq hx u i hi) (fac_le_sq hx u k hk) (fac_bounds hx u k).1 (sq_nonneg _))

lemma pt_four {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) (u : Multiset (Fin n)) (i : Fin n)
    (hi : 3 ≤ u.count i) : |monoVal x u| * oddP u x ≤ x i ^ 2 * x i ^ 2 := by
  rw [prod_form]
  refine (prod_le_one_factor _ (fac_bounds hx u) i).trans ?_
  calc |x i| ^ (u.count i + u.count i % 2) ≤ |x i| ^ 4 :=
        pow_le_pow_of_le_one (abs_nonneg _) (abs_le_one_of_sphere hx i) (by omega)
    _ = x i ^ 2 * x i ^ 2 := by rw [← sq_abs (x i)]; ring

/-! ## Moments -/

lemma int_sq (hn : 1 ≤ n) (i : Fin n) : ∫ x, x i ^ 2 ∂uniformSphere n = 1 / (n : ℝ) := by
  have h := (BstLean.Part29.uniformSphere_moments n hn).m2 i i
  simp only [ite_true] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

lemma int_sq_sq (hn : 1 ≤ n) (i k : Fin n) :
    ∫ x, x i ^ 2 * x k ^ 2 ∂uniformSphere n ≤ 3 / ((n : ℝ) * (n + 2)) := by
  have h := (BstLean.Part29.uniformSphere_moments n hn).m4 i i k k
  have e : ∫ x, x i ^ 2 * x k ^ 2 ∂uniformSphere n =
      ∫ x : Fin n → ℝ, x i * x i * x k * x k ∂uniformSphere n :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [e, h]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

/-! ## Row sums of the three degree blocks -/

lemma exists_mem_of_deg (p : Mono n d) (h : 1 ≤ (p.1 : ℕ)) : ∃ i, i ∈ p.2.1 := by
  apply Multiset.card_pos_iff_exists_mem.mp
  have e : Multiset.card p.2.1 = p.1 := p.2.2
  omega

/-- Row sums over a block of positive degree are at most `1/n`. -/
lemma row_pos (hn : 1 ≤ n) (p : Mono n d) (h : 1 ≤ (p.1 : ℕ)) :
    ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => q.1 = p.1), Mpq p q ≤
      1 / (n : ℝ) := by
  obtain ⟨i, hi⟩ := exists_mem_of_deg p h
  rw [← int_sq hn i]
  exact row_bound hn p (fun x => x i ^ 2)
    (BstLean.Part78.sphere_cont_integrable78 hn (by fun_prop)) (fun x hx => pt_one hx _ i hi)

/-- Row sums over the cubic block are at most `3/(n(n+2))`. -/
lemma row_three (hn : 1 ≤ n) (p : Mono n d) (h : (p.1 : ℕ) = 3) :
    ∑ q ∈ (Finset.univ : Finset (Mono n d)).filter (fun q => q.1 = p.1), Mpq p q ≤
      3 / ((n : ℝ) * (n + 2)) := by
  classical
  have hcard : Multiset.card p.2.1 = 3 := by rw [p.2.2]; exact h
  have key : ∃ i k : Fin n, ∀ x : Fin n → ℝ, ∑ j, x j ^ 2 = 1 →
      |monoVal x p.2.1| * oddP p.2.1 x ≤ x i ^ 2 * x k ^ 2 := by
    by_cases hd : ∃ i k : Fin n, i ≠ k ∧ i ∈ p.2.1 ∧ k ∈ p.2.1
    · obtain ⟨i, k, hik, hi, hk⟩ := hd
      exact ⟨i, k, fun x hx => pt_two hx _ i k hik hi hk⟩
    · push Not at hd
      obtain ⟨i, hi⟩ := exists_mem_of_deg p (by omega)
      have hrep : p.2.1 = Multiset.replicate 3 i := by
        rw [Multiset.eq_replicate]
        refine ⟨hcard, fun b hb => ?_⟩
        by_contra hne
        exact hd b i hne hb hi
      refine ⟨i, i, fun x hx => pt_four hx _ i ?_⟩
      rw [hrep, Multiset.count_replicate_self]
  obtain ⟨i, k, hik⟩ := key
  refine (row_bound hn p (fun x => x i ^ 2 * x k ^ 2)
    (BstLean.Part78.sphere_cont_integrable78 hn (by fun_prop)) hik).trans (int_sq_sq hn i k)

/-! ## The degree split at `d = 3` -/

lemma deg_cases (p : Mono n 3) : p = default ∨ p.1 = 1 ∨ p.1 = 2 ∨ p.1 = 3 := by
  by_cases h0 : (p.1 : ℕ) = 0
  · left
    apply mono_ext
    have e : Multiset.card p.2.1 = 0 := by rw [p.2.2]; exact h0
    exact (Multiset.card_eq_zero.mp e).trans rfl
  · right
    have h4 := p.1.2
    have : (p.1 : ℕ) = 1 ∨ (p.1 : ℕ) = 2 ∨ (p.1 : ℕ) = 3 := by omega
    rcases this with h | h | h
    · left; exact Fin.ext h
    · right; left; exact Fin.ext h
    · right; right; exact Fin.ext h

lemma part_split (a : Mono n 3 → ℝ) (ha0 : a default = 0) (p : Mono n 3) :
    a p = part 1 a p + part 2 a p + part 3 a p ∧
      a p ^ 2 = part 1 a p ^ 2 + part 2 a p ^ 2 + part 3 a p ^ 2 := by
  have hd : (default : Mono n 3).1 = 0 := rfl
  rcases deg_cases p with h | h | h | h
  · subst h; simp [part, hd, ha0]
  · simp [part, h]
  · simp [part, h]
  · simp [part, h]

/-- **The sharp bound at degree 3**, for coefficient vectors on `Mono n 3` that vanish at the
constant monomial. -/
theorem bound3 (hn : 1 ≤ n) (a : Mono n 3 → ℝ) (ha0 : a default = 0) :
    ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂uniformSphere n ≤
      (1 + 3 / ((n : ℝ) + 2)) / (n : ℝ) * ∑ p, a p ^ 2 := by
  classical
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set P : Fin 4 → (Fin n → ℝ) → ℝ := fun j x => ∑ p, part j a p * phiM x p with hPdef
  have hP : ∀ x, ∑ p, a p * phiM x p = P 1 x + P 2 x + P 3 x := by
    intro x
    simp only [hPdef]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p _
    conv_lhs => rw [(part_split a ha0 p).1]
    ring
  have hS : ∑ p, a p ^ 2 =
      ∑ p, part 1 a p ^ 2 + ∑ p, part 2 a p ^ 2 + ∑ p, part 3 a p ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => (part_split a ha0 p).2
  have hsupp : ∀ j : Fin 4, ∀ p : Mono n 3, p.1 ≠ j → part j a p = 0 := by
    intro j p hp; simp [part, hp]
  -- the three diagonal blocks
  have b1 : ∫ x, P 1 x * P 1 x ∂uniformSphere n ≤ 1 / (n : ℝ) * ∑ p, part 1 a p ^ 2 :=
    schur_deg hn 1 _ (fun p hp => row_pos hn p (by rw [hp]; decide)) _ (hsupp 1)
  have b2 : ∫ x, P 2 x * P 2 x ∂uniformSphere n ≤ 1 / (n : ℝ) * ∑ p, part 2 a p ^ 2 :=
    schur_deg hn 2 _ (fun p hp => row_pos hn p (by rw [hp]; decide)) _ (hsupp 2)
  have b3 : ∫ x, P 3 x * P 3 x ∂uniformSphere n ≤
      3 / ((n : ℝ) * (n + 2)) * ∑ p, part 3 a p ^ 2 :=
    schur_deg hn 3 _ (fun p hp => row_three hn p (by rw [hp]; rfl)) _ (hsupp 3)
  -- parity
  have c12 : ∫ x, P 1 x * P 2 x ∂uniformSphere n = 0 := cross_zero hn 1 2 (by decide) a a
  have c32 : ∫ x, P 3 x * P 2 x ∂uniformSphere n = 0 := cross_zero hn 3 2 (by decide) a a
  have i11 : Integrable (fun x => P 1 x * P 1 x) (uniformSphere n) := (int_pair hn _ _).1
  have i22 : Integrable (fun x => P 2 x * P 2 x) (uniformSphere n) := (int_pair hn _ _).1
  have i33 : Integrable (fun x => P 3 x * P 3 x) (uniformSphere n) := (int_pair hn _ _).1
  have i12 : Integrable (fun x => P 1 x * P 2 x) (uniformSphere n) := (int_pair hn _ _).1
  have i32 : Integrable (fun x => P 3 x * P 2 x) (uniformSphere n) := (int_pair hn _ _).1
  set θ : ℝ := 3 / ((n : ℝ) + 2) with hθ
  set ι : ℝ := ((n : ℝ) + 2) / 3 with hι
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hι0 : 0 < ι := by rw [hι]; positivity
  have hθι : θ * ι = 1 := by rw [hθ, hι]; field_simp
  have hpt : ∀ x, (P 1 x + P 2 x + P 3 x) ^ 2 ≤
      (1 + θ) * (P 1 x * P 1 x) + (1 + ι) * (P 3 x * P 3 x) + 2 * (P 1 x * P 2 x) +
        2 * (P 3 x * P 2 x) + P 2 x * P 2 x := by
    intro x
    have h1 : 0 ≤ (θ * P 1 x - P 3 x) ^ 2 * ι := mul_nonneg (sq_nonneg _) hι0.le
    have h2 : (θ * P 1 x - P 3 x) ^ 2 * ι =
        θ * (P 1 x * P 1 x) * (θ * ι) - 2 * (P 1 x * P 3 x) * (θ * ι) + ι * (P 3 x * P 3 x) := by
      ring
    rw [hθι] at h2
    nlinarith [h1, h2]
  have iA := (i11.const_mul (1 + θ)).add (i33.const_mul (1 + ι))
  have iB := iA.add (i12.const_mul 2)
  have iC := iB.add (i32.const_mul 2)
  have iD := iC.add i22
  have hint0 : Integrable (fun x => (P 1 x + P 2 x + P 3 x) ^ 2) (uniformSphere n) := by
    have e : (fun x => (P 1 x + P 2 x + P 3 x) ^ 2) =
        fun x => (∑ p, a p * phiM x p) * (∑ q, a q * phiM x q) := by
      funext x; rw [hP]; ring
    rw [e]; exact (int_pair hn a a).1
  simp_rw [hP]
  have hmono := integral_mono hint0 iD hpt
  have hval : ∫ x, ((1 + θ) * (P 1 x * P 1 x) + (1 + ι) * (P 3 x * P 3 x) + 2 * (P 1 x * P 2 x) +
        2 * (P 3 x * P 2 x) + P 2 x * P 2 x) ∂uniformSphere n =
      (1 + θ) * ∫ x, P 1 x * P 1 x ∂uniformSphere n +
        (1 + ι) * ∫ x, P 3 x * P 3 x ∂uniformSphere n +
        ∫ x, P 2 x * P 2 x ∂uniformSphere n := by
    have e1 := integral_add iC i22
    have e2 := integral_add iB (i32.const_mul 2)
    have e3 := integral_add iA (i12.const_mul 2)
    have e4 := integral_add (i11.const_mul (1 + θ)) (i33.const_mul (1 + ι))
    simp only [Pi.add_apply] at e1 e2 e3 e4
    rw [e1, e2, e3, e4]
    simp only [integral_const_mul]
    rw [c12, c32]; ring
  simp only [Pi.add_apply] at hmono
  rw [hval] at hmono
  refine hmono.trans ?_
  rw [hS]
  set S1 := ∑ p, part 1 a p ^ 2
  set S2 := ∑ p, part 2 a p ^ 2
  set S3 := ∑ p, part 3 a p ^ 2
  have hS1 : 0 ≤ S1 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS3 : 0 ≤ S3 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have t1 : (1 + θ) * ∫ x, P 1 x * P 1 x ∂uniformSphere n ≤ (1 + θ) * (1 / (n : ℝ) * S1) :=
    mul_le_mul_of_nonneg_left b1 (by linarith)
  have t3 : (1 + ι) * ∫ x, P 3 x * P 3 x ∂uniformSphere n ≤
      (1 + ι) * (3 / ((n : ℝ) * (n + 2)) * S3) :=
    mul_le_mul_of_nonneg_left b3 (by linarith)
  have e3 : (1 + ι) * (3 / ((n : ℝ) * (n + 2)) * S3) = (1 + θ) / (n : ℝ) * S3 := by
    rw [hθ, hι]; field_simp; ring
  have t2 : 1 / (n : ℝ) * S2 ≤ (1 + θ) / (n : ℝ) * S2 := by
    apply mul_le_mul_of_nonneg_right _ hS2
    apply div_le_div_of_nonneg_right _ hn0.le
    linarith
  have e1 : (1 + θ) * (1 / (n : ℝ) * S1) = (1 + θ) / (n : ℝ) * S1 := by ring
  have e5 : (1 + θ) / (n : ℝ) * (S1 + S2 + S3) =
      (1 + θ) / (n : ℝ) * S1 + (1 + θ) / (n : ℝ) * S2 + (1 + θ) / (n : ℝ) * S3 := by ring
  rw [e5]
  linarith

end BstLean.Part81.F3

namespace BstLean.Part81

/-- **(A) The sharp feature operator bound at map degree 3**:
`E (c·p(x))² ≤ (1 + 3/(n+2))/n · ‖c‖²`. -/
theorem featOp3 (n : ℕ) (hn : 1 ≤ n) : FeatOp n 3 (1 + 3 / ((n : ℝ) + 2)) :=
  F3.featOp_of_mono _ fun a ha0 => F3.bound3 hn a ha0

/-- **(B)** The bound with constant `2` (from (A), `3/(n+2) ≤ 1`). -/
theorem featOp3_two (n : ℕ) (hn : 1 ≤ n) : FeatOp n 3 2 := by
  intro c
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine (featOp3 n hn c).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 3 / ((n : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  linarith

end BstLean.Part81

#print axioms BstLean.Part81.featOp3
#print axioms BstLean.Part81.featOp3_two
#print axioms BstLean.Part81.featOpGen
