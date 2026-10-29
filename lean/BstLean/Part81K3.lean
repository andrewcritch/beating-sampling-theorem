import BstLean.Part81Defs
import BstLean.Part78Sphere
import BstLean.Part78Mean

/-!
# Part 81, map degree 3: explicit sphere constants of the kernel
-/

namespace BstLean.Part81.K3

open MeasureTheory
open BstLean.Part29 (uniformSphere gaussMom)
open BstLean.Part36 (monoVal gpm rhoD)
open BstLean.Part41 (Mono phiM)
open BstLean.Part81

variable {n : ℕ}

/-! ## Sums over `Sym (Fin n) (k+1)` -/

lemma sum_sym_succ {k : ℕ} (G : Sym (Fin n) (k + 1) → ℝ) :
    ((k : ℝ) + 1) * ∑ s, G s
      = ∑ a, ∑ t : Sym (Fin n) k, ((t.1.count a : ℝ) + 1) * G (a ::ₛ t) := by
  classical
  have h1 : ∀ s : Sym (Fin n) (k + 1), ((k : ℝ) + 1) = ∑ a, (s.1.count a : ℝ) := by
    intro s
    have := Multiset.sum_count_eq_card (s := Finset.univ) (m := s.1) (fun a _ => Finset.mem_univ a)
    rw [← Nat.cast_sum, this, s.2]; push_cast; ring
  rw [Finset.mul_sum]
  have h2 : ∑ s, ((k : ℝ) + 1) * G s = ∑ s, ∑ a, (s.1.count a : ℝ) * G s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [h1 s, Finset.sum_mul]
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h3 : ∑ s : Sym (Fin n) (k + 1), (s.1.count a : ℝ) * G s
      = ∑ s ∈ Finset.univ.filter (fun s : Sym (Fin n) (k + 1) => a ∈ s),
          (s.1.count a : ℝ) * G s := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · rfl
    · have : s.1.count a = 0 := Multiset.count_eq_zero_of_notMem h
      rw [this]; simp
  rw [h3]
  refine Finset.sum_bij' (fun s hs => s.erase a (Finset.mem_filter.mp hs).2)
    (fun t _ => a ::ₛ t) ?_ ?_ ?_ ?_ ?_
  · intro s _; exact Finset.mem_univ _
  · intro t _; simp
  · intro s hs; exact Sym.cons_erase _
  · intro t _; exact Sym.erase_cons_head _ _ _
  · intro s hs
    have hm : a ∈ s := (Finset.mem_filter.mp hs).2
    have e : a ::ₛ s.erase a hm = s := Sym.cons_erase hm
    have e2 : s.1.count a = (s.erase a hm).1.count a + 1 := by
      conv_lhs => rw [← e]
      show Multiset.count a (a ::ₘ (s.erase a hm).1) = _
      simp
    simp only [e, e2]
    push_cast; ring

lemma sum_sym_three (w : Fin n → ℝ) :
    ∑ β : Sym (Fin n) 3, (β.1.map w).prod
      = ((∑ i, w i) ^ 3 + 3 * (∑ i, w i) * (∑ i, w i ^ 2) + 2 * ∑ i, w i ^ 3) / 6 := by
  classical
  have h3 := sum_sym_succ (k := 2) (fun β : Sym (Fin n) 3 => (β.1.map w).prod)
  have h2 : ∀ a : Fin n, 2 * ∑ t : Sym (Fin n) 2, ((t.1.count a : ℝ) + 1) * (w a * (t.1.map w).prod)
      = ∑ b, ∑ u : Sym (Fin n) 1, ((u.1.count b : ℝ) + 1) *
          ((((b ::ₛ u).1.count a : ℝ) + 1) * (w a * ((b ::ₛ u).1.map w).prod)) := by
    intro a
    have := sum_sym_succ (k := 1)
      (fun t : Sym (Fin n) 2 => ((t.1.count a : ℝ) + 1) * (w a * (t.1.map w).prod))
    norm_num at this
    exact this
  have h1 : ∀ (F : Sym (Fin n) 1 → ℝ), ∑ u, F u = ∑ c, F (c ::ₛ Sym.nil) := by
    intro F
    have := sum_sym_succ (k := 0) F
    simp only [Fintype.sum_unique] at this
    simpa [Sym.eq_nil_of_card_zero] using this
  have hc : ∀ (a : Fin n) (t : Sym (Fin n) 2),
      ((a ::ₛ t).1.map w).prod = w a * (t.1.map w).prod := by
    intro a t
    show ((a ::ₘ t.1).map w).prod = _
    simp
  simp only [hc] at h3
  push_cast at h3
  have h6 : 6 * ∑ β : Sym (Fin n) 3, (β.1.map w).prod
      = ∑ a, ∑ b, ∑ c, ((if c = b then (1:ℝ) else 0) + 1) *
          (((if b = a then (1:ℝ) else 0) + (if c = a then (1:ℝ) else 0) + 1) *
            (w a * (w b * w c))) := by
    have : 6 * ∑ β : Sym (Fin n) 3, (β.1.map w).prod
        = 2 * (((2:ℝ) + 1) * ∑ β : Sym (Fin n) 3, (β.1.map w).prod) := by ring
    rw [this, h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h2 a]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 : (c ::ₛ (Sym.nil : Sym (Fin n) 0)).1 = {c} := rfl
    have e2 : (b ::ₛ c ::ₛ (Sym.nil : Sym (Fin n) 0)).1 = b ::ₘ {c} := rfl
    rw [e2, e1]
    simp [Multiset.count_cons, Multiset.count_singleton]
    simp only [@eq_comm _ b c, @eq_comm _ a c, @eq_comm _ a b]
    ring
  have p1 : (∑ i, w i) ^ 3 = ∑ a, ∑ b, ∑ c, w a * (w b * w c) := by
    rw [pow_succ, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have p2 : (∑ i, w i) * (∑ i, w i ^ 2) = ∑ a, ∑ b, w a * w b ^ 2 := Finset.sum_mul_sum _ _ _ _
  have key : ∑ a, ∑ b, ∑ c, ((if c = b then (1:ℝ) else 0) + 1) *
          (((if b = a then (1:ℝ) else 0) + (if c = a then (1:ℝ) else 0) + 1) *
            (w a * (w b * w c)))
      = (∑ i, w i) ^ 3 + 3 * (∑ i, w i) * (∑ i, w i ^ 2) + 2 * ∑ i, w i ^ 3 := by
    have e : ∀ a b c : Fin n, ((if c = b then (1:ℝ) else 0) + 1) *
          (((if b = a then (1:ℝ) else 0) + (if c = a then (1:ℝ) else 0) + 1) *
            (w a * (w b * w c)))
        = w a * (w b * w c) + (if c = b then w a * w b ^ 2 else 0)
          + (if b = a then w a ^ 2 * w c else 0) + (if c = a then w a ^ 2 * w b else 0)
          + (if c = b then (if b = a then w a ^ 3 else 0) else 0)
          + (if c = b then (if b = a then w a ^ 3 else 0) else 0) := by
      intro a b c
      by_cases h1 : c = b <;> by_cases h2 : b = a
      · subst h1; subst h2; simp; ring
      · subst h1; simp [h2]; ring
      · subst h2; simp [h1]; ring
      · by_cases h3 : c = a
        · subst h3; simp [h1, h2]; ring
        · simp [h1, h2, h3]
    simp_rw [e, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have t : ∑ x, ∑ x_1, ∑ x_2, (if x_1 = x then w x ^ 2 * w x_2 else 0)
        = ∑ x, ∑ x_2, w x ^ 2 * w x_2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp
    have p2' : (∑ i, w i ^ 2) * (∑ i, w i) = ∑ a, ∑ b, w a ^ 2 * w b :=
      Finset.sum_mul_sum _ _ _ _
    rw [t, ← p1, ← p2, ← p2']
    ring
  rw [← key, ← h6]; ring

/-! ## The kernel at map degree 3 -/

lemma sumJJ3 (g : Mono n 3 → ℝ) : ∑ q : JJ n 3, g q.1 = ∑ p, g p - g default := by
  classical
  have h : ∑ q : JJ n 3, g q.1
      = ∑ p ∈ Finset.univ.filter (fun p : Mono n 3 => p ≠ default), g p := by
    rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  rw [h, Finset.filter_ne' Finset.univ (default : Mono n 3),
    Finset.sum_erase_eq_sub (Finset.mem_univ _)]

/-- The degree-3 part of the kernel. -/
noncomputable def cub (x y : Fin n → ℝ) : ℝ :=
  ∑ β : Sym (Fin n) 3, monoVal x β.1 * monoVal y β.1

lemma kap3_split (x y : Fin n → ℝ) : kap 3 x y = BstLean.Part78.kap x y + cub x y := by
  classical
  rw [BstLean.Part78.kap_formula]
  unfold kap pf cub
  rw [sumJJ3 (fun p => phiM x p * phiM y p), Fintype.sum_sigma, Fin.sum_univ_four]
  have e0 := BstLean.Part78.sum_sym_zero x y
  have e1 := BstLean.Part78.sum_sym_one x y
  have e2 := BstLean.Part78.sum_sym_two x y
  simp only [phiM] at *
  have hd : monoVal x (default : Mono n 3).2.1 * monoVal y (default : Mono n 3).2.1 = 1 := by
    simp [monoVal, default]
  erw [e0, e1, e2, hd]
  ring_nf
  rfl

lemma cub_formula (x y : Fin n → ℝ) :
    cub x y = ((∑ i, x i * y i) ^ 3 + 3 * (∑ i, x i * y i) * (∑ i, x i ^ 2 * y i ^ 2)
      + 2 * ∑ i, x i ^ 3 * y i ^ 3) / 6 := by
  have h := sum_sym_three (fun i => x i * y i)
  simp only [mul_pow] at h
  rw [← h]
  unfold cub monoVal
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Multiset.prod_map_mul]

lemma kap3_formula (x y : Fin n → ℝ) :
    kap 3 x y = ∑ i, x i * y i + ((∑ i, x i * y i) ^ 2 + ∑ i, x i ^ 2 * y i ^ 2) / 2
      + ((∑ i, x i * y i) ^ 3 + 3 * (∑ i, x i * y i) * (∑ i, x i ^ 2 * y i ^ 2)
        + 2 * ∑ i, x i ^ 3 * y i ^ 3) / 6 := by
  rw [kap3_split, BstLean.Part78.kap_formula, cub_formula]

/-- `q6(x) = Σ_i x_i⁶`. -/
def q6 (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 6

lemma kap3_diag_sphere (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    kap 3 x x = 5 / 3 + BstLean.Part78.q4 x + q6 x / 3 := by
  rw [kap3_formula]
  have h1 : ∑ i, x i * x i = 1 := by rw [← hx]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : ∑ i, x i ^ 2 * x i ^ 2 = BstLean.Part78.q4 x :=
    Finset.sum_congr rfl (fun i _ => by ring)
  have h3 : ∑ i, x i ^ 3 * x i ^ 3 = q6 x := Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, h2, h3]; ring

lemma coord_sq_le (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) (i : Fin n) : x i ^ 2 ≤ 1 := by
  have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  rw [hx] at hi; exact hi

lemma q6_nonneg (x : Fin n → ℝ) : 0 ≤ q6 x :=
  Finset.sum_nonneg (fun i _ => by positivity)

lemma q6_le_q4 (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : q6 x ≤ BstLean.Part78.q4 x := by
  apply Finset.sum_le_sum
  intro i _
  have h := coord_sq_le x hx i
  have h4 : 0 ≤ x i ^ 4 := by positivity
  nlinarith

lemma q4_sq_le_q6 (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : BstLean.Part78.q4 x ^ 2 ≤ q6 x := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) x (fun i => x i ^ 3)
  rw [hx, one_mul] at h
  have e1 : ∑ i, x i * x i ^ 3 = BstLean.Part78.q4 x := Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, (x i ^ 3) ^ 2 = q6 x := Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1, e2] at h; exact h

lemma kap3_cont : Continuous (fun x : Fin n → ℝ => kap 3 x x) := by
  have : (fun x : Fin n → ℝ => kap 3 x x) = fun x =>
      ∑ i, x i * x i + ((∑ i, x i * x i) ^ 2 + ∑ i, x i ^ 2 * x i ^ 2) / 2
      + ((∑ i, x i * x i) ^ 3 + 3 * (∑ i, x i * x i) * (∑ i, x i ^ 2 * x i ^ 2)
        + 2 * ∑ i, x i ^ 3 * x i ^ 3) / 6 :=
    funext (fun x => kap3_formula x x)
  rw [this]; fun_prop

lemma q6_cont : Continuous (q6 (n := n)) := by unfold q6; fun_prop

/-! ## Moments -/

lemma mom (hn : 1 ≤ n) (u : Multiset (Fin n)) :
    Integrable (fun x => monoVal x u) (uniformSphere n) ∧
      ∫ x, monoVal x u ∂uniformSphere n = gpm u / rhoD n (Multiset.card u / 2) :=
  BstLean.Part36.sphere_multiset (uniformSphere n) (BstLean.Part33.uniformSphere_prod n _ hn) u
    le_rfl

lemma mom_odd (hn : 1 ≤ n) (u : Multiset (Fin n)) (h : ∃ i, ¬ Even (u.count i)) :
    ∫ x, monoVal x u ∂uniformSphere n = 0 := by
  rw [(mom hn u).2]
  obtain ⟨i, hi⟩ := h
  have : gpm u = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [gaussMom, hi])
  rw [this, zero_div]

lemma mom_card3 (hn : 1 ≤ n) (β : Sym (Fin n) 3) :
    ∫ x, monoVal x β.1 ∂uniformSphere n = 0 := by
  classical
  apply mom_odd hn
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h := Multiset.sum_count_eq_card (s := Finset.univ) (m := β.1)
    (fun a _ => Finset.mem_univ a)
  have he : Even (∑ a, β.1.count a) := Finset.even_sum _ (fun a _ => hcon a)
  rw [h, β.2] at he
  exact absurd he (by decide)

lemma mom_pow (hn : 1 ≤ n) (i : Fin n) (k : ℕ) :
    ∫ x, x i ^ k ∂uniformSphere n = gaussMom k / rhoD n (k / 2) := by
  classical
  have h := (mom hn (Multiset.replicate k i)).2
  have e : ∀ x : Fin n → ℝ, monoVal x (Multiset.replicate k i) = x i ^ k := by
    intro x; simp [monoVal]
  simp_rw [e] at h
  rw [h]
  have hg : gpm (Multiset.replicate k i) = gaussMom k := by
    unfold gpm
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [gaussMom, Multiset.count_replicate, Ne.symm hj]
    · simp
  rw [hg, Multiset.card_replicate]

lemma integral_q6 (hn : 1 ≤ n) :
    ∫ x, q6 x ∂uniformSphere n = 15 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold q6
  rw [integral_finsetSum _ (fun i _ => BstLean.Part78.sph_int hn (by fun_prop))]
  simp_rw [mom_pow hn _ 6]
  have hg : gaussMom 6 = 15 := by
    have : Even 6 := by decide
    simp [gaussMom, this, Nat.doubleFactorial]
  have hr : rhoD n (6 / 2) = (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 4) := by
    have : (6 / 2 : ℕ) = 3 := rfl
    rw [this]; unfold rhoD
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]; push_cast; ring
  rw [hg, hr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h4 : (n : ℝ) + 4 ≠ 0 := by positivity
  field_simp

lemma inner_cub (hn : 1 ≤ n) (x : Fin n → ℝ) : ∫ y, cub x y ∂uniformSphere n = 0 := by
  unfold cub
  rw [integral_finsetSum _ (fun β _ => ((mom hn β.1).1).const_mul _)]
  apply Finset.sum_eq_zero
  intro β _
  rw [integral_const_mul, mom_card3 hn β, mul_zero]

lemma int_cub (hn : 1 ≤ n) (x : Fin n → ℝ) : Integrable (fun y => cub x y) (uniformSphere n) :=
  integrable_finsetSum _ (fun β _ => ((mom hn β.1).1).const_mul _)

lemma kap2_cont_right (x : Fin n → ℝ) : Continuous (fun y : Fin n → ℝ => BstLean.Part78.kap x y) := by
  have : (fun y : Fin n → ℝ => BstLean.Part78.kap x y) = fun y =>
      ∑ i, x i * y i + ((∑ i, x i * y i) ^ 2 + ∑ i, x i ^ 2 * y i ^ 2) / 2 :=
    funext (fun y => BstLean.Part78.kap_formula n x y)
  rw [this]; fun_prop

lemma tG3_eq (hn : 1 ≤ n) :
    tG n 3 = 5 / 3 + 3 / ((n : ℝ) + 2) + 5 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold tG
  have h : (fun x : Fin n → ℝ => kap 3 x x) =ᵐ[uniformSphere n]
      fun x => 5 / 3 + BstLean.Part78.q4 x + q6 x / 3 := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact kap3_diag_sphere x hx
  have i4 := BstLean.Part78.sph_int hn (BstLean.Part78.q4_cont (n := n))
  have i6 := BstLean.Part78.sph_int hn (q6_cont (n := n))
  have hA : ∫ x, (5 / 3 + BstLean.Part78.q4 x + q6 x / 3) ∂uniformSphere n
      = ∫ x, (5 / 3 + BstLean.Part78.q4 x) ∂uniformSphere n + ∫ x, q6 x / 3 ∂uniformSphere n :=
    integral_add ((integrable_const _).add i4) (i6.div_const 3)
  have hB : ∫ x, (5 / 3 + BstLean.Part78.q4 x) ∂uniformSphere n
      = ∫ _x : Fin n → ℝ, (5 / 3 : ℝ) ∂uniformSphere n + ∫ x, BstLean.Part78.q4 x ∂uniformSphere n :=
    integral_add (integrable_const _) i4
  have hC : ∫ x, q6 x / 3 ∂uniformSphere n = (∫ x, q6 x ∂uniformSphere n) / 3 := integral_div _ _
  rw [integral_congr_ae h, hA, hB, hC, BstLean.Part78.integral_q4 hn, integral_q6 hn]
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h4 : (n : ℝ) + 4 ≠ 0 := by positivity
  simp
  field_simp
  ring

lemma kk2_var (hn : 1 ≤ n) :
    kk2 n 3 - tG n 3 ^ 2 ≤ 80 / 3 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have iK : Integrable (fun x : Fin n → ℝ => kap 3 x x) (uniformSphere n) :=
    BstLean.Part78.sph_int hn kap3_cont
  have iK2 : Integrable (fun x : Fin n → ℝ => kap 3 x x ^ 2) (uniformSphere n) :=
    BstLean.Part78.sph_int hn (kap3_cont.pow 2)
  have ex : ∀ c : ℝ, ∫ x, (kap 3 x x - c) ^ 2 ∂uniformSphere n
      = kk2 n 3 - 2 * c * tG n 3 + c ^ 2 := by
    intro c
    have e : ∀ x : Fin n → ℝ, (kap 3 x x - c) ^ 2 = kap 3 x x ^ 2 - 2 * c * kap 3 x x + c ^ 2 :=
      fun x => by ring
    simp_rw [e]
    have hA : ∫ x, (kap 3 x x ^ 2 - 2 * c * kap 3 x x + c ^ 2) ∂uniformSphere n
        = ∫ x, (kap 3 x x ^ 2 - 2 * c * kap 3 x x) ∂uniformSphere n
          + ∫ _x : Fin n → ℝ, c ^ 2 ∂uniformSphere n :=
      integral_add (iK2.sub (iK.const_mul _)) (integrable_const _)
    have hB : ∫ x, (kap 3 x x ^ 2 - 2 * c * kap 3 x x) ∂uniformSphere n
        = ∫ x, kap 3 x x ^ 2 ∂uniformSphere n - ∫ x, 2 * c * kap 3 x x ∂uniformSphere n :=
      integral_sub iK2 (iK.const_mul _)
    rw [hA, hB, integral_const_mul]
    simp [kk2, tG]
  have h := ex (5 / 3)
  have hle : ∫ x, (kap 3 x x - 5 / 3) ^ 2 ∂uniformSphere n
      ≤ ∫ x, 16 / 9 * q6 x ∂uniformSphere n := by
    apply integral_mono_ae
      (BstLean.Part78.sph_int hn ((kap3_cont.sub continuous_const).pow 2))
      ((BstLean.Part78.sph_int hn q6_cont).const_mul _)
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    show (kap 3 x x - 5 / 3) ^ 2 ≤ 16 / 9 * q6 x
    rw [kap3_diag_sphere x hx]
    have a1 := q6_nonneg x
    have a2 := q6_le_q4 x hx
    have a3 := q4_sq_le_q6 x hx
    have a4 := BstLean.Part78.q4_nonneg x
    nlinarith [mul_le_mul a2 a2 a1 a4]
  rw [integral_const_mul, integral_q6 hn] at hle
  have e3 : (16 / 9 : ℝ) * (15 / (((n : ℝ) + 2) * ((n : ℝ) + 4)))
      = 80 / 3 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by ring
  rw [e3] at hle
  nlinarith [sq_nonneg (tG n 3 - 5 / 3)]

end BstLean.Part81.K3

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part81.K3

theorem eD_three : eD 3 = 5 / 3 := by
  unfold eD BstLean.Part53.c0
  simp [Finset.sum_range_succ, Nat.factorial]
  norm_num

theorem kap3_diag_eq (n : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    kap 3 x x = 5 / 3 + (∑ i, x i ^ 4) + (∑ i, x i ^ 6) / 3 :=
  kap3_diag_sphere x hx

theorem kap3_diag_bounds (n : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    5 / 3 ≤ kap 3 x x ∧ kap 3 x x ≤ 5 / 3 + (∑ i, x i ^ 4) + (∑ i, x i ^ 6) / 3 := by
  have h := kap3_diag_eq n x hx
  refine ⟨?_, h.le⟩
  rw [h]
  have a1 : 0 ≤ ∑ i, x i ^ 4 := BstLean.Part78.q4_nonneg x
  have a2 : 0 ≤ ∑ i, x i ^ 6 := q6_nonneg x
  linarith

theorem inner_kap3 (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) :
    ∫ y, kap 3 x y ∂uniformSphere n = (∑ i, x i ^ 2) / n := by
  simp_rw [kap3_split]
  rw [integral_add (BstLean.Part78.sph_int hn (kap2_cont_right x)) (int_cub hn x),
    BstLean.Part78.inner_kap hn, inner_cub hn, add_zero]

theorem mm1_three (n : ℕ) (hn : 1 ≤ n) : mm1 n 3 = 1 / (n : ℝ) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold mm1
  simp_rw [inner_kap3 n hn]
  have h : (fun x : Fin n → ℝ => (∑ i, x i ^ 2) / (n : ℝ)) =ᵐ[uniformSphere n]
      fun _ => 1 / (n : ℝ) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    rw [hx]
  rw [integral_congr_ae h]; simp

theorem sphC3 (n : ℕ) (hn : 1000 ≤ n) (hK : KerGen n 3) (CF : ℝ) (hCF : 0 ≤ CF)
    (hF : FeatOp n 3 CF) :
    SphC n 3 1 (CF * (5 / 3 + 3 / (n : ℝ))) 3 (80 / (3 * (n : ℝ))) 3 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hm0, hs0, hk, hgen⟩ := hK
  obtain ⟨-, hss⟩ := hgen CF hCF hF
  have htG := tG3_eq hn1
  have hvar := kk2_var hn1
  have hB : 3 / ((n : ℝ) + 2) + 5 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) ≤ 3 / (n : ℝ) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hn0]
    nlinarith
  have hpos : 0 ≤ 3 / ((n : ℝ) + 2) + 5 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by positivity
  refine ⟨?_, ?_, hm0, ?_, hs0, ?_, hk, ?_, ?_⟩
  · rw [eD_three, htG]; linarith
  · rw [eD_three, htG]; linarith
  · rw [mm1_three n hn1]
  · have h1 : CF / (n : ℝ) * tG n 3 ≤ CF / (n : ℝ) * (5 / 3 + 3 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by rw [htG]; linarith) (by positivity)
    have e : CF * (5 / 3 + 3 / (n : ℝ)) / (n : ℝ) = CF / (n : ℝ) * (5 / 3 + 3 / (n : ℝ)) := by
      ring
    rw [e]; linarith
  · refine hvar.trans ?_
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 4) := by nlinarith
    field_simp
    nlinarith
  · intro x hx
    have hd := kap3_diag_sphere x hx
    have a1 := q6_nonneg x
    have a2 := q6_le_q4 x hx
    have a3 := BstLean.Part78.q4_le_one x hx
    have a4 := BstLean.Part78.q4_nonneg x
    have hin := inner_kap3 n hn1 x
    rw [hx] at hin
    have h1n : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]; linarith
    have h1p : 0 ≤ 1 / (n : ℝ) := by positivity
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [eD_three, hd]; linarith
    · rw [hd]; linarith
    · rw [hin]; exact h1p
    · rw [hin, hd]; linarith

end BstLean.Part81

#print axioms BstLean.Part81.eD_three
#print axioms BstLean.Part81.kap3_diag_eq
#print axioms BstLean.Part81.kap3_diag_bounds
#print axioms BstLean.Part81.inner_kap3
#print axioms BstLean.Part81.mm1_three
#print axioms BstLean.Part81.sphC3
