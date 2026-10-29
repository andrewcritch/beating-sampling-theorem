import BstLean.Part74Defs
import BstLean.Part69Mom
import BstLean.Part33Moments
import BstLean.Part36Index

/-!
# Part 74: the Stein core of the generic moment engine

* `gE_dir`: Stein in the direction `v`.
* `tilt74`: `E_g[γ^a G] = Σ_c C(a,c) gaussMom(a−c) E_g[∂_v^c G]` for a unit `v`.
* `sphere_hom74`: the uniform-sphere integral of a homogeneous polynomial of degree `2r` is its
  Gaussian expectation divided by `n(n+2)⋯(n+2r−2)`.
* `surr74`: the surrogate expectation of a homogeneous polynomial of degree `2q` in the Stein
  basis `W74`.
-/

namespace BstLean.Part74

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss uniformSphere gaussMom)
open BstLean.Part36 (rhoD)
open BstLean.Part56
open BstLean.Part69

variable {n : ℕ}

/-! ## The directional derivative -/

theorem dvD_apply (v : Fin n → ℝ) (F : MvPolynomial (Fin n) ℝ) :
    dvD v F = ∑ i, v i • pderiv i F := by
  classical
  unfold dvD
  have h : ∀ s : Finset (Fin n), (∑ i ∈ s, v i • pderiv (R := ℝ) i) F = ∑ i ∈ s, v i • pderiv i F := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]; rfl
  exact h _

theorem dvD_gamma (v : Fin n → ℝ) (hv : UnitV v) : dvD v (Sp v 1 1) = 1 := by
  rw [dvD_apply]
  unfold Sp
  have h : ∀ i : Fin n, pderiv i (∑ j, C (v j ^ 1) * X j ^ 1 : MvPolynomial (Fin n) ℝ) = C (v i) := by
    intro i
    simp only [map_sum, pow_one, Derivation.leibniz, pderiv_C, smul_zero, add_zero, pderiv_X,
      smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  simp only [h, smul_eq_C_mul, ← C_mul, ← map_sum]
  have : ∑ i, v i * v i = 1 := by simpa [UnitV, sq] using hv
  rw [this]; rfl

/-- Stein in the direction `v`. -/
theorem gE_dir (v : Fin n → ℝ) (F : MvPolynomial (Fin n) ℝ) :
    gE (Sp v 1 1 * F) = gE (dvD v F) := by
  rw [dvD_apply]
  unfold Sp
  simp only [pow_one, Finset.sum_mul, map_sum, ← smul_eq_C_mul, smul_mul_assoc, map_smul, gE_X_mul]

theorem gE_step (v : Fin n → ℝ) (hv : UnitV v) (a : ℕ) (G : MvPolynomial (Fin n) ℝ) :
    gE (Sp v 1 1 ^ (a + 2) * G) =
      ((a : ℝ) + 1) * gE (Sp v 1 1 ^ a * G) + gE (Sp v 1 1 ^ (a + 1) * dvD v G) := by
  rw [show Sp v 1 1 ^ (a + 2) * G = Sp v 1 1 * (Sp v 1 1 ^ (a + 1) * G) by ring, gE_dir,
    Derivation.leibniz, Derivation.leibniz_pow, dvD_gamma v hv]
  simp only [smul_eq_mul, mul_one, Nat.add_sub_cancel, map_add]
  rw [add_comm]
  congr 1
  rw [show G * ((a + 1 : ℕ) • Sp v 1 1 ^ a) = ((a : ℝ) + 1) • (Sp v 1 1 ^ a * G) by
    rw [nsmul_eq_mul, smul_eq_C_mul]; push_cast; simp only [map_add, map_natCast, map_one]; ring,
    map_smul, smul_eq_mul]

/-! ## The tilt coefficients -/

/-- `C(a, c) · gaussMom(a − c)`. -/
noncomputable def cf74 (a c : ℕ) : ℝ := (a.choose c : ℝ) * gaussMom (a - c)

theorem gaussMom_one74 : gaussMom 1 = 0 := by simp [gaussMom]
theorem gaussMom_zero74 : gaussMom 0 = 1 := by simp [gaussMom]

theorem gaussMom_add_two74 (m : ℕ) : gaussMom (m + 2) = ((m : ℝ) + 1) * gaussMom m := by
  rw [MomProg.gaussMom_eq, MomProg.gaussMom_eq, MomProg.gmN_add_two]; push_cast; ring

theorem gaussMom_odd74 (j : ℕ) : gaussMom (2 * j + 1) = 0 := gaussMom_odd69 j

theorem cf74_zero (a : ℕ) : cf74 (a + 2) 0 = ((a : ℝ) + 1) * cf74 a 0 := by
  simp [cf74, gaussMom_add_two74]

theorem cf74_succ (a c : ℕ) :
    cf74 (a + 2) (c + 1) = ((a : ℝ) + 1) * cf74 a (c + 1) + cf74 (a + 1) c := by
  unfold cf74
  rcases lt_trichotomy (c + 1) (a + 1) with h | h | h
  · obtain ⟨m, rfl⟩ : ∃ m, a = c + 1 + m := ⟨a - (c + 1), by omega⟩
    rw [show c + 1 + m + 2 - (c + 1) = m + 2 by omega, show c + 1 + m - (c + 1) = m by omega,
      show c + 1 + m + 1 - c = m + 2 by omega, gaussMom_add_two74]
    have h1 : (c + 1 + m + 2).choose (c + 1) = (c + m + 2).choose c + (c + m + 2).choose (c + 1) := by
      rw [show c + 1 + m + 2 = c + m + 2 + 1 by ring, Nat.choose_succ_succ]
    have h2 := Nat.choose_mul_succ_eq (c + m + 1) (c + 1)
    rw [show c + m + 1 + 1 - (c + 1) = m + 1 by omega] at h2
    have h2' : ((c + m + 1).choose (c + 1) : ℝ) * ((c : ℝ) + m + 1 + 1) =
        ((c + m + 2).choose (c + 1) : ℝ) * ((m : ℝ) + 1) := by exact_mod_cast h2
    rw [h1, show c + 1 + m + 1 = c + m + 2 by ring, show c + 1 + m = c + m + 1 by ring]
    push_cast
    linear_combination (-gaussMom m) * h2'
  · have ha : a = c := by omega
    subst ha
    rw [show a + 2 - (a + 1) = 1 by omega, show a + 1 - a = 1 by omega, gaussMom_one74,
      Nat.choose_eq_zero_of_lt (show a < a + 1 by omega)]
    simp
  · rcases Nat.lt_or_ge (a + 2) (c + 1) with h' | h'
    · rw [Nat.choose_eq_zero_of_lt h', Nat.choose_eq_zero_of_lt (show a < c + 1 by omega),
        Nat.choose_eq_zero_of_lt (show a + 1 < c by omega)]
      simp
    · have hc : c = a + 1 := by omega
      subst hc
      rw [Nat.choose_eq_zero_of_lt (show a < a + 1 + 1 by omega)]
      simp

theorem cf74_gt (a c : ℕ) (h : a < c) : cf74 a c = 0 := by
  unfold cf74; rw [Nat.choose_eq_zero_of_lt h]; simp

theorem sum_cf74_ext (a N : ℕ) (hN : a + 1 ≤ N) (g : ℕ → ℝ) :
    ∑ c ∈ Finset.range N, cf74 a c * g c = ∑ c ∈ Finset.range (a + 1), cf74 a c * g c := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro c _ hc
  rw [cf74_gt a c (by simpa using hc), zero_mul]

/-- **The tilt formula.** -/
theorem tilt74 (v : Fin n → ℝ) (hv : UnitV v) (a : ℕ) (G : MvPolynomial (Fin n) ℝ) :
    gE (Sp v 1 1 ^ a * G) = ∑ c ∈ Finset.range (a + 1),
      (a.choose c : ℝ) * gaussMom (a - c) * gE ((dvD v)^[c] G) := by
  change _ = ∑ c ∈ Finset.range (a + 1), cf74 a c * gE ((dvD v)^[c] G)
  induction a using Nat.twoStepInduction generalizing G with
  | zero => simp [cf74, gaussMom_zero74]
  | one =>
    rw [pow_one, gE_dir]
    simp [cf74, Finset.sum_range_succ, gaussMom_one74, gaussMom_zero74]
  | more a ih ih' =>
    rw [gE_step v hv, ih G, ih' (dvD v G),
      ← sum_cf74_ext a (a + 3) (by omega) (fun c => gE ((dvD v)^[c] G)),
      Finset.sum_range_succ' _ (a + 2), Finset.sum_range_succ' _ (a + 2), mul_add, Finset.mul_sum]
    have key : ∀ k, cf74 (a + 2) (k + 1) * gE ((dvD v)^[k + 1] G) =
        ((a : ℝ) + 1) * (cf74 a (k + 1) * gE ((dvD v)^[k + 1] G)) +
          cf74 (a + 1) k * gE ((dvD v)^[k] (dvD v G)) := by
      intro k
      rw [cf74_succ, Function.iterate_succ_apply]; ring
    simp_rw [key]
    rw [Finset.sum_add_distrib, cf74_zero]
    ring

/-! ## The coefficient identity -/

theorem gm2_74 (m : ℕ) : gaussMom (2 * m) * 2 ^ m * (m.factorial : ℝ) = ((2 * m).factorial : ℝ) := by
  induction m with
  | zero => simp [gaussMom_zero74]
  | succ m ih =>
    have e1 : ((2 * m + 2).factorial : ℝ) = (2 * (m : ℝ) + 2) * (2 * m + 1) * (2 * m).factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have e2 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, gaussMom_add_two74, e1, e2, ← ih]
    push_cast
    ring

/-- `C(2j, 2c) gaussMom(2j − 2c) = gaussMom(2j) 2^c j^{\underline c}/(2c)!`. -/
theorem cfid74 (j c : ℕ) :
    ((2 * j).choose (2 * c) : ℝ) * gaussMom (2 * j - 2 * c) =
      gaussMom (2 * j) * 2 ^ c * (j.descFactorial c : ℝ) / ((2 * c).factorial : ℝ) := by
  rcases Nat.lt_or_ge j c with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), (Nat.descFactorial_eq_zero_iff_lt).mpr h]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, j = c + m := ⟨j - c, by omega⟩
    rw [show 2 * (c + m) - 2 * c = 2 * m by omega]
    have h1 : (((2 * (c + m)).choose (2 * c) : ℕ) : ℝ) * ((2 * c).factorial : ℝ) *
        ((2 * m).factorial : ℝ) = ((2 * (c + m)).factorial : ℝ) := by
      have := Nat.choose_mul_factorial_mul_factorial (show 2 * c ≤ 2 * (c + m) by omega)
      rw [show 2 * (c + m) - 2 * c = 2 * m by omega] at this
      exact_mod_cast this
    have h2 := gm2_74 m
    have h3 := gm2_74 (c + m)
    have h4 : (((c + m).descFactorial c : ℕ) : ℝ) * (m.factorial : ℝ) = ((c + m).factorial : ℝ) := by
      have := Nat.factorial_mul_descFactorial (show c ≤ c + m by omega)
      rw [show c + m - c = m by omega] at this
      rw [mul_comm]; exact_mod_cast this
    have hc : ((2 * c).factorial : ℝ) ≠ 0 := by positivity
    have hm : (2 : ℝ) ^ m * (m.factorial : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff hc]
    apply mul_right_cancel₀ hm
    rw [pow_add] at h3
    linear_combination (((2 * (c + m)).choose (2 * c) : ℕ) : ℝ) * ((2 * c).factorial : ℝ) * h2 +
      h1 - h3 - gaussMom (2 * (c + m)) * 2 ^ c * 2 ^ m * h4

/-! ## Sphere integrals of homogeneous polynomials -/

theorem gE_monomial (d : Fin n →₀ ℕ) (c : ℝ) :
    gE (monomial d c) = c * ∏ i, gaussMom (d i) := by
  rw [gE_apply]
  simp only [eval_monomial]
  rw [integral_const_mul]
  congr 1
  simp_rw [Finsupp.prod_fintype d _ (fun i => pow_zero _)]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (f := fun (i : Fin n) (x : ℝ) => x ^ d i)]
  simp_rw [BstLean.Part29.gaussMom_eq]

theorem sphere_monomial74 (hn : 1 ≤ n) (d : Fin n →₀ ℕ) (c : ℝ) (r : ℕ)
    (hd : d.degree = 2 * r) :
    ∫ x, eval x (monomial d c) ∂uniformSphere n = gE (monomial d c) / rhoD n r := by
  classical
  rw [gE_monomial]
  simp only [eval_monomial]
  rw [integral_const_mul]
  have hcard : Multiset.card (Finsupp.toMultiset d) = 2 * r := by
    rw [Finsupp.card_toMultiset, ← hd]; rfl
  have hs := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (2 * r) hn) (Finsupp.toMultiset d) (by omega)).2
  have hmon (x : Fin n → ℝ) : BstLean.Part36.monoVal x (Finsupp.toMultiset d) =
      d.prod fun i k => x i ^ k := by
    unfold BstLean.Part36.monoVal
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  have hgp : BstLean.Part36.gpm (Finsupp.toMultiset d) = ∏ i, gaussMom (d i) := by
    unfold BstLean.Part36.gpm
    simp [Finsupp.count_toMultiset]
  simp only [hmon, hgp, hcard] at hs
  rw [hs, show 2 * r / 2 = r by omega]
  ring

/-- The uniform-sphere integral of a homogeneous polynomial of degree `2r`. -/
theorem sphere_hom74 (hn : 1 ≤ n) (P : MvPolynomial (Fin n) ℝ) (r : ℕ)
    (hP : P.IsHomogeneous (2 * r)) :
    ∫ x, eval x P ∂uniformSphere n = gE P / rhoD n r := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum]
  rw [integral_finsetSum _ (fun d _ =>
    MomProg.sphere_integrable hn (MvPolynomial.continuous_eval _)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  apply sphere_monomial74 hn
  have := hP (mem_support_iff.mp hd)
  rw [← this, Finsupp.degree_eq_weight_one]
  rfl

/-! ## Homogeneity and the directional derivative -/

theorem dvD_hom (v : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) (m : ℕ) (hP : P.IsHomogeneous m) :
    (dvD v P).IsHomogeneous (m - 1) := by
  rw [dvD_apply]
  apply IsHomogeneous.sum
  intro i _
  rw [smul_eq_C_mul]
  have := (isHomogeneous_C (Fin n) (v i)).mul (hP.pderiv (i := i))
  simpa using this

theorem dvD_iter_hom (v : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) (m : ℕ)
    (hP : P.IsHomogeneous m) (c : ℕ) : ((dvD v)^[c] P).IsHomogeneous (m - c) := by
  induction c with
  | zero => simpa using hP
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    have := dvD_hom v _ _ ih
    rwa [show m - c - 1 = m - (c + 1) by omega] at this

theorem dvD_iter_zero (v : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) (m : ℕ)
    (hP : P.IsHomogeneous m) (c : ℕ) (hc : m < c) : (dvD v)^[c] P = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  have h := dvD_iter_hom v P m hP c
  rw [show m - c = 0 by omega] at h
  have ht : ((dvD v)^[c] P).totalDegree = 0 := Nat.le_zero.mp h.totalDegree_le
  rw [totalDegree_eq_zero_iff_eq_C.mp ht]
  simp [dvD_apply]

/-! ## The surrogate -/

theorem sum_even_odd74 (M : ℕ) (f : ℕ → ℝ) :
    ∑ c ∈ Finset.range (2 * M), f c = ∑ c ∈ Finset.range M, (f (2 * c) + f (2 * c + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

theorem Sp11_eval (v x : Fin n → ℝ) : eval x (Sp v 1 1) = ∑ i, v i * x i := by
  simp [Sp]

theorem Sp11_hom (v : Fin n → ℝ) : (Sp v 1 1).IsHomogeneous 1 := by
  unfold Sp
  apply IsHomogeneous.sum
  intro i _
  have := (isHomogeneous_C (Fin n) (v i ^ 1)).mul (isHomogeneous_X_pow (R := ℝ) i 1)
  simpa using this

/-- The Gaussian expectation of `γ^{2j} P` for `P` homogeneous of degree `2q`. -/
theorem tilt_even74 (v : Fin n → ℝ) (hv : UnitV v) (j q : ℕ) (P : MvPolynomial (Fin n) ℝ)
    (hP : P.IsHomogeneous (2 * q)) :
    gE (Sp v 1 1 ^ (2 * j) * P) = gaussMom (2 * j) * ∑ c ∈ Finset.range (q + 1),
      2 ^ c / ((2 * c).factorial : ℝ) * (j.descFactorial c : ℝ) * gE ((dvD v)^[2 * c] P) := by
  rw [tilt74 v hv]
  change ∑ c ∈ Finset.range (2 * j + 1), cf74 (2 * j) c * gE ((dvD v)^[c] P) = _
  set M := max j q + 1 with hM
  rw [← sum_cf74_ext (2 * j) (2 * M) (by omega), sum_even_odd74]
  have hodd : ∀ c, cf74 (2 * j) (2 * c + 1) = 0 := by
    intro c
    unfold cf74
    rcases Nat.lt_or_ge (2 * j) (2 * c + 1) with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · obtain ⟨m, hm⟩ : ∃ m, 2 * j - (2 * c + 1) = 2 * m + 1 := ⟨j - c - 1, by omega⟩
      rw [hm, gaussMom_odd74]; simp
  simp only [hodd, zero_mul, add_zero]
  rw [Finset.mul_sum]
  have h1 : ∑ c ∈ Finset.range M, cf74 (2 * j) (2 * c) * gE ((dvD v)^[2 * c] P) =
      ∑ c ∈ Finset.range (q + 1), cf74 (2 * j) (2 * c) * gE ((dvD v)^[2 * c] P) := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro c _ hc
    rw [dvD_iter_zero v P (2 * q) hP (2 * c) (by simp at hc; omega)]
    simp
  rw [h1]
  apply Finset.sum_congr rfl
  intro c _
  unfold cf74
  rw [cfid74]
  ring

theorem rhoD_add74 (j q : ℕ) :
    rhoD n (j + q) = rhoD n j * ∏ i ∈ Finset.range q, ((n : ℝ) + 2 * (j : ℝ) + 2 * (i : ℝ)) := by
  unfold rhoD
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  push_cast; ring

/-- **The surrogate expectation of a homogeneous polynomial of degree `2q`, in the Stein basis.** -/
theorem surr74 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (P : MvPolynomial (Fin n) ℝ) (q : ℕ) (hP : P.IsHomogeneous (2 * q)) :
    ∫ x, eval x P ∂surrRK n K t v =
      (∑ c ∈ Finset.range (q + 1), 2 ^ c / ((2 * c).factorial : ℝ) *
        gE ((dvD v)^[2 * c] P) * W74 n K t c q) / Z69 n K t 0 := by
  have hn1 : 1 ≤ n := by omega
  rw [MomProg.integral_surrogate hn1 K t ht v, Z0_eq69 hn1 K t v hv]
  congr 1
  have hexp : ∀ x : Fin n → ℝ,
      eval x P * BstLean.Part37.taylorExp K (t * (∑ i, v i * x i) ^ 2) =
      ∑ j ∈ Finset.range (K + 1), t ^ j / (j.factorial : ℝ) *
        eval x (Sp v 1 1 ^ (2 * j) * P) := by
    intro x
    unfold BstLean.Part37.taylorExp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_mul, eval_pow, Sp11_eval, mul_pow, pow_mul]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun j _ =>
    (MomProg.sphere_integrable hn1 (MvPolynomial.continuous_eval _)).const_mul _)]
  simp only [integral_const_mul]
  have hterm : ∀ j ∈ Finset.range (K + 1), t ^ j / (j.factorial : ℝ) *
      ∫ x, eval x (Sp v 1 1 ^ (2 * j) * P) ∂uniformSphere n =
      ∑ c ∈ Finset.range (q + 1), 2 ^ c / ((2 * c).factorial : ℝ) * gE ((dvD v)^[2 * c] P) *
        (t ^ j / (j.factorial : ℝ) * U69 n j * (j.descFactorial c : ℝ) /
          ∏ i ∈ Finset.range q, ((n : ℝ) + 2 * (j : ℝ) + 2 * (i : ℝ))) := by
    intro j _
    have hh : (Sp v 1 1 ^ (2 * j) * P).IsHomogeneous (2 * (j + q)) := by
      have := ((Sp11_hom v).pow (2 * j)).mul hP
      rwa [show 1 * (2 * j) + 2 * q = 2 * (j + q) by ring] at this
    rw [sphere_hom74 hn1 _ (j + q) hh, tilt_even74 v hv j q P hP, rhoD_add74, U69_eq hn1,
      Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    have hr := rhoD_pos69 hn1 j
    have hp : (0 : ℝ) < ∏ i ∈ Finset.range q, ((n : ℝ) + 2 * (j : ℝ) + 2 * (i : ℝ)) := by
      apply Finset.prod_pos
      intro i _
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      positivity
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  unfold W74
  rw [Finset.mul_sum]

end BstLean.Part74

#print axioms BstLean.Part74.surr74
#print axioms BstLean.Part74.tilt74
#print axioms BstLean.Part74.sphere_hom74
