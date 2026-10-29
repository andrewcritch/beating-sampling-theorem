import BstLean.Part69Defs
import BstLean.Part56MomProg_Sphere
import BstLean.Part56MomProg_Formula
import BstLean.Part69Rot

/-!
# Part 69: directional moments of the surrogate `Q = surrRK n K t v`

For a unit `v` and any `u ∈ ℝⁿ`, with `c = u·v`, `ρ² = |u|² − c²`, `m = n − 1`:
* `E_Q (u·x)² = c² a + ρ² (1 − a)/m`;
* `E_Q (u·x)⁴ = c⁴ b + 6 c² ρ² (a − b)/m + 3 ρ⁴ (1 − 2a + b)/(m (m + 2))`.

The proof writes `u = c v + ρ e` with `e ⊥ v` a unit vector, moves `(v·x, e·x)` to `(x_a, x_b)` by
the two-direction invariance of the uniform sphere distribution (the hypothesis `PairInv69`,
proved in `Part69Rot`), and evaluates the two-coordinate sphere moments.
-/

namespace BstLean.Part69

open MeasureTheory
open BstLean.Part56
open BstLean.Part29 (uniformSphere gaussMom)
open BstLean.Part36 (rhoD)

variable {n : ℕ}

/-- The two-direction invariance of the uniform sphere distribution. -/
def PairInv69 (n : ℕ) : Prop :=
  ∀ (p1 p2 : Fin n → ℝ), ∑ i, p1 i ^ 2 = 1 → ∑ i, p2 i ^ 2 = 1 → ∑ i, p1 i * p2 i = 0 →
    ∀ (a b : Fin n), a ≠ b → ∀ G : ℝ → ℝ → ℝ, Continuous (fun z : ℝ × ℝ => G z.1 z.2) →
      ∫ x, G (∑ i, p1 i * x i) (∑ i, p2 i * x i) ∂uniformSphere n =
        ∫ x, G (x a) (x b) ∂uniformSphere n

/-- A unit vector orthogonal to a given unit vector exists. -/
def OrthEx69 (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, ∑ i, v i ^ 2 = 1 → ∃ u : Fin n → ℝ, ∑ i, u i ^ 2 = 1 ∧ ∑ i, v i * u i = 0

/-! ## Two-coordinate sphere moments -/

theorem mom2_69 (hn : 1 ≤ n) (a b : Fin n) (hab : a ≠ b) (α β : ℕ) :
    ∫ x, x a ^ α * x b ^ β ∂uniformSphere n =
      gaussMom α * gaussMom β / rhoD n ((α + β) / 2) := by
  classical
  let s : Multiset (Fin n) := Multiset.replicate α a + Multiset.replicate β b
  have hs := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (α + β) hn) s (by simp [s])).2
  have hmon (x : Fin n → ℝ) : BstLean.Part36.monoVal x s = x a ^ α * x b ^ β := by
    simp [s, BstLean.Part36.monoVal]
  have hgp : BstLean.Part36.gpm s = gaussMom α * gaussMom β := by
    unfold BstLean.Part36.gpm
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ b),
      ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)]
    rw [Finset.prod_eq_one]
    · simp [s, Multiset.count_replicate, hab, Ne.symm hab]
    · intro l hl
      have hlb : l ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
      have hla : l ≠ a := (Finset.mem_erase.mp hl).1
      simp [s, Multiset.count_replicate, Ne.symm hla, Ne.symm hlb, gaussMom]
  simpa only [hmon, hgp, show Multiset.card s = α + β by simp [s]] using hs

theorem gaussMom_odd69 (j : ℕ) : gaussMom (2 * j + 1) = 0 := by
  unfold gaussMom
  rw [if_neg (Nat.not_even_iff_odd.mpr ⟨j, rfl⟩)]

theorem gaussMom_succ69 (j : ℕ) : gaussMom (2 * j + 2) = (2 * j + 1) * gaussMom (2 * j) := by
  rw [MomProg.gaussMom_eq, MomProg.gaussMom_eq, MomProg.gmN_add_two]
  push_cast; ring

theorem rhoD_pos69 (hn : 1 ≤ n) (p : ℕ) : 0 < rhoD n p := MomProg.rhoD_pos hn p

/-- `U_j = gaussMom(2j)/rhoD n j`. -/
theorem U69_eq (hn : 1 ≤ n) (j : ℕ) : U69 n j = gaussMom (2 * j) / rhoD n j := by
  induction j with
  | zero => simp [U69, gaussMom, rhoD]
  | succ j ih =>
    have hr := rhoD_pos69 hn j
    have hn' : (0 : ℝ) < n + 2 * j := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    rw [U69, Finset.prod_range_succ, ← U69, ih, MomProg.rhoD_succ,
      show 2 * (j + 1) = 2 * j + 2 by ring, gaussMom_succ69]
    field_simp

theorem U69_rec69 (hn : 1 ≤ n) (j : ℕ) :
    U69 n (j + 1) = U69 n j * (2 * j + 1) / (n + 2 * j) := by
  rw [U69, Finset.prod_range_succ, ← U69]; ring

theorem U69_nonneg (j : ℕ) : 0 ≤ U69 n j := by
  unfold U69
  apply Finset.prod_nonneg
  intro i _
  positivity

/-! ## The tilted two-coordinate moments -/

theorem mom2e_69 (hn : 1 ≤ n) (a b : Fin n) (hab : a ≠ b) (i k : ℕ) :
    ∫ x, x a ^ (2 * i) * x b ^ (2 * k) ∂uniformSphere n =
      gaussMom (2 * i) * gaussMom (2 * k) / rhoD n (i + k) := by
  rw [mom2_69 hn a b hab, show (2 * i + 2 * k) / 2 = i + k by omega]

theorem mom2o_69 (hn : 1 ≤ n) (a b : Fin n) (hab : a ≠ b) (i k : ℕ) :
    ∫ x, x a ^ (2 * i + 1) * x b ^ (2 * k + 1) ∂uniformSphere n = 0 := by
  rw [mom2_69 hn a b hab, gaussMom_odd69]; simp

theorem gm0_69 : gaussMom (2 * 0) = 1 := by simp [gaussMom]
theorem gm1_69 : gaussMom (2 * 1) = 1 := by simp [gaussMom]
theorem gm2_69 : gaussMom (2 * 2) = 3 := by
  simp [gaussMom, show Even 4 from ⟨2, rfl⟩]

private theorem intg69 (hn : 1 ≤ n) (a b : Fin n) (α β : ℕ) (c : ℝ) :
    Integrable (fun x : Fin n → ℝ => c * (x a ^ α * x b ^ β)) (uniformSphere n) :=
  (MomProg.sphere_integrable hn (by fun_prop)).const_mul c

private theorem lin3_69 {μ : Measure (Fin n → ℝ)} (f g h : (Fin n → ℝ) → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ x, f x + g x + h x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ + ∫ x, h x ∂μ := by
  rw [integral_add (f := fun x => f x + g x) (hf.add hg) hh, integral_add hf hg]

private theorem lin5_69 {μ : Measure (Fin n → ℝ)} (f g h k l : (Fin n → ℝ) → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) (hk : Integrable k μ)
    (hl : Integrable l μ) :
    ∫ x, f x + g x + h x + k x + l x ∂μ =
      ∫ x, f x ∂μ + ∫ x, g x ∂μ + ∫ x, h x ∂μ + ∫ x, k x ∂μ + ∫ x, l x ∂μ := by
  rw [integral_add (f := fun x => f x + g x + h x + k x) (((hf.add hg).add hh).add hk) hl,
    integral_add (f := fun x => f x + g x + h x) ((hf.add hg).add hh) hk,
    integral_add (f := fun x => f x + g x) (hf.add hg) hh, integral_add hf hg]

/-- `∫ x_a^{2j} (c x_a + ρ x_b)² dσ`. -/
theorem tilt2_69 (hn : 1 ≤ n) (a b : Fin n) (hab : a ≠ b) (j : ℕ) (c ρ : ℝ) :
    ∫ x, x a ^ (2 * j) * (c * x a + ρ * x b) ^ 2 ∂uniformSphere n =
      c ^ 2 * U69 n (j + 1) + ρ ^ 2 * U69 n j / (n + 2 * j) := by
  have hexp : ∀ x : Fin n → ℝ, x a ^ (2 * j) * (c * x a + ρ * x b) ^ 2 =
      c ^ 2 * (x a ^ (2 * (j + 1)) * x b ^ (2 * 0)) +
        (2 * c * ρ) * (x a ^ (2 * j + 1) * x b ^ (2 * 0 + 1)) +
        ρ ^ 2 * (x a ^ (2 * j) * x b ^ (2 * 1)) := by
    intro x; ring
  simp_rw [hexp]
  rw [lin3_69 _ _ _ (intg69 hn a b _ _ _) (intg69 hn a b _ _ _) (intg69 hn a b _ _ _)]
  simp only [integral_const_mul, mom2e_69 hn a b hab, mom2o_69 hn a b hab, gm0_69, gm1_69]
  rw [U69_eq hn, U69_eq hn, MomProg.rhoD_succ]
  have hr := rhoD_pos69 hn j
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n + 2 * j := by positivity
  field_simp
  ring

/-- `∫ x_a^{2j} (c x_a + ρ x_b)⁴ dσ`. -/
theorem tilt4_69 (hn : 1 ≤ n) (a b : Fin n) (hab : a ≠ b) (j : ℕ) (c ρ : ℝ) :
    ∫ x, x a ^ (2 * j) * (c * x a + ρ * x b) ^ 4 ∂uniformSphere n =
      c ^ 4 * U69 n (j + 2) + 6 * c ^ 2 * ρ ^ 2 * U69 n (j + 1) / (n + 2 * (j + 1)) +
        3 * ρ ^ 4 * U69 n j / ((n + 2 * j) * (n + 2 * (j + 1))) := by
  have hexp : ∀ x : Fin n → ℝ, x a ^ (2 * j) * (c * x a + ρ * x b) ^ 4 =
      c ^ 4 * (x a ^ (2 * (j + 2)) * x b ^ (2 * 0)) +
        (4 * c ^ 3 * ρ) * (x a ^ (2 * (j + 1) + 1) * x b ^ (2 * 0 + 1)) +
        (6 * c ^ 2 * ρ ^ 2) * (x a ^ (2 * (j + 1)) * x b ^ (2 * 1)) +
        (4 * c * ρ ^ 3) * (x a ^ (2 * j + 1) * x b ^ (2 * 1 + 1)) +
        ρ ^ 4 * (x a ^ (2 * j) * x b ^ (2 * 2)) := by
    intro x; ring
  simp_rw [hexp]
  rw [lin5_69 _ _ _ _ _ (intg69 hn a b _ _ _) (intg69 hn a b _ _ _) (intg69 hn a b _ _ _)
    (intg69 hn a b _ _ _) (intg69 hn a b _ _ _)]
  simp only [integral_const_mul, mom2e_69 hn a b hab, mom2o_69 hn a b hab, gm0_69, gm1_69,
    gm2_69]
  rw [U69_eq hn, U69_eq hn, U69_eq hn]
  simp only [show j + 2 = j + 1 + 1 by ring, show j + 1 + 0 = j + 1 by ring,
    show j + 0 + 2 = j + 1 + 1 by ring, MomProg.rhoD_succ]
  have hr := rhoD_pos69 hn j
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n + 2 * j := by positivity
  have hn'' : (0 : ℝ) < n + 2 * ((j + 1 : ℕ) : ℝ) := by positivity
  push_cast at hn'' ⊢
  simp only [add_zero, mul_zero, zero_div]
  field_simp

/-! ## The surrogate -/

theorem Z0_eq69 (hn : 1 ≤ n) (K : ℕ) (t : ℝ) (v : Fin n → ℝ) (hv : UnitV v) :
    BstLean.Part50.ZKA n K (rk1 t v) = Z69 n K t 0 := by
  rw [MomProg.normalizer_scalarNumerator hn]
  unfold MomProg.scalarNumerator Z69
  apply Finset.sum_congr rfl
  intro i _
  rw [MomProg.sphere_directional_moment hn v hv, U69_eq hn, zero_add, add_zero]

theorem Z0_pos69 (K : ℕ) (t : ℝ) (ht : 0 ≤ t) : 1 ≤ Z69 n K t 0 := by
  unfold Z69
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (K + 1)) => mul_nonneg
      (div_nonneg (pow_nonneg ht i) (Nat.cast_nonneg i.factorial)) (U69_nonneg (n := n) (i + 0)))
    (Finset.mem_range.mpr (show 0 < K + 1 by omega))
  simpa [U69] using h

/-- Decomposition `u = c v + ρ e` with `e` a unit vector orthogonal to `v`. -/
theorem decomp69 (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (u : Fin n → ℝ) :
    ∃ (e : Fin n → ℝ) (ρ : ℝ), ∑ i, e i ^ 2 = 1 ∧ ∑ i, v i * e i = 0 ∧
      ρ ^ 2 = ∑ i, u i ^ 2 - (∑ i, u i * v i) ^ 2 ∧
      ∀ i, u i = (∑ l, u l * v l) * v i + ρ * e i := by
  set c := ∑ l, u l * v l with hc
  have hv' : ∑ i, v i ^ 2 = 1 := hv
  have hw : ∑ i, (u i - c * v i) ^ 2 = ∑ i, u i ^ 2 - c ^ 2 := by
    have : ∀ i, (u i - c * v i) ^ 2 = u i ^ 2 - 2 * c * (u i * v i) + c ^ 2 * v i ^ 2 := by
      intro i; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hc, hv']
    ring
  have hwv : ∑ i, v i * (u i - c * v i) = 0 := by
    have : ∀ i, v i * (u i - c * v i) = u i * v i - c * v i ^ 2 := by intro i; ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hc, hv']
    ring
  set ρ2 := ∑ i, u i ^ 2 - c ^ 2 with hρ2
  by_cases h0 : ρ2 = 0
  · obtain ⟨e, he1, he2⟩ := exists_orth69 hn v hv
    refine ⟨e, 0, he1, he2, by rw [h0]; ring, fun i => ?_⟩
    have hz : ∑ i, (u i - c * v i) ^ 2 = 0 := hw.trans h0
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u i - c * v i))).mp hz i
      (Finset.mem_univ i)
    have : u i - c * v i = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hi
    linarith
  · have hpos : 0 < ρ2 := lt_of_le_of_ne (hw ▸ Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Ne.symm h0)
    set ρ := Real.sqrt ρ2
    have hρ : ρ ^ 2 = ρ2 := Real.sq_sqrt hpos.le
    have hρ0 : ρ ≠ 0 := by positivity
    refine ⟨fun i => (u i - c * v i) / ρ, ρ, ?_, ?_, hρ, fun i => ?_⟩
    · simp only [div_pow, ← Finset.sum_div, hw, hρ]
      exact div_self h0
    · simp only [mul_div_assoc', ← Finset.sum_div, hwv, zero_div]
    · field_simp; ring

/-- The surrogate moment of `(u·x)^p` as a tilted two-coordinate integral. -/
theorem surr_dir69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (u : Fin n → ℝ) (p : ℕ) :
    ∃ ρ : ℝ, ρ ^ 2 = ∑ i, u i ^ 2 - (∑ i, u i * v i) ^ 2 ∧
      ∫ x, (∑ i, u i * x i) ^ p ∂surrRK n K t v =
        (∑ j ∈ Finset.range (K + 1), t ^ j / (j.factorial : ℝ) *
          ∫ x, x ⟨0, by omega⟩ ^ (2 * j) *
            ((∑ i, u i * v i) * x ⟨0, by omega⟩ + ρ * x ⟨1, by omega⟩) ^ p ∂uniformSphere n) /
          Z69 n K t 0 := by
  obtain ⟨e, ρ, he1, he2, hρ, hu⟩ := decomp69 hn v hv u
  refine ⟨ρ, hρ, ?_⟩
  set c := ∑ i, u i * v i
  have hn1 : 1 ≤ n := by omega
  rw [MomProg.integral_surrogate hn1 K t ht v, Z0_eq69 hn1 K t v hv]
  congr 1
  have hux : ∀ x : Fin n → ℝ, ∑ i, u i * x i = c * (∑ i, v i * x i) + ρ * (∑ i, e i * x i) := by
    intro x
    simp only [hu, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  simp_rw [hux]
  have hv' : ∑ i, v i ^ 2 = 1 := hv
  have hpair := sphere_pair69 hn1 v e hv' he1 he2 ⟨0, by omega⟩ ⟨1, by omega⟩
    (by simp [Fin.ext_iff])
    (fun s y => (c * s + ρ * y) ^ p * BstLean.Part37.taylorExp K (t * s ^ 2))
    (by unfold BstLean.Part37.taylorExp; fun_prop)
  try simp only at hpair
  rw [hpair]
  have hexp : ∀ x : Fin n → ℝ,
      (c * x ⟨0, by omega⟩ + ρ * x ⟨1, by omega⟩) ^ p *
        BstLean.Part37.taylorExp K (t * x ⟨0, by omega⟩ ^ 2) =
      ∑ j ∈ Finset.range (K + 1), t ^ j / (j.factorial : ℝ) *
        (x ⟨0, by omega⟩ ^ (2 * j) * (c * x ⟨0, by omega⟩ + ρ * x ⟨1, by omega⟩) ^ p) := by
    intro x
    unfold BstLean.Part37.taylorExp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow, pow_mul]
    ring
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun j _ => (MomProg.sphere_integrable hn1 (by fun_prop)).const_mul _)]
  simp only [integral_const_mul]

theorem Uid1_69 (hn : 2 ≤ n) (j : ℕ) :
    U69 n j / (n + 2 * j) = (U69 n j - U69 n (j + 1)) / ((n : ℝ) - 1) := by
  rw [U69_rec69 (by omega)]
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < n + 2 * j := by positivity
  have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  field_simp; ring

theorem Uid2_69 (hn : 2 ≤ n) (j : ℕ) :
    U69 n j / ((n + 2 * j) * (n + 2 * (j + 1))) =
      (U69 n j - 2 * U69 n (j + 1) + U69 n (j + 2)) / (((n : ℝ) - 1) * ((n : ℝ) + 1)) := by
  rw [show j + 2 = j + 1 + 1 by ring, U69_rec69 (by omega) (j + 1), U69_rec69 (by omega) j]
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < n + 2 * j := by positivity
  have : (0 : ℝ) < n + 2 * (j + 1) := by positivity
  have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  push_cast
  field_simp; ring

/-- **`E_Q (u·x)² = c² a + ρ² (1 − a)/(n − 1)`.** -/
theorem dir2_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (u : Fin n → ℝ) :
    ∫ x, (∑ i, u i * x i) ^ 2 ∂surrRK n K t v =
      (∑ i, u i * v i) ^ 2 * a69 n K t +
        (∑ i, u i ^ 2 - (∑ i, u i * v i) ^ 2) * (1 - a69 n K t) / ((n : ℝ) - 1) := by
  obtain ⟨ρ, hρ, h⟩ := surr_dir69 hn K t ht v hv u 2
  rw [h, ← hρ]
  set c := ∑ i, u i * v i
  simp only [tilt2_69 (by omega) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by simp [Fin.ext_iff]), Uid1_69 hn]
  have hterm : ∀ j ∈ Finset.range (K + 1), t ^ j / (j.factorial : ℝ) *
      (c ^ 2 * U69 n (j + 1) + ρ ^ 2 * ((U69 n j - U69 n (j + 1)) / ((n : ℝ) - 1))) =
      c ^ 2 * (t ^ j / (j.factorial : ℝ) * U69 n (j + 1)) +
        ρ ^ 2 / ((n : ℝ) - 1) * (t ^ j / (j.factorial : ℝ) * U69 n (j + 0)) -
        ρ ^ 2 / ((n : ℝ) - 1) * (t ^ j / (j.factorial : ℝ) * U69 n (j + 1)) := by
    intro j _; rw [add_zero]; ring
  have hm : ∀ j : ℕ, ρ ^ 2 * U69 n j / ((n : ℝ) + 2 * j) =
      ρ ^ 2 * (U69 n j / ((n : ℝ) + 2 * j)) := fun j => by ring
  simp only [hm, Uid1_69 hn]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  change (c ^ 2 * Z69 n K t 1 + ρ ^ 2 / ((n : ℝ) - 1) * Z69 n K t 0 -
    ρ ^ 2 / ((n : ℝ) - 1) * Z69 n K t 1) / Z69 n K t 0 = _
  have hZ := Z0_pos69 (n := n) K t ht
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  unfold a69
  field_simp
  ring

/-- **`E_Q (u·x)⁴ = c⁴ b + 6 c² ρ² (a − b)/m + 3 ρ⁴ (1 − 2a + b)/(m (m + 2))`.** -/
theorem dir4_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (u : Fin n → ℝ) :
    ∫ x, (∑ i, u i * x i) ^ 4 ∂surrRK n K t v =
      (∑ i, u i * v i) ^ 4 * b69 n K t +
        6 * (∑ i, u i * v i) ^ 2 * (∑ i, u i ^ 2 - (∑ i, u i * v i) ^ 2) *
          (a69 n K t - b69 n K t) / ((n : ℝ) - 1) +
        3 * (∑ i, u i ^ 2 - (∑ i, u i * v i) ^ 2) ^ 2 *
          (1 - 2 * a69 n K t + b69 n K t) / (((n : ℝ) - 1) * ((n : ℝ) + 1)) := by
  obtain ⟨ρ, hρ, h⟩ := surr_dir69 hn K t ht v hv u 4
  rw [h, ← hρ]
  set c := ∑ i, u i * v i
  simp only [tilt4_69 (by omega) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by simp [Fin.ext_iff])]
  have hm : ∀ j : ℕ, 3 * ρ ^ 4 * U69 n j / (((n : ℝ) + 2 * j) * ((n : ℝ) + 2 * ((j : ℝ) + 1))) =
      3 * ρ ^ 4 * (U69 n j / (((n : ℝ) + 2 * j) * ((n : ℝ) + 2 * ((j : ℝ) + 1)))) :=
    fun j => by ring
  have hm2 : ∀ j : ℕ, 6 * c ^ 2 * ρ ^ 2 * U69 n (j + 1) / ((n : ℝ) + 2 * ((j : ℝ) + 1)) =
      6 * c ^ 2 * ρ ^ 2 * (U69 n (j + 1) / ((n : ℝ) + 2 * ((j + 1 : ℕ) : ℝ))) :=
    fun j => by push_cast; ring
  simp only [hm, hm2, Uid1_69 hn, Uid2_69 hn]
  set m := (n : ℝ) - 1
  set m2 := ((n : ℝ) - 1) * ((n : ℝ) + 1)
  have hterm : ∀ j ∈ Finset.range (K + 1), t ^ j / (j.factorial : ℝ) *
      (c ^ 4 * U69 n (j + 2) + 6 * c ^ 2 * ρ ^ 2 * ((U69 n (j + 1) - U69 n (j + 1 + 1)) / m) +
        3 * ρ ^ 4 * ((U69 n j - 2 * U69 n (j + 1) + U69 n (j + 2)) / m2)) =
      (c ^ 4 - 6 * c ^ 2 * ρ ^ 2 / m + 3 * ρ ^ 4 / m2) * (t ^ j / (j.factorial : ℝ) * U69 n (j + 2)) +
        (6 * c ^ 2 * ρ ^ 2 / m - 6 * ρ ^ 4 / m2) * (t ^ j / (j.factorial : ℝ) * U69 n (j + 1)) +
        3 * ρ ^ 4 / m2 * (t ^ j / (j.factorial : ℝ) * U69 n (j + 0)) := by
    intro j _; rw [add_zero, show j + 1 + 1 = j + 2 by ring]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  change ((c ^ 4 - 6 * c ^ 2 * ρ ^ 2 / m + 3 * ρ ^ 4 / m2) * Z69 n K t 2 +
    (6 * c ^ 2 * ρ ^ 2 / m - 6 * ρ ^ 4 / m2) * Z69 n K t 1 + 3 * ρ ^ 4 / m2 * Z69 n K t 0) /
      Z69 n K t 0 = _
  have hZ := Z0_pos69 (n := n) K t ht
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < m := by simp only [m]; linarith
  have : (0 : ℝ) < m2 := by simp only [m2]; nlinarith
  unfold a69 b69
  field_simp
  ring

end BstLean.Part69
