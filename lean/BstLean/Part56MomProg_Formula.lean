import BstLean.Part56MomProg_Reflect

/-! The exact weight formula and the moment recurrence. -/

namespace BstLean.Part56.MomProg

open MeasureTheory MvPolynomial
open BstLean.Part56
open BstLean.Part29 (uniformSphere)

variable {n d : ℕ}

theorem integral_reflect (hn : 1 ≤ n) (a : Fin n) (v : Fin n → ℝ) (hv : UnitV v) (K : ℕ) (t : ℝ)
    (P : MvPolynomial (Fin n) ℝ) :
    (∫ x, eval x P * BstLean.Part37.taylorExp K (t * (∑ i, v i * x i) ^ 2) ∂uniformSphere n) =
      ∑ μ ∈ (bind₁ (Lform a v) P).support,
        (bind₁ (Lform a v) P).coeff μ * Ttab a K t μ := by
  obtain ⟨hm, hc⟩ := reflect_props a v hv
  rw [← integral_poly_tilt hn a K t]
  conv_lhs => rw [← hm]
  rw [integral_map (Rapp_continuous a v).aemeasurable]
  · simp only [hc, eval_bind_Lform]
  · apply Continuous.aestronglyMeasurable
    unfold BstLean.Part37.taylorExp
    have : Continuous (fun x : Fin n → ℝ => eval x P) := MvPolynomial.continuous_eval P
    fun_prop

theorem scalarTilt_eq_Ttab (hn : 1 ≤ n) (a : Fin n) (v : Fin n → ℝ) (hv : UnitV v) (K : ℕ)
    (t : ℝ) : scalarTilt n K 0 t = Ttab a K t 0 := by
  rw [← scalarTilt_normalizer hn K t v hv]
  unfold BstLean.Part50.ZKA
  simp_rw [qA_rk1]
  have h := integral_reflect hn a v hv K t 1
  simp only [map_one, one_mul] at h
  rw [h, support_one, Finset.sum_singleton, coeff_zero_one, one_mul]

/-- The reflected weight polynomial. -/
noncomputable def Qpoly (a : Fin n) (v : Fin n → ℝ) {k : ℕ} (κ : KeyRK k d) :
    MvPolynomial (Fin n) ℝ :=
  bind₁ (Lform a v) (weightPoly v κ)

theorem weight_formula (hn : 1 ≤ n) (a : Fin n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (v : Fin n → ℝ) (hv : UnitV v) {k : ℕ} (κ : KeyRK k d) :
    wRK (surrRK n K t v) d v κ =
      wickC κ.1.1 κ.1.2 * (1 / BstLean.Part36.DD n d) ^ (κ.1.2 : ℕ) *
        ((∑ μ : Idx n (2 * d * k), (Qpoly a v κ).coeff μ.1 * Ttab a K t μ.1) /
          Ttab a K t 0) := by
  have hS := sum_support_Idx (D := 2 * d * k) (bind₁ (Lform a v) (weightPoly v κ))
    ((totalDegree_bind_linear _ (totalDegree_Lform a v) _).trans
      (weightPoly_degree_all v κ)) (Ttab a K t)
  rw [surrogate_weight_ratio hn K t ht v hv κ, integral_reflect hn a v hv K t,
    scalarTilt_eq_Ttab hn a v hv K t, hS]
  rfl

/-! ## The moment recurrence -/

/-- The Gaussian moment as a natural number. -/
def gmN (c : ℕ) : ℕ := if Even c then (c - 1).doubleFactorial else 0

theorem gaussMom_eq (c : ℕ) : BstLean.Part29.gaussMom c = (gmN c : ℝ) := by
  unfold BstLean.Part29.gaussMom gmN
  split_ifs <;> simp

theorem gmN_add_two (c : ℕ) : gmN (c + 2) = (c + 1) * gmN c := by
  unfold gmN
  by_cases h : Even c
  · have h2 : Even (c + 2) := by
      rcases h with ⟨r, hr⟩; exact ⟨r + 1, by omega⟩
    rw [if_pos h2, if_pos h]
    rcases c with _ | c
    · simp
    · rw [show c + 1 + 2 - 1 = c + 2 by omega, show c + 1 - 1 = c by omega,
        Nat.doubleFactorial_add_two]
  · have h2 : ¬ Even (c + 2) := by
      intro h2; apply h; rcases h2 with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
    rw [if_neg h2, if_neg h, mul_zero]

/-- The multiset of `x_a^{2i} x^μ`. -/
noncomputable def msA (a : Fin n) (i : ℕ) (μ : Fin n →₀ ℕ) : Multiset (Fin n) :=
  Multiset.replicate (2 * i) a + Finsupp.toMultiset μ

theorem momA_formula (hn : 1 ≤ n) (a : Fin n) (i : ℕ) (μ : Fin n →₀ ℕ) :
    momA a i μ = BstLean.Part36.gpm (msA a i μ) /
      BstLean.Part36.rhoD n (Multiset.card (msA a i μ) / 2) := by
  have h := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n (Multiset.card (msA a i μ)) hn) (msA a i μ) le_rfl).2
  rw [← h]
  unfold momA
  congr 1
  funext x
  rw [msA, BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add,
    show (Multiset.map x (Finsupp.toMultiset μ)).prod = xpow x μ from monoVal_toMultiset x μ]
  simp

theorem card_msA (a : Fin n) (i : ℕ) (μ : Fin n →₀ ℕ) :
    Multiset.card (msA a i μ) = 2 * i + fdeg μ := by
  simp [msA, Finsupp.card_toMultiset, fdeg]
  rfl

theorem count_msA (a : Fin n) (i : ℕ) (μ : Fin n →₀ ℕ) (l : Fin n) :
    Multiset.count l (msA a i μ) = (if l = a then 2 * i else 0) + μ l := by
  classical
  simp only [msA, Multiset.count_add, Finsupp.count_toMultiset, Multiset.count_replicate]
  split_ifs with h1 h2 h2 <;> simp_all

theorem gpm_msA (a : Fin n) (i : ℕ) (μ : Fin n →₀ ℕ) :
    BstLean.Part36.gpm (msA a i μ) =
      ((∏ l, gmN ((if l = a then 2 * i else 0) + μ l) : ℕ) : ℝ) := by
  unfold BstLean.Part36.gpm
  push_cast
  apply Finset.prod_congr rfl
  intro l _
  rw [count_msA, gaussMom_eq]

theorem gpm_msA_succ (a : Fin n) (i : ℕ) (μ : Fin n →₀ ℕ) :
    BstLean.Part36.gpm (msA a (i + 1) μ) =
      BstLean.Part36.gpm (msA a i μ) * ((2 * i + μ a + 1 : ℕ) : ℝ) := by
  classical
  rw [gpm_msA, gpm_msA]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  have he : ∀ l ∈ Finset.univ.erase a,
      gmN ((if l = a then 2 * (i + 1) else 0) + μ l) =
        gmN ((if l = a then 2 * i else 0) + μ l) := by
    intro l hl
    rw [if_neg (Finset.ne_of_mem_erase hl), if_neg (Finset.ne_of_mem_erase hl)]
  rw [Finset.prod_congr rfl he]
  simp only [if_true]
  rw [show 2 * (i + 1) + μ a = (2 * i + μ a) + 2 by ring, gmN_add_two]
  push_cast
  ring

theorem rhoD_succ (x : ℝ) (p : ℕ) :
    BstLean.Part36.rhoD x (p + 1) = BstLean.Part36.rhoD x p * (x + 2 * p) := by
  simp [BstLean.Part36.rhoD, Finset.prod_range_succ]

theorem rhoD_pos (hn : 1 ≤ n) (p : ℕ) : 0 < BstLean.Part36.rhoD n p := by
  unfold BstLean.Part36.rhoD
  apply Finset.prod_pos
  intro j _
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

theorem momA_succ (hn : 1 ≤ n) (a : Fin n) (i : ℕ) (μ : Fin n →₀ ℕ) :
    momA a (i + 1) μ = momA a i μ * ((2 * i + μ a + 1 : ℕ) : ℝ) /
      ((n + 2 * (i + fdeg μ / 2) : ℕ) : ℝ) := by
  rw [momA_formula hn, momA_formula hn, gpm_msA_succ, card_msA, card_msA]
  rw [show (2 * (i + 1) + fdeg μ) / 2 = (i + fdeg μ / 2) + 1 by omega,
    show (2 * i + fdeg μ) / 2 = i + fdeg μ / 2 by omega, rhoD_succ]
  have h1 := rhoD_pos hn (i + fdeg μ / 2)
  have h2 : (0 : ℝ) < (n : ℝ) + 2 * ((i + fdeg μ / 2 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  push_cast at h2 ⊢
  field_simp

/-- The natural numbers of `m(0, μ)`. -/
def momNum (μ : Fin n →₀ ℕ) : ℕ := ∏ l, gmN (μ l)

def momDen (n : ℕ) (μ : Fin n →₀ ℕ) : ℕ := ∏ j ∈ Finset.range (fdeg μ / 2), (n + 2 * j)

theorem momA_zero (hn : 1 ≤ n) (a : Fin n) (μ : Fin n →₀ ℕ) :
    momA a 0 μ = (momNum μ : ℝ) / (momDen n μ : ℝ) := by
  rw [momA_formula hn, gpm_msA, card_msA]
  simp [momNum, momDen, BstLean.Part36.rhoD]

end BstLean.Part56.MomProg
