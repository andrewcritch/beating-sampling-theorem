import BstLean.Part90Defs
import BstLean.Part89QInst
import BstLean.Part89SliceRH
import BstLean.Part82BridgeB

/-!
# Part 90: facts of the instance `modRK m 3 t v E` used by the cubic variance bound

* `instFeat4`: the fourth-moment feature bound in every slice (slice reverse Hölder at degree 3).
* `instKup`: `κ(x, x) ≤ 6 R_p²` almost surely.
* `instCubRep`: `PU 3 f0 T U r sc` is a cubic in the sense of `CubRep`.
* `instTau3`: `(49/100)³ ≤ E_p (R_p²)³`.
-/

namespace BstLean.Part90

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono varU Tens TSymm fval)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV kJ tauR polarPoint perpDir axialR axialS axialMeasure polarState)
open BstLean.Part78 (nsq frobH zv contr1 contr2)
open BstLean.Part80 (kA FeatOpA)
open BstLean.Part82 (T3 SymT frobT trT cfun aU3 HU3)
open BstLean.Part86
open BstLean.Part89 (Ybar SliceOpF)

theorem instFeat4 (m : ℕ) (hm : 5000 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E) :
    ∀ (p : ℝ × (Fin m → ℝ)) (c : JR (m + 1) 3 → ℝ),
      ∫ g, (∑ q, c q * (modRK m 3 t v E).ps ((modRK m 3 t v E).X (p, g)) q) ^ 4
          ∂(modRK m 3 t v E).ga ≤
        (27 * (CLs 3 / (m : ℝ) * axialR p.1 (radF53 p.2) ^ 2)) ^ 2 * (∑ q, c q ^ 2) ^ 2 := by
  intro p c
  have hRH := BstLean.Part89.sliceRH_modRK9 m 3 t v hv E 3
    (BstLean.Part89.sliceRHRK9 m 3 (by omega))
  obtain ⟨-, hOp⟩ := BstLean.Part89.instSliceOpF m 3 t v E (by norm_num) hm hv hE
  obtain ⟨hτ, -, hop⟩ := hOp p
  have h2 := hop c
  set Q : MvPolynomial (Fin (m + 1)) ℝ := ∑ q, MvPolynomial.C (c q) * psPE E q with hQ
  have hdeg : Q.totalDegree ≤ 3 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro q _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact psPE_degree E q
  have hev : ∀ x : Fin (m + 1) → ℝ,
      MvPolynomial.eval x Q = ∑ q, c q * (modRK m 3 t v E).ps x q := by
    intro x
    rw [hQ]
    simp only [map_sum, map_mul, MvPolynomial.eval_C]
    rfl
  have h4 := hRH p Q hdeg
  simp only [hev] at h4
  have h0 : 0 ≤ ∫ g, (∑ q, c q * (modRK m 3 t v E).ps ((modRK m 3 t v E).X (p, g)) q) ^ 2
      ∂(modRK m 3 t v E).ga := integral_nonneg fun g => sq_nonneg _
  refine h4.trans ?_
  have hsq := pow_le_pow_left₀ h0 h2 2
  nlinarith [hsq]

theorem instKup (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) (hE : RotE v E) (hK : KernelUp3 (m + 1)) :
    ∀ᵐ p ∂(modRK m 3 t v E).pi, ∀ᵐ g ∂(modRK m 3 t v E).ga,
      kapm (modRK m 3 t v E) ((modRK m 3 t v E).X (p, g)) ((modRK m 3 t v E).X (p, g)) ≤
        6 * axialR p.1 (radF53 p.2) ^ 2 := by
  have hp0 : ∀ᵐ p ∂(modRK m 3 t v E).pi, p.1 ≠ 0 := BstLean.Part89.axial_ne_zero t v
  filter_upwards [BstLean.Part89.instSph m 3 t v E hm hv, hp0] with p hp hpne
  filter_upwards [hp] with g hg
  have e : kapm (modRK m 3 t v E) ((modRK m 3 t v E).X (p, g)) ((modRK m 3 t v E).X (p, g)) =
      tauR 3 v ((modRK m 3 t v E).X (p, g)) := rot_KR v hv E hE _ _
  rw [e]
  refine (hK v hv _ hg).trans (le_of_eq ?_)
  have eX : (modRK m 3 t v E).X (p, g) = axialS p.1 (radF53 p.2) • v +
      axialR p.1 (radF53 p.2) • perpDir v g := rfl
  have h1 : ∑ i, v i ^ 2 = 1 := hv
  have h2 := BstLean.Part56.perpDir_orth56 v g hv
  have h3 : ∑ i, v i * (modRK m 3 t v E).X (p, g) i =
      axialS p.1 (radF53 p.2) * ∑ i, v i ^ 2 +
        axialR p.1 (radF53 p.2) * ∑ i, v i * perpDir v g i := by
    rw [eX, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h3, h1, h2]
  have := BstLean.Part89.axial_sq_eq p.1 (radF53 p.2) hpne
  nlinarith

/-- **Tensor form = `(f₀, ℓ, H, T)` form** at `d_f = 3`. -/
theorem tensBridge3 (n : ℕ) (f0 : ℝ) (T : Tens n) (hsym : TSymm 3 T) :
    ∃ (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T' : T3 n), H.IsSymm ∧ SymT T' ∧
      ∀ y : Fin n → ℝ, fval 3 f0 T y = cfun f0 ℓ H T' y := by
  classical
  refine ⟨fun i => T 1 (fun _ => i), Matrix.of (fun i j => T 2 ![i, j]),
    fun i j k => T 3 ![i, j, k], ?_, ?_, ?_⟩
  · ext i j
    have h := hsym 2 (by norm_num) (by norm_num) (Equiv.swap 0 1) ![j, i]
    have e : (![j, i] ∘ (Equiv.swap (0 : Fin 2) 1)) = ![i, j] := by
      funext t; fin_cases t <;> simp
    rw [e] at h
    simpa using h.symm
  · intro i j k
    constructor
    · have h := hsym 3 (by norm_num) le_rfl (Equiv.swap 0 1) ![i, j, k]
      have e : (![i, j, k] ∘ (Equiv.swap (0 : Fin 3) 1)) = ![j, i, k] := by
        funext t; fin_cases t <;> simp [Equiv.swap_apply_of_ne_of_ne]
      rw [e] at h
      exact h.symm
    · have h := hsym 3 (by norm_num) le_rfl (Equiv.swap 1 2) ![i, j, k]
      have e : (![i, j, k] ∘ (Equiv.swap (1 : Fin 3) 2)) = ![i, k, j] := by
        funext t; fin_cases t <;> simp [Equiv.swap_apply_of_ne_of_ne]
      rw [e] at h
      exact h.symm
  · intro y
    unfold fval cfun
    have hI : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
    rw [hI, Finset.sum_insert (by decide), Finset.sum_pair (by norm_num), contr1, contr2,
      BstLean.Part82.BrAux.contr3]
    simp [add_assoc]

theorem instCubRep (m : ℕ) (t : ℝ) (v : Fin (m + 1) → ℝ)
    (E : JR (m + 1) 3 → Mono (m + 1) 3 → ℝ) :
    ∀ (f0 : ℝ) (T : Tens (m + 1)), TSymm 3 T →
      ∃ (ℓ : Fin (m + 1) → ℝ) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (T' : T3 (m + 1)),
        H.IsSymm ∧ SymT T' ∧
        ∀ (U : Fin (3 + 1) × Fin (m + 1) → ℝ) (r sc : ℝ),
          CubRep (modRK m 3 t v E) (PU 3 f0 T U r sc) f0 ℓ H T' (fun j i => U (j, i) / r) sc := by
  intro f0 T hT
  obtain ⟨ℓ, H, T', hsym, hT', hq⟩ := tensBridge3 (m + 1) f0 T hT
  refine ⟨ℓ, H, T', hsym, hT', ?_⟩
  intro U r sc lam W x
  rw [XIdent.Fm_PU, hq]
  congr 1
  funext i
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

theorem instTau3 (m : ℕ) (hm : 100 ≤ m + 1) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ)) :
    (49 / 100 : ℝ) ^ 3 ≤ ∫ p, (axialR p.1 (radF53 p.2) ^ 2) ^ 3 ∂axialMeasure t v := by
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  have : IsProbabilityMeasure (axialMeasure t v) :=
    BstLean.Part56.axialMeasure_probability b v hb0 t
  have hmin := BstLean.Part89.instTmin m t v hm hv ht0 htn
  have hle := BstLean.Part89.instTauLe m
  have hmeas := BstLean.Part89.measurable_tauF m
  have hI1 : Integrable (fun p : ℝ × (Fin m → ℝ) => axialR p.1 (radF53 p.2) ^ 2)
      (axialMeasure t v) :=
    XInst.int_bdd _ _ hmeas 1 fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact hle p
  have hI3 : Integrable (fun p : ℝ × (Fin m → ℝ) => (axialR p.1 (radF53 p.2) ^ 2) ^ 3)
      (axialMeasure t v) :=
    XInst.int_bdd _ _ (hmeas.pow_const 3) 1 fun p => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (sq_nonneg _) (hle p)
  have hpt : ∀ p : ℝ × (Fin m → ℝ),
      3 * (49 / 100 : ℝ) ^ 2 * axialR p.1 (radF53 p.2) ^ 2 - 2 * (49 / 100 : ℝ) ^ 3 ≤
        (axialR p.1 (radF53 p.2) ^ 2) ^ 3 := by
    intro p
    have hx : 0 ≤ axialR p.1 (radF53 p.2) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (sq_nonneg (axialR p.1 (radF53 p.2) ^ 2 - 49 / 100))
      (by linarith : (0 : ℝ) ≤ axialR p.1 (radF53 p.2) ^ 2 + 2 * (49 / 100))]
  have hI2 : Integrable (fun p : ℝ × (Fin m → ℝ) =>
      3 * (49 / 100 : ℝ) ^ 2 * axialR p.1 (radF53 p.2) ^ 2 - 2 * (49 / 100 : ℝ) ^ 3)
      (axialMeasure t v) := (hI1.const_mul _).sub (integrable_const _)
  have hmono := integral_mono hI2 hI3 hpt
  have heq : ∫ p : ℝ × (Fin m → ℝ),
      (3 * (49 / 100 : ℝ) ^ 2 * axialR p.1 (radF53 p.2) ^ 2 - 2 * (49 / 100 : ℝ) ^ 3)
        ∂axialMeasure t v =
      3 * (49 / 100 : ℝ) ^ 2 * (∫ p : ℝ × (Fin m → ℝ), axialR p.1 (radF53 p.2) ^ 2
        ∂axialMeasure t v) - 2 * (49 / 100 : ℝ) ^ 3 := by
    rw [integral_sub (hI1.const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
  rw [heq] at hmono
  nlinarith

end BstLean.Part90

#print axioms BstLean.Part90.instFeat4
#print axioms BstLean.Part90.instKup
#print axioms BstLean.Part90.instCubRep
#print axioms BstLean.Part90.instTau3
