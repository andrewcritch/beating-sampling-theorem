import BstLean.Part90Defs
import BstLean.Part82Wick
import BstLean.Part82Mean
import BstLean.Part82Transfer
import BstLean.Part82Prob

/-!
# Part 90: the single-point Wick variance of the cubic (`VarWC`)

`f(u + z) = f(u) + Φ(a_u, H_u, T; z)`, then `Wick3` at `p' = p`.
-/

namespace BstLean.Part90

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part78 (nsq frobH trH zv Good good_coord)
open BstLean.Part80 (kA)
open BstLean.Part82 (T3 SymT frobT trT cfun aU3 HU3 Phi3 C2 AA)

/-- The cubic at `u + z` is the cubic at `u` plus `Φ` with the coefficients at `u`. -/
lemma cfun_shift {n : ℕ} {J : Type} [Fintype J] (f0 : ℝ) (ℓ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (T : T3 n) (hT : SymT T) (u : Fin n → ℝ)
    (W : J × Fin n → ℝ) (p : J → ℝ) :
    cfun f0 ℓ H T (fun i => u i + zv W p i) =
      cfun f0 ℓ H T u + Phi3 (aU3 ℓ H T u) (HU3 H T u) T W p := by
  rw [BstLean.Part82.cfun_eq, BstLean.Part82.cfun_eq, BstLean.Part82.Phi3_eq,
    BstLean.Part82.linZ_add, BstLean.Part82.quadZ_add H hH, BstLean.Part82.cubZ_add T hT,
    BstLean.Part82.linZ_aU3, BstLean.Part82.quadZ_HU3]
  ring

lemma good_zv' {n : ℕ} {J : Type} [Fintype J] (p : J → ℝ) (i : Fin n) :
    Good (stdGauss (J × Fin n)) (fun W : J × Fin n → ℝ => zv W p i) :=
  Good.sum _ fun q _ => (good_coord (q, i)).mul_const (p q)

lemma good_Phi3 {n : ℕ} {J : Type} [Fintype J] (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (T : T3 n) (p : J → ℝ) :
    Good (stdGauss (J × Fin n)) (fun W : J × Fin n → ℝ => Phi3 a H T W p) := by
  unfold Phi3
  exact ((Good.sum _ fun i _ => (good_zv' p i).const_mul (a i)).add
    (Good.sum _ fun i _ => Good.sum _ fun j _ =>
      ((good_zv' p i).const_mul (H i j)).mul (good_zv' p j))).add
    (Good.sum _ fun i _ => Good.sum _ fun j _ => Good.sum _ fun k _ =>
      (((good_zv' p i).const_mul (T i j k)).mul (good_zv' p j)).mul (good_zv' p k))

/-- **Single-point Wick variance** of the cubic. -/
theorem varWC : VarWC := by
  intro n J _ f0 ℓ H hH T hT mu ψ x
  set a := aU3 ℓ H T (mu x) with ha
  set H' := HU3 H T (mu x) with hH'
  set c := cfun f0 ℓ H T (mu x) with hc
  set k := ∑ q, ψ x q ^ 2 with hk
  have hH's : H'.IsSymm := BstLean.Part82.HU3_symm H hH T hT (mu x)
  have hF : ∀ W, FC f0 ℓ H T mu ψ W x = c + Phi3 a H' T W (ψ x) := fun W => by
    unfold FC
    exact cfun_shift f0 ℓ H hH T hT (mu x) W (ψ x)
  have gP : Good (stdGauss (J × Fin n)) (fun W => Phi3 a H' T W (ψ x)) := good_Phi3 a H' T (ψ x)
  have hw := BstLean.Part82.wick3 J n a H' hH's T hT (ψ x) (ψ x)
  obtain ⟨hw1, hw2⟩ := hw
  have hkk : ∑ q, ψ x q * ψ x q = k := Finset.sum_congr rfl fun q _ => by ring
  rw [hkk, ← hk] at hw2
  rw [← hk] at hw1
  have hmean : ∫ W, FC f0 ℓ H T mu ψ W x ∂(stdGauss (J × Fin n)) = c + trH H' * k := by
    simp_rw [hF]
    rw [integral_add (integrable_const _) gP.integrable, integral_const, hw1]
    simp
  have hcen : ∀ W, (FC f0 ℓ H T mu ψ W x - ∫ W', FC f0 ℓ H T mu ψ W' x ∂(stdGauss (J × Fin n))) ^ 2 =
      Phi3 a H' T W (ψ x) * Phi3 a H' T W (ψ x) - (2 * (trH H' * k)) * Phi3 a H' T W (ψ x) +
        (trH H' * k) ^ 2 := fun W => by
    rw [hmean, hF]; ring
  have i1 : Integrable (fun W => Phi3 a H' T W (ψ x) * Phi3 a H' T W (ψ x)) (stdGauss (J × Fin n)) :=
    (gP.mul gP).integrable
  have i2 : Integrable (fun W => (2 * (trH H' * k)) * Phi3 a H' T W (ψ x)) (stdGauss (J × Fin n)) :=
    gP.integrable.const_mul _
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hF]
    exact (integrable_const _).add gP.integrable
  · simp_rw [hcen]
    exact (i1.sub i2).add (integrable_const _)
  · simp_rw [hcen]
    have e1 : ∫ W, (Phi3 a H' T W (ψ x) * Phi3 a H' T W (ψ x) -
        (2 * (trH H' * k)) * Phi3 a H' T W (ψ x) + (trH H' * k) ^ 2) ∂(stdGauss (J × Fin n)) =
        ∫ W, (Phi3 a H' T W (ψ x) * Phi3 a H' T W (ψ x) -
          (2 * (trH H' * k)) * Phi3 a H' T W (ψ x)) ∂(stdGauss (J × Fin n)) + ∫ _W, (trH H' * k) ^ 2 ∂(stdGauss (J × Fin n)) :=
      integral_add (i1.sub i2) (integrable_const _)
    have e2 : ∫ W, (Phi3 a H' T W (ψ x) * Phi3 a H' T W (ψ x) -
          (2 * (trH H' * k)) * Phi3 a H' T W (ψ x)) ∂(stdGauss (J × Fin n)) =
        ∫ W, Phi3 a H' T W (ψ x) * Phi3 a H' T W (ψ x) ∂(stdGauss (J × Fin n)) -
          ∫ W, (2 * (trH H' * k)) * Phi3 a H' T W (ψ x) ∂(stdGauss (J × Fin n)) := integral_sub i1 i2
    rw [e1, e2, integral_const_mul, integral_const, hw1, hw2]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    unfold C2 wC AxC HxC nsq kA AA
    rw [← hk, ← ha, ← hH']
    have e : ∑ i, (a i + 3 * k * trT T i) * (a i + 3 * k * trT T i) =
        ∑ i, (a i + 3 * k * trT T i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    ring

end BstLean.Part90

#print axioms BstLean.Part90.varWC
