import BstLean.Part33Defs

namespace BstLean.Part33

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (CoefIdx stdGauss unitOf cOf LOf aOf symOfRaw mapM qformC qformι AH AU keptOf frobSq
  coefX coeffS coefLaw gaussMom varOf)

variable {n : ℕ}

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma pow_integrable (a : ι → ℕ) :
    Integrable (fun z : ι → ℝ => ∏ i, z i ^ a i) (stdGauss ι) := by
  exact Integrable.fintype_prod (fun i =>
    integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) (a i))

private lemma eval_integrable (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply integrable_finset_sum
  intro d hd
  have he (z : ι → ℝ) : d.prod (fun i e => z i ^ e) = ∏ i, z i ^ d i := by
    exact Finsupp.prod_fintype _ _ (by simp)
  simp_rw [he]
  exact (pow_integrable d).const_mul _

private lemma mom_rec (a : ℕ) : gaussMom (a + 2) = (a + 1 : ℝ) * gaussMom a := by
  unfold gaussMom
  have h : Even (a + 2) ↔ Even a := by simp [Nat.even_add]
  simp only [h]
  split_ifs with ha
  · rw [show a + 2 - 1 = a + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    rfl
  · ring

private lemma power_radial (a : ι → ℕ) :
    ∫ z, (∑ i, z i ^ 2) * (∏ i, z i ^ a i) ∂stdGauss ι =
      ((Fintype.card ι : ℝ) + ∑ i, (a i : ℝ)) * ∫ z, (∏ i, z i ^ a i) ∂stdGauss ι := by
  classical
  have he (i : ι) (z : ι → ℝ) :
      z i ^ 2 * (∏ j, z j ^ a j) = ∏ j, z j ^ (a j + if j = i then 2 else 0) := by
    simp only [pow_add, Finset.prod_mul_distrib]
    simp [mul_comm, Finset.prod_ite_eq']
  simp_rw [Finset.sum_mul]
  have hi (i : ι) : Integrable (fun z : ι → ℝ => z i ^ 2 * ∏ j, z j ^ a j) (stdGauss ι) := by
    simp_rw [he]
    exact pow_integrable (fun j => a j + if j = i then 2 else 0)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [he]
  have hmom (b : ι → ℕ) : (∫ z : ι → ℝ, ∏ i, z i ^ b i ∂stdGauss ι) =
      ∏ i, gaussMom (b i) := by
    unfold stdGauss
    rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => x ^ b i)]
    simp_rw [BstLean.Part29.gaussMom_eq]
  simp_rw [hmom]
  have hm (i : ι) : (∏ j, gaussMom (a j + if j = i then 2 else 0)) =
      (a i + 1 : ℝ) * ∏ j, gaussMom (a j) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [ite_true, mom_rec]
    have hh : (∏ j ∈ Finset.univ.erase i, gaussMom (a j + if j = i then 2 else 0)) =
        ∏ j ∈ Finset.univ.erase i, gaussMom (a j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finset.ne_of_mem_erase hj]
    rw [hh]
    ring
  simp_rw [hm]
  rw [← Finset.sum_mul]
  congr 1
  simp [Finset.sum_add_distrib, add_comm]

/-- Euler/Stein: `E[‖Z‖² p(Z)] = (card ι + k) E[p(Z)]` for `p` homogeneous of degree `k`. -/
theorem stdGauss_normsq_mul (p : MvPolynomial ι ℝ) (k : ℕ) (hp : p.IsHomogeneous k) :
    ∫ z, (∑ i, z i ^ 2) * MvPolynomial.eval z p ∂stdGauss ι =
      ((Fintype.card ι : ℝ) + k) * ∫ z, MvPolynomial.eval z p ∂stdGauss ι := by
  classical
  have hmono (d : ι →₀ ℕ) (hd : d ∈ p.support) :
      ∫ z, (∑ i, z i ^ 2) * MvPolynomial.eval z (MvPolynomial.monomial d (p.coeff d)) ∂stdGauss ι =
        ((Fintype.card ι : ℝ) + k) *
          ∫ z, MvPolynomial.eval z (MvPolynomial.monomial d (p.coeff d)) ∂stdGauss ι := by
    have he (z : ι → ℝ) : d.prod (fun i e => z i ^ e) = ∏ i, z i ^ d i :=
      Finsupp.prod_fintype _ _ (by simp)
    simp only [MvPolynomial.eval_monomial, he]
    simp_rw [show ∀ z : ι → ℝ, (∑ i, z i ^ 2) * (p.coeff d * ∏ i, z i ^ d i) =
      p.coeff d * ((∑ i, z i ^ 2) * ∏ i, z i ^ d i) by intro z; ring]
    rw [integral_const_mul, integral_const_mul, power_radial]
    have hk : (∑ i, (d i : ℝ)) = (k : ℝ) := by
      rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum]
      rw [Finsupp.degree_apply]
      exact_mod_cast (hp.degree_eq_sum_deg_support hd).symm
    rw [hk]
    ring
  have hr (q : MvPolynomial ι ℝ) :
      Integrable (fun z => (∑ i, z i ^ 2) * MvPolynomial.eval z q) (stdGauss ι) := by
    convert eval_integrable ((∑ i : ι, MvPolynomial.X i ^ 2) * q) using 1
    funext z
    simp
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun d _ => hr _),
    integral_finsetSum _ (fun d _ => eval_integrable _), Finset.mul_sum]
  exact Finset.sum_congr rfl hmono

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def expectation : MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ z, MvPolynomial.eval z p ∂stdGauss ι
  map_add' p q := by
    simp only [MvPolynomial.eval_add]
    exact integral_add (eval_integrable p) (eval_integrable q)
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C, smul_eq_mul]
    exact integral_const_mul c _

/-- The cubic normalization: `E(X − λ‖z‖²/(D+2))² = E(X − λ)² − 2Eλ²/(D+2)` when `E[(X − λ)λ] = 0`. -/
theorem cubic_normalize_sq (X : MvPolynomial ι ℝ) (hX : X.IsHomogeneous 3) (ℓ : ι → ℝ)
    (horth : ∫ z, (MvPolynomial.eval z X - ∑ i, ℓ i * z i) * (∑ i, ℓ i * z i) ∂stdGauss ι = 0) :
    ∫ z, (MvPolynomial.eval z X - (∑ i, ℓ i * z i) * (∑ i, z i ^ 2) / ((Fintype.card ι : ℝ) + 2)) ^ 2
        ∂stdGauss ι =
      ∫ z, (MvPolynomial.eval z X - ∑ i, ℓ i * z i) ^ 2 ∂stdGauss ι
        - 2 * (∫ z, (∑ i, ℓ i * z i) ^ 2 ∂stdGauss ι) / ((Fintype.card ι : ℝ) + 2) := by
  classical
  let L : MvPolynomial ι ℝ := ∑ i, MvPolynomial.C (ℓ i) * MvPolynomial.X i
  let R : MvPolynomial ι ℝ := ∑ i, MvPolynomial.X i ^ 2
  let E := expectation (ι := ι)
  let d : ℝ := (Fintype.card ι : ℝ) + 2
  have hd : d ≠ 0 := by dsimp [d]; positivity
  have hL : L.IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  have hR : R.IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    exact MvPolynomial.isHomogeneous_X_pow _ _
  have eL (z : ι → ℝ) : MvPolynomial.eval z L = ∑ i, ℓ i * z i := by simp [L]
  have eR (z : ι → ℝ) : MvPolynomial.eval z R = ∑ i, z i ^ 2 := by simp [R]
  have radial (p : MvPolynomial ι ℝ) (k : ℕ) (hp : p.IsHomogeneous k) :
      E (R * p) = ((Fintype.card ι : ℝ) + k) * E p := by
    simpa only [E, expectation, LinearMap.coe_mk, AddHom.coe_mk,
      MvPolynomial.eval_mul, eR] using stdGauss_normsq_mul p k hp
  have ho : E (X * L) = E (L ^ 2) := by
    have hzero : E ((X - L) * L) = 0 := by
      simpa [E, expectation, MvPolynomial.eval_mul, MvPolynomial.eval_sub, eL] using horth
    have hh : (X - L) * L = X * L - L ^ 2 := by ring
    rw [hh, map_sub] at hzero
    linarith
  have hxl : E (R * (X * L)) = (d + 2) * E (L ^ 2) := by
    have hh := radial (X * L) 4 (hX.mul hL)
    rw [ho] at hh
    convert hh using 1 <;> dsimp [d] <;> ring
  have hlr : E (R * L ^ 2) = d * E (L ^ 2) := by
    exact radial (L ^ 2) 2 (hL.pow 2)
  have hlrr : E (R * (R * L ^ 2)) = (d + 2) * d * E (L ^ 2) := by
    have hh := radial (R * L ^ 2) 4 (hR.mul (hL.pow 2))
    rw [hlr] at hh
    convert hh using 1 <;> dsimp [d] <;> ring
  have hpoly : (X - (d⁻¹ : ℝ) • (L * R)) ^ 2 =
      X ^ 2 - (2 / d : ℝ) • (R * (X * L)) + (1 / d ^ 2 : ℝ) • (R * (R * L ^ 2)) := by
    have hc : (MvPolynomial.C (1 / d ^ 2) : MvPolynomial ι ℝ) = MvPolynomial.C d⁻¹ ^ 2 := by
      rw [show 1 / d ^ 2 = (d⁻¹) ^ 2 by simp [one_div, inv_pow]]
      exact MvPolynomial.C_pow _ _
    simp only [MvPolynomial.smul_eq_C_mul]
    rw [hc]
    simp only [div_eq_mul_inv, map_mul, map_ofNat]
    ring
  have hbase : (X - L) ^ 2 = X ^ 2 - (2 : ℝ) • (X * L) + L ^ 2 := by
    simp only [MvPolynomial.smul_eq_C_mul, map_ofNat]
    ring
  have heq : E ((X - (d⁻¹ : ℝ) • (L * R)) ^ 2) =
      E ((X - L) ^ 2) - 2 * E (L ^ 2) / d := by
    rw [hpoly, hbase]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hxl, hlrr, ho]
    field_simp [hd]
    <;> ring
  simpa [E, expectation, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_C, MvPolynomial.eval_mul, eL, eR, d, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using heq

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `stdGauss` is invariant under `z ↦ −z`. -/
theorem stdGauss_neg_invariant : (stdGauss ι).map (fun z => -z) = stdGauss ι := by
  unfold stdGauss
  change (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
    (fun z i => -z i) = _
  rw [Measure.pi_map_pi (fun _ => measurable_neg.aemeasurable)]
  simp only [gaussianReal_map_neg, neg_zero]

end

/-- Route B's radial moment: `E[‖Z‖² EF²] = (D + 4) E[EF²]`. -/
theorem normsq_EF_sq (A : Matrix (CoefIdx n) (CoefIdx n) ℝ) :
    ∫ Z, r2 Z * EF A Z ^ 2 ∂stdGauss (CoefIdx n) = (Dc n + 4) * ∫ Z, EF A Z ^ 2 ∂stdGauss (CoefIdx n) := by
  classical
  let B := A - (A.trace / Dc n) • (1 : Matrix (CoefIdx n) (CoefIdx n) ℝ)
  let q : MvPolynomial (CoefIdx n) ℝ :=
    ∑ i, ∑ j, MvPolynomial.C (B i j) * MvPolynomial.X i * MvPolynomial.X j
  have hq : q.IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    apply MvPolynomial.IsHomogeneous.sum
    intro j hj
    exact (MvPolynomial.isHomogeneous_C_mul_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)
  have he (z : CoefIdx n → ℝ) : MvPolynomial.eval z q = EF A z := by
    simp [q, EF, qformι, B]
  simpa only [MvPolynomial.eval_pow, he, Dc, r2, Nat.cast_ofNat] using
    stdGauss_normsq_mul (q ^ 2) 4 (hq.pow 2)


end BstLean.Part33
