import BstLean.Part56Orth_Residual
import BstLean.Part56Orth_Mean
import BstLean.Part56RKGErr_Kernel

/-! Joint laws of two linear Gaussian evaluations. -/
namespace BstLean.Part56.RKGErr

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono colM)
open BstLean.Part53 (linZ nsq)

variable {n d : ℕ}

private lemma gaussian_char {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∫ z, Complex.exp (((∑ i, z i * t i : ℝ) : ℂ) * Complex.I) ∂stdGauss ι) =
      Complex.exp ((-(∑ i, t i ^ 2 : ℝ) / 2 : ℝ) : ℂ) := by
  have h := ProbabilityTheory.charFun_stdGaussian (WithLp.toLp 2 t)
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)] at h
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq] at h
  simpa [BstLean.Part29.stdGauss, PiLp.inner_apply,
    EuclideanSpace.real_norm_sq_eq, mul_comm] using h

private lemma coef_sum (F : CoefIdxD n d → ℝ) :
    (∑ α, F α) = ∑ p : Mono n d, ∑ a : Fin n, F ⟨p.1, (p.2, a)⟩ := by
  classical
  let e := Equiv.sigmaProdDistrib (fun j : Fin (d + 1) => Sym (Fin n) j) (Fin n)
  have h := e.sum_comp F
  rw [Fintype.sum_prod_type] at h
  exact h.symm

noncomputable def linearPair (ψ χ : Mono n d → ℝ) (Z : CoefIdxD n d → ℝ) :
    (Fin n ⊕ Fin n) → ℝ := Sum.elim (linZ Z ψ) (linZ Z χ)

noncomputable def pairModel (a b ρ q : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n ⊕ Fin n) → ℝ := Sum.elim (a • z.1) (b • (ρ • z.1 + q • z.2))

private lemma linearPair_dot (ψ χ : Mono n d → ℝ) (Z : CoefIdxD n d → ℝ)
    (t : (Fin n ⊕ Fin n) → ℝ) :
    (∑ i, linearPair ψ χ Z i * t i) =
      ∑ α : CoefIdxD n d, Z α *
        (ψ ⟨α.1, α.2.1⟩ * t (.inl α.2.2) + χ ⟨α.1, α.2.1⟩ * t (.inr α.2.2)) := by
  classical
  rw [Fintype.sum_sum_type, coef_sum]
  simp only [linearPair, Sum.elim_inl, Sum.elim_inr, linZ, colM,
    Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a p => Z ⟨p.1, (p.2, a)⟩ * ψ p * t (.inl a)),
    Finset.sum_comm (f := fun a p => Z ⟨p.1, (p.2, a)⟩ * χ p * t (.inr a))]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro p hp <;>
    apply Finset.sum_congr rfl <;> intro a ha <;> ring

private lemma linearPair_energy (ψ χ : Mono n d → ℝ)
    (t : (Fin n ⊕ Fin n) → ℝ) :
    (∑ α : CoefIdxD n d,
      (ψ ⟨α.1, α.2.1⟩ * t (.inl α.2.2) + χ ⟨α.1, α.2.1⟩ * t (.inr α.2.2)) ^ 2) =
      ∑ a : Fin n, (nsq ψ * t (.inl a) ^ 2 + nsq χ * t (.inr a) ^ 2 +
        2 * (∑ p, ψ p * χ p) * (t (.inl a) * t (.inr a))) := by
  classical
  rw [coef_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have he (p : Mono n d) :
      (ψ p * t (.inl a) + χ p * t (.inr a)) ^ 2 =
        ψ p ^ 2 * t (.inl a) ^ 2 + χ p ^ 2 * t (.inr a) ^ 2 +
          (ψ p * χ p) * (2 * (t (.inl a) * t (.inr a))) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  simp only [nsq]
  ring

/-- A joint linear field has the correlated Gaussian pair law when its Gram entries match. -/
theorem linearPair_law (ψ χ : Mono n d → ℝ) (a b ρ q : ℝ)
    (hψ : nsq ψ = a ^ 2) (hχ : nsq χ = b ^ 2)
    (hcross : (∑ p, ψ p * χ p) = a * b * ρ) (hunit : ρ ^ 2 + q ^ 2 = 1) :
    (stdGauss (CoefIdxD n d)).map (linearPair ψ χ) =
      ((stdGauss (Fin n)).prod (stdGauss (Fin n))).map (pairModel a b ρ q) := by
  classical
  have hL : Measurable (linearPair ψ χ) := by
    apply Measurable.of_eval
    intro i
    cases i <;> simp only [linearPair, Sum.elim_inl, Sum.elim_inr, linZ, colM] <;> fun_prop
  have hR : Measurable (pairModel (n := n) a b ρ q) := by
    apply Measurable.of_eval
    intro i
    cases i <;> simp only [pairModel, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul] <;> fun_prop
  have he : ((stdGauss (CoefIdxD n d)).map (linearPair ψ χ)).map (WithLp.toLp 2) =
      (((stdGauss (Fin n)).prod (stdGauss (Fin n))).map (pairModel a b ρ q)).map
        (WithLp.toLp 2) := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, Measure.map_map (by fun_prop) hL,
      integral_map (by fun_prop) (by fun_prop)]
    rw [charFun_apply, Measure.map_map (by fun_prop) hR,
      integral_map (by fun_prop) (by fun_prop)]
    have hinner (x : (Fin n ⊕ Fin n) → ℝ) :
        inner ℝ (WithLp.toLp 2 x) t = ∑ i, x i * t i := by
      simp only [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      simp [RCLike.inner_apply, mul_comm]
    simp only [Function.comp_apply, hinner, linearPair_dot]
    rw [gaussian_char, linearPair_energy, hψ, hχ, hcross]
    have hd (z : (Fin n → ℝ) × (Fin n → ℝ)) :
        (∑ i, pairModel a b ρ q z i * t i) =
          (∑ i : Fin n, z.1 i * (a * t (.inl i) + b * ρ * t (.inr i))) +
          ∑ i : Fin n, z.2 i * (b * q * t (.inr i)) := by
      rw [Fintype.sum_sum_type]
      simp only [pairModel, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
        Pi.add_apply, smul_eq_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simp_rw [hd, Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [integral_prod_mul
      (fun z : Fin n → ℝ => Complex.exp
        (((∑ i, z i * (a * t (.inl i) + b * ρ * t (.inr i)) : ℝ) : ℂ) * Complex.I))
      (fun z : Fin n → ℝ => Complex.exp
        (((∑ i, z i * (b * q * t (.inr i)) : ℝ) : ℂ) * Complex.I)),
      gaussian_char, gaussian_char,
      ← Complex.exp_add, ← Complex.ofReal_add]
    congr 2
    have hterm (i : Fin n) :
        (a * t (.inl i) + b * ρ * t (.inr i)) ^ 2 + (b * q * t (.inr i)) ^ 2 =
          a ^ 2 * t (.inl i) ^ 2 + b ^ 2 * t (.inr i) ^ 2 +
            2 * (a * b * ρ) * (t (.inl i) * t (.inr i)) := by
      nlinarith [congrArg (fun r : ℝ => b ^ 2 * t (.inr i) ^ 2 * r) hunit]
    have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun i _ => hterm i)
    rw [Finset.sum_add_distrib] at hh
    linarith
  exact MeasurableEquiv.map_measurableEquiv_injective
    (MeasurableEquiv.toLp 2 ((Fin n ⊕ Fin n) → ℝ)) he

/-- The marginal law holds for zero as well as positive variance. -/
theorem linear_marginal_law (ψ : Mono n d → ℝ) (a : ℝ) (hψ : nsq ψ = a ^ 2) :
    (stdGauss (CoefIdxD n d)).map (fun Z => linZ Z ψ) =
      (stdGauss (Fin n)).map (fun g => a • g) := by
  have hpair := linearPair_law ψ ψ a a 1 0 hψ hψ
    (by simpa only [nsq, pow_two, mul_one] using hψ) (by norm_num)
  let π : ((Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ) := fun z i => z (.inl i)
  have hmπ : Measurable π := by unfold π; fun_prop
  have hL : Measurable (linearPair ψ ψ) := by
    apply Measurable.of_eval
    intro i
    cases i <;> simp only [linearPair, Sum.elim_inl, Sum.elim_inr, linZ, colM] <;> fun_prop
  have hR : Measurable (pairModel (n := n) a a 1 0) := by
    apply Measurable.of_eval
    intro i
    cases i <;> simp only [pairModel, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul] <;> fun_prop
  have he := congrArg (Measure.map π) hpair
  rw [Measure.map_map hmπ hL, Measure.map_map hmπ hR] at he
  change (stdGauss (CoefIdxD n d)).map (fun Z => linZ Z ψ) =
    ((stdGauss (Fin n)).prod (stdGauss (Fin n))).map (fun z => a • z.1) at he
  have hcomp : (fun z : (Fin n → ℝ) × (Fin n → ℝ) => a • z.1) =
      (fun g : Fin n → ℝ => a • g) ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod] at he
  simpa using he

theorem linear_marginal_integral (ψ : Mono n d → ℝ) (a : ℝ) (hψ : nsq ψ = a ^ 2)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    (∫ Z, F (linZ Z ψ) ∂stdGauss (CoefIdxD n d)) =
      ∫ g, F (a • g) ∂stdGauss (Fin n) := by
  have hL : Measurable (fun Z : CoefIdxD n d → ℝ => linZ Z ψ) := by
    unfold linZ colM
    fun_prop
  calc
    _ = ∫ z, F z ∂(stdGauss (CoefIdxD n d)).map (fun Z => linZ Z ψ) :=
      (integral_map hL.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by
      rw [linear_marginal_law ψ a hψ]
      exact integral_map (by fun_prop) hF.aestronglyMeasurable

end BstLean.Part56.RKGErr
