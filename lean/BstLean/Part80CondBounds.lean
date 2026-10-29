import BstLean.Part80Defs
import BstLean.Part56Weights

/-!
# Part 80: the conditional bounds `CondBoundsA` from the exact identities `MeanIdsA`
-/

namespace BstLean.Part80

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part56 (integrable_cont_sph56)
open BstLean.Part78 (nsq frobH trH qfun aU zv)

section
variable {n : ℕ}

/-- `(E u)² ≤ E u²`. -/
lemma sq_int_le {ν : Measure (Fin n → ℝ)} (hν : SphLaw n ν) {u : (Fin n → ℝ) → ℝ}
    (hu : Continuous u) : (∫ x, u x ∂ν) ^ 2 ≤ ∫ x, u x ^ 2 ∂ν := by
  have := hν.prob
  set m := ∫ x, u x ∂ν with hm
  have h : 0 ≤ ∫ x, (u x - m) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have he : (fun x => (u x - m) ^ 2) = fun x => (u x ^ 2 - (2 * m) * u x) + m ^ 2 := by
    funext x; ring
  have i1 : Integrable (fun x => u x ^ 2) ν := integrable_cont_sph56 hν (hu.pow 2)
  have i2 : Integrable (fun x => (2 * m) * u x) ν := (integrable_cont_sph56 hν hu).const_mul _
  have i12 : Integrable (fun x => u x ^ 2 - (2 * m) * u x) ν := i1.sub i2
  rw [he, integral_add i12 (integrable_const _), integral_sub i1 i2, integral_const_mul,
    integral_const, ← hm] at h
  simp at h
  nlinarith

/-- `E_{x,y} Σ_r u_r(x) u_r(y) = Σ_r (E u_r)²`. -/
lemma dbl_int {ν : Measure (Fin n → ℝ)} (hν : SphLaw n ν) {R : Type} [Fintype R]
    (u : R → (Fin n → ℝ) → ℝ) (hu : ∀ r, Continuous (u r)) :
    ∫ x, ∫ y, ∑ r, u r x * u r y ∂ν ∂ν = ∑ r, (∫ x, u r x ∂ν) ^ 2 := by
  have hin (x : Fin n → ℝ) : ∫ y, ∑ r, u r x * u r y ∂ν = ∑ r, u r x * ∫ y, u r y ∂ν := by
    rw [integral_finsetSum _ fun r _ => (integrable_cont_sph56 hν (hu r)).const_mul _]
    simp only [integral_const_mul]
  simp only [hin]
  rw [integral_finsetSum _ fun r _ => (integrable_cont_sph56 hν (hu r)).mul_const _]
  simp only [integral_mul_const]
  exact Finset.sum_congr rfl fun r _ => by ring

variable {J : Type} [Fintype J]

/-- Bessel inequality from the feature operator bound. -/
lemma besselA {ν : Measure (Fin n → ℝ)} (hν : SphLaw n ν) {ψ : (Fin n → ℝ) → J → ℝ}
    (hψ : Continuous ψ) {Γ : ℝ} (hΓ : 0 ≤ Γ) (hF : FeatOpA ν ψ Γ)
    (r : (Fin n → ℝ) → ℝ) (hr : Continuous r) :
    ∑ q : J, (∫ x, r x * ψ x q ∂ν) ^ 2 ≤ Γ * ∫ x, r x ^ 2 ∂ν := by
  have hψq (q : J) : Continuous fun x => ψ x q := (continuous_apply q).comp hψ
  have sint {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f ν :=
    integrable_cont_sph56 hν hf
  set c : J → ℝ := fun q => ∫ x, r x * ψ x q ∂ν with hc
  set g : (Fin n → ℝ) → ℝ := fun x => ∑ q, c q * ψ x q with hg
  have hgc : Continuous g := continuous_finsetSum _ fun q _ => continuous_const.mul (hψq q)
  set S := ∑ q : J, c q ^ 2 with hS
  set R := ∫ x, r x ^ 2 ∂ν with hR
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hrg : ∫ x, r x * g x ∂ν = S := by
    have he : (fun x => r x * g x) = fun x => ∑ q, c q * (r x * ψ x q) := by
      funext x; simp only [hg, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    have hi (q : J) : Integrable (fun x => c q * (r x * ψ x q)) ν :=
      (sint (hr.mul (hψq q))).const_mul _
    rw [he, integral_finsetSum _ fun q _ => hi q]
    simp only [integral_const_mul, hS]
    exact Finset.sum_congr rfl fun q _ => by simp only [hc]; ring
  have hgg : ∫ x, g x ^ 2 ∂ν ≤ Γ * S := hF c
  have hquad (t : ℝ) : 0 ≤ t ^ 2 * (Γ * S) - 2 * t * S + R := by
    have h : 0 ≤ ∫ x, (t * g x - r x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : (fun x => (t * g x - r x) ^ 2) = fun x =>
        (t ^ 2 * g x ^ 2 - (2 * t) * (r x * g x)) + r x ^ 2 := by funext x; ring
    have i1 : Integrable (fun x => t ^ 2 * g x ^ 2) ν := (sint (hgc.pow 2)).const_mul _
    have i2 : Integrable (fun x => (2 * t) * (r x * g x)) ν := (sint (hr.mul hgc)).const_mul _
    have i3 : Integrable (fun x => r x ^ 2) ν := sint (hr.pow 2)
    have i12 : Integrable (fun x => t ^ 2 * g x ^ 2 - (2 * t) * (r x * g x)) ν := i1.sub i2
    rw [he, integral_add i12 i3, integral_sub i1 i2, integral_const_mul,
      integral_const_mul, hrg] at h
    nlinarith [sq_nonneg t]
  rcases hΓ.lt_or_eq with hpos | hzero
  · have h := hquad (1 / Γ)
    have e : (1 / Γ) ^ 2 * (Γ * S) - 2 * (1 / Γ) * S + R = R - S / Γ := by
      field_simp; ring
    rw [e] at h
    have : S / Γ ≤ R := by linarith
    rw [div_le_iff₀ hpos] at this
    linarith
  · rw [← hzero, zero_mul]
    by_contra hcon
    rw [not_le] at hcon
    have h := hquad ((R + 1) / (2 * S))
    rw [← hzero] at h
    have e : (R + 1) / (2 * S) * S = (R + 1) / 2 := by field_simp
    nlinarith

end

theorem condBoundsA (hM : MeanIdsA) : CondBoundsA := by
  intro n J _ ν hν f0 ℓ H hH mu ψ hmu hψ Γ S I hΓ hF hb
  obtain ⟨-, -, -, hE, hV⟩ := hM n J ν hν f0 ℓ H hH mu ψ hmu hψ
  have := hν.prob
  have sint {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f ν :=
    integrable_cont_sph56 hν hf
  have sint2 {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable (fun x => f x ^ 2) ν :=
    sint (hf.pow 2)
  have sintm {f g : (Fin n → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
      Integrable (fun x => (f x * g x) ^ 2) ν := sint ((hf.mul hg).pow 2)
  have hψq (q : J) : Continuous fun x => ψ x q := (continuous_apply q).comp hψ
  have hmuj (j : Fin n) : Continuous fun x => mu x j := (continuous_apply j).comp hmu
  have ha (i : Fin n) : Continuous fun x => aA ℓ H mu x i := by
    unfold aA aU
    exact continuous_const.add (continuous_const.mul
      (continuous_finsetSum _ fun j _ => continuous_const.mul (hmuj j)))
  have hk : Continuous (kA ψ) := continuous_finsetSum _ fun q _ => (hψq q).pow 2
  have hA : Continuous fun x => nsq (aA ℓ H mu x) :=
    continuous_finsetSum _ fun i _ => (ha i).pow 2
  have hk0 (x : Fin n → ℝ) : 0 ≤ kA ψ x := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hv0 : 0 ≤ frobH H :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- double-integral formulas
  have hTa : TaA ν ℓ H mu ψ = ∑ i, ∑ q, (∫ x, aA ℓ H mu x i * ψ x q ∂ν) ^ 2 := by
    have := dbl_int hν (R := Fin n × J) (fun r x => aA ℓ H mu x r.1 * ψ x r.2)
      (fun r => (ha r.1).mul (hψq r.2))
    rw [Fintype.sum_prod_type] at this
    rw [← this]
    unfold TaA KA
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring
  have hS2 : S2A ν ψ = ∑ p, ∑ q, (∫ x, ψ x p * ψ x q ∂ν) ^ 2 := by
    have := dbl_int hν (R := J × J) (fun r x => ψ x r.1 * ψ x r.2)
      (fun r => (hψq r.1).mul (hψq r.2))
    rw [Fintype.sum_prod_type] at this
    rw [← this]
    unfold S2A KA
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring
  -- single-integral expansions
  have hAint : ∫ x, nsq (aA ℓ H mu x) ∂ν = ∑ i, ∫ x, aA ℓ H mu x i ^ 2 ∂ν := by
    unfold nsq
    exact integral_finsetSum _ fun i _ => sint2 (ha i)
  have heint : eA ν ψ = ∑ q, ∫ x, ψ x q ^ 2 ∂ν := by
    unfold eA kA
    exact integral_finsetSum _ fun q _ => sint2 (hψq q)
  have hAk : ∫ x, nsq (aA ℓ H mu x) * kA ψ x ∂ν =
      ∑ i, ∑ q, ∫ x, (aA ℓ H mu x i * ψ x q) ^ 2 ∂ν := by
    have he : (fun x => nsq (aA ℓ H mu x) * kA ψ x) =
        fun x => ∑ i, ∑ q, (aA ℓ H mu x i * ψ x q) ^ 2 := by
      funext x; unfold nsq kA; rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring
    rw [he]
    refine (integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun q _ => sintm (ha i) (hψq q)).trans ?_
    exact Finset.sum_congr rfl fun i _ =>
      integral_finsetSum _ fun q _ => sintm (ha i) (hψq q)
  have hkk : ∫ x, kA ψ x ^ 2 ∂ν = ∑ p, ∑ q, ∫ x, (ψ x p * ψ x q) ^ 2 ∂ν := by
    have he : (fun x => kA ψ x ^ 2) = fun x => ∑ p, ∑ q, (ψ x p * ψ x q) ^ 2 := by
      funext x; unfold kA; rw [pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring
    rw [he]
    refine (integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun q _ => sintm (hψq i) (hψq q)).trans ?_
    exact Finset.sum_congr rfl fun i _ =>
      integral_finsetSum _ fun q _ => sintm (hψq i) (hψq q)
  -- the bounds
  have hAS : ∫ x, nsq (aA ℓ H mu x) ∂ν ≤ S := by
    have : ∫ x, nsq (aA ℓ H mu x) ∂ν ≤ ∫ _x, S ∂ν :=
      integral_mono_ae (sint hA) (integrable_const _)
        (hν.sphere.mono fun x hx => (hb x hx).1)
    simpa using this
  have he2 : eA ν ψ ≤ 2 := by
    have : ∫ x, kA ψ x ∂ν ≤ ∫ _x, (2 : ℝ) ∂ν :=
      integral_mono_ae (sint hk) (integrable_const _)
        (hν.sphere.mono fun x hx => (hb x hx).2.2)
    unfold eA
    simpa using this
  have he0 : 0 ≤ eA ν ψ := integral_nonneg hk0
  have hTa1 : TaA ν ℓ H mu ψ ≤ Γ * S := by
    have h1 : TaA ν ℓ H mu ψ ≤ Γ * ∫ x, nsq (aA ℓ H mu x) ∂ν := by
      rw [hTa, hAint, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => besselA hν hψ hΓ hF _ (ha i)
    exact h1.trans (mul_le_mul_of_nonneg_left hAS hΓ)
  have hS21 : S2A ν ψ ≤ Γ * eA ν ψ := by
    rw [hS2, heint, Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => besselA hν hψ hΓ hF _ (hψq p)
  have hTa2 : TaA ν ℓ H mu ψ ≤ ∫ x, nsq (aA ℓ H mu x) * kA ψ x ∂ν := by
    rw [hTa, hAk]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun q _ =>
      sq_int_le hν ((ha i).mul (hψq q))
  have hS22 : S2A ν ψ ≤ ∫ x, kA ψ x ^ 2 ∂ν := by
    rw [hS2, hkk]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun q _ =>
      sq_int_le hν ((hψq i).mul (hψq q))
  have hee : eA ν ψ ^ 2 ≤ ∫ x, kA ψ x ^ 2 ∂ν := sq_int_le hν hk
  have hIe : I * eA ν ψ ≤ ∫ x, nsq (aA ℓ H mu x) * kA ψ x ∂ν := by
    unfold eA
    rw [← integral_const_mul]
    exact integral_mono_ae ((sint hk).const_mul _) (sint (hA.mul hk))
      (hν.sphere.mono fun x hx => mul_le_mul_of_nonneg_right (hb x hx).2.1 (hk0 x))
  have hvar : 0 ≤ varU ν (PhiA f0 ℓ H mu ψ) := integral_nonneg fun x => sq_nonneg _
  have p1 : frobH H * S2A ν ψ ≤ frobH H * (Γ * eA ν ψ) := mul_le_mul_of_nonneg_left hS21 hv0
  have p2 : frobH H * (Γ * eA ν ψ) ≤ frobH H * (Γ * 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he2 hΓ) hv0
  have p3 : frobH H * eA ν ψ ^ 2 ≤ frobH H * ∫ x, kA ψ x ^ 2 ∂ν :=
    mul_le_mul_of_nonneg_left hee hv0
  have p4 : frobH H * S2A ν ψ ≤ frobH H * ∫ x, kA ψ x ^ 2 ∂ν :=
    mul_le_mul_of_nonneg_left hS22 hv0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE]; nlinarith
  · rw [hV]; nlinarith
  · rw [hV]; nlinarith
  · rw [hV]; nlinarith

#print axioms condBoundsA

end BstLean.Part80
