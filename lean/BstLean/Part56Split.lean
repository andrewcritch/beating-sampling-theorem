import BstLean.Part56Defs

/-!
# Part 56, wave 1: the Gaussian split `Z = Π Z + (Z − Π Z)`

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56Split`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Proof route: for each output column `a`, `Z_{·,a}` is standard Gaussian in `ℝ^N` and `Π` is an orthogonal
projection (symmetric, idempotent: the blocks `φ_j(v)` have disjoint supports and `k_j(v,v) > 0` for
`v ≠ 0`). Hence `(Π Z, (I − Π) Z)` has the law of `(Π Z, (I − Π) Z')` with `Z'` an independent copy
(Gaussian vectors with zero cross-covariance are independent). Use `Measure.pi`, the characteristic
function or the rotation invariance of `stdGauss` (Part 48's `Part48Rot.lean`, Part 53's `Part53Polar.lean`).
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob Tens TSymm Pn NN baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (LemmaR53 GaussPolar53)
open BstLean.Part48 (SBLevel)

private lemma projA_apply {n d : ℕ} (v : Fin n → ℝ)
    (Z : CoefIdxD n d → ℝ) (α : CoefIdxD n d) :
    projA v Z α = BstLean.Part41.phiM v ⟨α.1, α.2.1⟩ / kJ d α.1 v v *
      ∑ p : Mono n d, phiB d α.1 v p * Z ⟨p.1, (p.2, α.2.2)⟩ := by
  classical
  unfold projA
  rw [Finset.sum_eq_single (α.1 : ℕ)]
  · simp [phiB]
  · intro j hj hne
    simp [phiB, Ne.symm hne]
  · intro h
    exact (h (Finset.mem_range.mpr α.1.isLt)).elim

private lemma kJ_block {n d : ℕ} (v : Fin n → ℝ) (j : Fin (d + 1)) :
    kJ d j v v = ∑ p : Sym (Fin n) j, BstLean.Part41.phiM v ⟨j, p⟩ ^ 2 := by
  classical
  unfold kJ
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp [phiB, sq]
  · intro b hb hne
    have hn : (b : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
    simp [phiB, hn]
  · simp

private lemma projA_block {n d : ℕ} (v : Fin n → ℝ)
    (Z : CoefIdxD n d → ℝ) (α : CoefIdxD n d) :
    projA v Z α = BstLean.Part41.phiM v ⟨α.1, α.2.1⟩ / kJ d α.1 v v *
      ∑ p : Sym (Fin n) α.1, BstLean.Part41.phiM v ⟨α.1, p⟩ * Z ⟨α.1, (p, α.2.2)⟩ := by
  classical
  rw [projA_apply, Fintype.sum_sigma]
  congr 1
  rw [Finset.sum_eq_single α.1]
  · simp [phiB]
  · intro b hb hne
    have hn : (b : ℕ) ≠ (α.1 : ℕ) := fun h => hne (Fin.ext h)
    simp [phiB, hn]
  · simp

private lemma projA_idem {n d : ℕ} (v : Fin n → ℝ)
    (Z : CoefIdxD n d → ℝ) : projA v (projA v Z) = projA v Z := by
  classical
  funext α
  simp only [projA_block]
  by_cases h : kJ d α.1 v v = 0
  · simp [h]
  · have he : (∑ p : Sym (Fin n) α.1,
        BstLean.Part41.phiM v ⟨α.1, p⟩ *
          (BstLean.Part41.phiM v ⟨α.1, p⟩ / kJ d α.1 v v *
            ∑ q : Sym (Fin n) α.1, BstLean.Part41.phiM v ⟨α.1, q⟩ *
              Z ⟨α.1, (q, α.2.2)⟩)) =
        (∑ p : Sym (Fin n) α.1, BstLean.Part41.phiM v ⟨α.1, p⟩ ^ 2) /
          kJ d α.1 v v *
            ∑ q : Sym (Fin n) α.1, BstLean.Part41.phiM v ⟨α.1, q⟩ *
              Z ⟨α.1, (q, α.2.2)⟩ := by
      simp only [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [he, ← kJ_block, div_self h, one_mul]

private lemma projA_symm {n d : ℕ} (v : Fin n → ℝ)
    (X Y : CoefIdxD n d → ℝ) :
    (∑ α, projA v X α * Y α) = ∑ α, X α * projA v Y α := by
  classical
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, projA_block]
  apply Finset.sum_congr rfl
  intro j hj
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hL (p : Sym (Fin n) j) :
      (BstLean.Part41.phiM v ⟨j, p⟩ / kJ d j v v *
        ∑ q : Sym (Fin n) j, BstLean.Part41.phiM v ⟨j, q⟩ * X ⟨j, (q, a)⟩) *
          Y ⟨j, (p, a)⟩ =
      ((∑ q : Sym (Fin n) j, BstLean.Part41.phiM v ⟨j, q⟩ * X ⟨j, (q, a)⟩) /
        kJ d j v v) * (BstLean.Part41.phiM v ⟨j, p⟩ * Y ⟨j, (p, a)⟩) := by ring
  have hR (p : Sym (Fin n) j) :
      X ⟨j, (p, a)⟩ * (BstLean.Part41.phiM v ⟨j, p⟩ / kJ d j v v *
        ∑ q : Sym (Fin n) j, BstLean.Part41.phiM v ⟨j, q⟩ * Y ⟨j, (q, a)⟩) =
      ((∑ q : Sym (Fin n) j, BstLean.Part41.phiM v ⟨j, q⟩ * Y ⟨j, (q, a)⟩) /
        kJ d j v v) * (BstLean.Part41.phiM v ⟨j, p⟩ * X ⟨j, (p, a)⟩) := by ring
  simp_rw [hL, hR]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

private lemma gaussian_char {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∫ z, Complex.exp (((∑ i, z i * t i : ℝ) : ℂ) * Complex.I) ∂stdGauss ι) =
      Complex.exp ((-(∑ i, t i ^ 2 : ℝ) / 2 : ℝ) : ℂ) := by
  have h := ProbabilityTheory.charFun_stdGaussian (WithLp.toLp 2 t)
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)] at h
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq] at h
  simpa [BstLean.Part29.stdGauss, PiLp.inner_apply,
    EuclideanSpace.real_norm_sq_eq, mul_comm] using h

private lemma split_preserving {ι : Type*} [Fintype ι]
    (P : (ι → ℝ) → (ι → ℝ)) (hP : Measurable P)
    (hS : ∀ x y, (∑ i, P x i * y i) = ∑ i, x i * P y i)
    (hI : ∀ x, P (P x) = P x) :
    MeasurePreserving (fun z : (ι → ℝ) × (ι → ℝ) => P z.1 + (z.2 - P z.2))
      ((stdGauss ι).prod (stdGauss ι)) (stdGauss ι) := by
  classical
  let S := fun z : (ι → ℝ) × (ι → ℝ) => P z.1 + (z.2 - P z.2)
  have hm : Measurable S := (hP.comp measurable_fst).add
    (measurable_snd.sub (hP.comp measurable_snd))
  refine ⟨hm, ?_⟩
  have he : (((stdGauss ι).prod (stdGauss ι)).map S).map (WithLp.toLp 2) =
      (stdGauss ι).map (WithLp.toLp 2) := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, Measure.map_map (by fun_prop) hm,
      integral_map (by fun_prop) (by fun_prop)]
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    have hinner (x : ι → ℝ) :
        inner ℝ (WithLp.toLp 2 x) t = ∑ i, x i * t i := by
      simp only [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      simp [RCLike.inner_apply, mul_comm]
    simp only [Function.comp_apply, hinner]
    change (∫ z, Complex.exp (((∑ i, S z i * t i : ℝ) : ℂ) * Complex.I)
      ∂(stdGauss ι).prod (stdGauss ι)) =
      ∫ z, Complex.exp (((∑ i, z i * t i : ℝ) : ℂ) * Complex.I) ∂stdGauss ι
    have hd (z : (ι → ℝ) × (ι → ℝ)) :
        (∑ i, S z i * t i) = (∑ i, z.1 i * P (WithLp.ofLp t) i) +
          ∑ i, z.2 i * (t i - P (WithLp.ofLp t) i) := by
      simp only [S, Pi.add_apply, Pi.sub_apply, add_mul, sub_mul,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, hS, mul_sub]
    simp_rw [hd, Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [integral_prod_mul
      (fun z : ι → ℝ => Complex.exp (((∑ i, z i * P (WithLp.ofLp t) i : ℝ) : ℂ) * Complex.I))
      (fun z : ι → ℝ => Complex.exp (((∑ i, z i * (t i - P (WithLp.ofLp t) i) : ℝ) : ℂ) * Complex.I))]
    rw [gaussian_char, gaussian_char, gaussian_char,
      ← Complex.exp_add, ← Complex.ofReal_add]
    congr 2
    have ho := hS (WithLp.ofLp t) (P (WithLp.ofLp t))
    rw [hI] at ho
    have hn : (∑ i, (P (WithLp.ofLp t) i) ^ 2) +
        (∑ i, (t i - P (WithLp.ofLp t) i) ^ 2) = ∑ i, t i ^ 2 := by
      have hf : (∑ i, (t i - P (WithLp.ofLp t) i) ^ 2) =
          (∑ i, t i ^ 2) - 2 * (∑ i, t i * P (WithLp.ofLp t) i) +
            ∑ i, (P (WithLp.ofLp t) i) ^ 2 := by
        calc
          _ = ∑ i, (t i ^ 2 - 2 * (t i * P (WithLp.ofLp t) i) +
              (P (WithLp.ofLp t) i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [← sq] at ho
      rw [hf]
      linarith
    linarith
  exact MeasurableEquiv.map_measurableEquiv_injective (MeasurableEquiv.toLp 2 (ι → ℝ)) he

/-- **Gaussian split.** -/
theorem propSplit56 (d : ℕ) : PropSplit56 d := by
  classical
  intro n v hv F hF
  have hP : Measurable (projA (d := d) v) := by
    unfold projA
    fun_prop
  have h := split_preserving (projA (d := d) v) hP (projA_symm v) (projA_idem v)
  rw [← h.lintegral_comp hF]
  exact lintegral_prod _ (hF.comp h.measurable).aemeasurable

end BstLean.Part56
