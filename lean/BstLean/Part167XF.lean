import BstLean.Part167Frame

/-!
# Part 167 (file `XF`): the Agent weights `A₁` in the frame (sub-lemma 5, second step)

No proof is left open; no `native_decide` or `axiom` is used.

Write each row of `A₁` as `√γ·R(z_i, t_i, Γ_i)` (file `Frame`), with `W_i = (z_i, t_i, Γ_i)` independent
and distributed as `ν = N(0,1) ⊗ N(0,1) ⊗ N(0, I_{n−2})`.

* **`gaussMat_frame`**: `gaussMat m n γ` is the image of `ν^{⊗m}` under `W ↦ (√γ R(W_i))_i`.
* **`frame_reads`**: in the frame, `(A₁x)_i = √γ z_i`, `(A₁u)_i = √γ(s z_i + c t_i)` and
  `|a_i|² = γ(z_i² + t_i² + |Γ_i|²)`: the quantities that `planeP`, the gates and `D₁` read
  (file `Adm`, `hT_adm`) depend on `Γ_i` only through `|Γ_i|`.
* **`latSq_vecMul_frame`**: `latSq((D₁A₁)ᵀp, u, w) = |Σ_i √γ p_i D_i Γ_i|²`.
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part151 (mask)

variable {n m : ℕ}

/-- The matrix of rows `√γ·R(W_i)`. -/
noncomputable def Aframe (γ : ℝ) (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ)
    (W : Fin m → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => √γ * Rmap x e' (W i).1 (W i).2.1 (W i).2.2 j

lemma measurable_Rmap (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ) :
    Measurable (fun p : ℝ × ℝ × (Fin (n - 1 - 1) → ℝ) => Rmap x e' p.1 p.2.1 p.2.2) := by
  unfold Rmap
  exact (BstLean.Part161.measurable_hh x).comp (BstLean.Part161.measurable_consV.comp
    (measurable_fst.prodMk ((BstLean.Part161.measurable_hh e').comp
      (BstLean.Part161.measurable_consV.comp measurable_snd))))

/-- **`A₁` in the frame.** -/
theorem gaussMat_frame (hn : 2 ≤ n) (γ : ℝ) (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ) :
    gaussMat m n γ = (Measure.pi fun _ : Fin m =>
      (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1 - 1))))).map
      (Aframe γ x e') := by
  rw [gaussMat_rows γ]
  have hR := row_frame hn x e'
  have hRm := measurable_Rmap x e'
  have hpi : (Measure.pi fun _ : Fin m => stdGauss (Fin n)) =
      (Measure.pi fun _ : Fin m =>
        (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1 - 1))))).map
        (fun W i => Rmap x e' (W i).1 (W i).2.1 (W i).2.2) := by
    rw [Measure.pi_map_pi (fun _ => hRm.aemeasurable)]
    simp_rw [hR]
  have hS : Measurable (fun G : Fin m → Fin n → ℝ => Matrix.of fun i j => √γ * G i j) := by
    have hc : Continuous (fun G : Fin m → Fin n → ℝ => fun i j => √γ * G i j) := by fun_prop
    exact hc.measurable
  have hW : Measurable (fun (W : Fin m → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) i =>
      Rmap x e' (W i).1 (W i).2.1 (W i).2.2) :=
    measurable_pi_iff.mpr fun i => hRm.comp (measurable_pi_apply i)
  rw [hpi, Measure.map_map hS hW]
  rfl

section reads

variable {u w : Fin n → ℝ} {s c : ℝ}

/-- **What the Agent quantities read, in the frame.** -/
theorem frame_reads (hn : 2 ≤ n) (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + c ^ 2 = 1) {γ : ℝ} (hγ : 0 ≤ γ)
    (W : Fin m → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) (i : Fin m) :
    (Aframe γ (s • u + c • w) (eprime hn u w s c) W *ᵥ (s • u + c • w)) i = √γ * (W i).1 ∧
    (Aframe γ (s • u + c • w) (eprime hn u w s c) W *ᵥ u) i =
      √γ * (s * (W i).1 + c * (W i).2.1) ∧
    ∑ j, Aframe γ (s • u + c • w) (eprime hn u w s c) W i j ^ 2 =
      γ * ((W i).1 ^ 2 + (W i).2.1 ^ 2 + normSq (W i).2.2) := by
  obtain ⟨h1, h2, h3⟩ := frame_coords hn hu hw huw hsc (W i).1 (W i).2.1 (W i).2.2
  set R := Rmap (s • u + c • w) (eprime hn u w s c) (W i).1 (W i).2.1 (W i).2.2
  have hmv : ∀ y : Fin n → ℝ, (Aframe γ (s • u + c • w) (eprime hn u w s c) W *ᵥ y) i =
      √γ * ∑ j, R j * y j := by
    intro y
    simp only [Aframe, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨by rw [hmv, h1], ?_, ?_⟩
  · rw [hmv]
    congr 1
    set A := ∑ j, R j * u j
    set B := ∑ j, R j * w j
    have e1 : ∑ j, R j * (s • u + c • w) j = s * A + c * B := by
      simp only [A, B, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, R j * xperp u w s c j = c * A - s * B := by
      simp only [A, B, xperp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
        Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1] at h1; rw [e2] at h2
    rw [← h1, ← h2]
    have : A = s * (s * A + c * B) + c * (c * A - s * B) := by
      have : A * (s ^ 2 + c ^ 2) = A := by rw [hsc, mul_one]
      nlinarith
    exact this
  · simp only [Aframe, Matrix.of_apply, mul_pow, Real.sq_sqrt hγ, ← Finset.mul_sum]
    congr 1

/-- **`latSq` of `(D₁A₁)ᵀp` in the frame.** -/
theorem latSq_vecMul_frame (hn : 2 ≤ n) (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + c ^ 2 = 1) (γ : ℝ)
    (W : Fin m → ℝ × ℝ × (Fin (n - 1 - 1) → ℝ)) (p : Fin m → ℝ) :
    latSq (vecMul p (D1A1 (Aframe γ (s • u + c • w) (eprime hn u w s c) W) (s • u + c • w))) u w =
      normSq (∑ i, (√γ * p i * mask ((Aframe γ (s • u + c • w) (eprime hn u w s c) W *ᵥ
        (s • u + c • w)) i)) • (W i).2.2) := by
  set A := Aframe γ (s • u + c • w) (eprime hn u w s c) W
  set cf : Fin m → ℝ := fun i => √γ * p i * mask ((A *ᵥ (s • u + c • w)) i)
  have hv : vecMul p (D1A1 A (s • u + c • w)) =
      ∑ i, cf i • Rmap (s • u + c • w) (eprime hn u w s c) (W i).1 (W i).2.1 (W i).2.2 := by
    funext j
    simp only [vecMul, dotProduct, D1A1, A, Aframe, Matrix.of_apply, cf, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hv, R_sum, latSq_frame hn hu hw huw hsc]

end reads

end BstLean.Part167
