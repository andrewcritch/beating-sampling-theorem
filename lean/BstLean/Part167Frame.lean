import BstLean.Part167Y

/-!
# Part 167 (file `Frame`): the two-reflection frame of a row of `A₁` (sub-lemma 5, first step)

No proof is left open; no `native_decide` or `axiom` is used.

For a unit input `x` in the plane of an orthonormal pair `(u, w)` (`x = su + cw`, `s² + c² = 1`),
put `x⊥ = cu − sw`, `H = H_x` (Part 161's reflection, `H e₀ = x`) and `e' = tail(H x⊥)` (a unit
vector of `ℝ^{n−1}`), `H' = H_{e'}`. For `(z, t, Γ) ∈ ℝ × ℝ × ℝ^{n−2}` put
`R(z, t, Γ) = H·(z, H'·(t, Γ))`.

* **`row_frame`**: `R` sends `N(0,1) ⊗ N(0,1) ⊗ N(0, I_{n−2})` to `N(0, I_n)`.
* **`frame_coords`**: `⟨R, x⟩ = z`, `⟨R, x⊥⟩ = t`, `|R|² = z² + t² + |Γ|²`.
* **`latSq_frame`**: `latSq(R(z, t, Γ), u, w) = |Γ|²`, and `R` is linear (`R_add`, `R_smul`), so
  `latSq(Σ_i c_i R(z_i, t_i, Γ_i)) = |Σ_i c_i Γ_i|²`: the paper's `|P_lat Σ c_i a_i|`.
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part161 (hhMat consV hh_dot hh_e0 hh_normSq normSq_consV consV_zero consV_map
  stdGauss_map_hh measurable_hh measurable_consV hh_symm)

variable {n : ℕ}

/-- The frame map `R(z, t, Γ) = H_x·(z, H_{e'}·(t, Γ))`. -/
noncomputable def Rmap (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ) (z t : ℝ)
    (Γ : Fin (n - 1 - 1) → ℝ) : Fin n → ℝ :=
  (hhMat x).mulVec (consV z ((hhMat e').mulVec (consV t Γ)))

/-- **The frame map keeps the standard Gaussian distribution.** -/
theorem row_frame (hn : 2 ≤ n) (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ) :
    ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1 - 1))))).map
      (fun p => Rmap x e' p.1 p.2.1 p.2.2) = stdGauss (Fin n) := by
  have hK : Measurable (fun q : ℝ × (Fin (n - 1 - 1) → ℝ) =>
      (hhMat e').mulVec (consV (n := n - 1) q.1 q.2)) :=
    (measurable_hh e').comp measurable_consV
  have inner : ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1 - 1)))).map
      (fun q => (hhMat e').mulVec (consV (n := n - 1) q.1 q.2)) = stdGauss (Fin (n - 1)) := by
    rw [show (fun q : ℝ × (Fin (n - 1 - 1) → ℝ) => (hhMat e').mulVec (consV (n := n - 1) q.1 q.2)) =
      (fun ξ => (hhMat e').mulVec ξ) ∘ (fun q : ℝ × (Fin (n - 1 - 1) → ℝ) =>
        consV (n := n - 1) q.1 q.2) from rfl,
      ← Measure.map_map (measurable_hh e') measurable_consV, consV_map (n := n - 1) (by omega),
      stdGauss_map_hh]
  have hprod : (gaussianReal 0 1).prod (stdGauss (Fin (n - 1))) =
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1 - 1))))).map
        (Prod.map id (fun q => (hhMat e').mulVec (consV (n := n - 1) q.1 q.2))) := by
    rw [← Measure.map_prod_map _ _ measurable_id hK, Measure.map_id, inner]
  have hC : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => (hhMat x).mulVec (consV (n := n) p.1 p.2)) :=
    (measurable_hh x).comp measurable_consV
  have e : (fun p : ℝ × ℝ × (Fin (n - 1 - 1) → ℝ) => Rmap x e' p.1 p.2.1 p.2.2) =
      (fun p : ℝ × (Fin (n - 1) → ℝ) => (hhMat x).mulVec (consV (n := n) p.1 p.2)) ∘
        Prod.map id (fun q => (hhMat e').mulVec (consV (n := n - 1) q.1 q.2)) := by
    funext p; rfl
  rw [e, ← Measure.map_map hC (measurable_id.prodMap hK), ← hprod,
    show (fun p : ℝ × (Fin (n - 1) → ℝ) => (hhMat x).mulVec (consV (n := n) p.1 p.2)) =
      (fun ξ => (hhMat x).mulVec ξ) ∘ (fun p : ℝ × (Fin (n - 1) → ℝ) => consV (n := n) p.1 p.2)
      from rfl,
    ← Measure.map_map (measurable_hh x) measurable_consV, consV_map (by omega), stdGauss_map_hh]

lemma R_add (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ) (z t z' t' : ℝ) (Γ Γ' : Fin (n - 1 - 1) → ℝ) :
    Rmap x e' z t Γ + Rmap x e' z' t' Γ' = Rmap x e' (z + z') (t + t') (Γ + Γ') := by
  unfold Rmap
  rw [BstLean.Part161.consV_add, Matrix.mulVec_add, BstLean.Part161.consV_add, Matrix.mulVec_add]

lemma R_smul (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ) (a z t : ℝ) (Γ : Fin (n - 1 - 1) → ℝ) :
    a • Rmap x e' z t Γ = Rmap x e' (a * z) (a * t) (a • Γ) := by
  unfold Rmap
  rw [BstLean.Part161.consV_smul, Matrix.mulVec_smul, BstLean.Part161.consV_smul,
    Matrix.mulVec_smul]

lemma R_sum {m : ℕ} (x : Fin n → ℝ) (e' : Fin (n - 1) → ℝ) (c Z T : Fin m → ℝ)
    (Γ : Fin m → Fin (n - 1 - 1) → ℝ) :
    ∑ i, c i • Rmap x e' (Z i) (T i) (Γ i) =
      Rmap x e' (∑ i, c i * Z i) (∑ i, c i * T i) (∑ i, c i • Γ i) := by
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold Rmap
    have h0 : consV (n := n - 1) 0 (0 : Fin (n - 1 - 1) → ℝ) = 0 := by
      funext i; unfold consV; split_ifs <;> rfl
    have h1 : consV (n := n) 0 (0 : Fin (n - 1) → ℝ) = 0 := by
      funext i; unfold consV; split_ifs <;> rfl
    rw [h0, Matrix.mulVec_zero, h1, Matrix.mulVec_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      ih, R_smul, R_add]

/-! ## Coordinates in the frame -/

lemma dot_polar {k : ℕ} (a b : Fin k → ℝ) :
    ∑ i, a i * b i = (normSq (a + b) - normSq a - normSq b) / 2 := by
  unfold normSq
  simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib]
  have e : ∑ x, 2 * a x * b x = 2 * ∑ i, a i * b i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]; ring

lemma dot_consV (hn : 1 ≤ n) (z z' : ℝ) (g g' : Fin (n - 1) → ℝ) :
    ∑ i, consV (n := n) z g i * consV z' g' i = z * z' + ∑ j, g j * g' j := by
  rw [dot_polar, dot_polar g g', ← BstLean.Part161.consV_add, normSq_consV hn, normSq_consV hn,
    normSq_consV hn]
  ring

lemma hh_dot_comm (u a b : Fin n → ℝ) :
    ∑ i, (hhMat u).mulVec a i * b i = ∑ i, a i * (hhMat u).mulVec b i := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hh_symm u j i]; ring

lemma dot_e0 (hn : 1 ≤ n) (a : Fin n → ℝ) : ∑ i, a i * e0 n i = a ⟨0, by omega⟩ := by
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp [e0]
  · intro b _ hb
    have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    simp [e0, this]
  · simp

section frame

variable {u w : Fin n → ℝ} {s c : ℝ}

/-- `x⊥ = cu − sw`. -/
noncomputable def xperp (u w : Fin n → ℝ) (s c : ℝ) : Fin n → ℝ := c • u - s • w

/-- `e' = tail(H_x x⊥)`. -/
noncomputable def eprime (hn : 2 ≤ n) (u w : Fin n → ℝ) (s c : ℝ) : Fin (n - 1) → ℝ :=
  fun j => (hhMat (s • u + c • w)).mulVec (xperp u w s c) ⟨j + 1, by omega⟩

lemma dot_uw_lin (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (a b p q : ℝ) :
    ∑ i, (a • u + b • w) i * (p • u + q • w) i = a * p + b * q := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : ∀ i, (a * u i + b * w i) * (p * u i + q * w i) =
      a * p * u i ^ 2 + b * q * w i ^ 2 + (a * q + b * p) * (u i * w i) := fun i => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  unfold normSq at hu hw
  rw [hu, hw, huw]; ring

theorem frame_coords (hn : 2 ≤ n) (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + c ^ 2 = 1) (z t : ℝ) (Γ : Fin (n - 1 - 1) → ℝ) :
    ∑ i, Rmap (s • u + c • w) (eprime hn u w s c) z t Γ i * (s • u + c • w) i = z ∧
    ∑ i, Rmap (s • u + c • w) (eprime hn u w s c) z t Γ i * xperp u w s c i = t ∧
    normSq (Rmap (s • u + c • w) (eprime hn u w s c) z t Γ) = z ^ 2 + t ^ 2 + normSq Γ := by
  have hn1 : 1 ≤ n := by omega
  set x := s • u + c • w with hx
  have hx1 : normSq x = 1 := by
    have h := dot_uw_lin hu hw huw s c s c
    have e : normSq x = ∑ i, (s • u + c • w) i * (s • u + c • w) i := by
      unfold normSq; exact Finset.sum_congr rfl fun i _ => by rw [hx]; ring
    rw [e, h]; nlinarith [hsc]
  have hHe : (hhMat x).mulVec (e0 n) = x := hh_e0 hn1 hx1
  have hxp : xperp u w s c = c • u + (-s) • w := by
    unfold xperp; rw [neg_smul, sub_eq_add_neg]
  have hperp0 : (hhMat x).mulVec (xperp u w s c) ⟨0, by omega⟩ = 0 := by
    rw [← dot_e0 hn1 ((hhMat x).mulVec (xperp u w s c)), hh_dot_comm, hHe, hxp,
      dot_uw_lin hu hw huw]
    ring
  have hcons : consV (n := n) 0 (eprime hn u w s c) = (hhMat x).mulVec (xperp u w s c) := by
    funext i
    unfold consV eprime
    split_ifs with h
    · rw [← hperp0]; congr 1; exact Fin.ext h.symm
    · congr 1; ext; simp; omega
  have hxpn : normSq (xperp u w s c) = 1 := by
    have h := dot_uw_lin hu hw huw c (-s) c (-s)
    have e : normSq (xperp u w s c) = ∑ i, (c • u + (-s) • w) i * (c • u + (-s) • w) i := by
      unfold normSq; rw [hxp]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, h]; nlinarith [hsc]
  have hen : normSq (eprime hn u w s c) = 1 := by
    have h1 := normSq_consV hn1 0 (eprime hn u w s c)
    rw [hcons, hh_normSq, hxpn] at h1
    linarith
  have hn2 : 1 ≤ n - 1 := by omega
  have hHe' : (hhMat (eprime hn u w s c)).mulVec (e0 (n - 1)) = eprime hn u w s c :=
    hh_e0 hn2 hen
  set G' := (hhMat (eprime hn u w s c)).mulVec (consV (n := n - 1) t Γ) with hG'
  refine ⟨?_, ?_, ?_⟩
  · have hd := hh_dot x (consV (n := n) z G') (e0 n)
    rw [hHe] at hd
    unfold Rmap
    rw [← hG', hd, dot_e0 hn1, consV_zero hn1]
  · unfold Rmap
    rw [← hG', hh_dot_comm, ← hcons, dot_consV hn1, mul_zero, zero_add]
    have hd := hh_dot (eprime hn u w s c) (consV (n := n - 1) t Γ) (e0 (n - 1))
    rw [hHe'] at hd
    rw [hG', hd, dot_e0 hn2, consV_zero hn2]
  · unfold Rmap
    rw [hh_normSq, normSq_consV hn1, ← hG', hG', hh_normSq, normSq_consV hn2]
    ring

/-- **`latSq` in the frame**: `latSq(R(z, t, Γ), u, w) = |Γ|²` (the paper's
`|P_lat a| = |P_lat a_i|` read in the frame). -/
theorem latSq_frame (hn : 2 ≤ n) (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (hsc : s ^ 2 + c ^ 2 = 1) (z t : ℝ) (Γ : Fin (n - 1 - 1) → ℝ) :
    latSq (Rmap (s • u + c • w) (eprime hn u w s c) z t Γ) u w = normSq Γ := by
  obtain ⟨h1, h2, h3⟩ := frame_coords hn hu hw huw hsc z t Γ
  set R := Rmap (s • u + c • w) (eprime hn u w s c) z t Γ
  set A := ∑ i, R i * u i
  set B := ∑ i, R i * w i
  have e1 : ∑ i, R i * (s • u + c • w) i = s * A + c * B := by
    simp only [A, B, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, R i * xperp u w s c i = c * A - s * B := by
    simp only [A, B, xperp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1] at h1
  rw [e2] at h2
  unfold latSq
  have : A ^ 2 + B ^ 2 = z ^ 2 + t ^ 2 := by
    rw [← h1, ← h2]; nlinarith [hsc]
  unfold normSq at h3 ⊢
  linarith

end frame

end BstLean.Part167
