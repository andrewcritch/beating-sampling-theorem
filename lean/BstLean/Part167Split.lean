import BstLean.Part167Adm

/-!
# Part 167 (file `Split`): the plane/transverse split of a Gaussian matrix against two vectors

No proof is left open; no `native_decide` or `axiom` is used.

Paper: proof of Lemma `t7:p07:LJ`, first paragraph: "Write the standardized second-layer rows as
the sum of their plane coordinates `ξ_j` and transverse components `η_j` ... `A₂ᵀD₂y = p + s_yζ`
... an equality of conditional distributions given `(A₁, ξ)`, with `ζ` Gaussian in `U_x^⊥`."

`M` is a Gaussian `q × m` matrix (entry variance `v`); `h, g ∈ ℝ^m` are fixed (for the Agent:
`h = h₁ = ReLU(A₁x)`, `g = h̃`, `q = m = m_A`, given `A₁`); `r = res h g` (the part of `g`
orthogonal to `h`).

* `perp b z = z − (⟨z, b⟩/|b|²) b` (the projection off `b`; `z` itself if `b = 0`).
* **`split_lint`**: Part 157's regression `gauss_split` in integral form.
* **`plane_split`**: `(Mh, Mg, M)` has the distribution of
  `(c₁, λ(g)c₁ + c₂, reb h c₁ (reb r c₂ N))`, with `c₁ = √v|h|ξ₁`, `c₂ = √v|r|ξ₂`, and
  `ξ₁, ξ₂, N` independent (integral form, for every measurable `F ≥ 0`).
* **`plane_split_vecMul`**: for a vector `w = W(Mh, Mg)` that reads `M` only through the plane,
  `Mᵀw` has the distribution of `α₁h + perp h (α₂ r + perp r (√v|w|·γ))`, where
  `α₁ = ⟨w, c₁⟩/|h|²`, `α₂ = ⟨w, c₂⟩/|r|²` depend on the plane coordinates only and `γ` is an
  independent standard Gaussian vector of `ℝ^m`: the paper's `p + s_yζ`, `s_y = √v|w|`,
  `ζ = perp h (perp r γ)` Gaussian in `U^⊥`.
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Matrix Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part157 (cOf reb reb_mulVec measurable_cOf_comp measurable_reb_comp gauss_split)
open BstLean.Part153 (gaussMat_vecMul)

variable {q m : ℕ}

/-- The projection off `b`: `z − (⟨z, b⟩/|b|²) b`. -/
noncomputable def perp (b z : Fin m → ℝ) : Fin m → ℝ :=
  z - ((normSq b)⁻¹ * ∑ j, z j * b j) • b

lemma measurable_perp (b : Fin m → ℝ) : Measurable (perp b) := by
  have : Continuous (perp b) := by unfold perp; fun_prop
  exact this.measurable

/-- `perp h` fixes `r = res h g` (`r ⊥ h`; for `h = 0`, `perp 0` is the identity). -/
lemma perp_res (h g : Fin m → ℝ) : perp h (res h g) = res h g := by
  by_cases h0 : h = 0
  · subst h0; simp [perp, normSq]
  · unfold perp
    rw [res_orth h0 g]; simp

/-- So the plane part of `plane_split_vecMul` is `α₁h + α₂r ∈ span(h, g)` and the transverse part
is `perp h (perp r (s·γ))`. -/
lemma perp_plane (h g z : Fin m → ℝ) (α : ℝ) :
    perp h (α • res h g + z) = α • res h g + perp h z := by
  have e : ∀ u w : Fin m → ℝ, perp h (u + w) = perp h u + perp h w := by
    intro u w; unfold perp
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add, add_smul]
    abel
  have e2 : perp h (α • res h g) = α • perp h (res h g) := by
    unfold perp
    simp only [Pi.smul_apply, smul_eq_mul, smul_sub, smul_smul]
    congr 2
    rw [show ∑ j, α * res h g j * h j = α * ∑ j, res h g j * h j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    ring
  rw [e, e2, perp_res]

lemma vecMul_vecMulVec' (w : Fin q → ℝ) (c : Fin q → ℝ) (b : Fin m → ℝ) :
    vecMul w (Matrix.vecMulVec c b) = (∑ i, w i * c i) • b := by
  funext j
  simp only [vecMul, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring

lemma vecMul_projPerp (b z : Fin m → ℝ) : vecMul z (projPerp b) = perp b z := by
  unfold projPerp perp
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_smul, vecMul_vecMulVec', smul_smul]

/-- `Mᵀw` for `M = reb b c N`: `(⟨w, c⟩/|b|²) b + perp b (Nᵀw)`. -/
lemma vecMul_reb (b : Fin m → ℝ) (c : Fin q → ℝ) (N : Matrix (Fin q) (Fin m) ℝ)
    (w : Fin q → ℝ) :
    vecMul w (reb b c N) = ((normSq b)⁻¹ * ∑ i, w i * c i) • b + perp b (vecMul w N) := by
  unfold reb glue
  rw [Matrix.vecMul_add, Matrix.vecMul_smul, vecMul_vecMulVec', smul_smul,
    ← Matrix.vecMul_vecMul, vecMul_projPerp]

lemma measurable_vecMul_joint :
    Measurable (fun p : (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ => vecMul p.1 p.2) :=
  (Continuous.matrix_vecMul continuous_fst continuous_snd).measurable

lemma measurable_mulVec_pair (b : Fin m → ℝ) :
    Measurable (fun M : Matrix (Fin q) (Fin m) ℝ => M *ᵥ b) :=
  (Continuous.matrix_mulVec continuous_id continuous_const).measurable

/-- **Part 157's regression in integral form**: `∫ G(Mb, M) = ∫∫ G(c, reb b c N)`,
`c = √v|b|ξ`, `ξ` and `N` independent. -/
theorem split_lint (v : ℝ) (b : Fin m → ℝ)
    {G : (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ M, G (M *ᵥ b, M) ∂gaussMat q m v =
      ∫⁻ ξ, ∫⁻ N, G (cOf v b ξ, reb b (cOf v b ξ) N) ∂gaussMat q m v ∂stdGauss (Fin q) := by
  have hT : Measurable (fun M : Matrix (Fin q) (Fin m) ℝ => (M *ᵥ b, M)) :=
    (measurable_mulVec_pair b).prodMk measurable_id
  have hc : Measurable (fun p : (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ => cOf v b p.1) :=
    measurable_cOf_comp v measurable_const measurable_fst
  have hS : Measurable (fun p : (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      (cOf v b p.1, reb b (cOf v b p.1) p.2)) :=
    hc.prodMk (measurable_reb_comp measurable_const hc measurable_snd)
  calc ∫⁻ M, G (M *ᵥ b, M) ∂gaussMat q m v
      = ∫⁻ z, G z ∂(gaussMat q m v).map (fun M => (M *ᵥ b, M)) := (lintegral_map hG hT).symm
    _ = ∫⁻ z, G z ∂((stdGauss (Fin q)).prod (gaussMat q m v)).map
          (fun p => (cOf v b p.1, reb b (cOf v b p.1) p.2)) := by
        have := gauss_split (q := q) v b
        rw [show (fun M : Matrix (Fin q) (Fin m) ℝ => (M *ᵥ b, M)) =
          (fun M => (M.mulVec b, M)) from rfl, this]
    _ = ∫⁻ p, G (cOf v b p.1, reb b (cOf v b p.1) p.2)
          ∂(stdGauss (Fin q)).prod (gaussMat q m v) := lintegral_map hG hS
    _ = _ := lintegral_prod _ (hG.comp hS).aemeasurable

/-- **The plane split** (two regressions): `(Mh, Mg, M)` has the distribution of
`(c₁, λ(g)c₁ + c₂, reb h c₁ (reb r c₂ N))`, `r = res h g`, `c₁ = √v|h|ξ₁`, `c₂ = √v|r|ξ₂`, with
`ξ₁, ξ₂, N` independent. -/
theorem plane_split (v : ℝ) (h g : Fin m → ℝ)
    {F : (Fin q → ℝ) × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ M, F (M *ᵥ h, M *ᵥ g, M) ∂gaussMat q m v =
      ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, F (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂,
        reb h (cOf v h ξ₁) (reb (res h g) (cOf v (res h g) ξ₂) N))
        ∂gaussMat q m v ∂stdGauss (Fin q) ∂stdGauss (Fin q) := by
  have hG : Measurable (fun p : (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      F (p.1, p.2 *ᵥ g, p.2)) :=
    hF.comp (measurable_fst.prodMk (((measurable_mulVec_pair g).comp measurable_snd).prodMk
      measurable_snd))
  rw [split_lint v h hG]
  refine lintegral_congr fun ξ₁ => ?_
  simp only [reb_mulVec]
  have hG2 : Measurable (fun p : (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      F (cOf v h ξ₁, lam h g • cOf v h ξ₁ + p.1, reb h (cOf v h ξ₁) p.2)) :=
    hF.comp (measurable_const.prodMk ((measurable_const.add measurable_fst).prodMk
      (measurable_reb_comp measurable_const measurable_const measurable_snd)))
  have := split_lint v (res h g) hG2
  rw [← this]

/-- **The transverse part is Gaussian given the plane** (the paper's `A₂ᵀD₂y = p + s_yζ`): for a
vector `w = W(Mh, Mg)` that reads `M` only through the plane, `Mᵀw` has the distribution of
`α₁h + perp h (α₂r + perp r (√v|w|·γ))`, with `γ` an independent standard Gaussian vector. -/
theorem plane_split_vecMul (v : ℝ) (h g : Fin m → ℝ)
    {W : (Fin q → ℝ) × (Fin q → ℝ) → (Fin q → ℝ)} (hW : Measurable W)
    {F : (Fin q → ℝ) × (Fin q → ℝ) × (Fin m → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ M, F (M *ᵥ h, M *ᵥ g, vecMul (W (M *ᵥ h, M *ᵥ g)) M) ∂gaussMat q m v =
      ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ γ,
        F (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂,
          ((normSq h)⁻¹ * ∑ i, W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂) i *
              cOf v h ξ₁ i) • h +
            perp h (((normSq (res h g))⁻¹ * ∑ i,
              W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂) i *
                cOf v (res h g) ξ₂ i) • res h g +
              perp (res h g) ((√v * √(normSq
                (W (cOf v h ξ₁, lam h g • cOf v h ξ₁ + cOf v (res h g) ξ₂)))) • γ)))
        ∂stdGauss (Fin m) ∂stdGauss (Fin q) ∂stdGauss (Fin q) := by
  have hF' : Measurable (fun t : (Fin q → ℝ) × (Fin q → ℝ) × Matrix (Fin q) (Fin m) ℝ =>
      F (t.1, t.2.1, vecMul (W (t.1, t.2.1)) t.2.2)) :=
    hF.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_vecMul_joint.comp ((hW.comp (measurable_fst.prodMk
        (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd)))))
  have := plane_split v h g hF'
  simp only [] at this
  rw [this]
  refine lintegral_congr fun ξ₁ => lintegral_congr fun ξ₂ => ?_
  set c₁ := cOf v h ξ₁
  set c₂ := cOf v (res h g) ξ₂
  set w := W (c₁, lam h g • c₁ + c₂)
  simp only [vecMul_reb]
  set K : (Fin m → ℝ) → ℝ≥0∞ := fun z => F (c₁, lam h g • c₁ + c₂,
    ((normSq h)⁻¹ * ∑ i, w i * c₁ i) • h +
      perp h (((normSq (res h g))⁻¹ * ∑ i, w i * c₂ i) • res h g + perp (res h g) z)) with hK
  have hKm : Measurable K :=
    hF.comp (measurable_const.prodMk (measurable_const.prodMk (measurable_const.add
      ((measurable_perp h).comp (measurable_const.add (measurable_perp (res h g)))))))
  change ∫⁻ N, K (vecMul w N) ∂gaussMat q m v = ∫⁻ γ, K ((√v * √(normSq w)) • γ) ∂stdGauss (Fin m)
  have hvm : Measurable (fun N : Matrix (Fin q) (Fin m) ℝ => vecMul w N) :=
    measurable_vecMul_joint.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hKm hvm, gaussMat_vecMul, lintegral_map hKm (measurable_const_smul _)]

end BstLean.Part167
