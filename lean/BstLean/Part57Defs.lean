import BstLean.Part56Defs
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Part 57, wave 0: frozen definitions — Theorem RR, the bucketed subspace program for fixed-rank
dense Bingham laws `D ∝ exp(Σ_a t_a (v_a·x)²)`

Source: `delegations/answers/omRR-opus-prover.md` (Theorem RR, Prop D′, Lemma T, Lemma C), with the
repairs of `chRR-opus.md` and `chRR-codex.md`:
1. the scale of a row is the projection coefficient `a_l = V_l·ω/|ω|²` (no square root);
2. the net directions are rows of `V` (`ω_g = V_{rep(l)}`), so every stage-2 coefficient is computed
   online from the input `V`; there are no real constants;
3. the bucket wiring `rep : Fin n → Fin n` is fixed when the program is built, so the headline has the
   Part 43 form `∀ V, ∃ (rep, pm, pg)`, not the Part 56 form `∃ (pm, pg), ∀ v`;
4. the Gram inverse is Lean's `Matrix.inv` (`Ring.inverse det • adjugate`), which a straight-line
   program computes with `+ − × ÷` and Lean's `x/0 = 0`; no Cholesky square root;
5. the sentence "`ϱ = 0` gives a `U`-measurable `F`" is not used; `{ϱ = 0}` is a null set.
Specification: `delegations/answers/p57-spec-opus.md`.

This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions. Part 41, 43, 50, 53 and 56 names are reused. `k = d_f`, `d = d_M`, `r` the rank,
`f = (f₀, T)`, `σ = sg n d`, `𝒟 = DD n d`.

* **Frame and law.** `V : Fin r → Fin n → ℝ` holds the columns `v_a` (so `V a l` is entry `l` of
  `v_a`, and row `l` of the `n × r` matrix is `a ↦ V a l`). `OrthoF V`: the columns are orthonormal.
  `rkR t V = Σ_a t_a v_a v_aᵀ`; `lawRR n t V = binghamA n (rkR t V)`;
  `surrRR n K t V = binghamKA n K (rkR t V) ∝ p_K(Σ_a t_a (v_a·x)²)` (Part 50's surrogate at the
  range bound `C n`; `K = KRK C n e` of Part 56). `BoxT C n t`: `t_a ∈ [0, C n]` for every `a`.
  `rhoSq V x = |P_{V⊥} x|²` (`ϱ²`).
* **Bucketing.** `bkt V rep` is the frame `V′` with rows `V′_l = a_l V_{rep l}`,
  `a_l = (V_l·V_{rep l})/|V_{rep l}|²`. `nBk rep` is the number of buckets (the size of the image of
  `rep`). `RowClose V W H`: `|V_l − W_l|² ≤ H |V_l|²` for every row (`H = h²`).
* **Anchor vectors.** The anchor index is `Mono r d` (a degree `j ≤ d` and a multiset `γ` of size `j`
  in `Fin r`). `xiF d W γ` is the vector `α ↦ [y^γ] Π_{l∈α} (W y)_l` on degree-`γ.1` monomials.
  `xiRR d V W γ` is `xiF d W γ` for `γ.1 = d` (the bucketed top block) and `xiF d V γ` for `γ.1 < d`
  (exact lower blocks).
* **General anchor family `Ξ : Mono r d → Mono n d → ℝ`.** `gramX Ξ` its Gram matrix, `prjF Ξ x` the
  vector `⟨ξ_γ, φ(x)⟩`, `kapX Ξ x = G⁻¹ prjF Ξ x` (the conditional-mean coefficients),
  `KRX Ξ x y = ⟨φ(x), φ(y)⟩ − ⟨prjF Ξ x, kapX Ξ y⟩` (the residual kernel), `tauX`, `rhoX`, `deltaSqX`
  as in Part 56. `ancX M Ξ γ = M ξ_γ`, `muxX M Ξ x = Σ_γ κ_γ(x) u_γ`.
* **Program value.** `gH57` (heat form), `wX` (the weights), `gWX` (the weighted sum),
  `gW57` (weight form), `Sfl57` (the quantity `S`), `projX` (the projection `Ξ G⁻¹ Ξᵀ`).
* **Programs.** The bucket program reads `In57 r n d k = In41 n d k ⊕ ((Fin r × Fin n) ⊕ KeyX k r d)`:
  `M`, `f₀`, `T`, then the entries of `V`, then the weights. The moment program reads
  `InM57 r n = Fin r ⊕ (Fin r × Fin n)` (`t`, then `V`). `GSpec57 pg rep`, `MomSpec57 pm rep K`.
* **Cost.** `costBk57 n d k r G` (Lemma C with the `F3` term removed and `G` buckets) and
  `onceCost57` (the moment program).
* **Statements.** §9 holds the interface `Prop`s between the wave-1 files.
-/

namespace BstLean.Part57

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM contr trL frob Tens TSymm fval In41 Pn NN baseline varU)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part50 (binghamA binghamKA)
open BstLean.Part53 (TF fvA heatA sg linZ inp53)
open BstLean.Part56 (KRK wickC cvarG EV56 PhiJI nuRK k0RK)

variable {n d r : ℕ}

/-! ## §1 The frame, the law and the surrogate -/

/-- The columns `v_1, …, v_r` of `V` are orthonormal. -/
def OrthoF (V : Fin r → Fin n → ℝ) : Prop :=
  ∀ a b : Fin r, ∑ i, V a i * V b i = if a = b then 1 else 0

/-- `t_a ∈ [0, C n]` for every `a`. -/
def BoxT (C : ℝ) (n : ℕ) (t : Fin r → ℝ) : Prop := ∀ a, 0 ≤ t a ∧ t a ≤ C * n

/-- `A = Σ_a t_a v_a v_aᵀ`. -/
def rkR (t : Fin r → ℝ) (V : Fin r → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ a, t a * V a i * V a j

/-- The rank-`r` Bingham law `D_{t,V} ∝ exp(Σ_a t_a (v_a·x)²) σ`. -/
noncomputable def lawRR (n : ℕ) (t : Fin r → ℝ) (V : Fin r → Fin n → ℝ) : Measure (Fin n → ℝ) :=
  binghamA n (rkR t V)

/-- The surrogate `Q̃ ∝ p_K(Σ_a t_a (v_a·x)²) σ`. -/
noncomputable def surrRR (n K : ℕ) (t : Fin r → ℝ) (V : Fin r → Fin n → ℝ) : Measure (Fin n → ℝ) :=
  binghamKA n K (rkR t V)

/-- `y_a = v_a·x`. -/
def coordY (V : Fin r → Fin n → ℝ) (x : Fin n → ℝ) (a : Fin r) : ℝ := ∑ i, V a i * x i

/-- `ϱ² = |x − Σ_a (v_a·x) v_a|²` (`= |P_{V⊥} x|²` for orthonormal `V`). -/
def rhoSq (V : Fin r → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (x i - ∑ a, coordY V x a * V a i) ^ 2

/-- The point `V y = Σ_a y_a v_a` of the subspace. -/
def spanV (V : Fin r → Fin n → ℝ) (y : Fin r → ℝ) : Fin n → ℝ := fun i => ∑ a, y a * V a i

/-- `w = P g/‖P g‖`, `P = I − Σ_a v_a v_aᵀ` (uniform on the sphere of `V^⊥` for `g` Gaussian and
orthonormal `V`). -/
noncomputable def perpDirR (V : Fin r → Fin n → ℝ) (g : Fin n → ℝ) : Fin n → ℝ :=
  (1 / Real.sqrt (∑ i, (g i - ∑ a, coordY V g a * V a i) ^ 2)) •
    fun i => g i - ∑ a, coordY V g a * V a i

/-! ## §2 Bucketing -/

/-- The bucketed frame `V′`: row `l` is `a_l V_{rep l}` with the projection coefficient
`a_l = (V_l·V_{rep l})/|V_{rep l}|²` (`0` if `V_{rep l} = 0`, by Lean's `x/0 = 0`). -/
noncomputable def bkt (V : Fin r → Fin n → ℝ) (rep : Fin n → Fin n) : Fin r → Fin n → ℝ :=
  fun a l => (∑ b, V b l * V b (rep l)) / (∑ b, V b (rep l) ^ 2) * V a (rep l)

/-- The number of buckets `G = |image rep|`. -/
def nBk (rep : Fin n → Fin n) : ℕ := (Finset.univ.image rep).card

/-- Rows are close: `|V_l − W_l|² ≤ H |V_l|²` for every row `l`. -/
def RowClose (V W : Fin r → Fin n → ℝ) (H : ℝ) : Prop :=
  ∀ l : Fin n, ∑ a, (V a l - W a l) ^ 2 ≤ H * ∑ a, V a l ^ 2

/-! ## §3 Anchor vectors -/

/-- `ξ_γ(W)`: the vector `α ↦ [y^γ] Π_{l∈α} (W y)_l` on monomials `α` of degree `γ.1`, `0` elsewhere.
Then `φ_j(W y) = Σ_{|γ| = j} y^γ ξ_γ(W)`. -/
noncomputable def xiF (d : ℕ) (W : Fin r → Fin n → ℝ) (γ : Mono r d) : Mono n d → ℝ := fun α =>
  if (α.1 : ℕ) = (γ.1 : ℕ) then
    (((α.2 : Multiset (Fin n)).map fun l =>
        ∑ a, (MvPolynomial.C (W a l) * MvPolynomial.X a : MvPolynomial (Fin r) ℝ)).prod).coeff
      (Multiset.toFinsupp (γ.2 : Multiset (Fin r)))
  else 0

/-- The anchor vectors of the bucketed subspace program: exact on `V` for the blocks `j < d`, on the
bucketed frame `W = V′` for the top block `j = d`. -/
noncomputable def xiRR (d : ℕ) (V W : Fin r → Fin n → ℝ) (γ : Mono r d) : Mono n d → ℝ :=
  if (γ.1 : ℕ) = d then xiF d W γ else xiF d V γ

/-! ## §4 A general anchor family: Gaussian conditioning -/

/-- The Gram matrix `G_{γγ'} = ⟨ξ_γ, ξ_γ'⟩`. -/
noncomputable def gramX (Ξ : Mono r d → Mono n d → ℝ) : Matrix (Mono r d) (Mono r d) ℝ :=
  fun γ γ' => ∑ p, Ξ γ p * Ξ γ' p

/-- `⟨ξ_γ, φ(x)⟩`. -/
noncomputable def prjF (Ξ : Mono r d → Mono n d → ℝ) (x : Fin n → ℝ) : Mono r d → ℝ :=
  fun γ => ∑ p, Ξ γ p * phiM x p

/-- `κ(x) = G⁻¹ (⟨ξ_γ, φ(x)⟩)_γ` (Lean's `Matrix.inv`; `0` if `G` is singular). -/
noncomputable def kapX (Ξ : Mono r d → Mono n d → ℝ) (x : Fin n → ℝ) : Mono r d → ℝ :=
  Matrix.mulVec (gramX Ξ)⁻¹ (prjF Ξ x)

/-- The residual kernel `K_R(x, y) = ⟨φ(x), φ(y)⟩ − ⟨Ξᵀφ(x), G⁻¹ Ξᵀφ(y)⟩`. -/
noncomputable def KRX (Ξ : Mono r d → Mono n d → ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ p : Mono n d, phiM x p * phiM y p - ∑ γ, prjF Ξ x γ * kapX Ξ y γ

/-- `τ(x) = K_R(x, x)`. -/
noncomputable def tauX (Ξ : Mono r d → Mono n d → ℝ) (x : Fin n → ℝ) : ℝ := KRX Ξ x x

/-- `ρ_R(x, y) = K_R(x,y)/√(τ(x)τ(y))` (`0` when a factor vanishes). -/
noncomputable def rhoX (Ξ : Mono r d → Mono n d → ℝ) (x y : Fin n → ℝ) : ℝ :=
  KRX Ξ x y / Real.sqrt (tauX Ξ x * tauX Ξ y)

/-- `δ² = E_{x,y ∼ μ⊗μ} ρ_R(x, y)²`. -/
noncomputable def deltaSqX (μ : Measure (Fin n → ℝ)) (Ξ : Mono r d → Mono n d → ℝ) : ℝ :=
  ∫ x, ∫ y, rhoX Ξ x y ^ 2 ∂μ ∂μ

/-- The anchor `u_γ = M ξ_γ ∈ ℝⁿ`. -/
noncomputable def ancX (M : CoefIdxD n d → ℝ) (Ξ : Mono r d → Mono n d → ℝ) (γ : Mono r d) :
    Fin n → ℝ :=
  linZ M (Ξ γ)

/-- The conditional mean `μ_x = Σ_γ κ_γ(x) u_γ`. -/
noncomputable def muxX (M : CoefIdxD n d → ℝ) (Ξ : Mono r d → Mono n d → ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  ∑ γ, kapX Ξ x γ • ancX M Ξ γ

/-! ## §5 The program value -/

/-- Heat form: `g_μ(M) = E_{x∼μ} (P_{σ² τ(x)} f)(μ_x)`. -/
noncomputable def gH57 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (Ξ : Mono r d → Mono n d → ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, fvA k (heatA k (sg n d ^ 2 * tauX Ξ x) (TF k f0 T)) (muxX M Ξ x) ∂μ

/-- The keys `(i, l, γ⃗)`, `i, l ≤ k`, `γ⃗ ∈ (Mono r d)^{i−2l}`. -/
abbrev KeyX (k r d : ℕ) :=
  Σ il : Fin (k + 1) × Fin (k + 1), Fin ((il.1 : ℕ) - 2 * (il.2 : ℕ)) → Mono r d

/-- The weight of a key under `μ`: `wickC i l · σ^{2l} · E_μ[τ^l Π_s κ_{γ_s}]`. -/
noncomputable def wX (μ : Measure (Fin n → ℝ)) (Ξ : Mono r d → Mono n d → ℝ) {k : ℕ}
    (κ : KeyX k r d) : ℝ :=
  wickC κ.1.1 κ.1.2 * (sg n d ^ 2) ^ (κ.1.2 : ℕ) *
    ∫ x, tauX Ξ x ^ (κ.1.2 : ℕ) * ∏ s, kapX Ξ x (κ.2 s) ∂μ

/-- The weighted sum `Σ_{2l ≤ i} c(i,l,γ⃗) (tr^l A_i)[u_{γ_1}, …, u_{γ_{i−2l}}]`. -/
noncomputable def gWX (k : ℕ) (A : Tens n) (c : KeyX k r d → ℝ) (u : Mono r d → Fin n → ℝ) : ℝ :=
  ∑ κ : KeyX k r d, if 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) then
    c κ * contr (trL (κ.1.2 : ℕ) (A κ.1.1)) (fun s => u (κ.2 s)) else 0

/-- Weight form: `g_μ(M) = gWX k (TF k f0 T) (wX μ Ξ) (u_γ)_γ`. -/
noncomputable def gW57 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (Ξ : Mono r d → Mono n d → ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  gWX k (TF k f0 T) (wX μ Ξ) (ancX M Ξ)

/-- `S_μ(M) = E_{x∼μ} Var(f(m(x)) | anchors)` at residual scale `σ√τ(x)`. -/
noncomputable def Sfl57 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (Ξ : Mono r d → Mono n d → ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, cvarG k f0 T (sg n d * Real.sqrt (tauX Ξ x)) (muxX M Ξ x) ∂μ

/-- The projection `Π = Ξ G⁻¹ Ξᵀ` on the monomial index, applied to each output column of `Z`. -/
noncomputable def projX (Ξ : Mono r d → Mono n d → ℝ) (Z : CoefIdxD n d → ℝ) : CoefIdxD n d → ℝ :=
  fun α => ∑ γ, ∑ γ', Ξ γ ⟨α.1, α.2.1⟩ * (gramX Ξ)⁻¹ γ γ' *
    ∑ p : Mono n d, Ξ γ' p * Z ⟨p.1, (p.2, α.2.2)⟩

/-- `Σ_{j=1}^k ‖T_j‖²/𝒟^j`. -/
noncomputable def Ssum57 (n d k : ℕ) (T : Tens n) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, frob (T j) / DD n d ^ j

/-! ## §6 Programs -/

/-- The bucket program's inputs: `M`, `f₀`, `T`, then the entries `V a l`, then the weights. -/
abbrev In57 (r n d k : ℕ) := In41 n d k ⊕ ((Fin r × Fin n) ⊕ KeyX k r d)

/-- The bucket program's input vector. -/
def inp57 {k : ℕ} (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) (V : Fin r → Fin n → ℝ)
    (c : KeyX k r d → ℝ) : In57 r n d k → ℝ :=
  Sum.elim (inp53 (k := k) f0 T M) (Sum.elim (fun p => V p.1 p.2) c)

/-- The moment program's inputs: `t`, then the entries `V a l`. -/
abbrev InM57 (r n : ℕ) := Fin r ⊕ (Fin r × Fin n)

/-- The moment program's input vector. -/
def inRR (t : Fin r → ℝ) (V : Fin r → Fin n → ℝ) : InM57 r n → ℝ :=
  Sum.elim t (fun p => V p.1 p.2)

/-- With the wiring `rep` fixed, the bucket program computes the weighted sum with the anchors of
`xiRR d V (bkt V rep)` from `M`, `f`, the entries of `V` and arbitrary weights `c`, for every `V`. -/
def GSpec57 {k : ℕ} (pg : Prog (In57 r n d k) Unit) (rep : Fin n → Fin n) : Prop :=
  ∀ (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) (V : Fin r → Fin n → ℝ) (c : KeyX k r d → ℝ),
    TSymm k T →
    pg.eval (inp57 f0 T M V c) () = gWX k (TF k f0 T) c (ancX M (xiRR d V (bkt V rep)))

/-- With the wiring `rep` fixed, the moment program returns the surrogate weights for every `t ≥ 0`
and every orthonormal `V`. -/
def MomSpec57 {k : ℕ} (pm : Prog (InM57 r n) (KeyX k r d)) (rep : Fin n → Fin n) (K : ℕ) : Prop :=
  ∀ (t : Fin r → ℝ) (V : Fin r → Fin n → ℝ), (∀ a, 0 ≤ t a) → OrthoF V → ∀ κ : KeyX k r d,
    pm.eval (inRR t V) κ = wX (surrRR n K t V) (xiRR d V (bkt V rep)) κ

/-! ## §7 Cost -/

/-- `L = |Mono r d| = C(r+d, d)`, the number of anchors per row. -/
noncomputable def Lr (r d : ℕ) : ℝ := (Fintype.card (Mono r d) : ℝ)

/-- The proved-cost bound of the bucket program with `G` buckets (Lemma C, repaired):
`2P` for stage 1 and the coefficient reads; `(d+1)N` for the products `a^α` and `φ`-type constants;
`4(r+1)(L+1)²(G+2)^d(n+1)^d` for the exact lower-block anchors, the scales `a_l`, the stage-2
coefficients `[y^γ](Ωy)^β` and the stage-2 sums; `4(k+2)³(L+1)^k(n+1)^k` for the traces, the
multilinear values and the weighted sum. -/
noncomputable def costBk57 (n d k r G : ℕ) : ℝ :=
  2 * Pn n d + ((d : ℝ) + 1) * NN n d +
    4 * ((r : ℝ) + 1) * (Lr r d + 1) ^ 2 * ((G : ℝ) + 2) ^ d * ((n : ℝ) + 1) ^ d +
    4 * ((k : ℝ) + 2) ^ 3 * (Lr r d + 1) ^ k * ((n : ℝ) + 1) ^ k

/-- The proved-cost bound of the moment program (polynomial in `n` and `K` for fixed `r, d, k`). -/
noncomputable def onceCost57 (n d k r K : ℕ) : ℝ :=
  ((K : ℝ) + 2) ^ (2 * r + 2) * ((n : ℝ) + 2) ^ (8 * (d + 1) * (k + 1) * (r + 1)) *
    ((8 * (d + 1) * (k + 1) * (r + 1)).factorial : ℝ)

/-! ## §9 The interface statements -/

/-- **Weights** (Wick expansion, algebra): the weight form equals the heat form, for every anchor
family. -/
def PropWeights57 (d k r : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ Ξ : Mono r d → Mono n d → ℝ,
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → ∀ M : CoefIdxD n d → ℝ,
      gW57 μ k f0 T Ξ M = gH57 μ k f0 T Ξ M

/-- **Gaussian split**: for a nonsingular Gram matrix, `Π Z` and `Z − Π Z` are independent under the
standard Gaussian. -/
def PropSplit57 (d r : ℕ) : Prop :=
  ∀ (n : ℕ) (Ξ : Mono r d → Mono n d → ℝ), (gramX Ξ).det ≠ 0 →
    ∀ F : (CoefIdxD n d → ℝ) → ℝ≥0∞, Measurable F →
    ∫⁻ Z, F Z ∂stdGauss (CoefIdxD n d) =
      ∫⁻ Z, ∫⁻ Z', F (projX Ξ Z + (Z' - projX Ξ Z')) ∂stdGauss (CoefIdxD n d)
        ∂stdGauss (CoefIdxD n d)

/-- **Orthogonality**: the heat form is `E[B | anchors]` in the proxy `M = σZ`. -/
def PropOrth57 (d k r : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ Ξ : Mono r d → Mono n d → ℝ,
    (gramX Ξ).det ≠ 0 → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      MemLp (fun Z : CoefIdxD n d → ℝ => BofQ μ k f0 T (sg n d • Z)) 2 (stdGauss (CoefIdxD n d)) ∧
      MemLp (fun Z : CoefIdxD n d → ℝ => gH57 μ k f0 T Ξ (sg n d • Z)) 2 (stdGauss (CoefIdxD n d)) ∧
      Integrable (fun Z : CoefIdxD n d → ℝ => varFQ μ k f0 T (sg n d • Z)) (stdGauss (CoefIdxD n d)) ∧
      ∀ h : (Mono r d → Fin n → ℝ) → ℝ, Measurable h →
        MemLp (fun Z : CoefIdxD n d → ℝ => h (ancX (sg n d • Z) Ξ)) 2 (stdGauss (CoefIdxD n d)) →
        ∫ Z, (BofQ μ k f0 T (sg n d • Z) - gH57 μ k f0 T Ξ (sg n d • Z)) *
          h (ancX (sg n d • Z) Ξ) ∂stdGauss (CoefIdxD n d) = 0

/-- **Theorem RK-G, error part** (law-free, any anchor family with nonsingular Gram matrix). -/
def PropRKGErr57 (d k r : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ Ξ : Mono r d → Mono n d → ℝ,
    (gramX Ξ).det ≠ 0 → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      Integrable (fun Z : CoefIdxD n d → ℝ =>
          (BofQ μ k f0 T (sg n d • Z) - gH57 μ k f0 T Ξ (sg n d • Z)) ^ 2) (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (BofQ μ k f0 T (sg n d • Z) - gH57 μ k f0 T Ξ (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) ≤
        Real.sqrt (deltaSqX μ Ξ) * ∫ Z, Sfl57 μ k f0 T Ξ (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-- **Theorem RK-G, floor part**: `(1 − δ) E_Z S(σZ) ≤ E_Z Var_μ f(σZφ)`. -/
def PropRKGFloor57 (d k r : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ Ξ : Mono r d → Mono n d → ℝ,
    (gramX Ξ).det ≠ 0 → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      (1 - Real.sqrt (deltaSqX μ Ξ)) * ∫ Z, Sfl57 μ k f0 T Ξ (sg n d • Z) ∂stdGauss (CoefIdxD n d) ≤
        EV56 d μ k f0 T

/-- **Rank**: if the rows of `W` are close to those of an orthonormal `V` (`H r < 1/2`, so
`‖V − W‖_op < 1`), the Gram matrix of `xiRR d V W` is nonsingular. -/
def PropRank57 (d r : ℕ) : Prop :=
  ∀ (n : ℕ) (V W : Fin r → Fin n → ℝ) (H : ℝ), OrthoF V → 0 ≤ H → H * r < 1 / 2 → RowClose V W H →
    (gramX (xiRR d V W)).det ≠ 0

/-- **Net** (the build-time bucketing; repair F2(a)): for every `H ∈ (0, 1]` there is a bucket count
`G₀` that does not depend on `n` such that every frame has a wiring with at most `G₀` buckets whose
projection-coefficient frame `bkt V rep` has close rows. -/
def PropNet57 (r : ℕ) : Prop :=
  ∀ H : ℝ, 0 < H → H ≤ 1 → ∃ G0 : ℕ, ∀ (n : ℕ) (V : Fin r → Fin n → ℝ),
    ∃ rep : Fin n → Fin n, nBk rep ≤ G0 ∧ RowClose V (bkt V rep) H

/-- **Key Lemma** on a rank-`r` subspace: for `a, a′` in the subspace with `|a|, |a′| ≤ 1`,
`w, w′` independent uniform on the sphere of `V^⊥`, and `1 ≤ i, i' ≤ j ≤ d`:
`E ⟨Φ_{j,i}(a, w), Φ_{j,i'}(a′, w′)⟩² ≤ C_K/(n − r)`, for `n ≥ 2r`. -/
def KeyLemma57 (d r : ℕ) (CK : ℝ) : Prop :=
  ∀ n : ℕ, 2 * r ≤ n → ∀ V : Fin r → Fin n → ℝ, OrthoF V → ∀ y y' : Fin r → ℝ,
    ∑ a, y a ^ 2 ≤ 1 → ∑ a, y' a ^ 2 ≤ 1 →
    ∀ j i i' : ℕ, j ≤ d → 1 ≤ i → i ≤ j → 1 ≤ i' → i' ≤ j →
      ∫ g, ∫ g', (∑ p : Mono n d, PhiJI d j i (spanV V y) (perpDirR V g) p *
          PhiJI d j i' (spanV V y') (perpDirR V g') p) ^ 2 ∂stdGauss (Fin n) ∂stdGauss (Fin n) ≤
        CK / ((n : ℝ) - r)

/-- **Prop D′** (δ for the bucketed anchors), with `I = E_D ϱ^{−2}` and `H = h²`:
`δ² ≤ C₁/(n − r) + C₂ (H I + H² I²)` for `n ≥ 2r`, `2 ≤ d`, `H r ≤ 1/(4d²)`, every real `t`, and
`ϱ^{−2}` integrable. -/
def PropDp57 (d r : ℕ) (CD1 CD2 : ℝ) : Prop :=
  ∀ n : ℕ, 2 * r ≤ n → ∀ (V W : Fin r → Fin n → ℝ) (H : ℝ), OrthoF V → 0 ≤ H →
    H * r ≤ 1 / (4 * (d : ℝ) ^ 2) → RowClose V W H → ∀ t : Fin r → ℝ,
    Integrable (fun x => (rhoSq V x)⁻¹) (lawRR n t V) →
      deltaSqX (lawRR n t V) (xiRR d V W) ≤
        CD1 / ((n : ℝ) - r) + CD2 * (H * (∫ x, (rhoSq V x)⁻¹ ∂lawRR n t V) +
          H ^ 2 * (∫ x, (rhoSq V x)⁻¹ ∂lawRR n t V) ^ 2)

/-- **Lemma T** (inverse moment): `ϱ^{−2}` is integrable and `E_D ϱ^{−2} ≤ 3/θ` for `n ≥ n₁`,
orthonormal `V` and `t ∈ [0, C n]^r`. -/
def LemmaT57 (r : ℕ) (C θ : ℝ) (n1 : ℕ) : Prop :=
  ∀ n : ℕ, n1 ≤ n → ∀ V : Fin r → Fin n → ℝ, OrthoF V → ∀ t : Fin r → ℝ, BoxT C n t →
    Integrable (fun x => (rhoSq V x)⁻¹) (lawRR n t V) ∧ ∫ x, (rhoSq V x)⁻¹ ∂lawRR n t V ≤ 3 / θ

/-- **Surrogate**: for `t ∈ [0, C n]^r` and any anchor family with nonsingular Gram matrix,
`E_Z (g_{Q̃} − g_D)(σZ)² ≤ etaQ(e)² E_Z Var_D f(σZφ)`, `Q̃ = surrRR n (KRK C n e) t V`. -/
def PropSurr57 (d k r : ℕ) (C η : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ V : Fin r → Fin n → ℝ, OrthoF V → ∀ t : Fin r → ℝ, BoxT C n t →
    ∀ Ξ : Mono r d → Mono n d → ℝ, (gramX Ξ).det ≠ 0 → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      Integrable (fun Z : CoefIdxD n d → ℝ =>
          (gH57 (surrRR n (KRK C n η) t V) k f0 T Ξ (sg n d • Z) -
            gH57 (lawRR n t V) k f0 T Ξ (sg n d • Z)) ^ 2) (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (gH57 (surrRR n (KRK C n η) t V) k f0 T Ξ (sg n d • Z) -
          gH57 (lawRR n t V) k f0 T Ξ (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) ≤
        BstLean.Part43.etaQ η ^ 2 * EV56 d (lawRR n t V) k f0 T

/-- **Prop T1′** (error on the coefficient sphere, with Markov), for any anchor family with
nonsingular Gram matrix and `δ ≤ δ₀ ≤ 1/2`:
`Pr_M{c · EV < (B_D − g_{Q̃})(M)²} ≤ (10(k+1)² δ₀ + 5(k+1)² etaQ(e)²)/c`. -/
def PropT1_57 (d k r : ℕ) (C η : ℝ) : Prop :=
  ∀ n : ℕ, 100 ≤ n → ∀ V : Fin r → Fin n → ℝ, OrthoF V → ∀ t : Fin r → ℝ, BoxT C n t →
    ∀ Ξ : Mono r d → Mono n d → ℝ, (gramX Ξ).det ≠ 0 → ∀ δ0 : ℝ, 0 ≤ δ0 → δ0 ≤ 1 / 2 →
    deltaSqX (lawRR n t V) Ξ ≤ δ0 ^ 2 →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) → ∀ c : ℝ, 0 < c →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        c * EV56 d (lawRR n t V) k f0 T <
          (BofQ (lawRR n t V) k f0 T (unitOfD Z) -
            gW57 (surrRR n (KRK C n η) t V) k f0 T Ξ (unitOfD Z)) ^ 2} ≤
        ENNReal.ofReal ((10 * ((k : ℝ) + 1) ^ 2 * δ0 +
          5 * ((k : ℝ) + 1) ^ 2 * BstLean.Part43.etaQ η ^ 2) / c)

/-- **Angular moment** (Lemma T, lower tail): `E_D ϱ^{2k} ≥ a` for `n ≥ n₀`, orthonormal `V` and
`t ∈ [0, C n]^r`. -/
def PropAng57 (r k : ℕ) (C a : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ V : Fin r → Fin n → ℝ, OrthoF V → ∀ t : Fin r → ℝ, BoxT C n t →
    a ≤ ∫ x, rhoSq V x ^ k ∂lawRR n t V

/-- **Lower bound on `S`** for the anchors `xiRR d V W` (`2 ≤ d`, so block 1 is anchored exactly on
`V` and `τ ≥ ϱ²`), with the rank-`r` lower tail `E_D ϱ^{2k} ≥ θ^k/2` (Lemma T):
`E_Z S(σZ) ≥ c_L n^{−⌊(k−1)/2⌋} Σ_{j=1}^k ‖T_j‖²/𝒟^j`. -/
def PropLow57 (d k r : ℕ) (C cL : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ V : Fin r → Fin n → ℝ, OrthoF V → ∀ t : Fin r → ℝ, BoxT C n t →
    ∀ W : Fin r → Fin n → ℝ, (gramX (xiRR d V W)).det ≠ 0 →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      cL * Ssum57 n d k T / (n : ℝ) ^ ((k - 1) / 2) ≤
        ∫ Z, Sfl57 (lawRR n t V) k f0 T (xiRR d V W) (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-- **Lower bound on the proxy variance** (a statement about the law only):
`E_Z Var_D f(σZφ) ≥ c_E n^{−⌊(k−1)/2⌋} Σ_{j=1}^k ‖T_j‖²/𝒟^j`. -/
def PropEVLow57 (d k r : ℕ) (C cE : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ V : Fin r → Fin n → ℝ, OrthoF V → ∀ t : Fin r → ℝ, BoxT C n t →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      cE * Ssum57 n d k T / (n : ℝ) ^ ((k - 1) / 2) ≤ EV56 d (lawRR n t V) k f0 T

/-- **Prop T2′** (floor on the coefficient sphere): `Pr_M{Var_D f(Mφ) < s · EV} ≤ p + C₂/n`. -/
def PropT2_57 (d k r : ℕ) (C p s C2 : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ V : Fin r → Fin n → ℝ, OrthoF V → ∀ t : Fin r → ℝ, BoxT C n t →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        varFQ (lawRR n t V) k f0 T (unitOfD Z) < s * EV56 d (lawRR n t V) k f0 T} ≤
        ENNReal.ofReal (p + C2 / n)

end BstLean.Part57
