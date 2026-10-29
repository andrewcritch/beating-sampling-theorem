import BstLean.Part33ExactFormula
import BstLean.Part33Certificate
import BstLean.Part29Main
import BstLean.Part29Final
import BstLean.Part29Overlap
import BstLean.Part29Bessel
import BstLean.Part29Probability

/-!
# Part 33, wave 0: definitions and statement stubs for layers L2–L4 (cubic `(3,2)`)

Specification: `delegations/answers/p33-l2l4-spec-opus.md` (Route B, `Uof3` reusing Part 29's `AU`, the crude
level-6 ratio `6075` in `V6'`). This file holds definitions only; the theorems are proved in the wave-1 files
named in each section's comment.

Name clashes: `Part29Certificate` and `Part33Certificate` both define `P`, `CE`, `CH`, `CU`. This file opens only
selected Part 29 names; unqualified `P`, `CE`, `CG`, `CH`, `CU`, `D` are Part 33's.
-/

namespace BstLean.Part33

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (CoefIdx stdGauss unitOf cOf LOf aOf symOfRaw mapM qformC qformι AH AU keptOf frobSq
  coefX coeffS coefLaw gaussMom varOf)

variable {n : ℕ}

/-! ## §0 Conventions -/

/-- `D` as the real cardinality of the raw coefficient space. -/
noncomputable def Dc (n : ℕ) : ℝ := (Fintype.card (CoefIdx n) : ℝ)

/-- `‖Z‖²`. -/
noncomputable def r2 (Z : CoefIdx n → ℝ) : ℝ := ∑ α, Z α ^ 2

/-- Part 29's raw quadratic array `G (i, j, k) = a_{k,ij}`. -/
noncomputable def rawQ (Z : CoefIdx n → ℝ) : Fin n × Fin n × Fin n → ℝ := fun p => aOf Z p.2.2 p.1 p.2.1

/-- `‖T‖_F²`. -/
noncomputable def frobT (T : Fin n → Fin n → Fin n → ℝ) : ℝ := ∑ a, ∑ b, ∑ p, T a b p ^ 2

/-- `tr A²`, `A_ab = Σ_cd T_acd T_bcd`. -/
noncomputable def trA2 (T : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, (∑ c, ∑ d, T a c d * T b c d) ^ 2

/-- Products of at most `R` coordinates have the uniform-sphere moments; with integrability. -/
structure SphereProd (n R : ℕ) (μ : Measure (Fin n → ℝ)) : Prop where
  integ : ∀ r, r ≤ R → ∀ τ : Fin r → Fin n, Integrable (fun x : Fin n → ℝ => ∏ s, x (τ s)) μ
  mom : ∀ r, r ≤ R → ∀ τ : Fin r → Fin n,
    ∫ x, ∏ s, x (τ s) ∂μ =
      (∏ i, gaussMom (Finset.univ.filter fun s => τ s = i).card) / ∏ j ∈ Finset.range (r / 2), ((n : ℝ) + 2 * j)

/-- `w₄ = 1/ρ₄` (Part 29's private `floorW`, restated). -/
noncomputable def floorW4 (n : ℕ) : ℝ := 1 / ((n : ℝ) * (n + 2) * (n + 4) * (n + 6))

/-- `w₆ = 1/ρ₆`. -/
noncomputable def floorW6 (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (n + 2) * (n + 4) * (n + 6) * (n + 8) * (n + 10))

/-! ## §1 The coefficient readers, the dropped pieces and the programs -/

section readers
variable (M : CoefIdx n → ℝ)

noncomputable def QOf : Fin n → Matrix (Fin n) (Fin n) ℝ := fun k => symOfRaw (aOf M k)
noncomputable def tOf : Fin n → ℝ := fun k => ∑ i, QOf M k i i
noncomputable def nuOf : Fin n → ℝ := fun k => cOf M k + tOf M k / n
noncomputable def KOf : Fin n → Fin n → ℝ := fun k l => ∑ i, ∑ j, QOf M k i j * QOf M l j i
noncomputable def LLOf : Fin n → Fin n → ℝ := fun k l => ∑ i, LOf M k i * LOf M l i
/-- `C = LLᵀ/n + (2/ρ₂) K − (2/(nρ₂)) ttᵀ`. -/
noncomputable def COf : Fin n → Fin n → ℝ := fun k l =>
  LLOf M k l / n + 2 / rho2 n * KOf M k l - 2 / (n * rho2 n) * tOf M k * tOf M l

end readers

section pieces
variable (T : Fin n → Fin n → Fin n → ℝ) (M : CoefIdx n → ℝ)

/-- `v = tr₁₂ T`. -/
noncomputable def vT : Fin n → ℝ := fun p => ∑ a, T a a p
noncomputable def vt : ℝ := ∑ p, vT T p * tOf M p
noncomputable def vc : ℝ := ∑ p, vT T p * cOf M p

/-- `⟨T[c], K⟩`. -/
noncomputable def pcK : ℝ := ∑ a, ∑ b, ∑ p, T a b p * cOf M a * KOf M b p
/-- `⟨T[t], K⟩`, as `exact_formula3` writes it. -/
noncomputable def ptK : ℝ := ∑ a, ∑ b, ∑ p, T a b p * tOf M p * KOf M a b
/-- The triangle `Δ = Σ T_abc tr(Q_a Q_b Q_c)`. -/
noncomputable def pDel : ℝ :=
  ∑ a, ∑ b, ∑ p, T a b p * ∑ i, ∑ j, ∑ k, QOf M a i j * QOf M b j k * QOf M p k i
/-- `G₃ = Σ_c ⟨T_c, L Q_c Lᵀ⟩`. -/
noncomputable def pG3 : ℝ :=
  ∑ a, ∑ b, ∑ p, T a b p * ∑ i, ∑ j, LOf M a i * QOf M p i j * LOf M b j
/-- `⟨T[c], LLᵀ⟩`. -/
noncomputable def pcLL : ℝ := ∑ a, ∑ b, ∑ p, T a b p * cOf M p * LLOf M a b
/-- `⟨T[t], LLᵀ⟩`. -/
noncomputable def ptLL : ℝ := ∑ a, ∑ b, ∑ p, T a b p * tOf M p * LLOf M a b
/-- `T[c,t,t]`. -/
noncomputable def pctt : ℝ := ∑ a, ∑ b, ∑ p, T a b p * cOf M a * tOf M b * tOf M p
/-- `T[t,t,t]`. -/
noncomputable def pttt : ℝ := ∑ a, ∑ b, ∑ p, T a b p * tOf M a * tOf M b * tOf M p

/-! The chaos-1 parts `λ = ½ Δ_Z` (raw coordinates). -/
noncomputable def lcK : ℝ := ((n : ℝ) + n * (n - 1) / 4) * vc T M
noncomputable def ltK : ℝ := ((n : ℝ) + 2 + n * (n - 1) / 4) * vt T M
noncomputable def lDel : ℝ := 3 * ((n : ℝ) + 3) / 4 * vt T M
noncomputable def lG3 : ℝ := vt T M
noncomputable def lcLL : ℝ := (n : ℝ) * vc T M
noncomputable def ltLL : ℝ := (n : ℝ) * vt T M
noncomputable def lctt : ℝ := (n : ℝ) * vc T M
noncomputable def lttt : ℝ := 3 * (n : ℝ) * vt T M

end pieces

/-- The dropped cubic, in `ST2`'s order `α = (aCK, actt, aG, atLL, aΔ, aX, aW, acLL)`. -/
noncomputable def Xof (α : Fin 8 → ℝ) (T : Fin n → Fin n → Fin n → ℝ) (M : CoefIdx n → ℝ) : ℝ :=
  α 0 * pcK T M + α 1 * pctt T M + α 2 * pG3 T M + α 3 * ptLL T M + α 4 * pDel T M + α 5 * ptK T M
    + α 6 * pttt T M + α 7 * pcLL T M

/-- Its chaos-1 part. -/
noncomputable def lamOf (α : Fin 8 → ℝ) (T : Fin n → Fin n → Fin n → ℝ) (M : CoefIdx n → ℝ) : ℝ :=
  α 0 * lcK T M + α 1 * lctt T M + α 2 * lG3 T M + α 3 * ltLL T M + α 4 * lDel T M + α 5 * ltK T M
    + α 6 * lttt T M + α 7 * lcLL T M

noncomputable def alphaG (x : ℝ) : Fin 8 → ℝ := ![0, 0, 0, 0, 8 / rho3 x, 0, 0, 0]
noncomputable def alphaH (x : ℝ) : Fin 8 → ℝ :=
  ![6 / rho2 x, 0, 6 / rho2 x, -6 / (x * rho2 x), 8 / rho3 x, 6 / (x * rho2 x) - 24 / (x * rho3 x), gam x, 0]
noncomputable def alphaU (x : ℝ) : Fin 8 → ℝ :=
  ![6 / rho2 x, -6 / (x * rho2 x), 6 / rho2 x, 3 / x ^ 2 - 6 / (x * rho2 x), 8 / rho3 x,
    6 / (x * rho2 x) - 24 / (x * rho3 x), gam x - 6 / (x ^ 2 * rho2 x), 3 / x]

section programs
variable (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ)
  (M : CoefIdx n → ℝ)

/-- `B(M) = E_x f(m_M(x))`, cubic `f`. -/
noncomputable def Bof3 (μ : Measure (Fin n → ℝ)) : ℝ :=
  ∫ x, funF3 f0 b F T (mapM (cOf M) (LOf M) (QOf M) x) ∂μ

/-- `sd(M)² = Var_x f(m_M(x))`. -/
noncomputable def varOf3 (μ : Measure (Fin n → ℝ)) : ℝ :=
  ∫ x, (funF3 f0 b F T (mapM (cOf M) (LOf M) (QOf M) x) - Bof3 f0 b F T M μ) ^ 2 ∂μ

/-- Branch E: the right-hand side of `exact_formula3`. -/
noncomputable def Eof3 : ℝ :=
  f0 + ∑ k, b k * nuOf M k + ∑ k, ∑ l, F k l * nuOf M k * nuOf M l + ∑ k, ∑ l, F k l * COf M k l
    + ∑ a, ∑ b', ∑ p, T a b' p * nuOf M a * nuOf M b' * nuOf M p
    + 3 * ∑ a, ∑ b', ∑ p, T a b' p * nuOf M a * COf M b' p
    + 6 / rho2 n * pG3 T M - 6 / (n * rho2 n) * ptLL T M
    + 8 / rho3 n * pDel T M - 24 / (n * rho3 n) * ptK T M
    + gam n * pttt T M

/-- Branch G (quartic): `Δ` replaced by `λ_Δ/(D+2)`. -/
noncomputable def Gof3 : ℝ :=
  Eof3 f0 b F T M - Xof (alphaG n) T M + lamOf (alphaG n) T M / (Dc n + 2)

/-- Branch H (cubic heat): kept terms only. -/
noncomputable def Hof3 : ℝ :=
  keptOf f0 b F M + (∑ k, ∑ l, F k l * LLOf M k l) / n + (AH F).trace / Dc n
    - 2 / rho2 n * ((∑ k, ∑ l, F k l * tOf M k * tOf M l) / n)
    + ∑ a, ∑ b', ∑ p, T a b' p * nuOf M a * nuOf M b' * nuOf M p
    + 3 / n * ∑ a, ∑ b', ∑ p, T a b' p * nuOf M a * LLOf M b' p
    - 6 / (n * rho2 n) * ∑ a, ∑ b', ∑ p, T a b' p * nuOf M a * tOf M b' * tOf M p
    + lamOf (alphaH n) T M / (Dc n + 2)

/-- Branch U (below one sample), reusing Part 29's `AU` (drops `tᵀFt`). -/
noncomputable def Uof3 : ℝ :=
  keptOf f0 b F M + (AU F).trace / Dc n
    + ∑ a, ∑ b', ∑ p, T a b' p * nuOf M a * nuOf M b' * nuOf M p
    + lamOf (alphaU n) T M / (Dc n + 2)

end programs

/-! ## §2 Errors and normalization — file `Part33Branches.lean` -/

/-- The centred F-error numerator in Z-units. -/
noncomputable def EF (A : Matrix (CoefIdx n) (CoefIdx n) ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  qformι (A - (A.trace / Dc n) • (1 : Matrix (CoefIdx n) (CoefIdx n) ℝ)) Z

/-- The T-error numerator in Z-units: a homogeneous cubic polynomial of `Z`. -/
noncomputable def HT (α : Fin 8 → ℝ) (T : Fin n → Fin n → Fin n → ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  Xof α T Z - lamOf α T Z * r2 Z / (Dc n + 2)

section branches
variable (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ)

end branches

/-! ## §3.1 Generic Gaussian lemmas — file `Part33Euler.lean` -/

section euler
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end euler

/-! ## §3.2 The T-part, per group — files `Part33Grp124.lean`, `Part33Grp3.lean`, `Part33GrpAssembly.lean` -/

/-- The chaos-3 parts of the four variable-type groups. -/
noncomputable def grp (i : Fin 4) (α : Fin 8 → ℝ) (T : Fin n → Fin n → Fin n → ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  match i with
  | 0 => α 0 * (pcK T Z - lcK T Z) + α 1 * (pctt T Z - lctt T Z)
  | 1 => α 2 * (pG3 T Z - lG3 T Z) + α 3 * (ptLL T Z - ltLL T Z)
  | 2 => α 4 * (pDel T Z - lDel T Z) + α 5 * (ptK T Z - ltK T Z) + α 6 * (pttt T Z - lttt T Z)
  | 3 => α 7 * (pcLL T Z - lcLL T Z)

section groups
variable (α : Fin 8 → ℝ) (T : Fin n → Fin n → Fin n → ℝ)

-- file `Part33Grp124.lean`
end groups

/-! ## §3.3 F-part, parity cross term, per-branch total — file `Part33GrpAssembly.lean` -/

section totals
variable (F : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ)

end totals

/-! ## §4.1 Floor definitions -/

/-- The 15 perfect matchings of `Fin 6`, each pair `(x, y)` with `x < y`. -/
def matchings6 : Fin 15 → (Fin 6 × Fin 6) × (Fin 6 × Fin 6) × (Fin 6 × Fin 6) :=
  ![((0,1),(2,3),(4,5)), ((0,1),(2,4),(3,5)), ((0,1),(2,5),(3,4)),
    ((0,2),(1,3),(4,5)), ((0,2),(1,4),(3,5)), ((0,2),(1,5),(3,4)),
    ((0,3),(1,2),(4,5)), ((0,3),(1,4),(2,5)), ((0,3),(1,5),(2,4)),
    ((0,4),(1,2),(3,5)), ((0,4),(1,3),(2,5)), ((0,4),(1,5),(2,3)),
    ((0,5),(1,2),(3,4)), ((0,5),(1,3),(2,4)), ((0,5),(1,4),(2,3))]

/-- `C_S = 6 Σ_matchings T[a_{p₁}, a_{p₂}, a_{p₃}]` for a six-subset `S`, in raw coefficients `G`. -/
noncomputable def coefC6 (T : Fin n → Fin n → Fin n → ℝ) (S : Finset (Fin n)) (hS : S.card = 6)
    (G : Fin n × Fin n × Fin n → ℝ) : ℝ :=
  let s := S.orderEmbOfFin hS
  6 * ∑ m : Fin 15, ∑ a, ∑ b, ∑ p, T a b p
    * G (s (matchings6 m).1.1, s (matchings6 m).1.2, a)
    * G (s (matchings6 m).2.1.1, s (matchings6 m).2.1.2, b)
    * G (s (matchings6 m).2.2.1, s (matchings6 m).2.2.2, p)

/-- `C_S²`, extended by `0` off the six-subsets. -/
noncomputable def coefX6 (T : Fin n → Fin n → Fin n → ℝ) (S : Finset (Fin n))
    (G : Fin n × Fin n × Fin n → ℝ) : ℝ :=
  if hS : S.card = 6 then coefC6 T S hS G ^ 2 else 0

/-- The level-6 parity floor `Y₆` (Z-units via `G = rawQ Z`). -/
noncomputable def floorY6 (T : Fin n → Fin n → Fin n → ℝ) (G : Fin n × Fin n × Fin n → ℝ) : ℝ :=
  floorW6 n * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 6, coefX6 T S G

/-- Part 29's private level-4 floor `floorY`, restated: `‖e‖²`. -/
noncomputable def floorY4 (F : Matrix (Fin n) (Fin n) ℝ) (G : Fin n × Fin n × Fin n → ℝ) : ℝ :=
  floorW4 n * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 4, coefX F S G

/-- The sphere coefficient of `x_σ` (`σ : Fin 6 → Fin n`) in `T[q,q,q]`. -/
noncomputable def coeffS6 (T : Fin n → Fin n → Fin n → ℝ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (σ : Fin 6 → Fin n) : ℝ :=
  ∑ a, ∑ b, ∑ p, T a b p * ∑ π : Equiv.Perm (Fin 6),
    Q a (σ (π 0)) (σ (π 1)) * Q b (σ (π 2)) (σ (π 3)) * Q p (σ (π 4)) (σ (π 5))

/-- `T[c]` as a matrix. -/
noncomputable def Tc (T : Fin n → Fin n → Fin n → ℝ) (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun b p => ∑ a, T a b p * c a

/-- `o_c`, from `3T[c,q,q]`. -/
noncomputable def oC (T : Fin n → Fin n → Fin n → ℝ) (c : Fin n → ℝ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (σ : Fin 4 → Fin n) : ℝ :=
  3 * coeffS (Tc T c) Q σ

/-- `o_L`, from `3T[Lx,Lx,q]`. -/
noncomputable def oL (T : Fin n → Fin n → Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (σ : Fin 4 → Fin n) : ℝ :=
  3 * ∑ a, ∑ b, ∑ p, T a b p * ∑ π : Equiv.Perm (Fin 4),
    L a (σ (π 0)) * L b (σ (π 1)) * Q p (σ (π 2)) (σ (π 3))

/-- `o_Q`, the degree-6 leak of `T[q,q,q]` into level 4. -/
noncomputable def oQ (T : Fin n → Fin n → Fin n → ℝ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (σ : Fin 4 → Fin n) : ℝ :=
  1 / ((n : ℝ) + 8) * ∑ a, ∑ b, ∑ p, T a b p * ∑ τ : Fin 6 → Fin n,
    Q a (τ 0) (τ 1) * Q b (τ 2) (τ 3) * Q p (τ 4) (τ 5)
      * ∏ i, gaussMom (Finset.univ.filter fun s : Fin 10 => Fin.append τ σ s = i).card

/-- The level-4 T-coefficient `o_S`. -/
noncomputable def oS (T : Fin n → Fin n → Fin n → ℝ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (σ : Fin 4 → Fin n) : ℝ :=
  oC T c Q σ + oL T L Q σ + oQ T Q σ

/-- `w₄ Σ_{|S|=4} h(S)²`, over sorted enumerations. -/
noncomputable def sumSq4 (h : (Fin 4 → Fin n) → ℝ) : ℝ :=
  floorW4 n * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 4,
    if hS : S.card = 4 then h (S.orderEmbOfFin hS) ^ 2 else 0

/-- `w₄ Σ_{|S|=4} h₁(S) h₂(S)`. -/
noncomputable def sumProd4 (h₁ h₂ : (Fin 4 → Fin n) → ℝ) : ℝ :=
  floorW4 n * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 4,
    if hS : S.card = 4 then h₁ (S.orderEmbOfFin hS) * h₂ (S.orderEmbOfFin hS) else 0

/-- `‖o‖²` in Z-units. -/
noncomputable def normO (T : Fin n → Fin n → Fin n → ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  sumSq4 (oS T (cOf Z) (LOf Z) (QOf Z))

/-- The `Var/E²` bound of `Y₆` with the crude ratio `6075` at overlaps 4, 5, 6. -/
noncomputable def V6p (x : ℝ) : ℝ :=
  (6075 * (1 + 6 * (x - 6) + 15 * ch2 (x - 6)) + 6 / 25 * 20 * ch3 (x - 6) + 2 / 25 * 15 * ch4 (x - 6)) / ch6 x

/-! Route-B constants. -/
noncomputable def sBarHB : ℝ := 803 / 200 * (1001 / 999)
noncomputable def sBarUB : ℝ := 321 / 40 * (1001 / 999)
noncomputable def cB : ℝ := (27 / 2) / (6 / 25)
noncomputable def SHB : ℝ := 2701 / 100
noncomputable def SUB : ℝ := 1801 / 100
/-- `D₋ = (999/1000) D`. -/
noncomputable def Dm (n : ℕ) : ℝ := 999 / 1000 * Dc n

/-- The two-level floor `G'(f, t) = Φ t² + (√(D₋ φ) f − √ĉ t)₊²`. -/
noncomputable def Gfloor (Phi phi c Dmin f t : ℝ) : ℝ :=
  Phi * t ^ 2 + (max 0 (Real.sqrt (Dmin * phi) * f - Real.sqrt c * t)) ^ 2

/-! ## §4.2 The pointwise floor — file `Part33Parity.lean` -/

section parity
variable (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ)

end parity

/-! ## §4.3 Level 6 — files `Part33Cov6.lean`, `Part33Cov6High.lean`, `Part33Overlap6.lean` -/

section level6
variable (T : Fin n → Fin n → Fin n → ℝ)

-- file `Part33Cov6.lean`
end level6

-- file `Part33Overlap6.lean`
section overlap6
variable {Ω : Type*} [MeasurableSpace Ω]

end overlap6

/-! ## §4.4 Level-4 F-floor — file `Part33OFloor.lean` (restates Part 29's private `floor_gauss_failure`) -/

/-! ## §4.5 Level-4 T-part `‖o‖²` — file `Part33OFloor.lean` -/

section ofloor
variable (T : Fin n → Fin n → Fin n → ℝ)

end ofloor

/-! ## §4.6 The radial event — file `Part33Radial.lean` -/

/-! ## §4.7 and §5.1 — file `Part33Probability.lean` -/

section cheb
variable {Ω : Type*} [MeasurableSpace Ω]

end cheb

/-! ## §5 Route-B arithmetic — file `Part33CertB.lean` -/

section certB
variable (t : ℕ)

end certB

/-! ## §5.2 The branch theorems — file `Part33Main.lean` -/

section main
variable (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ)

end main

/-! ## Moments — file `Part33Moments.lean`; and the instantiation — file `Part33Final.lean` -/

section final
variable (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ)

end final

end BstLean.Part33
