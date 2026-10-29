import BstLean.Part56Defs
import BstLean.Part48Defs

/-!
# Part 58, wave 0: frozen definitions — law-sensitivity (Claim LS) and formulation (a)

Source: `delegations/answers/omLS-opus-prover.md` §§2–8 (Prop W′, Lemmas P, Q, U, K, Y1–Y3,
Theorem LS-i-G, Theorem LS-i, consequences C1 and C3), and the structural facts of
`omLS-codex-disprover.md` §2–§3. Specification: `delegations/answers/p58-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions. Part 41, 43, 53 and 56 names are reused. `k = d_f`, `d = d_M`, `f = (f₀, T)`,
`σ = sg n d`. The function `f` is a constant plus a homogeneous form of degree `k`: `HomF k T` says
`T_j = 0` for `1 ≤ j < k`.

* **Laws.** `lawRK n t v ∝ exp(t (v·x)²) σ` (Part 56). The uniform law is `uniformSphere n`
  (`= lawRK n 0 v`, proved in `Part58Main.lawRK_zero`).
* **The tilt statistic.** `yv v x = (v·x)²`, `meanY n t v = E_{D_{t,v}} y`, `varY n t v = Var_{D_{t,v}} y`,
  `y0 C n = 1 − 1/(2C) − ln(2C)/(2C) − ln(n)/(C n)` (Lemma Y1).
* **Kernels.** `kap d x = κ_x = ‖φ(x)‖² = K(x, x)`; `Kxy d x y = K(x, y) = ⟨φ(x), φ(y)⟩`;
  `k2 d v x = k_2(x, v) = ⟨φ_2(x), φ_2(v)⟩` (Part 56's `kJ d 2`).
* **Chaos weights.** `lc k c = (k − c)/2`. `wc58 n d k T c = c! σ^{2c} (σ⁴/4)^l (l!)^{−2} (k!/c!)² ‖tr^l T_k‖²`
  for `c ≤ k`, `c ≡ k (mod 2)`, `l = lc k c`, and `0` otherwise (`= σ^{2c}‖H_c‖²/c!` of the source).
* **Chaos Gram terms.** `Gc d k c μ ν = ∫∫ (κ_x κ_y)^l K(x,y)^c dν(y) dμ(x)`;
  `Qc d k c μ ν = Gc μ μ − 2 Gc μ ν + Gc ν ν` (`= ‖X_c(μ) − X_c(ν)‖²`);
  `mk2 d k c μ v = E_μ κ^l k_2(·, v)^c` (the projection of `X_c(μ)` on `φ_2(v)^{⊗c}`).
* **The law-gap.** `dB n d k f0 T t v M = B_{D_{t,v}}(M) − B_U(M)`.
* **Statements.** The interfaces between the wave-1 files are the `Prop`-valued definitions of §5.
  A wave-1 file proves one or two of them, and may take others as hypotheses; it does not import
  another wave-1 file.
-/

namespace BstLean.Part58

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM phiSq contr trL frob Tens TSymm fval varU)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (sg)
open BstLean.Part56 (UnitV lawRK kJ EV56)

variable {n d : ℕ}

/-! ## §1 The admissible functions -/

/-- `f = f₀ + T_k[y^{⊗k}]`: every `T_j` with `1 ≤ j < k` vanishes. -/
def HomF (k : ℕ) (T : Tens n) : Prop := ∀ j, 1 ≤ j → j < k → ∀ w, T j w = 0

/-! ## §2 The tilt statistic -/

/-- `y = (v·x)²`. -/
def yv (v x : Fin n → ℝ) : ℝ := (∑ i, v i * x i) ^ 2

/-- `E_{D_{t,v}} y`. -/
noncomputable def meanY (n : ℕ) (t : ℝ) (v : Fin n → ℝ) : ℝ := ∫ x, yv v x ∂lawRK n t v

/-- `Var_{D_{t,v}} y`. -/
noncomputable def varY (n : ℕ) (t : ℝ) (v : Fin n → ℝ) : ℝ := varU (lawRK n t v) (yv v)

/-- `y₀(C, n) = 1 − 1/(2C) − ln(2C)/(2C) − ln(n)/(C n)` (Lemma Y1). -/
noncomputable def y0 (C : ℝ) (n : ℕ) : ℝ :=
  1 - 1 / (2 * C) - Real.log (2 * C) / (2 * C) - Real.log n / (C * n)

/-! ## §3 Kernels and chaos weights -/

/-- `κ_x = ‖φ(x)‖² = K(x, x)`. -/
noncomputable def kap (d : ℕ) (x : Fin n → ℝ) : ℝ := phiSq d x

/-- `K(x, y) = ⟨φ(x), φ(y)⟩` (all degrees `0..d`, unweighted monomials). -/
noncomputable def Kxy (d : ℕ) (x y : Fin n → ℝ) : ℝ := ∑ p : Mono n d, phiM x p * phiM y p

/-- `k_2(x, v) = ⟨φ_2(x), φ_2(v)⟩`. -/
noncomputable def k2 (d : ℕ) (v x : Fin n → ℝ) : ℝ := kJ d 2 x v

/-- `l_c = (k − c)/2`. -/
def lc (k c : ℕ) : ℕ := (k - c) / 2

/-- The chaos weight `w_c = c! σ^{2c} (σ⁴/4)^l (l!)^{−2} (k!/c!)² ‖tr^l T_k‖²` (`c ≤ k`, `c ≡ k mod 2`). -/
noncomputable def wc58 (n d k : ℕ) (T : Tens n) (c : ℕ) : ℝ :=
  if c ≤ k ∧ (k - c) % 2 = 0 then
    (c.factorial : ℝ) * sg n d ^ (2 * c) * (sg n d ^ 4 / 4) ^ lc k c / ((lc k c).factorial : ℝ) ^ 2 *
      ((k.factorial : ℝ) / (c.factorial : ℝ)) ^ 2 * frob (trL (lc k c) (T k))
  else 0

/-- `G_c(μ, ν) = ∫∫ (κ_x κ_y)^l K(x, y)^c dν(y) dμ(x)`. -/
noncomputable def Gc (d k c : ℕ) (μ ν : Measure (Fin n → ℝ)) : ℝ :=
  ∫ x, ∫ y, (kap d x * kap d y) ^ lc k c * Kxy d x y ^ c ∂ν ∂μ

/-- `Q_c(μ, ν) = G_c(μ, μ) − 2 G_c(μ, ν) + G_c(ν, ν) = ‖X_c(μ) − X_c(ν)‖²`. -/
noncomputable def Qc (d k c : ℕ) (μ ν : Measure (Fin n → ℝ)) : ℝ :=
  Gc d k c μ μ - 2 * Gc d k c μ ν + Gc d k c ν ν

/-- `E_μ κ^l k_2(·, v)^c`. -/
noncomputable def mk2 (d k c : ℕ) (μ : Measure (Fin n → ℝ)) (v : Fin n → ℝ) : ℝ :=
  ∫ x, kap d x ^ lc k c * k2 d v x ^ c ∂μ

/-! ## §4 The law-gap -/

/-- `Δ(M) = B_{D_{t,v}}(M) − B_U(M)`. -/
noncomputable def dB (n d k : ℕ) (f0 : ℝ) (T : Tens n) (t : ℝ) (v : Fin n → ℝ)
    (M : CoefIdxD n d → ℝ) : ℝ :=
  BofQ (lawRK n t v) k f0 T M - BofQ (uniformSphere n) k f0 T M

/-! ## §5 The interface statements -/

/-- **Prop W′, gap part** (exact chaos identity, from Part 53's Lemma W): for laws `μ, ν` on the
sphere and homogeneous `f`, `E_Z (B_μ − B_ν)(σZ)² = Σ_{c ≤ k} w_c Q_c(μ, ν)`, with the integrand
integrable. -/
def PropW58 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ ν : Measure (Fin n → ℝ)), SphLaw n μ → SphLaw n ν →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → HomF k T →
      Integrable (fun Z : CoefIdxD n d → ℝ =>
          (BofQ μ k f0 T (sg n d • Z) - BofQ ν k f0 T (sg n d • Z)) ^ 2) (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (BofQ μ k f0 T (sg n d • Z) - BofQ ν k f0 T (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) =
        ∑ c ∈ Finset.range (k + 1), wc58 n d k T c * Qc d k c μ ν

/-- **Prop W′, variance part**: `E_Z Var_μ f(σZφ) = Σ_{c ≤ k} w_c (E_μ κ^k − G_c(μ, μ))`, with the
integrand integrable. -/
def PropWV58 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → HomF k T →
      Integrable (fun Z : CoefIdxD n d → ℝ => varFQ μ k f0 T (sg n d • Z)) (stdGauss (CoefIdxD n d)) ∧
      EV56 d μ k f0 T =
        ∑ c ∈ Finset.range (k + 1), wc58 n d k T c * ((∫ x, kap d x ^ k ∂μ) - Gc d k c μ μ)

/-- **Lemma P** (positivity and projection): `Q_c(μ, ν) ≥ 0`, and for unit `v` and `c ≥ 1`,
`Q_c(μ, ν) ≥ (E_μ κ^l k_2^c − E_ν κ^l k_2^c)²`. -/
def LemmaP58 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ ν : Measure (Fin n → ℝ)), SphLaw n μ → SphLaw n ν → ∀ c : ℕ,
    0 ≤ Qc d k c μ ν ∧
    ∀ v : Fin n → ℝ, UnitV v → 1 ≤ c → (mk2 d k c μ v - mk2 d k c ν v) ^ 2 ≤ Qc d k c μ ν

/-- **Lemma Q (hi)**: for `d ≥ 2`, every law on the sphere and unit `v`:
`E_μ κ^l k_2^c ≥ 2^{−c} (E_μ y)^c`. -/
def LemmaQhi58 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ v : Fin n → ℝ, UnitV v → ∀ c : ℕ,
    (∫ x, yv v x ∂μ) ^ c / 2 ^ c ≤ mk2 d k c μ v

/-- **Lemma Q (U)**, weak form: under the uniform law, `E κ^l k_2^c ≤ (d+1)^l/n` (`c ≥ 1`).
(The source proves `(d+1)^l (2c−1)!!/n^c`; the weak form suffices and needs only second moments.) -/
def LemmaQU58 (d k : ℕ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ c : ℕ, 1 ≤ c →
    mk2 d k c (uniformSphere n) v ≤ ((d : ℝ) + 1) ^ lc k c / n

/-- **Lemma U** (chaos `c ≥ 1`): `E_μ κ^k − G_c(μ, μ) ≤ (d+1)^k − 1`. -/
def LemmaUp58 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ c : ℕ, 1 ≤ c →
    (∫ x, kap d x ^ k ∂μ) - Gc d k c μ μ ≤ ((d : ℝ) + 1) ^ k - 1

/-- **Lemma U** (chaos `0`, even `k ≥ 2`): the chaos-`0` variance is charged to chaos `2`,
`w_0 (E κ^k − G_0) ≤ w_2 (d+1)^{k−2} n Var_μ(κ)/2`. -/
def LemmaV0_58 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ T : Tens n, TSymm k T →
    wc58 n d k T 0 * ((∫ x, kap d x ^ k ∂μ) - Gc d k 0 μ μ) ≤
      wc58 n d k T 2 * (((d : ℝ) + 1) ^ (k - 2) * n * varU μ (kap d) / 2)

/-- **Lemma K** (fluctuation of `κ` under a rank-one Bingham law):
`Var_{D_{t,v}} κ ≤ d²(d+1)²/(n − 2) + d⁶ Var_{D_{t,v}} y` for `n ≥ 3`. -/
def LemmaK58 (d : ℕ) : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ,
    varU (lawRK n t v) (kap d) ≤
      (d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2 / ((n : ℝ) - 2) + (d : ℝ) ^ 6 * varY n t v

/-- **Lemma Y1** (the mean of `y` under the tilt): for `n ≥ 3`, `C > 1/2` and `t ≥ C n`,
`E_{D_{t,v}} y ≥ y₀(C, n)`. -/
def LemmaY1_58 : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ C : ℝ, 1 / 2 < C → ∀ t : ℝ, C * n ≤ t → ∀ v : Fin n → ℝ, UnitV v →
    y0 C n ≤ meanY n t v

/-- **Tail of `y` under the uniform law** (the input of Lemma Y1): for `n ≥ 3`, `0 < b < 1` and unit
`v`, `U{y ≥ b} ≥ (1 − b)^{(n−1)/2}/(n − 1)`. -/
def LemmaTail58 : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ b : ℝ, 0 < b → b < 1 → ∀ v : Fin n → ℝ, UnitV v →
    ENNReal.ofReal ((1 - b) ^ (((n : ℝ) - 1) / 2) / ((n : ℝ) - 1)) ≤
      uniformSphere n {x | b ≤ yv v x}

/-- **Lemma Y2 (b)** (a tilt with small variance of `y`): for `n ≥ 3` and `0 ≤ C' < C` there is
`t* ∈ [C' n, C n]`, depending on `n, C, C'` only, with `Var_{D_{t*,v}} y ≤ 1/((C − C') n)` for every
unit `v`. -/
def LemmaY2_58 : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ C' C : ℝ, 0 ≤ C' → C' < C →
    ∃ ts : ℝ, C' * n ≤ ts ∧ ts ≤ C * n ∧
      ∀ v : Fin n → ℝ, UnitV v → varY n ts v ≤ 1 / ((C - C') * n)

/-- **Polynomiality**: for a law on the sphere and a scale `s`, `Z ↦ B_μ(s Z)` is a real polynomial
of total degree `≤ k` in the coefficients. -/
def PropPoly58 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (s f0 : ℝ) (T : Tens n),
    ∃ P : MvPolynomial (CoefIdxD n d) ℝ, P.totalDegree ≤ k ∧
      ∀ Z : CoefIdxD n d → ℝ, MvPolynomial.eval Z P = BofQ μ k f0 T (s • Z)

/-- **Theorem LS-i-G** at some tilt (the Gaussian-proxy ratio): for `n ≥ n₁` there is
`t* ∈ [C' n, C n]` such that for every unit `v` and homogeneous `f`:
`r · E_Z Var_{D_{t*,v}} ≤ E_Z Δ(σZ)²`. -/
def PropG58 (d k : ℕ) (C C' r : ℝ) (n1 : ℕ) : Prop :=
  ∀ n : ℕ, n1 ≤ n → ∃ ts : ℝ, C' * n ≤ ts ∧ ts ≤ C * n ∧
    ∀ v : Fin n → ℝ, UnitV v → ∀ (f0 : ℝ) (T : Tens n), TSymm k T → HomF k T →
      r * EV56 d (lawRK n ts v) k f0 T ≤
        ∫ Z, dB n d k f0 T ts v (sg n d • Z) ^ 2 ∂stdGauss (CoefIdxD n d)

/-- **Theorem LS-i-G** at every tilt `t ∈ [C' n, C n]` (the form proved for odd `k`). -/
def PropGall58 (d k : ℕ) (C C' r : ℝ) (n1 : ℕ) : Prop :=
  ∀ n : ℕ, n1 ≤ n → ∀ ts : ℝ, C' * n ≤ ts → ts ≤ C * n →
    ∀ v : Fin n → ℝ, UnitV v → ∀ (f0 : ℝ) (T : Tens n), TSymm k T → HomF k T →
      r * EV56 d (lawRK n ts v) k f0 T ≤
        ∫ Z, dB n d k f0 T ts v (sg n d • Z) ^ 2 ∂stdGauss (CoefIdxD n d)

/-- **High probability on the coefficient sphere** (Theorem LS-i from LS-i-G): small ball for
`Δ(σZ)²` (degree `≤ 2k`), Markov for `Var(σZ)`, and the cone property of both events (homogeneity of
`f − f₀`). For a small-ball level `t_sb` at probability `p`, a ratio `r` and `δ₁ > 0`:
`Pr_M{Δ(M)² < t_sb r δ₁ Var_{D_{t,v}}(M)} ≤ p + δ₁`, `M = Z/‖Z‖`. -/
def PropHP58 (d k : ℕ) : Prop :=
  ∀ (p tsb : ℝ), 0 ≤ p → SBLevel (2 * k) p tsb → 0 < tsb → ∀ (r δ1 : ℝ), 0 < r → 0 < δ1 →
    ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ) (v : Fin n → ℝ), UnitV v →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → HomF k T →
        r * EV56 d (lawRK n t v) k f0 T ≤
          ∫ Z, dB n d k f0 T t v (sg n d • Z) ^ 2 ∂stdGauss (CoefIdxD n d) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          dB n d k f0 T t v (unitOfD Z) ^ 2 < tsb * r * δ1 * varFQ (lawRK n t v) k f0 T (unitOfD Z)} ≤
          ENNReal.ofReal (p + δ1)

end BstLean.Part58
