import BstLean.Part157Hell
import BstLean.Part150Bin

/-!
# Part 157, item 4: the centres, `τ₀` and the sampling step of the paper's program in Lean

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-01-statement-program.tex`, "Arithmetic and finite sums" and the ordered program,
steps 1, 2, 3 (centres and `τ₀`) and steps 4, 6 (grid, nearest node, the input of `F`).

This file is a TRANSCRIPTION of the paper's formulas into Lean definitions, with the
measurability proofs that `Design n` needs. No property of these definitions is proved here
except measurability. A reviewer must check the transcription against the paper.

* Step 1: `ATsum`, `QTsum`, `Tpi`, `piT`, `cNt`, `dNt`, `rNt`, `Tkap`, `kapT`, `JW`.
* Step 2: `SWp`, `sWp`, `bWp` (the binomial World centre `b_W`), `tau0p` (`τ₀`).
* Step 3: `bAp` (the global Agent centre `b = b'/ρ`, `n` signs in each binomial sum).
* `paperCentres n : Centres n`.
* Steps 4 and 6: `gridMix`: the clipping of the latitude to `[L, H]`, the nearest node of the
  `512 n` nodes, `λ̃ = f̃_g/√e_b`, `S̃ = γ_A·max(1/5, ω̃_g − f̃_g²)`, for stored tables
  `f̃`, `ω̃` that are measurable functions of the retained data.
* `paperDesign n fT wT`: the design of the paper's program for given stored tables. The
  conditional passes (step 5, the first-layer sphere moments) that compute the tables are NOT
  defined in Lean.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part141 (aOf rowS measurable_aOf measurable_rowS)
open BstLean.Part150 (binMean bT rhoC measurable_bT measurable_rhoC measurable_binMean_affine)

/-! ## Step 1: the constants of the program -/

/-- `A_T(v) = Σ_{j<T} (−1)^j v^{2j+1}/(2j+1)` (the finite sum for the inverse tangent). -/
noncomputable def ATsum (T : ℕ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range T, (-1 : ℝ) ^ j * v ^ (2 * j + 1) / (2 * (j : ℝ) + 1)

/-- `Q_T(v) = Σ_{j<T} (2j)! v^{2j+1}/(4^j (j!)² (2j+1))` (the finite sum for the inverse sine). -/
noncomputable def QTsum (T : ℕ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range T, ((2 * j).factorial : ℝ) * v ^ (2 * j + 1) /
    (4 ^ j * (j.factorial : ℝ) ^ 2 * (2 * (j : ℝ) + 1))

/-- `T_π = min{T ≥ 1 : 25^T ≥ 10²³ N²}`, `N = 2n`. -/
noncomputable def Tpi (n : ℕ) : ℕ := sInf {T : ℕ | 1 ≤ T ∧ 10 ^ 23 * (2 * n) ^ 2 ≤ 25 ^ T}

/-- `π̃ = 16 A_{T_π}(1/5) − 4 A_{T_π}(1/239)`. -/
noncomputable def piT (n : ℕ) : ℝ := 16 * ATsum (Tpi n) (1 / 5) - 4 * ATsum (Tpi n) (1 / 239)

/-- `c̃_N = π̃⁻¹ ∏_{j=1}^{n−1} 2j/(2j+1)`. -/
noncomputable def cNt (n : ℕ) : ℝ :=
  (piT n)⁻¹ * ∏ j ∈ Finset.Icc 1 (n - 1), (2 * (j : ℝ)) / (2 * (j : ℝ) + 1)

/-- `d̃_N = 1/N − 2 c̃_N²`. -/
noncomputable def dNt (n : ℕ) : ℝ := 1 / (2 * (n : ℝ)) - 2 * cNt n ^ 2

/-- `r̃ = 2 N c̃_N²`. -/
noncomputable def rNt (n : ℕ) : ℝ := 2 * (2 * (n : ℝ)) * cNt n ^ 2

/-- `T_κ = min{T ≥ 1 : (355/1000)(1014/10000)^T ≤ 10⁻⁵/n²}`. -/
noncomputable def Tkap (n : ℕ) : ℕ :=
  sInf {T : ℕ | 1 ≤ T ∧ (355 / 1000 : ℝ) * (1014 / 10000) ^ T ≤ 1 / (10 ^ 5 * (n : ℝ) ^ 2)}

/-- `κ̃ = (√(1 − r̃²) + r̃ (π̃/2 + Q_{T_κ}(r̃)))/π̃`. -/
noncomputable def kapT (n : ℕ) : ℝ :=
  (√(1 - rNt n ^ 2) + rNt n * (piT n / 2 + QTsum (Tkap n) (rNt n))) / piT n

/-- `J_W = ⌈√m_W⌉`: the number of signs of the World binomial sum. -/
noncomputable def JW (n : ℕ) : ℕ := ⌈√(mW n : ℝ)⌉₊

variable {n : ℕ}

/-! ## Step 2: the World centre and `τ₀` -/

/-- `S_W = m_W⁻¹ Σ_i |row_i(W₁)|²`. -/
noncomputable def SWp (θ : WHid n) : ℝ := rowS θ.1 / (mW n : ℝ)

/-- `s_W = √(S_W d̃_N)`. -/
noncomputable def sWp (θ : WHid n) : ℝ := √(SWp θ * dNt n)

/-- **The World centre of the paper**: `b_{W,i} = B_{J_W}[z ↦ ReLU((W₂ h_W)_i + s_W z)]`,
`h_{W,i} = c̃_N |row_i(W₁)|`. -/
noncomputable def bWp (θ : WHid n) : Fin (mW n) → ℝ :=
  fun i => binMean (JW n) (fun z => relu (aOf (cNt n) θ i + sWp θ * z))

/-- **`τ₀` of the paper**: `τ₀² = t_W ν_W max(0, w₀)`, `ν_W = |b_W|²`,
`w₀ = N t_W ν_W/(S_W κ̃²) − 1`, `t_W = 2/m_W`, `N = 2n`. -/
noncomputable def tau0p (θ : WHid n) : ℝ :=
  √(2 / (mW n : ℝ) * normSq (bWp θ) *
    max 0 (2 * (n : ℝ) * (2 / (mW n : ℝ)) * normSq (bWp θ) / (SWp θ * kapT n ^ 2) - 1))

lemma measurable_SWp : Measurable (SWp (n := n)) :=
  (measurable_rowS.comp measurable_fst).div_const _

lemma measurable_sWp : Measurable (sWp (n := n)) := (measurable_SWp.mul_const _).sqrt

lemma measurable_bWp : Measurable (bWp (n := n)) :=
  measurable_pi_iff.mpr fun i =>
    measurable_binMean_affine (JW n) measurable_relu
      ((measurable_pi_apply i).comp (measurable_aOf (cNt n))) measurable_sWp

lemma measurable_tau0p : Measurable (tau0p (n := n)) := by
  have hν : Measurable (fun θ : WHid n => normSq (bWp θ)) := measurable_normSq.comp measurable_bWp
  unfold tau0p
  exact ((hν.const_mul _).mul (measurable_const.max
    (((hν.const_mul _).div (measurable_SWp.mul_const _)).sub_const 1))).sqrt

/-! ## Step 3: the global Agent centre -/

/-- **The global Agent centre of the paper**: `b = b'/ρ`, `ρ = √(|ĉ|² + n τ₀²)`,
`b'_j = B_n[z ↦ ReLU((A₂ ĥ₁)_j + √(ŝ_h²) z)]`, with `ĥ₁`, `ŝ_h²` the binomial first-layer
moments (`bT n n` of Part 150: `n` signs in each of the two global sums). -/
noncomputable def bAp (wc : WRet n) (θ : AHid n) : Fin (mA n) → ℝ :=
  fun j => bT n n θ.1 θ.2 wc.2 (tau0p wc.1) j / rhoC wc.2 (tau0p wc.1)

lemma measurable_bAp : Measurable (fun p : WRet n × AHid n => bAp p.1 p.2) := by
  have hx : Measurable (fun p : WRet n × AHid n =>
      (((p.1.2, tau0p p.1.1), p.2) : ((Fin n → ℝ) × ℝ) × HidParam n (mA n))) :=
    (((measurable_snd.comp measurable_fst).prodMk
      (measurable_tau0p.comp (measurable_fst.comp measurable_fst))).prodMk measurable_snd)
  have h1 : Measurable (fun p : WRet n × AHid n => bT n n p.2.1 p.2.2 p.1.2 (tau0p p.1.1)) := by
    have h := (measurable_bT (n := n) (m := mA n) n n).comp hx
    exact h
  have h2 : Measurable (fun p : WRet n × AHid n => rhoC p.1.2 (tau0p p.1.1)) := by
    have h := (measurable_rhoC (n := n)).comp (measurable_fst.comp hx)
    exact h
  exact measurable_pi_iff.mpr fun j => ((measurable_pi_apply j).comp h1).div h2

/-- **The two centres of the paper's program.** -/
noncomputable def paperCentres (n : ℕ) : Centres n where
  bW := bWp
  bA := bAp
  mbW := measurable_bWp
  mbA := measurable_bAp

/-! ## Steps 4 and 6: the grid and the nearest node -/

/-- The number of latitude nodes: `J_s = 512 n`. -/
def Js (n : ℕ) : ℕ := 512 * n

/-- The index of the nearest node of the latitude `s`: clip `s` to `[L, H]`, then
`g = min(J_s − 1, ⌊(s − L)/Δ⌋)` (the nodes are `s_g = L + (g + 1/2)Δ`; at a midpoint between two
nodes the larger index; at `H` the last node). -/
noncomputable def nodeIdx (Jn : ℕ) (L H s : ℝ) : ℕ :=
  min (Jn - 1) ⌊(max L (min H s) - L) / ((H - L) / (Jn : ℝ))⌋₊

/-- **The mixture table of the paper's sampling step.** For stored values `f̃_g`, `ω̃_g`
(`fT c g`, `wT c g`): `L = s_c − 6τ₀/ρ`, `H = s_c + 6τ₀/ρ`, `s_c = |ĉ|/ρ`, `e_b = |b|²/n`,
and at the nearest node `g` of the latitude `s`:
`λ̃ = f̃_g/√e_b`, `S̃ = (2/n)·max(1/5, ω̃_g − f̃_g²)`. -/
noncomputable def gridMix (D : Centres n) (τ : Ret n → ℝ) (fT wT : Ret n → ℕ → ℝ) (c : Ret n)
    (s : ℝ) : ℝ × ℝ :=
  (fT c (nodeIdx (Js n) (√(normSq c.1.2) / rhoC c.1.2 (τ c) - 6 * τ c / rhoC c.1.2 (τ c))
      (√(normSq c.1.2) / rhoC c.1.2 (τ c) + 6 * τ c / rhoC c.1.2 (τ c)) s) /
      √(normSq (D.bA c.1 c.2.1.1) / (n : ℝ)),
    2 / (n : ℝ) * max (1 / 5)
      (wT c (nodeIdx (Js n) (√(normSq c.1.2) / rhoC c.1.2 (τ c) - 6 * τ c / rhoC c.1.2 (τ c))
        (√(normSq c.1.2) / rhoC c.1.2 (τ c) + 6 * τ c / rhoC c.1.2 (τ c)) s) -
      fT c (nodeIdx (Js n) (√(normSq c.1.2) / rhoC c.1.2 (τ c) - 6 * τ c / rhoC c.1.2 (τ c))
        (√(normSq c.1.2) / rhoC c.1.2 (τ c) + 6 * τ c / rhoC c.1.2 (τ c)) s) ^ 2))

lemma measurable_nodeIdx_comp {α : Type*} [MeasurableSpace α] (Jn : ℕ) {L H s : α → ℝ}
    (hL : Measurable L) (hH : Measurable H) (hs : Measurable s) :
    Measurable (fun x => nodeIdx Jn (L x) (H x) (s x)) := by
  unfold nodeIdx
  exact measurable_const.min
    (Nat.measurable_floor.comp (((hL.max (hH.min hs)).sub hL).div ((hH.sub hL).div_const _)))

lemma measurable_table_comp {α : Type*} [MeasurableSpace α] {f : Ret n → ℕ → ℝ}
    (hf : ∀ g, Measurable (fun c => f c g)) {c : α → Ret n} {g : α → ℕ} (hc : Measurable c)
    (hg : Measurable g) : Measurable (fun x => f (c x) (g x)) := by
  have h1 : Measurable (fun p : Ret n × ℕ => f p.1 p.2) :=
    measurable_from_prod_countable_left hf
  have h2 := h1.comp (hc.prodMk hg)
  exact h2

lemma measurable_gridMix (D : Centres n) {τ : Ret n → ℝ} (hτ : Measurable τ)
    {fT wT : Ret n → ℕ → ℝ} (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) :
    Measurable (fun p : Ret n × ℝ => gridMix D τ fT wT p.1 p.2) := by
  have hc : Measurable (fun p : Ret n × ℝ => p.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hτ' : Measurable (fun p : Ret n × ℝ => τ p.1) := hτ.comp measurable_fst
  have hρ : Measurable (fun p : Ret n × ℝ => rhoC p.1.1.2 (τ p.1)) := by
    have h := (measurable_rhoC (n := n)).comp (hc.prodMk hτ')
    exact h
  have hsc : Measurable (fun p : Ret n × ℝ => √(normSq p.1.1.2) / rhoC p.1.1.2 (τ p.1)) :=
    ((measurable_normSq.comp hc).sqrt).div hρ
  have hd : Measurable (fun p : Ret n × ℝ => 6 * τ p.1 / rhoC p.1.1.2 (τ p.1)) :=
    (hτ'.const_mul 6).div hρ
  have hg : Measurable (fun p : Ret n × ℝ =>
      nodeIdx (Js n) (√(normSq p.1.1.2) / rhoC p.1.1.2 (τ p.1) - 6 * τ p.1 / rhoC p.1.1.2 (τ p.1))
        (√(normSq p.1.1.2) / rhoC p.1.1.2 (τ p.1) + 6 * τ p.1 / rhoC p.1.1.2 (τ p.1)) p.2) :=
    measurable_nodeIdx_comp (Js n) (hsc.sub hd) (hsc.add hd) measurable_snd
  have hF := measurable_table_comp hf (measurable_fst : Measurable (fun p : Ret n × ℝ => p.1)) hg
  have hW := measurable_table_comp hw (measurable_fst : Measurable (fun p : Ret n × ℝ => p.1)) hg
  have hb : Measurable (fun p : Ret n × ℝ => normSq (D.bA p.1.1 p.1.2.1.1)) :=
    measurable_normSq.comp (D.mbA.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))))
  unfold gridMix
  exact (hF.div ((hb.div_const _).sqrt)).prodMk
    ((measurable_const.max (hW.sub (hF.pow_const 2))).const_mul _)

/-- **The design of the paper's program**, for given stored tables `f̃` (`fT`) and `ω̃` (`wT`)
that are measurable functions of the retained data: the centres of steps 2 and 3, `τ₀` of step 2,
and the mixture table of steps 4 and 6. -/
noncomputable def paperDesign (n : ℕ) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    Design n where
  toCentres := paperCentres n
  tau0 := fun c => tau0p c.1.1
  mix := gridMix (paperCentres n) (fun c => tau0p c.1.1) fT wT
  mtau0 := measurable_tau0p.comp (measurable_fst.comp measurable_fst)
  mmix := measurable_gridMix (paperCentres n)
    (measurable_tau0p.comp (measurable_fst.comp measurable_fst)) hf hw

/-- **The conditional classifier theorem for the paper's centres, `τ₀` and sampling step (every
`n ≥ 16 384`).** The design is `paperDesign n fT wT`: the World centre `b_W` and `τ₀` of step 2,
the global Agent centre `b` of step 3, and the sampling of steps 4 and 6 with stored tables
`fT`, `wT` (any measurable functions of the retained data; the paper's step 5 computes one such
pair). The hypotheses are those of `classifier_networks_conditional_hell`. -/
theorem classifier_paper_conditional (hn : 16384 ≤ n) (hG : GaussFrameMGF)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) {H E₁ : Set (Ret n)}
    (hEv : EVENTS_hyp (paperCentres n) H E₁ (HbarW (paperDesign n fT wT hf hw))
      BstLean.Part156.δhidL BstLean.Part156.vWL BstLean.Part156.δextraL)
    (hFW : FRAME_W_hyp (paperCentres n) (BstLean.Part156.cWL / n)
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) BstLean.Part156.hWL))
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (BstLean.Part156.cfL / n)
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) BstLean.Part156.hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t BstLean.Part156.hAL
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) BstLean.Part156.hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t
        (progOut (paperDesign n fT wT hf hw) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_hell hn hG (paperDesign n fT wT hf hw) t hEv hFW hFA hRA

end BstLean.Part157

open BstLean.Part157 in
#print axioms paperCentres
open BstLean.Part157 in
#print axioms paperDesign
open BstLean.Part157 in
#print axioms classifier_paper_conditional
