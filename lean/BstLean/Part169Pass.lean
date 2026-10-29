import BstLean.Part168End

/-!
# Part 169 (file `Pass`): the stored tables as the paper's conditional passes

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-01-statement-program.tex`, the ordered program, steps 4 and 5, and Lemma
`t7:p01:moments`; `theorem7-08-bias.tex`, formula `t7:p08:passes`.

This file is a TRANSCRIPTION of the paper's passes into Lean definitions, with the measurability
that `paperDesign` asks for. The first-layer sphere moments are the EXACT latitude integrals
`ā_i(s) = E_V ReLU(a_i·X_s)`, `ē_i(s) = E_V ReLU(a_i·X_s)²`, `X_s = s·u + √(1 − s²)·V`
(`xLat`, `V = G/|G|`, `G` standard Gaussian in `ℝ^{n−1}`). The paper's Lemma `t7:p01:moments`
states that its closed forms (even `n`) give exactly these integrals; that lemma is NOT proved
in Lean. For odd `n` the paper's program uses an arithmetic rule with error at most
`ε|a_i|`, `3ε|a_i|²` (`ε = 10⁻⁹⁰n⁻¹⁰`, Lemma `t7:p01:odd-error`); the Lean tables are the
exact-moment program.

* `nodeL`, `nodeH`, `nodeD`, `nodeS c g`: `L = s_c − 6τ₀/ρ`, `H = s_c + 6τ₀/ρ`, `Δ = (H − L)/J_s`,
  `s_g = L + (g + 1/2)Δ` (step 4).
* `a1Bar c s i`, `e1Bar c s i`: the exact first-layer sphere moments at the latitude `s`.
* `vsig2 c s = max(0, t_A(Σ_i ē_i − |ā|²))` (`ς²`), `Jz n = ⌈n^{3/2}⌉ − 1`.
* `betaP`, `beta2P`: `β_j = B_{J_z}[z ↦ ReLU((A₂ā)_j + ςz)]`, `β⁽²⁾_j` (the same with a square).
* **`passF c g = Σ_j β_j b_j/(√n|b|)`**, **`passW c g = Σ_j β⁽²⁾_j/n`** at the node `s_g`, with
  `b = bAp` the global Agent centre of step 3 (`b = b'/ρ`).
* `measurable_passF`, `measurable_passW`; `paperDesignP n = paperDesign n passF passW`.
* **`mixP_eq`**: the mixture table of `paperDesignP` at a latitude `s` is
  `(f̃_g/√e_b, (2/n)·max(1/5, ω̃_g − f̃_g²))` with `g` the node index of `s` and `f̃_g`, `ω̃_g` the
  paper's passes at the node `s_g` (steps 5 and 6).
-/

namespace BstLean.Part169

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part150 (binMean rhoC measurable_binMean_affine)
open BstLean.Part161 (xLat hhMat uHat consV measurable_consV)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-! ## Measurability of the latitude point in the retained data -/

lemma measurable_hhMat : Measurable (fun u : Fin n → ℝ => hhMat u) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold hhMat
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  refine measurable_const.sub ?_
  have he : Measurable (fun u : Fin n → ℝ => e0 n - u) := measurable_const.sub measurable_id
  have hn : Measurable (fun u : Fin n → ℝ => normSq (e0 n - u)) :=
    continuous_normSq.measurable.comp he
  exact ((hn.inv.const_mul 2)).mul (((measurable_pi_apply i).comp he).mul
    ((measurable_pi_apply j).comp he))

lemma measurable_uHat : Measurable (fun c : Ret n => uHat c) := by
  unfold uHat
  have h : Measurable (fun c : Ret n => c.1.2) := measurable_snd.comp measurable_fst
  exact ((continuous_normSq.measurable.comp h).sqrt.inv).smul h

/-- `(c, s, v) ↦ xLat c s v` is jointly measurable. -/
lemma measurable_xLat_joint {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    {g : β → Fin (n - 1) → ℝ} (hC : Measurable C) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => xLat (C x) (f x) (g x)) := by
  unfold xLat
  have h1 : Measurable (fun x => consV (n := n) (f x) (√(1 - f x ^ 2) • g x)) :=
    measurable_consV.comp (hf.prodMk
      (((measurable_const.sub (hf.pow_const 2)).sqrt).smul hg))
  have h2 : Measurable (fun x => hhMat (uHat (C x))) :=
    measurable_hhMat.comp (measurable_uHat.comp hC)
  exact BstLean.Part149.measurable_mulVec_joint.comp (h2.prodMk h1)

/-! ## The grid of step 4 -/

/-- `τ₀` of the retained data (step 2). -/
noncomputable def tauR (c : Ret n) : ℝ := tau0p c.1.1

/-- `ρ = √(|ĉ|² + nτ₀²)`. -/
noncomputable def rhoR (c : Ret n) : ℝ := rhoC c.1.2 (tauR c)

/-- `L = s_c − 6τ₀/ρ`, `s_c = |ĉ|/ρ`. -/
noncomputable def nodeL (c : Ret n) : ℝ := √(normSq c.1.2) / rhoR c - 6 * tauR c / rhoR c

/-- `H = s_c + 6τ₀/ρ`. -/
noncomputable def nodeH (c : Ret n) : ℝ := √(normSq c.1.2) / rhoR c + 6 * tauR c / rhoR c

/-- `Δ = (H − L)/J_s`, `J_s = 512 n`. -/
noncomputable def nodeD (c : Ret n) : ℝ := (nodeH c - nodeL c) / (Js n : ℝ)

/-- **The node** `s_g = L + (g + 1/2)Δ`. -/
noncomputable def nodeS (c : Ret n) (g : ℕ) : ℝ := nodeL c + ((g : ℝ) + 1 / 2) * nodeD c

/-- The node index of the latitude `s` used by `gridMix` (clip to `[L, H]`, then the cell). -/
noncomputable def gIdx (c : Ret n) (s : ℝ) : ℕ := nodeIdx (Js n) (nodeL c) (nodeH c) s

lemma measurable_tauR : Measurable (tauR (n := n)) :=
  measurable_tau0p.comp (measurable_fst.comp measurable_fst)

lemma measurable_rhoR : Measurable (rhoR (n := n)) := by
  have h := (BstLean.Part150.measurable_rhoC (n := n)).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_tauR)
  exact h

lemma measurable_nodeL : Measurable (nodeL (n := n)) := by
  unfold nodeL
  exact ((continuous_normSq.measurable.comp (measurable_snd.comp measurable_fst)).sqrt.div
    measurable_rhoR).sub ((measurable_tauR.const_mul 6).div measurable_rhoR)

lemma measurable_nodeH : Measurable (nodeH (n := n)) := by
  unfold nodeH
  exact ((continuous_normSq.measurable.comp (measurable_snd.comp measurable_fst)).sqrt.div
    measurable_rhoR).add ((measurable_tauR.const_mul 6).div measurable_rhoR)

lemma measurable_nodeS (g : ℕ) : Measurable (fun c : Ret n => nodeS c g) := by
  unfold nodeS nodeD
  exact measurable_nodeL.add (((measurable_nodeH.sub measurable_nodeL).div_const _).const_mul _)

/-! ## The exact first-layer sphere moments and the passes (step 5) -/

/-- The first-layer matrix `A₁` of the retained data. -/
abbrev A1 (c : Ret n) : Matrix (Fin (mA n)) (Fin n) ℝ := c.2.1.1.1

/-- The second-layer matrix `A₂` of the retained data. -/
abbrev A2 (c : Ret n) : Matrix (Fin (mA n)) (Fin (mA n)) ℝ := c.2.1.1.2

/-- **The exact first sphere moment** `ā_i(s) = E_V ReLU((A₁ X_s)_i)`, `X_s = xLat c s V`. -/
noncomputable def a1Bar (c : Ret n) (s : ℝ) (i : Fin (mA n)) : ℝ :=
  ∫ v, relu ((A1 c).mulVec (xLat c s (unitF53 v)) i) ∂stdGauss (Fin (n - 1))

/-- **The exact second sphere moment** `ē_i(s) = E_V ReLU((A₁ X_s)_i)²`. -/
noncomputable def e1Bar (c : Ret n) (s : ℝ) (i : Fin (mA n)) : ℝ :=
  ∫ v, relu ((A1 c).mulVec (xLat c s (unitF53 v)) i) ^ 2 ∂stdGauss (Fin (n - 1))

/-- `ς² = max(0, t_A(Σ_i ē_i − |ā|²))`, `t_A = 2/m_A`. -/
noncomputable def vsig2 (c : Ret n) (s : ℝ) : ℝ :=
  max 0 (2 / (mA n : ℝ) * (∑ i, e1Bar c s i - normSq (a1Bar c s)))

/-- The sign count of the second-layer rule: `J_z = ⌈n^{3/2}⌉ − 1`. -/
noncomputable def Jz (n : ℕ) : ℕ := ⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ - 1

/-- `β_j = B_{J_z}[z ↦ ReLU((A₂ ā)_j + ς z)]`. -/
noncomputable def betaP (c : Ret n) (s : ℝ) (j : Fin (mA n)) : ℝ :=
  binMean (Jz n) (fun z => relu ((A2 c).mulVec (a1Bar c s) j + √(vsig2 c s) * z))

/-- `β⁽²⁾_j = B_{J_z}[z ↦ ReLU((A₂ ā)_j + ς z)²]`. -/
noncomputable def beta2P (c : Ret n) (s : ℝ) (j : Fin (mA n)) : ℝ :=
  binMean (Jz n) (fun z => relu ((A2 c).mulVec (a1Bar c s) j + √(vsig2 c s) * z) ^ 2)

/-- The global Agent centre `b = b'/ρ` of step 3 (kept fixed at all nodes). -/
noncomputable def bR (c : Ret n) : Fin (mA n) → ℝ := bAp c.1 c.2.1.1

/-- `f̃(s) = Σ_j β_j b_j/(√n |b|)` at the latitude `s`. -/
noncomputable def fPass (c : Ret n) (s : ℝ) : ℝ :=
  (∑ j, betaP c s j * bR c j) / (√(n : ℝ) * √(normSq (bR c)))

/-- `ω̃(s) = Σ_j β⁽²⁾_j/n` at the latitude `s`. -/
noncomputable def wPass (c : Ret n) (s : ℝ) : ℝ := (∑ j, beta2P c s j) / (n : ℝ)

/-- **The paper's location table**: `f̃_g = fPass c s_g`. -/
noncomputable def passF (c : Ret n) (g : ℕ) : ℝ := fPass c (nodeS c g)

/-- **The paper's energy table**: `ω̃_g = wPass c s_g`. -/
noncomputable def passW (c : Ret n) (g : ℕ) : ℝ := wPass c (nodeS c g)

/-! ## Measurability -/

lemma measurable_relu_row {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    {g : β → Fin (n - 1) → ℝ} (hC : Measurable C) (hf : Measurable f) (hg : Measurable g)
    (i : Fin (mA n)) :
    Measurable (fun x => relu ((A1 (C x)).mulVec (xLat (C x) (f x) (unitF53 (g x))) i)) := by
  have hA : Measurable (fun x => A1 (C x)) :=
    measurable_fst.comp (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp hC)))
  have hx := measurable_xLat_joint hC hf (measurable_unitF.comp hg)
  exact measurable_relu.comp
    ((measurable_pi_apply i).comp (BstLean.Part149.measurable_mulVec_joint.comp (hA.prodMk hx)))

/-- Parametric integrals over the direction are measurable. -/
lemma measurable_int_dir {β : Type*} [MeasurableSpace β] {F : β × (Fin (n - 1) → ℝ) → ℝ}
    (hF : Measurable F) : Measurable (fun x => ∫ v, F (x, v) ∂stdGauss (Fin (n - 1))) :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin (n - 1)))).measurable

lemma measurable_a1Bar_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) (i : Fin (mA n)) :
    Measurable (fun x => a1Bar (C x) (f x) i) :=
  measurable_int_dir (measurable_relu_row (hC.comp measurable_fst) (hf.comp measurable_fst)
    measurable_snd i)

lemma measurable_e1Bar_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) (i : Fin (mA n)) :
    Measurable (fun x => e1Bar (C x) (f x) i) :=
  measurable_int_dir ((measurable_relu_row (hC.comp measurable_fst) (hf.comp measurable_fst)
    measurable_snd i).pow_const 2)

lemma measurable_vsig2_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => vsig2 (C x) (f x)) := by
  unfold vsig2
  refine measurable_const.max (((Finset.measurable_sum _ fun i _ =>
    measurable_e1Bar_comp hC hf i).sub ?_).const_mul _)
  unfold normSq
  exact Finset.measurable_sum _ fun i _ => (measurable_a1Bar_comp hC hf i).pow_const 2

lemma measurable_A2a {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) (j : Fin (mA n)) :
    Measurable (fun x => (A2 (C x)).mulVec (a1Bar (C x) (f x)) j) := by
  have hA : Measurable (fun x => A2 (C x)) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp hC)))
  have ha : Measurable (fun x => a1Bar (C x) (f x)) :=
    measurable_pi_iff.mpr fun i => measurable_a1Bar_comp hC hf i
  exact (measurable_pi_apply j).comp (BstLean.Part149.measurable_mulVec_joint.comp (hA.prodMk ha))

lemma measurable_bR : Measurable (bR (n := n)) := by
  have h1 : Measurable (fun c : Ret n => ((c.1, c.2.1.1) : WRet n × AHid n)) :=
    measurable_fst.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have h2 := (measurable_bAp (n := n)).comp h1
  exact h2

lemma measurable_fPass_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => fPass (C x) (f x)) := by
  unfold fPass betaP
  have hb : Measurable (fun x => bR (C x)) := measurable_bR.comp hC
  refine (Finset.measurable_sum _ fun j _ => ?_).div
    (measurable_const.mul ((continuous_normSq.measurable.comp hb).sqrt))
  exact (measurable_binMean_affine (Jz n) measurable_relu (measurable_A2a hC hf j)
    (measurable_vsig2_comp hC hf).sqrt).mul ((measurable_pi_apply j).comp hb)

lemma measurable_wPass_comp {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => wPass (C x) (f x)) := by
  unfold wPass beta2P
  refine (Finset.measurable_sum _ fun j _ => ?_).div_const _
  exact measurable_binMean_affine (Jz n) (measurable_relu.pow_const 2) (measurable_A2a hC hf j)
    (measurable_vsig2_comp hC hf).sqrt

lemma measurable_passF (g : ℕ) : Measurable (fun c : Ret n => passF c g) :=
  measurable_fPass_comp measurable_id (measurable_nodeS g)

lemma measurable_passW (g : ℕ) : Measurable (fun c : Ret n => passW c g) :=
  measurable_wPass_comp measurable_id (measurable_nodeS g)

/-! ## The design of the paper's program with the paper's tables -/

/-- **The paper's program as a design**: the centres and `τ₀` of steps 1 to 3, and the mixture
table of steps 4 to 6 with the tables `f̃`, `ω̃` computed by the conditional passes. -/
noncomputable def paperDesignP (n : ℕ) : Design n :=
  paperDesign n passF passW measurable_passF measurable_passW

lemma paperDesignP_tau0 (c : Ret n) : (paperDesignP n).tau0 c = tau0p c.1.1 := rfl

lemma paperDesignP_bA (c : Ret n) : (paperDesignP n).bA c.1 c.2.1.1 = bR c := rfl

/-- **The mixture table of the paper's program** at the latitude `s`: with `g` the node index of
`s` (clipping to `[L, H]`, `J_s = 512n` cells), `λ̃ = f̃_g/√e_b` and
`S̃ = (2/n)·max(1/5, ω̃_g − f̃_g²)`, where `f̃_g = fPass c s_g`, `ω̃_g = wPass c s_g` are the
conditional passes at the node `s_g` and `e_b = |b|²/n`. -/
theorem mixP_eq (c : Ret n) (s : ℝ) :
    (paperDesignP n).mix c s =
      (fPass c (nodeS c (gIdx c s)) / √(normSq (bR c) / (n : ℝ)),
        2 / (n : ℝ) * max (1 / 5) (wPass c (nodeS c (gIdx c s)) -
          fPass c (nodeS c (gIdx c s)) ^ 2)) := rfl

/-- The pass in closed form: `f̃_g = Σ_j B_{J_z}[ReLU((A₂ā(s_g))_j + ς(s_g)z)]·b_j/(√n|b|)`. -/
theorem passF_eq (c : Ret n) (g : ℕ) :
    passF c g = (∑ j, binMean (Jz n) (fun z => relu ((A2 c).mulVec (a1Bar c (nodeS c g)) j +
      √(vsig2 c (nodeS c g)) * z)) * bR c j) / (√(n : ℝ) * √(normSq (bR c))) := rfl

theorem passW_eq (c : Ret n) (g : ℕ) :
    passW c g = (∑ j, binMean (Jz n) (fun z => relu ((A2 c).mulVec (a1Bar c (nodeS c g)) j +
      √(vsig2 c (nodeS c g)) * z) ^ 2)) / (n : ℝ) := rfl

end BstLean.Part169
