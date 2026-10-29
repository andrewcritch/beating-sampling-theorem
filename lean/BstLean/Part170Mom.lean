import BstLean.Part170Dec

/-!
# Part 170 (file `Mom`): the node moments from the fluctuation bound and the bias moments

No proof is left open; no `native_decide` or `axiom` is used.

* `opSet O`: `{A₁ | ‖A₁‖_op ≤ O}` (closed, so measurable).
* `GsOf O Gb`: the Agent event family `{(wr, (A₁, A₂)) | ‖A₁‖_op ≤ O, (wr, A₁) ∈ Gb}` for a free
  measurable family `Gb` of first-layer events (the paper's statistics events).
* `node_bulk`: in the World window, every node `s_g` (`g < J_s`) has `s_g² ≤ 1` (`n ≥ 80 000`).
* `BiasMomF O Gb B`: at every World datum in the window, every node and every `A₁` with
  `(wr, A₁) ∈ Gb` and `‖A₁‖_op ≤ O`: `E_{ξ₁,ξ₂} biasF⁸ ≤ B⁸` (the paper's `t7:p08:biasmom`
  for the location pass, at the node level).
* **`nodeMomF_of_bias`**: the location half of `NodeMom (GsOf O Gb)` with `F = F_fl + B`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- `{A₁ | ‖A₁‖_op ≤ O}`. -/
def opSet (n : ℕ) (O : ℝ) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A | OpB A O}

lemma measurableSet_opSet (O : ℝ) : MeasurableSet (opSet n O) := by
  have e : opSet n O = ⋂ z : Fin n → ℝ, {A : Matrix (Fin (mA n)) (Fin n) ℝ |
      normSq (A *ᵥ z) ≤ O ^ 2 * normSq z} := by
    ext A; simp [opSet, OpB]
  rw [e]
  refine IsClosed.measurableSet (isClosed_iInter fun z => isClosed_le ?_ continuous_const)
  exact continuous_normSq.comp (Continuous.matrix_mulVec continuous_id continuous_const)

/-- The Agent event family: `‖A₁‖_op ≤ O` and `(wr, A₁) ∈ Gb`. -/
def GsOf (O : ℝ) (Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)) :
    Set (WRet n × AHid n) :=
  {p | p.2.1 ∈ opSet n O ∧ (p.1, p.2.1) ∈ Gb}

lemma measurableSet_GsOf (O : ℝ) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : MeasurableSet Gb) : MeasurableSet (GsOf O Gb) := by
  have h1 : Measurable (fun p : WRet n × AHid n => p.2.1) := measurable_fst.comp measurable_snd
  exact (h1 (measurableSet_opSet O)).inter ((measurable_fst.prodMk h1) hGb)

/-- In the World window every node `s_g`, `g < J_s`, has `s_g² ≤ 1`. -/
lemma node_bulk (hn : 80000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (hg : g < Js n) : nodeS (mkR wr θ) g ^ 2 ≤ 1 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  obtain ⟨hLH, hb, -⟩ := bulk_of_window (by omega) (mkR wr θ) hτ hθ0 hθ1
  have hq := qB_pos hn
  have hJ : (0 : ℝ) < Js n := by exact_mod_cast (show 0 < Js n by unfold Js; omega)
  have hD : 0 ≤ nodeD (mkR wr θ) := div_nonneg (by linarith) hJ.le
  have hg' : (g : ℝ) + 1 / 2 ≤ Js n := by
    have : (g : ℝ) + 1 ≤ Js n := by exact_mod_cast hg
    linarith
  have h1 : nodeL (mkR wr θ) ≤ nodeS (mkR wr θ) g := by
    unfold nodeS; have : 0 ≤ ((g : ℝ) + 1 / 2) * nodeD (mkR wr θ) := by positivity
    linarith
  have h2 : nodeS (mkR wr θ) g ≤ nodeH (mkR wr θ) := by
    unfold nodeS
    have e : nodeH (mkR wr θ) = nodeL (mkR wr θ) + (Js n : ℝ) * nodeD (mkR wr θ) := by
      unfold nodeD; field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hg' hD
    linarith
  have := hb _ h1 h2
  linarith

/-- **The bias moments of the location pass** (the remaining hypothesis of the location half). -/
def BiasMomF (O : ℝ) (Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)) (B : ℝ) : Prop :=
  ∀ wr : WRet n, windowW wr → ∀ g < Js n, ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
    A₁ ∈ opSet n O → (wr, A₁) ∈ Gb →
      ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF (mkR wr (A₁, 0)) g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
        ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)

/-- Tonelli on `ν_A` restricted to a first-layer event. -/
lemma lint_nuA_restrict {G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ)} (_hG : MeasurableSet G₁)
    {f : AHid n → ENNReal} (hf : Measurable f) :
    ∫⁻ θ in {θ : AHid n | θ.1 ∈ G₁}, f θ ∂nuA n =
      ∫⁻ A₁ in G₁, ∫⁻ A₂, f (A₁, A₂) ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
  have e : {θ : AHid n | θ.1 ∈ G₁} = G₁ ×ˢ (Set.univ : Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ)) := by
    ext θ; simp
  rw [e, ← Measure.prod_restrict, Measure.restrict_univ]
  exact lintegral_prod _ hf.aemeasurable

/-- **The location half of the node moments**: from the fluctuation bound (`exFn_mom`) and the
bias moments, `∫_{θ ∈ Gs} exFn⁸ dν_A ≤ (F_fl + B)⁸` at every node of every World datum in the
window. -/
theorem nodeMomF_of_bias (hn : 80000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomF O Gb B) (wr : WRet n) (hw : windowW wr) (g : ℕ) (hg : g < Js n) :
    ∫⁻ θ in {θ | (wr, θ) ∈ GsOf O Gb}, ENNReal.ofReal (exFn (mkR wr θ) g ^ 8) ∂nuA n ≤
      ENNReal.ofReal ((Ffl n O + B) ^ 8) := by
  set G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A₁ | A₁ ∈ opSet n O ∧ (wr, A₁) ∈ Gb}
  have hG₁ : MeasurableSet G₁ :=
    (measurableSet_opSet O).inter (measurable_prodMk_left hGb)
  have e : {θ : AHid n | (wr, θ) ∈ GsOf O Gb} = {θ : AHid n | θ.1 ∈ G₁} := rfl
  have mf : Measurable (fun θ : AHid n => ENNReal.ofReal (exFn (mkR wr θ) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exFn_comp (measurable_mkR.comp
      (measurable_const.prodMk measurable_id)) measurable_const).pow_const 8)
  rw [e, lint_nuA_restrict hG₁ mf]
  have hin : ∀ A₁ ∈ G₁, ∫⁻ A₂, ENNReal.ofReal (exFn (mkR wr (A₁, A₂)) g ^ 8)
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((Ffl n O + B) ^ 8) := by
    intro A₁ hA₁
    have := exFn_mom (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 hB0
      (hB wr hw g hg A₁ hA₁.1 hA₁.2)
    exact this
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exFn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((Ffl n O + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((Ffl n O + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((Ffl n O + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((Ffl n O + B) ^ 8) * 1 := by gcongr; exact prob_le_one
          _ = _ := mul_one _

end BstLean.Part170
