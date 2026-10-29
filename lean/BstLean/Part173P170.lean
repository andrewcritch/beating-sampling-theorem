import BstLean.Part173P169
import BstLean.Part170All

/-!
# Part 173 (file `P170`): Part 170's results that need `n ≥ 80 000`, re-proved for `n ≥ 70 000`

No proof is left open; no `native_decide` or `axiom` is used.

This file was made by copying every theorem of Part 170 whose statement or proof uses `80000`,
replacing `80000` by `70000` and the tag `80k` by `70k`, and then repairing the proofs that fail.
Each copy shadows the original inside `BstLean.Part173`; definitions are NOT copied (the copies use
Part 170's definitions). The docstrings are Part 170's, with `80 000` replaced by `70 000`; other
numbers in the docstrings can be Part 170's. The Lean statements are authoritative.

Changed constants: `F_fl ≤ 0.0108` (0.0101), `W_fl ≤ 0.1512` (0.1413; new polynomial certificate at `r = √n ≥ 264`); the linear condition `A_ω + 8.08A_f ≤ 0.679`; in `classifier_paper_bias_num70k`: `A_f = 0.037`, `A_ω = 0.38` (0.04, 0.39), `B_ω = 0.0041` (0.02), `δ_G ≤ 10⁻⁴` (6·10⁻⁴); ledger `10⁻⁴ + ((0.0108+0.004)/0.037)⁸ + ((0.1512+0.0041)/0.38)⁸ ≤ 0.001792`.
-/

namespace BstLean.Part173

-- ===== from Part170Mom.lean =====
section SPart170Mom
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- In the World window every node `s_g`, `g < J_s`, has `s_g² ≤ 1`. -/
lemma node_bulk (hn : 70000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
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

/-- **The location half of the node moments**: from the fluctuation bound (`exFn_mom`) and the
bias moments, `∫_{θ ∈ Gs} exFn⁸ dν_A ≤ (F_fl + B)⁸` at every node of every World datum in the
window. -/
theorem nodeMomF_of_bias (hn : 70000 ≤ n) {O : ℝ} (hO : 0 < O)
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

end SPart170Mom

-- ===== from Part170End.lean =====
section SPart170End
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)
open BstLean.Part166 (goodD)
variable {n : ℕ}
/-- **The classifier theorem with `MomZ` and the bias charge removed** (every `n ≥ 70 000`).
Remaining: the node moments `NodeMom Gs F E` (eighth moments of the exact Gaussian-rule errors
over the Agent hidden matrices, at a fixed World datum in the window and a fixed node,
restricted to the Agent event family `Gs`), the charge `δ_G` of `Gs`, the linear condition,
the charge `δ_A` of the caller's `E_A`, and `δ_A + δ_G + (F/A_f)⁸ + (E/A_ω)⁸ ≤ roomE`. -/
theorem classifier_paper_node70k (hn : 70000 ≤ n) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs) {δG : ℝ}
    (hδG : ∀ wr : WRet n, (nuA n).real {θ | (wr, θ) ∉ Gs} ≤ δG)
    {F E Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hlin : Aw + 808 / 100 * Af ≤ 679 / 1000)
    (hM : NodeMom Gs F E)
    (hroom : δA + (δG + (F / Af) ^ 8 + (E / Aw) ^ 8) ≤ BstLean.Part167.roomE) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  exact classifier_paper_A70k hn t hEA (measurableSet_Ebias hG Af Aw) hA
    (Ebias_charge hn1 (paperCentres n) hG hAf hAw hM hδG) hroom hAf hAw hlin
    (fun c hc => momZ_of_Ebias hn1 (Ebias_of_goodD hc) (windowW_of_goodD (by omega) hc))

end SPart170End

-- ===== from Part170Fin.lean =====
section SPart170Fin
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)
open BstLean.Part166 (goodD)
variable {n : ℕ}
/-- `MomZ` on the good set with the bias event. -/
theorem momZ_of_EbiasF (hn : 70000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    {Af Aw : ℝ} {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) (EA ∩ EbiasF (O1n n) Gb Af Aw)) : MomZ c Af Aw := by
  have hn1 : 1 ≤ n := by omega
  have hw := windowW_of_goodD (by omega) hc
  have hE : c ∈ EbiasF (O1n n) Gb Af Aw := Ebias_of_goodD hc
  have hop := (opB_goodD (by omega) hc).1
  have hGs : (c.1, c.2.1.1) ∈ GsOf (O1n n) Gb := ⟨hop, hE.2 hw⟩
  obtain ⟨hF, hW⟩ := hE.1 hw hGs
  exact ⟨(int_pow8_le_univ (measurable_exF c) (bdd_exF hn1 c) _).trans hF,
    (int_pow8_le_univ (measurable_exW c) (bdd_exW hn1 c) _).trans hW⟩

lemma Ffl_le (hn : 70000 ≤ n) : Ffl n (O1n n) ≤ 108 / 10000 := by
  have hnR : (70000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hs283 : 264 ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  -- `√n·√X = √(nX)`, `nX = 4(1 + 2/√n)²/(n − 2)`
  have hX : (n : ℝ) * (tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) =
      4 * (1 + 2 / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
    unfold tA O1n mA
    push_cast
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    set r := √(n : ℝ) with hr
    have hnr : (n : ℝ) = r ^ 2 := hsq.symm
    have hr2 : r ^ 2 - 2 ≠ 0 := by nlinarith
    rw [hnr]
    field_simp
    ring
  have hX2 : 4 * (1 + 2 / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) ≤ (762 / 100000) ^ 2 := by
    have h1 : 2 / √(n : ℝ) ≤ 2 / 264 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs283
    have h2 : (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2 / 264) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpi : π ≤ 3.1416 := Real.pi_lt_d4.le
  have hroot : √(n : ℝ) * √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) ≤ 762 / 100000 := by
    rw [← Real.sqrt_mul hn0.le, hX]
    rw [Real.sqrt_le_left (by norm_num)]; exact hX2
  unfold Ffl
  have e : π / 2 * (18 / 10) * √(n : ℝ) * √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) / 2 =
      π / 2 * (18 / 10) / 2 * (√(n : ℝ) * √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2)))) := by ring
  rw [e]
  have h0 : 0 ≤ √(n : ℝ) * √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) := by positivity
  nlinarith [Real.pi_pos]

/-- **The classifier theorem with the location fluctuation proved** (every `n ≥ 70 000`,
`E_A = univ`). Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the
window); the bias moments of the location pass `BiasMomF (O1n n) Gb B_f`; the energy node moments
`NodeMomW (GsOf (O1n n) Gb) E`; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + (E/A_ω)⁸ ≤ roomE`. -/
theorem classifier_paper_fl70k (hn : 70000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Bf E Af Aw : ℝ} (hBf : 0 < Bf) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 808 / 100 * Af ≤ 679 / 1000)
    (hBias : BiasMomF (O1n n) Gb Bf) (hW : NodeMomW (GsOf (O1n n) Gb) E)
    (hroom : δG + ((Ffl n (O1n n) + Bf) / Af) ^ 8 + (E / Aw) ^ 8 ≤ BstLean.Part167.roomE) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hO : 0 < O1n n := O1n_pos hn1
  have hM : NodeMom (GsOf (O1n n) Gb) (Ffl n (O1n n) + Bf) E := fun wr hw g hg =>
    ⟨nodeMomF_of_bias hn hO hGb hBf hBias wr hw g hg, hW wr hw g hg⟩
  have hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
      (Set.univ : Set (Ret n))ᶜ) ≤ 0 := by
    rw [Set.compl_univ, Set.inter_empty, measureReal_empty]
  exact classifier_paper_A70k hn t MeasurableSet.univ (measurableSet_EbiasF (O1n n) hGb Af Aw) hA
    (EbiasF_charge hn1 (paperCentres n) hGb hδ0 hAf hAw hM hδG) (by linarith) hAf hAw hlin
    (fun c hc => momZ_of_EbiasF hn hc)

end SPart170Fin

-- ===== from Part170FinW.lean =====
section SPart170FinW
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)
open BstLean.Part166 (goodD)
variable {n : ℕ}
/-- **The energy half of the node moments.** -/
theorem nodeMomW_of_bias (hn : 70000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomW O Gb B) : NodeMomW (GsOf O Gb) (Wfl n O + B) := by
  intro wr hw g hg
  set G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A₁ | A₁ ∈ opSet n O ∧ (wr, A₁) ∈ Gb}
  have hG₁ : MeasurableSet G₁ :=
    (measurableSet_opSet O).inter (measurable_prodMk_left hGb)
  have e : {θ : AHid n | (wr, θ) ∈ GsOf O Gb} = {θ : AHid n | θ.1 ∈ G₁} := rfl
  have mf : Measurable (fun θ : AHid n => ENNReal.ofReal (exWn (mkR wr θ) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exWn_comp (measurable_mkR.comp
      (measurable_const.prodMk measurable_id)) measurable_const).pow_const 8)
  rw [e, lint_nuA_restrict hG₁ mf]
  have hin : ∀ A₁ ∈ G₁, ∫⁻ A₂, ENNReal.ofReal (exWn (mkR wr (A₁, A₂)) g ^ 8)
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((Wfl n O + B) ^ 8) := by
    intro A₁ hA₁
    exact exWn_mom (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 hB0
      (hB wr hw g hg A₁ hA₁.1 hA₁.2)
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exWn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((Wfl n O + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((Wfl n O + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((Wfl n O + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((Wfl n O + B) ^ 8) * 1 := by gcongr; exact prob_le_one
          _ = _ := mul_one _

/-- **The classifier theorem with both fluctuations proved** (every `n ≥ 70 000`, `E_A = univ`).
Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the window); the bias
moments of both passes; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + ((W_fl + B_ω)/A_ω)⁸ ≤ roomE`. -/
theorem classifier_paper_flw70k (hn : 70000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Bf Bw Af Aw : ℝ} (hBf : 0 < Bf) (hBw : 0 < Bw) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 808 / 100 * Af ≤ 679 / 1000)
    (hBiasF : BiasMomF (O1n n) Gb Bf) (hBiasW : BiasMomW (O1n n) Gb Bw)
    (hroom : δG + ((Ffl n (O1n n) + Bf) / Af) ^ 8 + ((Wfl n (O1n n) + Bw) / Aw) ^ 8 ≤
      BstLean.Part167.roomE) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hO : 0 < O1n n := O1n_pos (by omega)
  exact classifier_paper_fl70k hn t hGb hδ0 hδG hBf hAf hAw hlin hBiasF
    (nodeMomW_of_bias hn hO hGb hBw hBiasW) hroom

end SPart170FinW

-- ===== from Part170NumW.lean =====
section SPart170NumW
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- **`W_fl ≤ 0.1413`** for every `n ≥ 70 000`. -/
lemma Wfl_le (hn : 70000 ≤ n) : Wfl n (O1n n) ≤ 1512 / 10000 := by
  have hnR : (70000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr : 264 ≤ r := by rw [hrd, Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  have hr0 : 0 < r := by linarith
  -- the pieces in terms of `r`
  have hO2 : O1n n ^ 2 = 2 * (r + 2) ^ 2 := by
    unfold O1n
    rw [mul_pow, Real.sq_sqrt (by positivity), ← hrd, ← hr2]
    field_simp
  have htA : tA n = 2 / r ^ 4 := by
    unfold tA mA
    push_cast
    rw [← hr2]; ring
  set L := √(tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) with hLd
  set Lb := 2 * (r + 2) / (r ^ 2 * (r - 1 / 250)) with hLbd
  have hr4 : 0 < r - 1 / 250 := by linarith
  have hLb0 : 0 < Lb := by positivity
  have hL : L ≤ Lb := by
    rw [hLd, Real.sqrt_le_left hLb0.le, htA, hO2, ← hr2]
    rw [hLbd, div_pow, mul_pow]
    have h1 : (r - 1 / 250) ^ 2 ≤ r ^ 2 - 2 := by nlinarith
    have h2 : 0 < r ^ 2 - 2 := by nlinarith
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 0 ≤ (r + 2) ^ 2 := sq_nonneg _
    have h4 : 0 < r ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h4.le)]
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hT : √(tA n * O1n n ^ 2) = 2 * (r + 2) / r ^ 2 := by
    rw [htA, hO2]
    rw [show 2 / r ^ 4 * (2 * (r + 2) ^ 2) = (2 * (r + 2) / r ^ 2) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hM : √((mA n : ℝ) + 8) ≤ r ^ 2 + 1 / 1000 := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold mA; push_cast; rw [← hr2]; nlinarith
  have h3 : √(3 : ℝ) ≤ 17321 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hpi : π ≤ 31416 / 10000 := by have := Real.pi_lt_d4; norm_num at this ⊢; linarith
  -- the polynomial inequalities
  have hX : Lb * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) ≤ 154 / 10000 := by
    rw [hLbd]
    set d := r - 264 with hdd
    have hd : 0 ≤ d := by linarith
    have hrd' : r = 264 + d := by linarith
    rw [show 2 * (r + 2) / (r ^ 2 * (r - 1 / 250)) * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) =
      4 * (r + 2) ^ 2 * (r ^ 2 + 1 / 1000) / (r ^ 4 * (r - 1 / 250)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    have hP : 154 / 10000 * (r ^ 4 * (r - 1 / 250)) - 4 * (r + 2) ^ 2 * (r ^ 2 + 1 / 1000) =
        77 / 5000 * d ^ 5 + 20409923 / 1250000 * d ^ 4 + 507274918 / 78125 * d ^ 3 +
        179397314431 / 156250 * d ^ 2 + 5959039078678 / 78125 * d + 1784654645998 / 78125 := by
      rw [hrd']; ring
    have : 0 ≤ 77 / 5000 * d ^ 5 + 20409923 / 1250000 * d ^ 4 + 507274918 / 78125 * d ^ 3 +
        179397314431 / 156250 * d ^ 2 + 5959039078678 / 78125 * d + 1784654645998 / 78125 := by
      positivity
    linarith
  have hLs : Lb ≤ 29 / 1000000 := by
    rw [hLbd, div_le_iff₀ (by positivity)]
    set d := r - 264 with hdd
    have hd : 0 ≤ d := by linarith
    have hrd' : r = 264 + d := by linarith
    rw [hrd']
    nlinarith [pow_nonneg hd 2, pow_nonneg hd 3, mul_nonneg hd (pow_nonneg hd 2)]
  -- assemble
  unfold Wfl
  rw [← hLd, hT]
  have hpos : 0 ≤ 2 * (r + 2) / r ^ 2 := by positivity
  have hm0 : 0 ≤ √((mA n : ℝ) + 8) := Real.sqrt_nonneg _
  have hmain : 2 * (π / 2 * (18 / 10) * L) * (2 * (r + 2) / r ^ 2) * (√3 * √((mA n : ℝ) + 8)) ≤
      2 * (31416 / 10000 / 2 * (18 / 10)) * (17321 / 10000) * (154 / 10000) := by
    have e : 2 * (π / 2 * (18 / 10) * L) * (2 * (r + 2) / r ^ 2) * (√3 * √((mA n : ℝ) + 8)) =
        2 * (π / 2 * (18 / 10)) * √3 * (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)) := by ring
    rw [e]
    have h1 : L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8) ≤ 154 / 10000 := by
      calc L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)
          ≤ Lb * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) := by gcongr
        _ ≤ 154 / 10000 := hX
    have h0 : 0 ≤ L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8) := by positivity
    have hpi0 := Real.pi_pos
    have h30 : 0 ≤ √(3 : ℝ) := Real.sqrt_nonneg _
    have hA : 2 * (π / 2 * (18 / 10)) * √3 ≤ 2 * (31416 / 10000 / 2 * (18 / 10)) * (17321 / 10000) := by
      have : π / 2 * (18 / 10) ≤ 31416 / 10000 / 2 * (18 / 10) := by linarith
      have := mul_le_mul this h3 h30 (by norm_num)
      linarith
    calc 2 * (π / 2 * (18 / 10)) * √3 * (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8))
        ≤ 2 * (31416 / 10000 / 2 * (18 / 10)) * (17321 / 10000) *
          (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)) :=
          mul_le_mul_of_nonneg_right hA h0
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hLL : L ≤ 29 / 1000000 := hL.trans hLs
  have ha1 : (π / 2 * (25 / 10) * L) ^ 2 + 2 * (π / 2 * (18 / 10) * L) + (π / 2 * L) ^ 2 ≤
      2 / 10000 := by
    have hpl := mul_le_mul hpi hLL hL0 (by norm_num)
    have hpi0 := Real.pi_pos
    have e1 : π / 2 * (25 / 10) * L ≤ 31416 / 10000 / 2 * (25 / 10) * (29 / 1000000) := by
      linarith [hpl]
    have e2 : π / 2 * (18 / 10) * L ≤ 31416 / 10000 / 2 * (18 / 10) * (29 / 1000000) := by
      linarith [hpl]
    have e3 : π / 2 * L ≤ 31416 / 10000 / 2 * (29 / 1000000) := by linarith [hpl]
    have p1 : 0 ≤ π / 2 * (25 / 10) * L := by positivity
    have p3 : 0 ≤ π / 2 * L := by positivity
    have q1 := pow_le_pow_left₀ p1 e1 2
    have q3 := pow_le_pow_left₀ p3 e3 2
    have hnum : (31416 / 10000 / 2 * (25 / 10) * (29 / 1000000) : ℝ) ^ 2 +
        2 * (31416 / 10000 / 2 * (18 / 10) * (29 / 1000000)) +
        (31416 / 10000 / 2 * (29 / 1000000) : ℝ) ^ 2 ≤ 2 / 10000 := by norm_num
    linarith
  norm_num at hmain
  linarith

/-- **The numeric end theorem**: every `n ≥ 70 000`, with `A_f = 0.04` and `A_ω = 0.39`.
Remaining hypotheses: a measurable first-layer event family `Gb` with charge `δ_G ≤ 0.0006` in the
window, and the bias moments `B_f = 0.004` (location) and `B_ω = 0.02` (energy) on `Gb`. -/
theorem classifier_paper_bias_num70k (hn : 70000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ 1 / 10000)
    (hBiasF : BiasMomF (O1n n) Gb (4 / 1000)) (hBiasW : BiasMomW (O1n n) Gb (41 / 10000)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_flw70k hn t hGb (by norm_num) hδG (by norm_num) (by norm_num)
    (Af := 37 / 1000) (Aw := 38 / 100) (by norm_num) (by norm_num) (by norm_num) hBiasF hBiasW ?_
  have hF := Ffl_le hn
  have hW := Wfl_le hn
  have hF0 : 0 ≤ Ffl n (O1n n) := by unfold Ffl; have := Real.pi_pos; positivity
  have hW0 : 0 ≤ Wfl n (O1n n) := by unfold Wfl; have := Real.pi_pos; positivity
  have h1 : ((Ffl n (O1n n) + 4 / 1000) / (37 / 1000)) ^ 8 ≤ ((108 / 10000 + 4 / 1000) / (37 / 1000)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have h2 : ((Wfl n (O1n n) + 41 / 10000) / (38 / 100)) ^ 8 ≤
      ((1512 / 10000 + 41 / 10000) / (38 / 100)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have hr := BstLean.Part167.roomE_ge
  have h3 : (1 : ℝ) / 10000 + ((108 / 10000 + 4 / 1000) / (37 / 1000)) ^ 8 +
      ((1512 / 10000 + 41 / 10000) / (38 / 100)) ^ 8 ≤ 1792 / 10 ^ 6 := by norm_num
  linarith

end SPart170NumW

end BstLean.Part173
