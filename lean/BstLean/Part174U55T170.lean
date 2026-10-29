import BstLean.Part174U55T169
import BstLean.Part171All
import BstLean.Part173Cov
import BstLean.Part174Wfl

/-!
# Part 174 (file `U55T170`): Part 170's results that need `n ≥ 80 000`, re-proved for `n ≥ 55 000`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of file `T170` (57 000 chain) for `n ≥ 55 000`, namespace `BstLean.Part174.N55`. The energy
fluctuation uses `WflR` (file `Wfl`). The docstrings can carry older numbers; the Lean statements are
authoritative.

Changed constants (57 000 → 55 000): node latitude `s_g² ≥ 0.4248` (was 0.4253), so `q = 0.5752`;
`FflQ_le`: `F_fl ≤ 0.0093` (was 0.0091); `WflR_le`: `W_fl ≤ 0.0749` (was 0.0736); the linear
condition `A_ω + 8.08A_f ≤ 0.598` (was 0.609); room `roomE55`. In `classifier_paper_bias_num55k`:
`A_f = 0.0429`, `A_ω = 0.251`, `B_f = 0.0050`, `B_ω = 0.0052`, `δ_G ≤ 10⁻⁴`; ledger
`10⁻⁴ + ((0.0093 + 0.0050)/0.0429)⁸ + ((0.0749 + 0.0052)/0.251)⁸ ≈ 3.6·10⁻⁴ ≤ 0.000692 ≤ roomE55`.
-/

namespace BstLean.Part174.N55

open BstLean.Part173 (FflQ exFn_mom_q)

section SNodeLat
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (windowW mkR)
variable {n : ℕ}
theorem node_lat0 (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (_hg : g < Js n) : 0 ≤ nodeS (mkR wr θ) g ∧ 4248 / 10000 ≤ nodeS (mkR wr θ) g ^ 2 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  set c := mkR wr θ with hcd
  have hτ' : 0 < tauR c := hτ
  have hθ0' : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c) := hθ0
  have hθ1' : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100 := hθ1
  obtain ⟨hLH, -, -⟩ := bulk_of_window (by omega) c hτ' hθ0' hθ1'
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set ρ := rhoR c with hρ
  have hρ2 : ρ ^ 2 = normSq c.1.2 + n * tauR c ^ 2 := by
    rw [hρ]; unfold rhoR BstLean.Part150.rhoC
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hρ0 : 0 < ρ := by
    rw [hρ]; unfold rhoR BstLean.Part150.rhoC
    exact Real.sqrt_pos.mpr (by have := normSq_nonneg c.1.2; positivity)
  set a := √(normSq c.1.2) / ρ with ha
  set b := tauR c / ρ with hb
  have hb0 : 0 < b := div_pos hτ' hρ0
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hθ : BstLean.Part150.thetaC c.1.2 (tauR c) = n * b ^ 2 := by
    unfold BstLean.Part150.thetaC; rw [← rhoR, ← hρ, hb, div_pow]; ring
  have hab : a ^ 2 + n * b ^ 2 = 1 := by
    rw [ha, hb, div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp; rw [hρ2]
  rw [hθ] at hθ0' hθ1'
  have hL : nodeL c = a - 6 * b := by unfold nodeL; rw [← hρ]; ring
  have ha2 : 45 / 100 ≤ a ^ 2 := by linarith
  have hb2 : b ^ 2 ≤ 55 / 100 / n := by rw [le_div_iff₀ hn0]; linarith
  have hb2' : b ^ 2 ≤ 55 / 100 / 55000 :=
    hb2.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hbs : b ≤ 3163 / 1000000 := by nlinarith
  have has : 6708 / 10000 ≤ a := by nlinarith
  have hD : 0 ≤ nodeD c := by
    unfold nodeD
    exact div_nonneg (by linarith) (by positivity)
  have hS : nodeL c ≤ nodeS c g := by
    unfold nodeS
    have : 0 ≤ ((g : ℝ) + 1 / 2) * nodeD c := mul_nonneg (by positivity) hD
    linarith
  rw [hL] at hS
  have h1 : 0 ≤ a - 6 * b := by linarith
  refine ⟨by linarith, ?_⟩
  have h2 : 65182 / 100000 ≤ a - 6 * b := by linarith
  nlinarith

/-- At every node of a World datum in the window (`n ≥ 55 000`): `1 − s_g² ≤ 0.5752`. -/
theorem node_lat_q (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (hg : g < Js n) : 1 - nodeS (mkR wr θ) g ^ 2 ≤ 5752 / 10000 := by
  have := (node_lat0 hn hw θ hg).2
  linarith

end SNodeLat

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
lemma node_bulk (hn : 55000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
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
theorem nodeMomF_of_bias (hn : 55000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomF O Gb B) (wr : WRet n) (hw : windowW wr) (g : ℕ) (hg : g < Js n) :
    ∫⁻ θ in {θ | (wr, θ) ∈ GsOf O Gb}, ENNReal.ofReal (exFn (mkR wr θ) g ^ 8) ∂nuA n ≤
      ENNReal.ofReal ((FflQ n O (5752 / 10000) + B) ^ 8) := by
  set G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A₁ | A₁ ∈ opSet n O ∧ (wr, A₁) ∈ Gb}
  have hG₁ : MeasurableSet G₁ :=
    (measurableSet_opSet O).inter (measurable_prodMk_left hGb)
  have e : {θ : AHid n | (wr, θ) ∈ GsOf O Gb} = {θ : AHid n | θ.1 ∈ G₁} := rfl
  have mf : Measurable (fun θ : AHid n => ENNReal.ofReal (exFn (mkR wr θ) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exFn_comp (measurable_mkR.comp
      (measurable_const.prodMk measurable_id)) measurable_const).pow_const 8)
  rw [e, lint_nuA_restrict hG₁ mf]
  have hin : ∀ A₁ ∈ G₁, ∫⁻ A₂, ENNReal.ofReal (exFn (mkR wr (A₁, A₂)) g ^ 8)
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((FflQ n O (5752 / 10000) + B) ^ 8) := by
    intro A₁ hA₁
    have := exFn_mom_q (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 hB0
      (hB wr hw g hg A₁ hA₁.1 hA₁.2) (q := 5752 / 10000) (hq0 := by norm_num)
      (hq := node_lat_q hn hw (A₁, 0) hg)
    exact this
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exFn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((FflQ n O (5752 / 10000) + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((FflQ n O (5752 / 10000) + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((FflQ n O (5752 / 10000) + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((FflQ n O (5752 / 10000) + B) ^ 8) * 1 := by gcongr; exact prob_le_one
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
/-- **The classifier theorem with `MomZ` and the bias charge removed** (every `n ≥ 55 000`).
Remaining: the node moments `NodeMom Gs F E` (eighth moments of the exact Gaussian-rule errors
over the Agent hidden matrices, at a fixed World datum in the window and a fixed node,
restricted to the Agent event family `Gs`), the charge `δ_G` of `Gs`, the linear condition,
the charge `δ_A` of the caller's `E_A`, and `δ_A + δ_G + (F/A_f)⁸ + (E/A_ω)⁸ ≤ roomE55`. -/
theorem classifier_paper_node55k (hn : 55000 ≤ n) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs) {δG : ℝ}
    (hδG : ∀ wr : WRet n, (nuA n).real {θ | (wr, θ) ∉ Gs} ≤ δG)
    {F E Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hlin : Aw + 808 / 100 * Af ≤ 598 / 1000)
    (hM : NodeMom Gs F E)
    (hroom : δA + (δG + (F / Af) ^ 8 + (E / Aw) ^ 8) ≤ roomE55) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  exact classifier_paper_A55k hn t hEA (measurableSet_Ebias hG Af Aw) hA
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
theorem momZ_of_EbiasF (hn : 55000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
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

/-- **`F_fl ≤ 0.0093`** with the latitude factor `q = 0.5752`, every `n ≥ 55 000`. -/
lemma FflQ_le (hn : 55000 ≤ n) : FflQ n (O1n n) (5752 / 10000) ≤ 93 / 10000 := by
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hs242 : 234 ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  have hX : (n : ℝ) * (tA n * (5752 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) =
      5752 / 10000 * (4 * (1 + 2 / √(n : ℝ)) ^ 2) / ((n : ℝ) - 2) := by
    unfold tA O1n mA
    push_cast
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    set r := √(n : ℝ) with hr
    have hnr : (n : ℝ) = r ^ 2 := hsq.symm
    have hr2 : r ^ 2 - 2 ≠ 0 := by nlinarith
    rw [hnr]
    field_simp
    ring
  have hX2 : 5752 / 10000 * (4 * (1 + 2 / √(n : ℝ)) ^ 2) / ((n : ℝ) - 2) ≤ (653 / 100000) ^ 2 := by
    have h1 : 2 / √(n : ℝ) ≤ 2 / 234 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs242
    have h2 : (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2 / 234) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hroot : √(n : ℝ) * √(tA n * (5752 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) ≤ 653 / 100000 := by
    rw [← Real.sqrt_mul hn0.le, hX]
    rw [Real.sqrt_le_left (by norm_num)]; exact hX2
  unfold FflQ
  have e : π / 2 * (18 / 10) * √(n : ℝ) * √(tA n * (5752 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) / 2 =
      π / 2 * (18 / 10) / 2 * (√(n : ℝ) * √(tA n * (5752 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2)))) := by
    ring
  rw [e]
  have h0 : 0 ≤ √(n : ℝ) * √(tA n * (5752 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) := by positivity
  have hpi : π ≤ 3.1416 := Real.pi_lt_d4.le
  nlinarith [Real.pi_pos]

/-- **The classifier theorem with the location fluctuation proved** (every `n ≥ 55 000`,
`E_A = univ`). Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the
window); the bias moments of the location pass `BiasMomF (O1n n) Gb B_f`; the energy node moments
`NodeMomW (GsOf (O1n n) Gb) E`; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + (E/A_ω)⁸ ≤ roomE55`. -/
theorem classifier_paper_fl55k (hn : 55000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Bf E Af Aw : ℝ} (hBf : 0 < Bf) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 808 / 100 * Af ≤ 598 / 1000)
    (hBias : BiasMomF (O1n n) Gb Bf) (hW : NodeMomW (GsOf (O1n n) Gb) E)
    (hroom : δG + ((FflQ n (O1n n) (5752 / 10000) + Bf) / Af) ^ 8 + (E / Aw) ^ 8 ≤ roomE55) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hO : 0 < O1n n := O1n_pos hn1
  have hM : NodeMom (GsOf (O1n n) Gb) (FflQ n (O1n n) (5752 / 10000) + Bf) E := fun wr hw g hg =>
    ⟨nodeMomF_of_bias hn hO hGb hBf hBias wr hw g hg, hW wr hw g hg⟩
  have hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
      (Set.univ : Set (Ret n))ᶜ) ≤ 0 := by
    rw [Set.compl_univ, Set.inter_empty, measureReal_empty]
  exact classifier_paper_A55k hn t MeasurableSet.univ (measurableSet_EbiasF (O1n n) hGb Af Aw) hA
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
theorem nodeMomW_of_bias (hn : 55000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomW O Gb B) : NodeMomW (GsOf O Gb) (WflR n O (5752 / 10000) + B) := by
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
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((WflR n O (5752 / 10000) + B) ^ 8) := by
    intro A₁ hA₁
    exact exWn_mom_r (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 hB0
      (hB wr hw g hg A₁ hA₁.1 hA₁.2) (q := 5752 / 10000) (hq0 := by norm_num)
      (hq := node_lat_q hn hw (A₁, 0) hg)
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exWn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((WflR n O (5752 / 10000) + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((WflR n O (5752 / 10000) + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((WflR n O (5752 / 10000) + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((WflR n O (5752 / 10000) + B) ^ 8) * 1 := by gcongr; exact prob_le_one
          _ = _ := mul_one _

/-- **The classifier theorem with both fluctuations proved** (every `n ≥ 55 000`, `E_A = univ`).
Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the window); the bias
moments of both passes; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + ((W_fl + B_ω)/A_ω)⁸ ≤ roomE55`. -/
theorem classifier_paper_flw55k (hn : 55000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Bf Bw Af Aw : ℝ} (hBf : 0 < Bf) (hBw : 0 < Bw) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 808 / 100 * Af ≤ 598 / 1000)
    (hBiasF : BiasMomF (O1n n) Gb Bf) (hBiasW : BiasMomW (O1n n) Gb Bw)
    (hroom : δG + ((FflQ n (O1n n) (5752 / 10000) + Bf) / Af) ^ 8 + ((WflR n (O1n n) (5752 / 10000) + Bw) / Aw) ^ 8 ≤
      roomE55) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hO : 0 < O1n n := O1n_pos (by omega)
  exact classifier_paper_fl55k hn t hGb hδ0 hδG hBf hAf hAw hlin hBiasF
    (nodeMomW_of_bias hn hO hGb hBw hBiasW) hroom

end SPart170FinW

-- ===== from Part170NumW.lean =====
section SPart170NumW
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- **`W_fl ≤ 0.0749`** for Part 174's energy allowance `WflR` (no factor `√3`) with the latitude
factor `q = 0.5752`, every `n ≥ 55 000`. -/
lemma WflR_le (hn : 55000 ≤ n) : WflR n (O1n n) (5752 / 10000) ≤ 749 / 10000 := by
  have hnR : (55000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr : 234 ≤ r := by rw [hrd, Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  have hr0 : 0 < r := by linarith
  have hO2 : O1n n ^ 2 = 2 * (r + 2) ^ 2 := by
    unfold O1n
    rw [mul_pow, Real.sq_sqrt (by positivity), ← hrd, ← hr2]
    field_simp
  have htA : tA n = 2 / r ^ 4 := by
    unfold tA mA
    push_cast
    rw [← hr2]; ring
  set Lb := 2 * (r + 2) / (r ^ 2 * (r - 1 / 120)) with hLbd
  have hr4 : 0 < r - 1 / 120 := by linarith
  have hLb0 : 0 < Lb := by positivity
  have hL1 : tA n * (O1n n ^ 2 / ((n : ℝ) - 2)) ≤ Lb ^ 2 := by
    rw [htA, hO2, ← hr2]
    rw [hLbd, div_pow, mul_pow]
    have h1 : (r - 1 / 120) ^ 2 ≤ r ^ 2 - 2 := by nlinarith
    have h2 : 0 < r ^ 2 - 2 := by nlinarith
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 0 ≤ (r + 2) ^ 2 := sq_nonneg _
    have h4 : 0 < r ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h4.le)]
  set L := √(tA n * (5752 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) with hLd
  have hL : L ≤ 7585 / 10000 * Lb := by
    rw [hLd, Real.sqrt_le_left (by positivity)]
    have e : tA n * (5752 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2)) =
        5752 / 10000 * (tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) := by ring
    rw [e]
    have : (5752 / 10000 : ℝ) * (tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) ≤ 5752 / 10000 * Lb ^ 2 :=
      mul_le_mul_of_nonneg_left hL1 (by norm_num)
    nlinarith [sq_nonneg Lb]
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hT : √(tA n * O1n n ^ 2) = 2 * (r + 2) / r ^ 2 := by
    rw [htA, hO2]
    rw [show 2 / r ^ 4 * (2 * (r + 2) ^ 2) = (2 * (r + 2) / r ^ 2) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hTm : √(tA n * O1n n ^ 2 * ((mA n : ℝ) + 8)) = √(tA n * O1n n ^ 2) * √((mA n : ℝ) + 8) :=
    Real.sqrt_mul (by rw [htA]; positivity) _
  have hM : √((mA n : ℝ) + 8) ≤ r ^ 2 + 1 / 1000 := by
    rw [Real.sqrt_le_left (by positivity)]
    unfold mA; push_cast; rw [← hr2]; nlinarith
  have hpi : π ≤ 31416 / 10000 := by have := Real.pi_lt_d4; norm_num at this ⊢; linarith
  have hX : Lb * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) ≤ 174 / 10000 := by
    rw [hLbd]
    set d := r - 234 with hdd
    have hd : 0 ≤ d := by linarith
    have hrd' : r = 234 + d := by linarith
    rw [show 2 * (r + 2) / (r ^ 2 * (r - 1 / 120)) * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) =
      4 * (r + 2) ^ 2 * (r ^ 2 + 1 / 1000) / (r ^ 4 * (r - 1 / 120)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    have hP : 174 / 10000 * (r ^ 4 * (r - 1 / 120)) - 4 * (r + 2) ^ 2 * (r ^ 2 + 1 / 1000) =
        87 / 5000 * d ^ 5 + 3271571 / 200000 * d ^ 4 + 144185207 / 25000 * d ^ 3 +
        22600141357 / 25000 * d ^ 2 + 332471414123 / 6250 * d + 104437427011 / 12500 := by
      rw [hrd']; ring
    have : 0 ≤ 87 / 5000 * d ^ 5 + 3271571 / 200000 * d ^ 4 + 144185207 / 25000 * d ^ 3 +
        22600141357 / 25000 * d ^ 2 + 332471414123 / 6250 * d + 104437427011 / 12500 := by
      positivity
    linarith
  have hLs : Lb ≤ 37 / 1000000 := by
    rw [hLbd, div_le_iff₀ (by positivity)]
    set d := r - 234 with hdd
    have hd : 0 ≤ d := by linarith
    have hrd' : r = 234 + d := by linarith
    have hP : 37 / 1000000 * (r ^ 2 * (r - 1 / 120)) - 2 * (r + 2) =
        37 / 1000000 * d ^ 3 + 3116843 / 120000000 * d ^ 2 + 40777717 / 10000000 * d +
        20605649 / 10000000 := by
      rw [hrd']; ring
    have : 0 ≤ 37 / 1000000 * d ^ 3 + 3116843 / 120000000 * d ^ 2 + 40777717 / 10000000 * d +
        20605649 / 10000000 := by positivity
    linarith
  unfold WflR
  rw [← hLd, hTm, hT]
  have hm0 : 0 ≤ √((mA n : ℝ) + 8) := Real.sqrt_nonneg _
  have hmain : 2 * (π / 2 * (18 / 10) * L) * (2 * (r + 2) / r ^ 2 * √((mA n : ℝ) + 8)) ≤
      2 * (31416 / 10000 / 2 * (18 / 10)) * (7585 / 10000 * (174 / 10000)) := by
    have e : 2 * (π / 2 * (18 / 10) * L) * (2 * (r + 2) / r ^ 2 * √((mA n : ℝ) + 8)) =
        2 * (π / 2 * (18 / 10)) * (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)) := by ring
    rw [e]
    have h1 : L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8) ≤ 7585 / 10000 * (174 / 10000) := by
      calc L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)
          ≤ (7585 / 10000 * Lb) * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) := by gcongr
        _ = 7585 / 10000 * (Lb * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000)) := by ring
        _ ≤ 7585 / 10000 * (174 / 10000) := by gcongr
    have h0 : 0 ≤ L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8) := by positivity
    have hpi0 := Real.pi_pos
    have hA : 2 * (π / 2 * (18 / 10)) ≤ 2 * (31416 / 10000 / 2 * (18 / 10)) := by linarith
    calc 2 * (π / 2 * (18 / 10)) * (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8))
        ≤ 2 * (31416 / 10000 / 2 * (18 / 10)) *
          (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)) :=
          mul_le_mul_of_nonneg_right hA h0
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hLL : L ≤ 29 / 1000000 := by
    have := mul_le_mul_of_nonneg_left hLs (by norm_num : (0 : ℝ) ≤ 7585 / 10000)
    linarith
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

/-- **The numeric end theorem**: every `n ≥ 55 000`, with `A_f = 0.0429` and `A_ω = 0.251`
(`0.251 + 8.08·0.0429 ≤ 0.598`). Remaining hypotheses: a measurable first-layer event family `Gb`
with charge `δ_G ≤ 10⁻⁴` in the window, and the bias moments `B_f = 0.0050` (location) and
`B_ω = 0.0052` (energy) on `Gb`. Ledger:
`10⁻⁴ + ((0.0093 + 0.0050)/0.0429)⁸ + ((0.0749 + 0.0052)/0.251)⁸ ≤ 0.000692 ≤ roomE55`. -/
theorem classifier_paper_bias_num55k (hn : 55000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ 1 / 10000)
    (hBiasF : BiasMomF (O1n n) Gb (50 / 10000)) (hBiasW : BiasMomW (O1n n) Gb (52 / 10000)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_flw55k hn t hGb (by norm_num) hδG (by norm_num) (by norm_num)
    (Af := 429 / 10000) (Aw := 251 / 1000) (by norm_num) (by norm_num) (by norm_num) hBiasF hBiasW ?_
  have hF := FflQ_le hn
  have hW := WflR_le hn
  have hF0 : 0 ≤ FflQ n (O1n n) (5752 / 10000) := by unfold FflQ; have := Real.pi_pos; positivity
  have hW0 : 0 ≤ WflR n (O1n n) (5752 / 10000) := by unfold WflR; have := Real.pi_pos; positivity
  have h1 : ((FflQ n (O1n n) (5752 / 10000) + 50 / 10000) / (429 / 10000)) ^ 8 ≤ ((93 / 10000 + 50 / 10000) / (429 / 10000)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have h2 : ((WflR n (O1n n) (5752 / 10000) + 52 / 10000) / (251 / 1000)) ^ 8 ≤
      ((749 / 10000 + 52 / 10000) / (251 / 1000)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have hr := roomE55_ge
  have h3 : (1 : ℝ) / 10000 + ((93 / 10000 + 50 / 10000) / (429 / 10000)) ^ 8 +
      ((749 / 10000 + 52 / 10000) / (251 / 1000)) ^ 8 ≤ 692 / 10 ^ 6 := by norm_num
  linarith

end SPart170NumW

end BstLean.Part174.N55
