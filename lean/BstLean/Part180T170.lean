import BstLean.Part180T169

/-!
# Part 180 (file `Part180T170`): the T170 link of the chain at `n ≥ 24 000`
(namespace `BstLean.Part179.N30.N27.N26.N25.N24`)

No proof is left open; no `native_decide` or `axiom` is used.

A copy of Part 179's file `Part179T170N` (the chain at `n ≥ 25 000`) with `25 000 ↦ 24 000`, in the
sub-namespace `N24` of `BstLean.Part179.N30.N27.N26.N25` (its names shadow those of `N25`, `N26`,
`N27`, `N30`; the split data `dP`, `KR`, `dStar`, `fb_of_SEn` are `N30`'s: `sd = 0.452`,
`η = 1/50`). Upstream: `BstLean.Part179.N30.N27.N26.N24.classifier_paper_JM24H` (file `Part180TopJ`): `K² ≤ 5`,
bias root `0.00533`, room `roomK = roomC − 10⁻⁴ ≥ 0.002892`.
Changed constants: node latitude `s_g² ≥ 0.4122`, `1 − s² ≤ 0.5878`; `F_fl ≤ 0.01418`, `W_fl ≤ 0.1153` (polynomial certificates at `r₀ = 154.9`); allowances `A_f = 0.070`, `A_ω = 0.306`; `B_f = 0.0113`, `B_ω = 0.0117`, statistics charge `δ_G ≤ 3·10⁻⁵`. Ledger `3·10⁻⁵ + ((0.01418 + 0.0113)/0.070)⁸ + ((0.1153 + 0.0117)/0.306)⁸ + 10⁻⁶ ≈ 1.22·10⁻³ ≤ 0.002892 ≤ roomK`.
Every `classifier_paper_*` theorem here takes `hHQ : BstLean.Part180.HQ_stmt` (Lemma HQ, passed
through to the top).
The docstrings of the copied lemmas can carry older numbers; the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N25.N24

open BstLean.Part173 (FflQ exFn_mom_q)

section SNodeLat
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (windowW mkR)
variable {n : ℕ}
theorem node_lat0 (hn : 24000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (_hg : g < Js n) : 0 ≤ nodeS (mkR wr θ) g ∧ 4122 / 10000 ≤ nodeS (mkR wr θ) g ^ 2 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  set c := mkR wr θ with hcd
  have hτ' : 0 < tauR c := hτ
  have hθ0' : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c) := hθ0
  have hθ1' : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100 := hθ1
  obtain ⟨hLH, -, -⟩ := bulk_of_window (by omega) c hτ' hθ0' hθ1'
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have hb2' : b ^ 2 ≤ 55 / 100 / 24000 :=
    hb2.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hbs : b ≤ 47872 / 10000000 := by nlinarith
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
  have h2 : 64207 / 100000 ≤ a - 6 * b := by linarith
  nlinarith

/-- At every node of a World datum in the window (`n ≥ 45 000`): `1 − s_g² ≤ 0.5767`. -/
theorem node_lat_q (hn : 24000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (hg : g < Js n) : 1 - nodeS (mkR wr θ) g ^ 2 ≤ 5878 / 10000 := by
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
lemma node_bulk (hn : 24000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
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
theorem nodeMomF_of_bias (hn : 24000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomF O Gb B) (wr : WRet n) (hw : windowW wr) (g : ℕ) (hg : g < Js n) :
    ∫⁻ θ in {θ | (wr, θ) ∈ GsOf O Gb}, ENNReal.ofReal (exFn (mkR wr θ) g ^ 8) ∂nuA n ≤
      ENNReal.ofReal ((FflQ n O (5878 / 10000) + B) ^ 8) := by
  set G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A₁ | A₁ ∈ opSet n O ∧ (wr, A₁) ∈ Gb}
  have hG₁ : MeasurableSet G₁ :=
    (measurableSet_opSet O).inter (measurable_prodMk_left hGb)
  have e : {θ : AHid n | (wr, θ) ∈ GsOf O Gb} = {θ : AHid n | θ.1 ∈ G₁} := rfl
  have mf : Measurable (fun θ : AHid n => ENNReal.ofReal (exFn (mkR wr θ) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exFn_comp (measurable_mkR.comp
      (measurable_const.prodMk measurable_id)) measurable_const).pow_const 8)
  rw [e, lint_nuA_restrict hG₁ mf]
  have hin : ∀ A₁ ∈ G₁, ∫⁻ A₂, ENNReal.ofReal (exFn (mkR wr (A₁, A₂)) g ^ 8)
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((FflQ n O (5878 / 10000) + B) ^ 8) := by
    intro A₁ hA₁
    have := exFn_mom_q (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 hB0
      (hB wr hw g hg A₁ hA₁.1 hA₁.2) (q := 5878 / 10000) (hq0 := by norm_num)
      (hq := node_lat_q hn hw (A₁, 0) hg)
    exact this
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exFn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((FflQ n O (5878 / 10000) + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((FflQ n O (5878 / 10000) + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((FflQ n O (5878 / 10000) + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((FflQ n O (5878 / 10000) + B) ^ 8) * 1 := by gcongr; exact prob_le_one
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
/-- **`MomZ` on the bias event** (World data in the window; the N36 copy of Part 170's lemma,
for the kept indices of `η = 1/50`). -/
theorem momZ_of_Ebias (hn : 1 ≤ n) {Gs : Set (WRet n × AHid n)} {Af Aw : ℝ} {c : Ret n}
    (hc : c ∈ Ebias Gs Af Aw) (hw : windowW c.1) : MomZ c Af Aw := by
  obtain ⟨-, hF, hW⟩ := hc hw
  exact ⟨(int_pow8_le_univ (measurable_exF c) (bdd_exF hn c) _).trans hF,
    (int_pow8_le_univ (measurable_exW c) (bdd_exW hn c) _).trans hW⟩

/-- **The classifier theorem with `MomZ` and the bias charge removed** (every `n ≥ 45 000`).
Remaining: the node moments `NodeMom Gs F E` (eighth moments of the exact Gaussian-rule errors
over the Agent hidden matrices, at a fixed World datum in the window and a fixed node,
restricted to the Agent event family `Gs`), the charge `δ_G` of `Gs`, the linear condition,
the charge `δ_A` of the caller's `E_A`, and `δ_A + δ_G + (F/A_f)⁸ + (E/A_ω)⁸ ≤ roomK`. -/
theorem classifier_paper_node24k (hHQ : BstLean.Part180.HQ_stmt) (hn : 24000 ≤ n) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs) {δG : ℝ}
    (hδG : ∀ wr : WRet n, (nuA n).real {θ | (wr, θ) ∉ Gs} ≤ δG)
    {F E Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hlin : Aw + 201 / 100 * Af ≤ 4468 / 10000) (hAf' : Af ≤ 97 / 1000)
    (hM : NodeMom Gs F E)
    (hroom : δA + (δG + (F / Af) ^ 8 + (E / Aw) ^ 8) + 1 / 10 ^ 6 ≤ roomK) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  exact classifier_paper_AE30 hHQ hn t hEA (measurableSet_Ebias hG Af Aw) hEenm hA
    (Ebias_charge hn1 (paperCentres n) hG hAf hAw hM hδG) hEen hfE hroom hAf hAw hlin hAf'
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
theorem momZ_of_EbiasF (hn : 24000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
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

/-- **`F_fl ≤ 0.0093`** with the latitude factor `q = 0.5767`, every `n ≥ 45 000`. -/
lemma FflQ_le (hn : 24000 ≤ n) : FflQ n (O1n n) (5878 / 10000) ≤ 1418 / 100000 := by
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hs242 : 1549 / 10 ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  have hX : (n : ℝ) * (tA n * (5878 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) =
      5878 / 10000 * (4 * (1 + 2 / √(n : ℝ)) ^ 2) / ((n : ℝ) - 2) := by
    unfold tA O1n mA
    push_cast
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    set r := √(n : ℝ) with hr
    have hnr : (n : ℝ) = r ^ 2 := hsq.symm
    have hr2 : r ^ 2 - 2 ≠ 0 := by nlinarith
    rw [hnr]
    field_simp
    ring
  have hX2 : 5878 / 10000 * (4 * (1 + 2 / √(n : ℝ)) ^ 2) / ((n : ℝ) - 2) ≤ (10027 / 1000000) ^ 2 := by
    have h1 : 2 / √(n : ℝ) ≤ 2 / (1549 / 10) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs242
    have h2 : (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2 / (1549 / 10)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hroot : √(n : ℝ) * √(tA n * (5878 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) ≤ 10027 / 1000000 := by
    rw [← Real.sqrt_mul hn0.le, hX]
    rw [Real.sqrt_le_left (by norm_num)]; exact hX2
  unfold FflQ
  have e : π / 2 * (18 / 10) * √(n : ℝ) * √(tA n * (5878 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) / 2 =
      π / 2 * (18 / 10) / 2 * (√(n : ℝ) * √(tA n * (5878 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2)))) := by
    ring
  rw [e]
  have h0 : 0 ≤ √(n : ℝ) * √(tA n * (5878 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) := by positivity
  have hpi : π ≤ 3.1416 := Real.pi_lt_d4.le
  nlinarith [Real.pi_pos]

/-- **The classifier theorem with the location fluctuation proved** (every `n ≥ 45 000`,
`E_A = univ`). Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the
window); the bias moments of the location pass `BiasMomF (O1n n) Gb B_f`; the energy node moments
`NodeMomW (GsOf (O1n n) Gb) E`; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + (E/A_ω)⁸ ≤ roomK`. -/
theorem classifier_paper_fl24k (hHQ : BstLean.Part180.HQ_stmt) (hn : 24000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    {Bf E Af Aw : ℝ} (hBf : 0 < Bf) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 201 / 100 * Af ≤ 4468 / 10000) (hAf' : Af ≤ 97 / 1000)
    (hBias : BiasMomF (O1n n) Gb Bf) (hW : NodeMomW (GsOf (O1n n) Gb) E)
    (hroom : δG + ((FflQ n (O1n n) (5878 / 10000) + Bf) / Af) ^ 8 + (E / Aw) ^ 8 + 1 / 10 ^ 6 ≤ roomK) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hO : 0 < O1n n := O1n_pos hn1
  have hM : NodeMom (GsOf (O1n n) Gb) (FflQ n (O1n n) (5878 / 10000) + Bf) E := fun wr hw g hg =>
    ⟨nodeMomF_of_bias hn hO hGb hBf hBias wr hw g hg, hW wr hw g hg⟩
  have hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
      (Set.univ : Set (Ret n))ᶜ) ≤ 0 := by
    rw [Set.compl_univ, Set.inter_empty, measureReal_empty]
  exact classifier_paper_AE30 hHQ hn t MeasurableSet.univ (measurableSet_EbiasF (O1n n) hGb Af Aw) hEenm hA
    (EbiasF_charge hn1 (paperCentres n) hGb hδ0 hAf hAw hM hδG) hEen hfE (by linarith) hAf hAw hlin hAf'
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
theorem nodeMomW_of_bias (hn : 24000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomW O Gb B) : NodeMomW (GsOf O Gb) (BstLean.Part174.WflR n O (5878 / 10000) + B) := by
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
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((BstLean.Part174.WflR n O (5878 / 10000) + B) ^ 8) := by
    intro A₁ hA₁
    exact BstLean.Part174.exWn_mom_r (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 hB0
      (hB wr hw g hg A₁ hA₁.1 hA₁.2) (q := 5878 / 10000) (hq0 := by norm_num)
      (hq := node_lat_q hn hw (A₁, 0) hg)
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exWn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((BstLean.Part174.WflR n O (5878 / 10000) + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((BstLean.Part174.WflR n O (5878 / 10000) + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((BstLean.Part174.WflR n O (5878 / 10000) + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((BstLean.Part174.WflR n O (5878 / 10000) + B) ^ 8) * 1 := by gcongr; exact prob_le_one
          _ = _ := mul_one _

/-- **The classifier theorem with both fluctuations proved** (every `n ≥ 45 000`, `E_A = univ`).
Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the window); the bias
moments of both passes; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + ((W_fl + B_ω)/A_ω)⁸ ≤ roomK`. -/
theorem classifier_paper_flw24k (hHQ : BstLean.Part180.HQ_stmt) (hn : 24000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    {Bf Bw Af Aw : ℝ} (hBf : 0 < Bf) (hBw : 0 < Bw) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 201 / 100 * Af ≤ 4468 / 10000) (hAf' : Af ≤ 97 / 1000)
    (hBiasF : BiasMomF (O1n n) Gb Bf) (hBiasW : BiasMomW (O1n n) Gb Bw)
    (hroom : δG + ((FflQ n (O1n n) (5878 / 10000) + Bf) / Af) ^ 8 + ((BstLean.Part174.WflR n (O1n n) (5878 / 10000) + Bw) / Aw) ^ 8 +
      1 / 10 ^ 6 ≤ roomK) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hO : 0 < O1n n := O1n_pos (by omega)
  exact classifier_paper_fl24k hHQ hn t hGb hδ0 hδG hEenm hEen hfE hBf hAf hAw hlin hAf' hBiasF
    (nodeMomW_of_bias hn hO hGb hBw hBiasW) hroom

end SPart170FinW

-- ===== from Part170NumW.lean =====
section SPart170NumW
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- **`W_fl ≤ 0.0749`** for Part 174's energy allowance `BstLean.Part174.WflR` (no factor `√3`) with the latitude
factor `q = 0.5767`, every `n ≥ 45 000`. -/
lemma WflR_le (hn : 24000 ≤ n) : BstLean.Part174.WflR n (O1n n) (5878 / 10000) ≤ 1153 / 10000 := by
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr : 1549 / 10 ≤ r := by rw [hrd, Real.le_sqrt (by norm_num) hn0.le]; nlinarith
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
  set L := √(tA n * (5878 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) with hLd
  have hL : L ≤ 7667 / 10000 * Lb := by
    rw [hLd, Real.sqrt_le_left (by positivity)]
    have e : tA n * (5878 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2)) =
        5878 / 10000 * (tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) := by ring
    rw [e]
    have : (5878 / 10000 : ℝ) * (tA n * (O1n n ^ 2 / ((n : ℝ) - 2))) ≤ 5878 / 10000 * Lb ^ 2 :=
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
  have hX : Lb * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) ≤ 2650 / 100000 := by
    rw [hLbd]
    set d := r - 1549 / 10 with hdd
    have hd : 0 ≤ d := by linarith
    have hrd' : r = 1549 / 10 + d := by linarith
    rw [show 2 * (r + 2) / (r ^ 2 * (r - 1 / 120)) * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) =
      4 * (r + 2) ^ 2 * (r ^ 2 + 1 / 1000) / (r ^ 4 * (r - 1 / 120)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    have hP : 2650 / 100000 * (r ^ 4 * (r - 1 / 120)) - 4 * (r + 2) ^ 2 * (r ^ 2 + 1 / 1000) =
        53 / 2000 * d ^ 5 + 3965767 / 240000 * d ^ 4 + 2318325493 / 600000 * d ^ 3 +
        1606315533687 / 4000000 * d ^ 2 + 469656011235449 / 30000000 * d +
        925353027995911 / 2400000000 := by
      rw [hrd']; ring
    have : 0 ≤ 53 / 2000 * d ^ 5 + 3965767 / 240000 * d ^ 4 + 2318325493 / 600000 * d ^ 3 +
        1606315533687 / 4000000 * d ^ 2 + 469656011235449 / 30000000 * d +
        925353027995911 / 2400000000 := by
      positivity
    linarith
  have hLs : Lb ≤ 845 / 10000000 := by
    rw [hLbd, div_le_iff₀ (by positivity)]
    set d := r - 1549 / 10 with hdd
    have hd : 0 ≤ d := by linarith
    have hrd' : r = 1549 / 10 + d := by linarith
    have hP : 845 / 10000000 * (r ^ 2 * (r - 1 / 120)) - 2 * (r + 2) =
        169 / 2000000 * d ^ 3 + 9423947 / 240000000 * d ^ 2 + 4898716061 / 1200000000 * d +
        5805619403 / 24000000000 := by
      rw [hrd']; ring
    have : 0 ≤ 169 / 2000000 * d ^ 3 + 9423947 / 240000000 * d ^ 2 + 4898716061 / 1200000000 * d +
        5805619403 / 24000000000 := by positivity
    linarith
  unfold BstLean.Part174.WflR
  rw [← hLd, hTm, hT]
  have hm0 : 0 ≤ √((mA n : ℝ) + 8) := Real.sqrt_nonneg _
  have hmain : 2 * (π / 2 * (18 / 10) * L) * (2 * (r + 2) / r ^ 2 * √((mA n : ℝ) + 8)) ≤
      2 * (31416 / 10000 / 2 * (18 / 10)) * (7667 / 10000 * (2650 / 100000)) := by
    have e : 2 * (π / 2 * (18 / 10) * L) * (2 * (r + 2) / r ^ 2 * √((mA n : ℝ) + 8)) =
        2 * (π / 2 * (18 / 10)) * (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)) := by ring
    rw [e]
    have h1 : L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8) ≤ 7667 / 10000 * (2650 / 100000) := by
      calc L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)
          ≤ (7667 / 10000 * Lb) * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000) := by gcongr
        _ = 7667 / 10000 * (Lb * (2 * (r + 2) / r ^ 2) * (r ^ 2 + 1 / 1000)) := by ring
        _ ≤ 7667 / 10000 * (2650 / 100000) := by gcongr
    have h0 : 0 ≤ L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8) := by positivity
    have hpi0 := Real.pi_pos
    have hA : 2 * (π / 2 * (18 / 10)) ≤ 2 * (31416 / 10000 / 2 * (18 / 10)) := by linarith
    calc 2 * (π / 2 * (18 / 10)) * (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8))
        ≤ 2 * (31416 / 10000 / 2 * (18 / 10)) *
          (L * (2 * (r + 2) / r ^ 2) * √((mA n : ℝ) + 8)) :=
          mul_le_mul_of_nonneg_right hA h0
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hLL : L ≤ 648 / 10000000 := by
    have := mul_le_mul_of_nonneg_left hLs (by norm_num : (0 : ℝ) ≤ 7667 / 10000)
    linarith
  have ha1 : (π / 2 * (25 / 10) * L) ^ 2 + 2 * (π / 2 * (18 / 10) * L) + (π / 2 * L) ^ 2 ≤
      37 / 100000 := by
    have hpl := mul_le_mul hpi hLL hL0 (by norm_num)
    have hpi0 := Real.pi_pos
    have e1 : π / 2 * (25 / 10) * L ≤ 31416 / 10000 / 2 * (25 / 10) * (648 / 10000000) := by
      linarith [hpl]
    have e2 : π / 2 * (18 / 10) * L ≤ 31416 / 10000 / 2 * (18 / 10) * (648 / 10000000) := by
      linarith [hpl]
    have e3 : π / 2 * L ≤ 31416 / 10000 / 2 * (648 / 10000000) := by linarith [hpl]
    have p1 : 0 ≤ π / 2 * (25 / 10) * L := by positivity
    have p3 : 0 ≤ π / 2 * L := by positivity
    have q1 := pow_le_pow_left₀ p1 e1 2
    have q3 := pow_le_pow_left₀ p3 e3 2
    have hnum : (31416 / 10000 / 2 * (25 / 10) * (648 / 10000000) : ℝ) ^ 2 +
        2 * (31416 / 10000 / 2 * (18 / 10) * (648 / 10000000)) +
        (31416 / 10000 / 2 * (648 / 10000000) : ℝ) ^ 2 ≤ 37 / 100000 := by norm_num
    linarith
  norm_num at hmain
  linarith

/-- **The numeric end theorem**: every `n ≥ 45 000`, with `A_f = 0.0429` and `A_ω = 0.251`
(`0.251 + 8.08·0.0429 ≤ 0.598`). Remaining hypotheses: a measurable first-layer event family `Gb`
with charge `δ_G ≤ 10⁻⁴` in the window, and the bias moments `B_f = 0.0050` (location) and
`B_ω = 0.0052` (energy) on `Gb`. Ledger:
`10⁻⁴ + ((0.0093 + 0.0050)/0.0429)⁸ + ((0.0749 + 0.0052)/0.251)⁸ ≤ 0.000692 ≤ roomK`. -/
theorem classifier_paper_bias_num24k (hHQ : BstLean.Part180.HQ_stmt) (hn : 24000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ 3 / 100000)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    (hBiasF : BiasMomF (O1n n) Gb (113 / 10000)) (hBiasW : BiasMomW (O1n n) Gb (117 / 10000)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_flw24k hHQ hn t hGb (by norm_num) hδG hEenm hEen hfE (by norm_num) (by norm_num)
    (Af := 700 / 10000) (Aw := 3060 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hBiasF hBiasW ?_
  have hF := FflQ_le hn
  have hW := WflR_le hn
  have hF0 : 0 ≤ FflQ n (O1n n) (5878 / 10000) := by unfold FflQ; have := Real.pi_pos; positivity
  have hW0 : 0 ≤ BstLean.Part174.WflR n (O1n n) (5878 / 10000) := by
    unfold BstLean.Part174.WflR; have := Real.pi_pos; positivity
  have h1 : ((FflQ n (O1n n) (5878 / 10000) + 113 / 10000) / (700 / 10000)) ^ 8 ≤
      ((1418 / 100000 + 113 / 10000) / (700 / 10000)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have h2 : ((BstLean.Part174.WflR n (O1n n) (5878 / 10000) + 117 / 10000) / (3060 / 10000)) ^ 8 ≤
      ((1153 / 10000 + 117 / 10000) / (3060 / 10000)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have hr := roomK_ge
  have h3 : (3 : ℝ) / 100000 + ((1418 / 100000 + 113 / 10000) / (700 / 10000)) ^ 8 +
      ((1153 / 10000 + 117 / 10000) / (3060 / 10000)) ^ 8 + 1 / 10 ^ 6 ≤ 2892 / 10 ^ 6 := by
    norm_num
  linarith

end SPart170NumW

end BstLean.Part179.N30.N27.N26.N25.N24

