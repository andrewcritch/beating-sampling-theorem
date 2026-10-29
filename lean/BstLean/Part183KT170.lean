import BstLean.Part183KT169
import BstLean.Part183Def

/-!
# Part 183 (file `KT170`): the T170 link (node moments, fluctuations, ledger). `F_fl ≤ 0.01602`, `W_fl = WflJ ≤ 0.0708`, `B_f = 0.01422`, `B_ω = 0.01474`, `A_f = 0.066`, `A_ω = 0.2188`; ledger `≤ 2.6·10⁻³ ≤ roomK + roomX + roomT19` (`≥ 0.003692`)

No proof is left open; no `native_decide` or `axiom` is used.

A copy of the Part 183 `C` series (floor 20 000) for every `n ≥ 19 000` (statistics cap `n ≤ 20 000`), namespace
`….J19` / `BstLean.Part183.K`. The constants above are those of the Lean statements; the
docstrings of copied lemmas can carry older numbers, and the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J19.M

open BstLean.Part173 (FflQ exFn_mom_q)

section SNodeLat
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (windowW mkR)
variable {n : ℕ}
theorem node_lat0 (hn : 19000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (_hg : g < Js n) : 0 ≤ nodeS (mkR wr θ) g ∧ 4077 / 10000 ≤ nodeS (mkR wr θ) g ^ 2 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  set c := mkR wr θ with hcd
  have hτ' : 0 < tauR c := hτ
  have hθ0' : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c) := hθ0
  have hθ1' : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100 := hθ1
  obtain ⟨hLH, -, -⟩ := bulk_of_window (by omega) c hτ' hθ0' hθ1'
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have hb2' : b ^ 2 ≤ 55 / 100 / 19000 :=
    hb2.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hbs : b ≤ 5381 / 1000000 := by nlinarith
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
  have h2 : 63851 / 100000 ≤ a - 6 * b := by linarith
  nlinarith

/-- At every node of a World datum in the window (`n ≥ 45 000`): `1 − s_g² ≤ 0.5767`. -/
theorem node_lat_q (hn : 19000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
    (hg : g < Js n) : 1 - nodeS (mkR wr θ) g ^ 2 ≤ 5923 / 10000 := by
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
lemma node_bulk (hn : 19000 ≤ n) {wr : WRet n} (hw : windowW wr) (θ : AHid n) {g : ℕ}
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
theorem nodeMomF_of_bias (hn : 19000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomF O Gb B) (wr : WRet n) (hw : windowW wr) (g : ℕ) (hg : g < Js n) :
    ∫⁻ θ in {θ | (wr, θ) ∈ GsOf O Gb}, ENNReal.ofReal (exFn (mkR wr θ) g ^ 8) ∂nuA n ≤
      ENNReal.ofReal ((FflQ n O (5923 / 10000) + B) ^ 8) := by
  set G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A₁ | A₁ ∈ opSet n O ∧ (wr, A₁) ∈ Gb}
  have hG₁ : MeasurableSet G₁ :=
    (measurableSet_opSet O).inter (measurable_prodMk_left hGb)
  have e : {θ : AHid n | (wr, θ) ∈ GsOf O Gb} = {θ : AHid n | θ.1 ∈ G₁} := rfl
  have mf : Measurable (fun θ : AHid n => ENNReal.ofReal (exFn (mkR wr θ) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exFn_comp (measurable_mkR.comp
      (measurable_const.prodMk measurable_id)) measurable_const).pow_const 8)
  rw [e, lint_nuA_restrict hG₁ mf]
  have hin : ∀ A₁ ∈ G₁, ∫⁻ A₂, ENNReal.ofReal (exFn (mkR wr (A₁, A₂)) g ^ 8)
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((FflQ n O (5923 / 10000) + B) ^ 8) := by
    intro A₁ hA₁
    have := exFn_mom_q (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 hB0
      (hB wr hw g hg A₁ hA₁.1 hA₁.2) (q := 5923 / 10000) (hq0 := by norm_num)
      (hq := node_lat_q hn hw (A₁, 0) hg)
    exact this
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exFn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((FflQ n O (5923 / 10000) + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((FflQ n O (5923 / 10000) + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((FflQ n O (5923 / 10000) + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((FflQ n O (5923 / 10000) + B) ^ 8) * 1 := by gcongr; exact prob_le_one
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
theorem classifier_paper_node22k (hHQ : BstLean.Part183.K.HQG n) (hn : 19000 ≤ n) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    {Gs : Set (WRet n × AHid n)} (hG : MeasurableSet Gs) {δG : ℝ}
    (hδG : ∀ wr : WRet n, (nuA n).real {θ | (wr, θ) ∉ Gs} ≤ δG)
    {F E Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hlin : Aw + 201 / 100 * Af ≤ 35153 / 100000) (hAf' : Af ≤ 66 / 1000)
    (hM : NodeMom Gs F E)
    (hroom : δA + (δG + (F / Af) ^ 8 + (E / Aw) ^ 8) + 1 / 10 ^ 6 ≤ roomK + BstLean.Part181.roomX + BstLean.Part183.roomT19) :
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
theorem momZ_of_EbiasF (hn : 19000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
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
lemma FflQ_le (hn : 19000 ≤ n) : FflQ n (O1n n) (5923 / 10000) ≤ 1602 / 100000 := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hs242 : 13784 / 100 ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  have hX : (n : ℝ) * (tA n * (5923 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) =
      5923 / 10000 * (4 * (1 + 2 / √(n : ℝ)) ^ 2) / ((n : ℝ) - 2) := by
    unfold tA O1n mA
    push_cast
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    set r := √(n : ℝ) with hr
    have hnr : (n : ℝ) = r ^ 2 := hsq.symm
    have hr2 : r ^ 2 - 2 ≠ 0 := by nlinarith
    rw [hnr]
    field_simp
    ring
  have hX2 : 5923 / 10000 * (4 * (1 + 2 / √(n : ℝ)) ^ 2) / ((n : ℝ) - 2) ≤ (11330 / 1000000) ^ 2 := by
    have h1 : 2 / √(n : ℝ) ≤ 2 / (13784 / 100) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs242
    have h2 : (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2 / (13784 / 100)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hroot : √(n : ℝ) * √(tA n * (5923 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) ≤ 11330 / 1000000 := by
    rw [← Real.sqrt_mul hn0.le, hX]
    rw [Real.sqrt_le_left (by norm_num)]; exact hX2
  unfold FflQ
  have e : π / 2 * (18 / 10) * √(n : ℝ) * √(tA n * (5923 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) / 2 =
      π / 2 * (18 / 10) / 2 * (√(n : ℝ) * √(tA n * (5923 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2)))) := by
    ring
  rw [e]
  have h0 : 0 ≤ √(n : ℝ) * √(tA n * (5923 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) := by positivity
  have hpi : π ≤ 3.1416 := Real.pi_lt_d4.le
  nlinarith [Real.pi_pos]

/-- **The classifier theorem with the location fluctuation proved** (every `n ≥ 45 000`,
`E_A = univ`). Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the
window); the bias moments of the location pass `BiasMomF (O1n n) Gb B_f`; the energy node moments
`NodeMomW (GsOf (O1n n) Gb) E`; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + (E/A_ω)⁸ ≤ roomK`. -/
theorem classifier_paper_fl22k (hHQ : BstLean.Part183.K.HQG n) (hn : 19000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    {Bf E Af Aw : ℝ} (hBf : 0 < Bf) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 201 / 100 * Af ≤ 35153 / 100000) (hAf' : Af ≤ 66 / 1000)
    (hBias : BiasMomF (O1n n) Gb Bf) (hW : NodeMomW (GsOf (O1n n) Gb) E)
    (hroom : δG + ((FflQ n (O1n n) (5923 / 10000) + Bf) / Af) ^ 8 + (E / Aw) ^ 8 + 1 / 10 ^ 6 ≤ roomK + BstLean.Part181.roomX + BstLean.Part183.roomT19) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hO : 0 < O1n n := O1n_pos hn1
  have hM : NodeMom (GsOf (O1n n) Gb) (FflQ n (O1n n) (5923 / 10000) + Bf) E := fun wr hw g hg =>
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
theorem nodeMomW_of_bias (hEn : BstLean.Part183.EnJ_stmt) (hn : 19000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomW O Gb B) : NodeMomW (GsOf O Gb) (BstLean.Part183.WflJ n O (5923 / 10000) + B) := by
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
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((BstLean.Part183.WflJ n O (5923 / 10000) + B) ^ 8) := by
    intro A₁ hA₁
    exact hEn (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 (q := 5923 / 10000)
      (by norm_num) (node_lat_q hn hw (A₁, 0) hg) hB0 (hB wr hw g hg A₁ hA₁.1 hA₁.2)
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exWn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((BstLean.Part183.WflJ n O (5923 / 10000) + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((BstLean.Part183.WflJ n O (5923 / 10000) + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((BstLean.Part183.WflJ n O (5923 / 10000) + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((BstLean.Part183.WflJ n O (5923 / 10000) + B) ^ 8) * 1 := by gcongr; exact prob_le_one
          _ = _ := mul_one _

/-- **The classifier theorem with both fluctuations proved** (every `n ≥ 45 000`, `E_A = univ`).
Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the window); the bias
moments of both passes; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + ((W_fl + B_ω)/A_ω)⁸ ≤ roomK`. -/
theorem classifier_paper_flw22k (hHQ : BstLean.Part183.K.HQG n) (hn : 19000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    {Bf Bw Af Aw : ℝ} (hBf : 0 < Bf) (hBw : 0 < Bw) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 201 / 100 * Af ≤ 35153 / 100000) (hAf' : Af ≤ 66 / 1000)
    (hBiasF : BiasMomF (O1n n) Gb Bf) (hBiasW : BiasMomW (O1n n) Gb Bw)
    (hroom : δG + ((FflQ n (O1n n) (5923 / 10000) + Bf) / Af) ^ 8 + ((BstLean.Part183.WflJ n (O1n n) (5923 / 10000) + Bw) / Aw) ^ 8 +
      1 / 10 ^ 6 ≤ roomK + BstLean.Part181.roomX + BstLean.Part183.roomT19) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hO : 0 < O1n n := O1n_pos (by omega)
  exact classifier_paper_fl22k hHQ hn t hGb hδ0 hδG hEenm hEen hfE hBf hAf hAw hlin hAf' hBiasF
    (nodeMomW_of_bias hHQ.2.2 hn hO hGb hBw hBiasW) hroom

end SPart170FinW

-- ===== from Part170NumW.lean =====
section SPart170NumW
open BstLean.Part170
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- **`W_fl ≤ 0.0689`** for the centred allowance `WflJ` at `q = 0.5913`, every `n ≥ 20 000`:
`WflJ = 2c₈(L·S + c₈·L·√t·O)`, `L·S = 2√2 q(r+2)²/(r(r²−2)) ≤ 0.012165`, `L·√t·O ≤ 2·10⁻⁶`
(`r = √n ≥ 141.42`; polynomial certificates in `d = r − 141.42`). -/
lemma WflJ_le (hn : 19000 ≤ n) : BstLean.Part183.WflJ n (O1n n) (5923 / 10000) ≤ 708 / 10000 := by
  have hnR : (19000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr : 13784 / 100 ≤ r := by rw [hrd, Real.le_sqrt (by norm_num) hn0.le]; nlinarith
  have hr0 : 0 < r := by linarith
  have hO2 : O1n n ^ 2 = 2 * (r + 2) ^ 2 := by
    unfold O1n
    rw [mul_pow, Real.sq_sqrt (by positivity), ← hrd, ← hr2]
    field_simp
  have htA : tA n = 2 / r ^ 4 := by
    unfold tA mA
    push_cast
    rw [← hr2]; ring
  have hmA : ((mA n : ℕ) : ℝ) = r ^ 4 := by unfold mA; push_cast; rw [← hr2]; ring
  have hd2 : 0 < r ^ 2 - 2 := by nlinarith
  set d := r - 13784 / 100 with hdd
  have hd : 0 ≤ d := by linarith
  have hrd' : r = 13784 / 100 + d := by linarith
  set L := √(tA n * (5923 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2))) with hLd
  set S := √((mA n : ℝ) * tA n * (5923 / 10000 * n * O1n n ^ 2 / ((n : ℝ) - 2)) / 2) with hSd
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hLS : L * S ≤ 12511 / 1000000 := by
    rw [hLd, hSd, ← Real.sqrt_mul (by rw [htA, hO2, ← hr2]; positivity)]
    rw [Real.sqrt_le_left (by norm_num)]
    have key : tA n * (5923 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2)) *
        ((mA n : ℝ) * tA n * (5923 / 10000 * n * O1n n ^ 2 / ((n : ℝ) - 2)) / 2) =
        8 * (5923 / 10000) ^ 2 * (r + 2) ^ 4 / (r ^ 2 * (r ^ 2 - 2) ^ 2) := by
      rw [htA, hmA, hO2, ← hr2]; field_simp; ring
    rw [key, div_le_iff₀ (by positivity)]
    have hP : (12511 / 1000000) ^ 2 * (r ^ 2 * (r ^ 2 - 2) ^ 2) - 8 * (5923 / 10000) ^ 2 * (r + 2) ^ 4 =
        156525121 / 1000000000000 * d ^ 6 + 809078350449 / 6250000000000 * d ^ 5 + 653158804841751 / 15625000000000 * d ^ 4 + 161825761522191933 / 24414062500000 * d ^ 3 + 10121159131625494891457 / 19531250000000000 * d ^ 2 + 9781433747759922410203911 / 610351562500000000 * d + 1700178108794455839155801 / 15258789062500000000 := by
      rw [hrd']; ring
    have : 0 ≤ 156525121 / 1000000000000 * d ^ 6 + 809078350449 / 6250000000000 * d ^ 5 + 653158804841751 / 15625000000000 * d ^ 4 + 161825761522191933 / 24414062500000 * d ^ 3 + 10121159131625494891457 / 19531250000000000 * d ^ 2 + 9781433747759922410203911 / 610351562500000000 * d + 1700178108794455839155801 / 15258789062500000000 := by positivity
    linarith
  have hLT : L * (√(tA n) * O1n n) ≤ 2 / 1000000 := by
    have hO0 : 0 ≤ O1n n := by unfold O1n; positivity
    have hT : √(tA n) * O1n n = √(tA n * O1n n ^ 2) := by
      rw [Real.sqrt_mul (by rw [htA]; positivity), Real.sqrt_sq hO0]
    rw [hT, hLd, ← Real.sqrt_mul (by rw [htA, hO2, ← hr2]; positivity)]
    rw [Real.sqrt_le_left (by norm_num)]
    have key : tA n * (5923 / 10000 * O1n n ^ 2 / ((n : ℝ) - 2)) * (tA n * O1n n ^ 2) =
        16 * (5923 / 10000) * (r + 2) ^ 4 / (r ^ 8 * (r ^ 2 - 2)) := by
      rw [htA, hO2, ← hr2]; field_simp; ring
    rw [key, div_le_iff₀ (by positivity)]
    have hP : 4 / 10 ^ 12 * (r ^ 8 * (r ^ 2 - 2)) - 16 * (5923 / 10000) * (r + 2) ^ 4 =
        1 / 250000000000 * d ^ 10 + 1723 / 312500000000 * d ^ 9 + 53436997 / 15625000000000 * d ^ 8 + 30690505027 / 24414062500000 * d ^ 7 + 92538895873193 / 305175781250000 * d ^ 6 + 119582269259618998 / 2384185791015625 * d ^ 5 + 1097060924025896744163 / 190734863281250000 * d ^ 4 + 267315222829683974709657 / 596046447753906250 * d ^ 3 + 665892783407514207162644579 / 29802322387695312500 * d ^ 2 + 114514659069992434793827704013 / 186264514923095703125 * d + 292389185351831309750532899968673 / 46566128730773925781250 := by
      rw [hrd']; ring
    have : 0 ≤ 1 / 250000000000 * d ^ 10 + 1723 / 312500000000 * d ^ 9 + 53436997 / 15625000000000 * d ^ 8 + 30690505027 / 24414062500000 * d ^ 7 + 92538895873193 / 305175781250000 * d ^ 6 + 119582269259618998 / 2384185791015625 * d ^ 5 + 1097060924025896744163 / 190734863281250000 * d ^ 4 + 267315222829683974709657 / 596046447753906250 * d ^ 3 + 665892783407514207162644579 / 29802322387695312500 * d ^ 2 + 114514659069992434793827704013 / 186264514923095703125 * d + 292389185351831309750532899968673 / 46566128730773925781250 := by positivity
    nlinarith
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hT0 : 0 ≤ √(tA n) * O1n n := by unfold O1n; positivity
  unfold BstLean.Part183.WflJ
  rw [← hLd, ← hSd]
  have hpi : π ≤ 31416 / 10000 := by have := Real.pi_lt_d4; norm_num at this ⊢; linarith
  have hc : π / 2 * (18 / 10) ≤ 282744 / 100000 := by linarith
  have hc0 : 0 ≤ π / 2 * (18 / 10) := by have := Real.pi_pos; positivity
  have e : 2 * (π / 2 * (18 / 10) * L) * (S + π / 2 * (18 / 10) * (√(tA n) * O1n n)) =
      2 * (π / 2 * (18 / 10)) * (L * S) + 2 * (π / 2 * (18 / 10)) ^ 2 * (L * (√(tA n) * O1n n)) := by
    ring
  rw [e]
  have hLS0 : 0 ≤ L * S := by positivity
  have hLT0 : 0 ≤ L * (√(tA n) * O1n n) := by positivity
  have h1 : 2 * (π / 2 * (18 / 10)) * (L * S) ≤ 2 * (282744 / 100000) * (12511 / 1000000) :=
    mul_le_mul (by linarith) hLS hLS0 (by norm_num)
  have hc2 : (π / 2 * (18 / 10)) ^ 2 ≤ (282744 / 100000) ^ 2 := pow_le_pow_left₀ hc0 hc 2
  have h2 : 2 * (π / 2 * (18 / 10)) ^ 2 * (L * (√(tA n) * O1n n)) ≤
      2 * (282744 / 100000) ^ 2 * (2 / 1000000) :=
    mul_le_mul (by linarith) hLT hLT0 (by norm_num)
  have h3 : 2 * (282744 / 100000 : ℝ) * (12511 / 1000000) + 2 * (282744 / 100000) ^ 2 * (2 / 1000000) ≤
      708 / 10000 := by norm_num
  linarith

/-- **The numeric end theorem**: every `n ≥ 45 000`, with `A_f = 0.0429` and `A_ω = 0.251`
(`0.251 + 8.08·0.0429 ≤ 0.598`). Remaining hypotheses: a measurable first-layer event family `Gb`
with charge `δ_G ≤ 10⁻⁴` in the window, and the bias moments `B_f = 0.0050` (location) and
`B_ω = 0.0052` (energy) on `Gb`. Ledger:
`10⁻⁴ + ((0.0093 + 0.0050)/0.0429)⁸ + ((0.0749 + 0.0052)/0.251)⁸ ≤ 0.000692 ≤ roomK`. -/
theorem classifier_paper_bias_num22k (hHQ : BstLean.Part183.K.HQG n) (hn : 19000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ 36 / 1000000)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    (hBiasF : BiasMomF (O1n n) Gb (1422 / 100000)) (hBiasW : BiasMomW (O1n n) Gb (1474 / 100000)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_flw22k hHQ hn t hGb (by norm_num) hδG hEenm hEen hfE (by norm_num) (by norm_num)
    (Af := 66 / 1000) (Aw := 2188 / 10000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hBiasF hBiasW ?_
  have hF := FflQ_le hn
  have hW := WflJ_le hn
  have hF0 : 0 ≤ FflQ n (O1n n) (5923 / 10000) := by unfold FflQ; have := Real.pi_pos; positivity
  have hW0 : 0 ≤ BstLean.Part183.WflJ n (O1n n) (5923 / 10000) := by
    unfold BstLean.Part183.WflJ; have := Real.pi_pos; have : 0 ≤ O1n n := by unfold O1n; positivity
    positivity
  have h1 : ((FflQ n (O1n n) (5923 / 10000) + 1422 / 100000) / (66 / 1000)) ^ 8 ≤
      ((1602 / 100000 + 1422 / 100000) / (66 / 1000)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have h2 : ((BstLean.Part183.WflJ n (O1n n) (5923 / 10000) + 1474 / 100000) / (2188 / 10000)) ^ 8 ≤
      ((708 / 10000 + 1474 / 100000) / (2188 / 10000)) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 8
  have hr := roomK_ge
  have hX := BstLean.Part181.roomX_eq
  have hT21 := BstLean.Part183.roomT19_eq
  have h3 : (3 : ℝ) / 100000 + ((1602 / 100000 + 1422 / 100000) / (66 / 1000)) ^ 8 +
      ((708 / 10000 + 1474 / 100000) / (2188 / 10000)) ^ 8 + 1 / 10 ^ 6 ≤ 2600 / 10 ^ 6 := by
    norm_num
  linarith

end SPart170NumW

end BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J19.M

