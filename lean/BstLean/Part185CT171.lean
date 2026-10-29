import BstLean.Part185CT170

/-!
# Part 185 (file `CT171`): the T171 link (bias moments from the statistics event).

No proof is left open; no `native_decide` or `axiom` is used.

A copy of the Part 184 `M` chain (floor 17 500) for every `n ≥ 17 250` (statistics cap `n ≤ 17 500`), with the removal tolerance `η = 1/250` and the floor `sd = 0.4482` (file `Part185Q`),
namespaces `….J1725` / `BstLean.Part185.C`. The constants above are those of the Lean statements; the
docstrings of copied lemmas can carry older numbers, and the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.M

-- ===== from Part171Stat.lean =====
section SPart171Stat
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (biasF biasW tA BiasMomF BiasMomW opSet windowW mkR node_bulk)
variable {n : ℕ}
/-- **The location bias moments on the statistics event.** -/
theorem biasMomF_of_stat (hn : 17250 ≤ n) {O : ℝ} (hO : 0 ≤ O) {Smin Smax Dm Hm Vm Pm : ℝ}
    (hSm : 0 < Smin) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEv n Smin Smax Dm Hm Vm Pm) {z₁ z₂ : ℝ} (hz1 : 0 < z₁) (hz2 : 0 < z₂)
    (hz1' : 384 ≤ z₁ ^ 8) (hz2' : 10321920 ≤ z₂ ^ 8)
    (hA0 : 0 < AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 < AF1 √Smin Dm Vm Pm (√(tA n) * O)) (hA2 : 0 < AF2 √Smin Dm) {B : ℝ}
    (hB : ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 * (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AF1 √Smin Dm Vm Pm (√(tA n) * O) * z₁ + AF2 √Smin Dm * z₂) ^ 8 ≤ B ^ 8) :
    BiasMomF O Gb B := by
  intro wr hw g hg A₁ hA₁ hG
  have hn1 : 1 ≤ n := by omega
  set c := mkR wr (A₁, 0)
  have hs := node_bulk hn hw (A₁, 0) hg
  have h1 : OpB (A1 c) O := hA₁
  have H := hGb hG g hg
  set A₀ := AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm
  set A₁' := AF1 √Smin Dm Vm Pm (√(tA n) * O)
  set A₂ := AF2 √Smin Dm
  set K := (n : ℝ) ^ 4 * ((mA n : ℕ) : ℝ) ^ 3
  have hK : 0 ≤ K := by positivity
  set F : Fin (mA n) → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → ℝ := fun j p =>
    (A₀ + A₁' * √(p.1 j ^ 2 + p.2 j ^ 2) + A₂ * √(p.1 j ^ 2 + p.2 j ^ 2) ^ 2) ^ 8 with hFd
  have hF : ∀ j, Measurable (F j) := fun j => by
    simp only [hFd]
    refine Measurable.pow_const ?_ 8
    have hq : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => p.1 j ^ 2 + p.2 j ^ 2) := by
      fun_prop
    exact (measurable_const.add (measurable_const.mul hq.sqrt)).add
      (measurable_const.mul (hq.sqrt.pow_const 2))
  have hF0 : ∀ j p, 0 ≤ F j p := fun j p => by simp only [hFd]; positivity
  have hQ : 0 ≤ (A₀ + A₁' * z₁ + A₂ * z₂) ^ 8 := by positivity
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
        ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (K * ∑ j, F j (ξ₁, ξ₂)) ∂stdGauss (Fin (mA n))
          ∂stdGauss (Fin (mA n)) := by
        refine lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => ENNReal.ofReal_le_ofReal ?_
        exact node_biasF hn1 c g hs hO h1 hSm H ξ₁ ξ₂
    _ ≤ ENNReal.ofReal (K * (mA n : ℕ) * (A₀ + A₁' * z₁ + A₂ * z₂) ^ 8) :=
        lint_sum_bound hK hQ hF hF0 fun j => zeta_poly j hA0 hA1 hA2 hz1 hz2 hz1' hz2'
    _ ≤ ENNReal.ofReal (B ^ 8) := by
        refine ENNReal.ofReal_le_ofReal (le_of_eq_of_le ?_ hB)
        simp only [K]; ring

/-- **The energy bias moments on the statistics event.** -/
theorem biasMomW_of_stat (hn : 17250 ≤ n) {O : ℝ} (hO : 0 ≤ O) {Smin Smax Dm Hm Vm Pm : ℝ}
    (hSm : 0 < Smin) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEv n Smin Smax Dm Hm Vm Pm) {z₁ z₂ : ℝ} (hz1 : 0 < z₁) (hz2 : 0 < z₂)
    (hz1' : 384 ≤ z₁ ^ 8) (hz2' : 10321920 ≤ z₂ ^ 8)
    (hA0 : 0 < AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 < AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) (hA2 : 0 < AW2 Dm Pm (√(tA n) * O))
    {B : ℝ}
    (hB : ((mA n : ℕ) : ℝ) ^ 8 * (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O) * z₁ + AW2 Dm Pm (√(tA n) * O) * z₂) ^ 8 ≤ B ^ 8) :
    BiasMomW O Gb B := by
  intro wr hw g hg A₁ hA₁ hG
  have hn1 : 1 ≤ n := by omega
  set c := mkR wr (A₁, 0)
  have hs := node_bulk hn hw (A₁, 0) hg
  have h1 : OpB (A1 c) O := hA₁
  have H := hGb hG g hg
  set A₀ := AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm
  set A₁' := AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)
  set A₂ := AW2 Dm Pm (√(tA n) * O)
  set K := ((mA n : ℕ) : ℝ) ^ 7
  have hK : 0 ≤ K := by positivity
  set F : Fin (mA n) → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → ℝ := fun j p =>
    (A₀ + A₁' * √(p.1 j ^ 2 + p.2 j ^ 2) + A₂ * √(p.1 j ^ 2 + p.2 j ^ 2) ^ 2) ^ 8 with hFd
  have hF : ∀ j, Measurable (F j) := fun j => by
    simp only [hFd]
    refine Measurable.pow_const ?_ 8
    have hq : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => p.1 j ^ 2 + p.2 j ^ 2) := by
      fun_prop
    exact (measurable_const.add (measurable_const.mul hq.sqrt)).add
      (measurable_const.mul (hq.sqrt.pow_const 2))
  have hF0 : ∀ j p, 0 ≤ F j p := fun j p => by simp only [hFd]; positivity
  have hQ : 0 ≤ (A₀ + A₁' * z₁ + A₂ * z₂) ^ 8 := by positivity
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
        ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (K * ∑ j, F j (ξ₁, ξ₂)) ∂stdGauss (Fin (mA n))
          ∂stdGauss (Fin (mA n)) := by
        refine lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => ENNReal.ofReal_le_ofReal ?_
        exact node_biasW hn1 c g hs hO h1 hSm H ξ₁ ξ₂
    _ ≤ ENNReal.ofReal (K * (mA n : ℕ) * (A₀ + A₁' * z₁ + A₂ * z₂) ^ 8) :=
        lint_sum_bound hK hQ hF hF0 fun j => zeta_poly j hA0 hA1 hA2 hz1 hz2 hz1' hz2'
    _ ≤ ENNReal.ofReal (B ^ 8) := by
        refine ENNReal.ofReal_le_ofReal (le_of_eq_of_le ?_ hB)
        simp only [K]; ring

end SPart171Stat

-- ===== from Part171Num.lean =====
section SPart171Num
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (phiG phiG_pos)
open BstLean.Part170 (tA)
variable {n : ℕ}
/-- The quantities in terms of `r = √n`. -/
lemma r_facts (hn : 17250 ≤ n) :
    13133 / 100 ≤ √(n : ℝ) ∧ √(n : ℝ) ^ 2 = n ∧
    √(SminN n) = 1 / (√5 * √(n : ℝ)) ∧ √(SmaxN n) = √5 / √(n : ℝ) ∧
    tA n = 2 / √(n : ℝ) ^ 4 ∧ √(tA n) = √2 / √(n : ℝ) ^ 2 ∧
    O1n n = √2 * (√(n : ℝ) + 2) ∧ √(DmN n) = 4 / √(n : ℝ) ^ 3 ∧ √(VmN n) = 8 / √(n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr : 13133 / 100 ≤ r := by
    rw [hrd, Real.le_sqrt (by norm_num) hn0.le]
    have : (17250 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  refine ⟨hr, hr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SminN
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
  · unfold SmaxN; rw [Real.sqrt_div' _ hn0.le]
  · unfold tA; rw [hmA, ← hr2]; ring
  · unfold tA
    rw [hmA, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hn0.le, ← hr2]
  · unfold O1n
    rw [Real.sqrt_div' _ hn0.le, ← hrd]
    field_simp
    linear_combination (-1 : ℝ) * hr2
  · unfold DmN
    rw [Real.sqrt_div' _ (by positivity), show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), ← hr2, show (r ^ 2) ^ 3 = (r ^ 3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  · unfold VmN
    rw [Real.sqrt_div' _ (by positivity), show (64 : ℝ) = 8 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), ← hr2, show (r ^ 2) ^ 4 = (r ^ 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]

end SPart171Num

-- ===== from Part171Op.lean =====
section SPart171Op
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW mkR node_bulk opSet measurableSet_opSet
  biasF biasW measurable_mkR)
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- **On the operator event, `ς² ≤ 5/n`.** -/
lemma vsig2_upper (hn : 17250 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1)
    (h1 : OpB (A1 c) (O1n n)) : vsig2 c s ≤ SmaxN n := by
  have hle := vsig2_le (by omega) c hs
  have hop := opN_le_of_OpB (O1n_nonneg n) h1
  have hn0 : (17250 : ℝ) ≤ n := by exact_mod_cast hn
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hop2 : BstLean.Part152.opN (A1 c) ^ 2 ≤ O1n n ^ 2 :=
    pow_le_pow_left₀ (BstLean.Part152.opN_nonneg _) hop 2
  have hO2 : O1n n ^ 2 ≤ 2 * (n : ℝ) * (1 + 307 / 10000) := by
    obtain ⟨hr, hr2, -, -, -, -, hO, -, -⟩ := r_facts hn
    rw [hO, mul_pow, Real.sq_sqrt (by norm_num)]
    set r := √(n : ℝ)
    rw [← hr2]
    nlinarith
  have hs0 : 0 ≤ 1 - s ^ 2 := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h1' : (1 - s ^ 2) * ((n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      (n : ℝ) * (2 * (n : ℝ) * (1 + 307 / 10000)) := by
    have a1 : 1 - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    have a2 : (n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2 ≤ (n : ℝ) * (2 * (n : ℝ) * (1 + 307 / 10000)) :=
      mul_le_mul_of_nonneg_left (hop2.trans hO2) (by positivity)
    have a3 : 0 ≤ (n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2 := by positivity
    nlinarith
  refine hle.trans ?_
  rw [hmA]
  unfold SmaxN
  calc 2 / (n : ℝ) ^ 2 * ((1 - s ^ 2) * ((n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) / ((n : ℝ) - 1))
      ≤ 2 / (n : ℝ) ^ 2 * ((n : ℝ) * (2 * (n : ℝ) * (1 + 307 / 10000)) / ((n : ℝ) - 1)) := by
        gcongr
    _ = (41228 / 10000) / ((n : ℝ) - 1) := by field_simp; ring
    _ ≤ 5 / (n : ℝ) := by
        rw [div_le_div_iff₀ hn1 (by positivity)]
        nlinarith

end SPart171Op

-- ===== from Part171Gen.lean =====
section SPart171Gen
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW mkR node_bulk opSet measurableSet_opSet
  measurable_mkR)
open BstLean.Part153 (nuA)
variable {n : ℕ}
lemma statOpG_sub (hn : 17250 ≤ n) (Sm Dm Vm Pm : ℝ) :
    StatEvOpG n Sm Dm Vm Pm ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆
      StatEv n Sm (SmaxN n) Dm Dm Vm Pm := by
  rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
  obtain ⟨a, b, d, f⟩ := hG hA g hg
  have hs := node_bulk hn hw (A₁, 0) hg
  have hU := hUN_eq_DstN (by omega) (mkR wr (A₁, 0)) g hs (O1n_nonneg n) hA
  exact ⟨a, vsig2_upper hn _ hs hA, b, hU ▸ b, d, f⟩

/-- **The classifier theorem with free thresholds** (every `n ≥ 45 000`). -/
theorem classifier_paper_gen22k (hHQ : BstLean.Part185.C.HQG n) (hn : 17250 ≤ n) (t : ℝ) {Sm Dm Vm Pm z₁ z₂ : ℝ} (hSm : 0 < Sm)
    (hz1 : 0 < z₁) (hz2 : 0 < z₂) (hz1' : 384 ≤ z₁ ^ 8) (hz2' : 10321920 ≤ z₂ ^ 8)
    (hF0 : 0 < AF0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm)
    (hF1 : 0 < AF1 √Sm Dm Vm Pm (√(tA n) * O1n n)) (hF2 : 0 < AF2 √Sm Dm)
    (hF : ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 * (AF0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm +
      AF1 √Sm Dm Vm Pm (√(tA n) * O1n n) * z₁ + AF2 √Sm Dm * z₂) ^ 8 ≤ (1566 / 100000) ^ 8)
    (hW0 : 0 < AW0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm)
    (hW1 : 0 < AW1 √Sm √(SmaxN n) Dm Vm Pm (√(tA n) * O1n n))
    (hW2 : 0 < AW2 Dm Pm (√(tA n) * O1n n))
    (hW : ((mA n : ℕ) : ℝ) ^ 8 * (AW0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm +
      AW1 √Sm √(SmaxN n) Dm Vm Pm (√(tA n) * O1n n) * z₁ +
      AW2 Dm Pm (√(tA n) * O1n n) * z₂) ^ 8 ≤ (1624 / 100000) ^ 8)
    (hδG : ∀ wr : WRet n, windowW wr →
      (nuA n).real {θ | (wr, θ.1) ∉ StatEvOpG n Sm Dm Vm Pm} ≤ 70 / 1000000)
    {Een : Set (Ret n)} (hEenm : MeasurableSet Een)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have HF := biasMomF_of_stat hn (O1n_nonneg n) hSm (statOpG_sub hn Sm Dm Vm Pm) hz1 hz2
    hz1' hz2' hF0 hF1 hF2 hF
  have HW := biasMomW_of_stat hn (O1n_nonneg n) hSm (statOpG_sub hn Sm Dm Vm Pm) hz1 hz2
    hz1' hz2' hW0 hW1 hW2 hW
  refine classifier_paper_bias_num22k hHQ hn t (measurableSet_StatEvOpG n Sm Dm Vm Pm)
    hδG hEenm hEen hfE ?_ ?_
  · intro wr hw g hg A₁ hA hG
    exact HF wr hw g hg A₁ hA ⟨hG, hA, hw⟩
  · intro wr hw g hg A₁ hA hG
    exact HW wr hw g hg A₁ hA ⟨hG, hA, hw⟩

end SPart171Gen

end BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J1725.M
