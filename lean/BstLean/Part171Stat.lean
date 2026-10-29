import BstLean.Part171Node

/-!
# Part 171 (file `Stat`): the statistics event and the bias moments on it

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `t7:p08:biasmom` ("on `E₁`, ... give deterministic bounds
`B_f`, `B_ω`").

* `StatEv n Smin Smax Dm Hm Vm Pm`: the first-layer event "at every node `g < J_s`,
  `NodeStat`" (a set of pairs (World data, `A₁`)).
* `lint_sum_bound`: `∫⁻∫⁻ K Σ_j F_j ≤ K·m·Q` if every `∫⁻∫⁻ F_j ≤ Q`.
* **`biasMomF_of_stat`**: if `Gb ⊆ StatEv …` and `(n m)⁴(A₀ + A₁z₁ + A₂z₂)⁸ ≤ B⁸`, then
  `BiasMomF O Gb B`.
* **`biasMomW_of_stat`**: if `Gb ⊆ StatEv …` and `m⁸(A₀' + A₁'z₁ + A₂'z₂)⁸ ≤ B⁸`, then
  `BiasMomW O Gb B`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (biasF biasW tA BiasMomF BiasMomW opSet windowW mkR node_bulk)

variable {n : ℕ}

/-- **The statistics event**: at every node `g < J_s`, the node statistics hold. -/
def StatEv (n : ℕ) (Smin Smax Dm Hm Vm Pm : ℝ) : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {p | ∀ g < Js n, NodeStat (mkR p.1 (p.2, 0)) g Smin Smax Dm Hm Vm Pm}

/-- `∫⁻∫⁻ K Σ_j F_j ≤ K·m·Q` if every `∫⁻∫⁻ F_j ≤ Q`. -/
lemma lint_sum_bound {m : ℕ} {K Q : ℝ} (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    {F : Fin m → (Fin m → ℝ) × (Fin m → ℝ) → ℝ} (hF : ∀ j, Measurable (F j))
    (hF0 : ∀ j p, 0 ≤ F j p)
    (hb : ∀ j, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (F j (ξ₁, ξ₂)) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal Q) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (K * ∑ j, F j (ξ₁, ξ₂)) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (K * m * Q) := by
  have e : ∀ ξ₁ ξ₂ : Fin m → ℝ, ENNReal.ofReal (K * ∑ j, F j (ξ₁, ξ₂)) =
      ENNReal.ofReal K * ∑ j, ENNReal.ofReal (F j (ξ₁, ξ₂)) := by
    intro ξ₁ ξ₂
    rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_sum_of_nonneg fun j _ => hF0 j _]
  simp_rw [e]
  have hm : ∀ j, Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => ENNReal.ofReal (F j p)) :=
    fun j => ENNReal.measurable_ofReal.comp (hF j)
  have hin : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, ENNReal.ofReal K * ∑ j, ENNReal.ofReal (F j (ξ₁, ξ₂))
      ∂stdGauss (Fin m) = ENNReal.ofReal K * ∑ j, ∫⁻ ξ₂, ENNReal.ofReal (F j (ξ₁, ξ₂))
      ∂stdGauss (Fin m) := by
    intro ξ₁
    have hmj : ∀ j, Measurable (fun ξ₂ : Fin m → ℝ => ENNReal.ofReal (F j (ξ₁, ξ₂))) :=
      fun j => (hm j).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hmj j),
      lintegral_finsetSum _ fun j _ => hmj j]
  simp_rw [hin]
  have hout : ∀ j, Measurable (fun ξ₁ : Fin m → ℝ =>
      ∫⁻ ξ₂, ENNReal.ofReal (F j (ξ₁, ξ₂)) ∂stdGauss (Fin m)) :=
    fun j => (hm j).lintegral_prod_right'
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hout j),
    lintegral_finsetSum _ fun j _ => hout j]
  calc ENNReal.ofReal K * ∑ j, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (F j (ξ₁, ξ₂)) ∂stdGauss (Fin m)
        ∂stdGauss (Fin m)
      ≤ ENNReal.ofReal K * ∑ _j : Fin m, ENNReal.ofReal Q := by
        gcongr with j; exact hb j
    _ = ENNReal.ofReal (K * m * Q) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul hK, mul_assoc]

/-- **The location bias moments on the statistics event.** -/
theorem biasMomF_of_stat (hn : 80000 ≤ n) {O : ℝ} (hO : 0 ≤ O) {Smin Smax Dm Hm Vm Pm : ℝ}
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
theorem biasMomW_of_stat (hn : 80000 ≤ n) {O : ℝ} (hO : 0 ≤ O) {Smin Smax Dm Hm Vm Pm : ℝ}
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

end BstLean.Part171
