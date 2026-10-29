import BstLean.Part143FC
import BstLean.Part142Final
import BstLean.Part143AgentC

/-!
# Part 143: the `L²` bound of the distance kernel with two orthogonality steps

Setting: `Ω = (u, u′) × (W, A, A′, F)`, `x = x(u)`, `x′ = x(u′)`, `t = ⟨x, x′⟩`, `y = A(x)`,
`y′ = A(x′)`, `S = 4/n`, `Q = κ^{∘6}(0)`. With `cF`, `rF` of `Part143FC` and an abstract centred
part `cA` of the link of the last matrix of the Agent network:

`kD − S(1 − Q) = X1 + X2 + X3 + X4 + X5` (`kD_split`),
`X1 = cF F y y′`, `X2 = rF F y y′`, `X3 = (2/n)·cA A x x′`,
`X4 = (2/n)·[Φ_{κ∘κ}(y, y′) − 2(1 − κ^{∘4}(t)) − cA A x x′]`, `X5 = S·(Q − κ^{∘4}(t))`.

`X1 ⟂ X2 + X3 + X4 + X5` (mean zero over `F₂`), `X3 ⟂ X5` (mean zero over `A`). Hence
(`kernDist143_of`) `‖kD − S(1 − Q)‖₂ ≤ S·√(E1² + (E2 + E4 + √(E3² + pW²))²)`.

* `L2le.add_orth`: `‖f + g‖₂ ≤ √(a² + b²)` if `∫ f·g = 0`.
* `chord_pW`: `‖κ^{∘4}(t) − Q‖₂ ≤ σ₄·τ` from `‖t − κ(κ(0))‖₂ ≤ τ`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142

/-! ## Abstract tools -/

section tools

/-- **Sum of squares.** `‖f + g‖₂ ≤ √(a² + b²)` if `∫ f·g = 0` (the hypothesis may use that
`f·g` is integrable). -/
theorem L2le.add_orth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ} {a b : ℝ}
    (hf : L2le μ f a) (hg : L2le μ g b)
    (h0 : Integrable (fun ω => f ω * g ω) μ → ∫ ω, f ω * g ω ∂μ = 0) :
    L2le μ (fun ω => f ω + g ω) (√(a ^ 2 + b ^ 2)) := by
  have i12 : Integrable (fun ω => f ω ^ 2 + g ω ^ 2) μ := hf.int_sq.add hg.int_sq
  have hfg : Integrable (fun ω => f ω * g ω) μ := by
    refine Integrable.mono' i12 (hf.aesm.mul hg.aesm) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (f ω - g ω), sq_nonneg (f ω + g ω)]
  have e : (fun ω => (f ω + g ω) ^ 2) = fun ω => f ω ^ 2 + g ω ^ 2 + 2 * (f ω * g ω) := by
    funext ω; ring
  have i3 : Integrable (fun ω => (f ω + g ω) ^ 2) μ := by
    rw [e]; exact i12.add (hfg.const_mul 2)
  have e3 : ∫ ω, (f ω + g ω) ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ + ∫ ω, g ω ^ 2 ∂μ := by
    rw [e, integral_add i12 (hfg.const_mul 2), integral_add hf.int_sq hg.int_sq,
      integral_const_mul, h0 hfg]
    ring
  refine ⟨hf.aesm.add hg.aesm, i3, ?_⟩
  have h3 : ∫ ω, (f ω + g ω) ^ 2 ∂μ ≤ a ^ 2 + b ^ 2 := by
    rw [e3]; exact add_le_add hf.le hg.le
  rw [Real.sq_sqrt (by positivity)]
  exact h3

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- The integral on a product is `0` if every (integrable) section has integral `0`. -/
lemma integral_prod_zero [SFinite μ] [SFinite ν] {H : α × β → ℝ} (hH : Integrable H (μ.prod ν))
    (h : ∀ x, Integrable (fun y => H (x, y)) ν → ∫ y, H (x, y) ∂ν = 0) :
    ∫ z, H z ∂(μ.prod ν) = 0 := by
  rw [integral_prod _ hH]
  have h1 : ∀ᵐ x ∂μ, ∫ y, H (x, y) ∂ν = (fun _ : α => (0 : ℝ)) x :=
    hH.prod_right_ae.mono fun x hx => h x hx
  rw [integral_congr_ae h1]
  simp

lemma integral_mul_const_zero {g : α → ℝ} (h0 : ∫ x, g x ∂μ = 0) (c : ℝ) :
    ∫ x, g x * c ∂μ = 0 := by
  rw [integral_mul_const, h0, zero_mul]

lemma integral_fst_mul_zero [SFinite μ] [IsProbabilityMeasure ν] {g : α → ℝ}
    (h0 : ∫ x, g x ∂μ = 0) (c : ℝ) : ∫ z : α × β, g z.1 * c ∂(μ.prod ν) = 0 := by
  refine integral_mul_const_zero ?_ c
  have h := integral_fun_fst (μ := μ) (ν := ν) g
  rw [h0] at h
  refine Eq.trans h ?_
  simp

end tools

section General

variable {N mW n mA mF : ℕ}

/-! ## The functions of `(u, u′, W)` -/

/-- **`chord_pW`**: `‖κ^{∘4}(t) − κ^{∘6}(0)‖₂ ≤ σ₄·τ` from `‖t − κ(κ(0))‖₂ ≤ τ`. -/
theorem chord_pW (hn : 1 ≤ n) {τ : ℝ}
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        kappa^[4] (tX z) - kappa^[6] 0) (sig4 * τ) := by
  have hs4 := sig4_nonneg
  have hk4 : Measurable (kappa^[4]) := (continuous_kappa.iterate 4).measurable
  have mtX : Measurable (tX (N := N) (mW := mW) (n := n)) := measurable_tX
  refine L2le.of_abs_le ((hk4.comp mtX).sub measurable_const).aestronglyMeasurable
    (hT.const_mul_nonneg hs4) (fun z => ?_)
  rw [abs_mul, abs_of_nonneg hs4]
  exact iter4_chord (tX_mem hn z)

/-- `t ↦ S·(g₀ + g₁(1 − κ(κ(t))) + g₂(1 − t) + g₃(1 − κ^{∘4}(t)))`. -/
noncomputable def linB (n : ℕ) (g0 g1 g2 g3 : ℝ) (t : ℝ) : ℝ :=
  4 / (n : ℝ) * (g0 + g1 * (1 - kappa (kappa t)) + g2 * (1 - t) + g3 * (1 - kappa^[4] t))

lemma a2_nonneg : 0 ≤ 1 - kappa (kappa 0) := by have := kappa2_zero_le; linarith

lemma aQ_nonneg : 0 ≤ 1 - kappa^[6] 0 := by have := kappa6_zero_le; linarith

lemma lin_nonneg {g0 g1 g2 g3 : ℝ} (h0 : 0 ≤ g0) (h1 : 0 ≤ g1) (h2 : 0 ≤ g2) (h3 : 0 ≤ g3) :
    0 ≤ g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - kappa (kappa 0)) + g3 * (1 - kappa^[6] 0) := by
  have := mul_nonneg h1 one_sub_k4_nonneg
  have := mul_nonneg h2 a2_nonneg
  have := mul_nonneg h3 aQ_nonneg
  linarith

/-- A function `S·(g₀ + g₁(1 − κ(κ(t))) + g₂(1 − t) + g₃(1 − κ^{∘4}(t)))` of `t = t_x`, in
`L²((u, u′) ⊗ W)`; `g₁` has any sign. -/
lemma tX_lin_L2 (hn : 1 ≤ n) (hN : 1 ≤ N) {g0 g1 g2 g3 τ : ℝ}
    (h2 : 0 ≤ g2) (h3 : 0 ≤ g3) (hτ : 0 ≤ τ)
    (hC : 0 ≤ g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - kappa (kappa 0)) + g3 * (1 - kappa^[6] 0))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => linB n g0 g1 g2 g3 (tX z))
      (4 / (n : ℝ) * (g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - kappa (kappa 0)) +
        g3 * (1 - kappa^[6] 0) + (|g1| + g2 + g3 * sig4) * τ)) := by
  have := lawU2_prob hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs4 := sig4_nonneg
  set q := kappa (kappa 0) with hq
  have hqm : q ∈ Icc (-1 : ℝ) 1 := kk_memIcc KGood.zero_mem
  have e40 : kappa^[4] 0 = kappa (kappa q) := rfl
  set μ1 := (lawU2 N).prod (mlpGauss N mW n) with hμ1
  have hk4 : Measurable (kappa^[4]) := (continuous_kappa.iterate 4).measurable
  have hkk : Measurable (fun t : ℝ => kappa (kappa t)) :=
    (continuous_kappa.comp continuous_kappa).measurable
  have mtX : Measurable (tX (N := N) (mW := mW) (n := n)) := measurable_tX
  set C0 : ℝ := g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - q) + g3 * (1 - kappa^[6] 0) with hC0
  have hC00 : 0 ≤ C0 := hC
  set Lc : ℝ := |g1| + g2 + g3 * sig4 with hLc
  have hLc0 : 0 ≤ Lc := by rw [hLc]; positivity
  have c1 : L2le μ1 (fun _ : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => C0) C0 := by
    have := L2le.const (μ := μ1) C0
    rwa [abs_of_nonneg hC00] at this
  have c2 := (L2le.abs' hT).const_mul_nonneg (c := Lc) hLc0
  have c3 := (c1.add0 c2 hC00 (by positivity)).const_mul_nonneg (c := 4 / (n : ℝ))
    (by positivity)
  have mm : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      4 / (n : ℝ) * (g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z) +
        g3 * (1 - kappa^[4] (tX z)))) :=
    (((measurable_const.add ((measurable_const.sub (hkk.comp mtX)).const_mul _)).add
      ((measurable_const.sub mtX).const_mul _)).add
      ((measurable_const.sub (hk4.comp mtX)).const_mul _)).const_mul _
  refine L2le.of_abs_le mm.aestronglyMeasurable c3 (fun z => ?_)
  unfold linB
  have ht := tX_mem (N := N) (mW := mW) hn z
  have hkt := kk_memIcc ht
  have hl := kk_lip ht hqm
  rw [← e40] at hl
  have hl' := abs_le.mp hl
  have habs := abs_nonneg (tX z - q)
  have hle := le_abs_self (tX z - q)
  have hge := neg_abs_le (tX z - q)
  have hch := iter4_chord ht
  have hch' := abs_le.mp hch
  have hs4a := mul_nonneg hs4 habs
  have u4 : 1 - tX z ≤ 1 - q + |tX z - q| := by linarith
  have t1 : g1 * (1 - kappa (kappa (tX z))) ≤ g1 * (1 - kappa^[4] 0) + |g1| * |tX z - q| := by
    have e : g1 * (1 - kappa (kappa (tX z))) =
        g1 * (1 - kappa^[4] 0) + g1 * (kappa^[4] 0 - kappa (kappa (tX z))) := by ring
    rw [e]
    have : g1 * (kappa^[4] 0 - kappa (kappa (tX z))) ≤ |g1| * |tX z - q| := by
      calc g1 * (kappa^[4] 0 - kappa (kappa (tX z)))
          ≤ |g1 * (kappa^[4] 0 - kappa (kappa (tX z)))| := le_abs_self _
        _ = |g1| * |kappa (kappa (tX z)) - kappa^[4] 0| := by rw [abs_mul, abs_sub_comm]
        _ ≤ |g1| * |tX z - q| := mul_le_mul_of_nonneg_left hl (abs_nonneg _)
    linarith
  have t1' : g1 * (1 - kappa^[4] 0) - |g1| * |tX z - q| ≤ g1 * (1 - kappa (kappa (tX z))) := by
    have e : g1 * (1 - kappa (kappa (tX z))) =
        g1 * (1 - kappa^[4] 0) + g1 * (kappa^[4] 0 - kappa (kappa (tX z))) := by ring
    rw [e]
    have : -(|g1| * |tX z - q|) ≤ g1 * (kappa^[4] 0 - kappa (kappa (tX z))) := by
      have h5 : |g1 * (kappa^[4] 0 - kappa (kappa (tX z)))| ≤ |g1| * |tX z - q| := by
        rw [abs_mul, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hl (abs_nonneg _)
      linarith [neg_abs_le (g1 * (kappa^[4] 0 - kappa (kappa (tX z))))]
    linarith
  have t2 : g2 * (1 - tX z) ≤ g2 * (1 - q) + g2 * |tX z - q| := by
    have := mul_le_mul_of_nonneg_left u4 h2
    linarith
  have t2' : g2 * (1 - q) - g2 * |tX z - q| ≤ g2 * (1 - tX z) := by
    have : 1 - q - |tX z - q| ≤ 1 - tX z := by linarith
    have := mul_le_mul_of_nonneg_left this h2
    linarith
  have t3 : g3 * (1 - kappa^[4] (tX z)) ≤ g3 * (1 - kappa^[6] 0) + g3 * (sig4 * |tX z - q|) := by
    have : 1 - kappa^[4] (tX z) ≤ 1 - kappa^[6] 0 + sig4 * |tX z - q| := by linarith [hch'.1]
    have := mul_le_mul_of_nonneg_left this h3
    linarith
  have t3' : g3 * (1 - kappa^[6] 0) - g3 * (sig4 * |tX z - q|) ≤
      g3 * (1 - kappa^[4] (tX z)) := by
    have : 1 - kappa^[6] 0 - sig4 * |tX z - q| ≤ 1 - kappa^[4] (tX z) := by linarith [hch'.2]
    have := mul_le_mul_of_nonneg_left this h3
    linarith
  have eL : Lc * |tX z - q| = |g1| * |tX z - q| + g2 * |tX z - q| + g3 * (sig4 * |tX z - q|) := by
    rw [hLc]; ring
  have innerabs : |g0 + g1 * (1 - kappa (kappa (tX z))) + g2 * (1 - tX z) +
      g3 * (1 - kappa^[4] (tX z))| ≤ C0 + Lc * |tX z - q| := by
    rw [abs_le, eL, hC0]
    constructor
    · have hLn : 0 ≤ |g1| * |tX z - q| + g2 * |tX z - q| + g3 * (sig4 * |tX z - q|) := by
        positivity
      have hC00' : 0 ≤ g0 + g1 * (1 - kappa^[4] 0) + g2 * (1 - q) + g3 * (1 - kappa^[6] 0) := hC
      linarith
    · linarith
  have hR0 : 0 ≤ C0 + Lc * |tX z - q| := add_nonneg hC00 (mul_nonneg hLc0 habs)
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ)),
    abs_of_nonneg hR0]
  exact mul_le_mul_of_nonneg_left innerabs (by positivity)

/-! ## From fixed inputs to `Ω` -/

/-- **The lift.** A function `X (A, A′, F) x x′` with the bound `b(⟨x, x′⟩)` in `L²(A, A′, F)`
for unit `x, x′` has the `L²(Ω)` bound of `b(t_x)` at `x = x(u)`, `x′ = x(u′)`. -/
theorem lift_L2 (hn : 1 ≤ n) (hN : 1 ≤ N)
    {X : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hXm : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => X z.1 z.2.1 z.2.2))
    {b : ℝ → ℝ} {B : ℝ}
    (hb : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => b (tX z)) B)
    (hS : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 => X p x x')
        (b (dotp x x'))) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        X ω.2.2 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2)) B := by
  have := lawU2_prob hN
  set μ1 := (lawU2 N).prod (mlpGauss N mW n) with hμ1
  set P := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)) with hP
  have mf : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      X ω.2.2 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2)) :=
    hXm.comp (f := fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      (ω.2.2, (xW ω.2.1 ω.1.1, xW ω.2.1 ω.1.2)))
      ((measurable_snd.comp measurable_snd).prodMk
        ((measurable_xW_comp (measurable_fst.comp measurable_snd)
          (measurable_fst.comp measurable_fst)).prodMk
        (measurable_xW_comp (measurable_fst.comp measurable_snd)
          (measurable_snd.comp measurable_fst))))
  have mf1 : Measurable (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
      (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
      X z.2 (xW z.1.2 z.1.1.1) (xW z.1.2 z.1.1.2)) :=
    hXm.comp (f := fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
      (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
      (z.2, (xW z.1.2 z.1.1.1, xW z.1.2 z.1.1.2)))
      (measurable_snd.prodMk
        ((measurable_xW_comp (measurable_snd.comp measurable_fst)
          (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        (measurable_xW_comp (measurable_snd.comp measurable_fst)
          (measurable_snd.comp (measurable_fst.comp measurable_fst)))))
  have B1 : L2le (μ1.prod P)
      (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
        X z.2 (xW z.1.2 z.1.1.1) (xW z.1.2 z.1.1.2)) B := by
    refine L2le.prod' mf1.aestronglyMeasurable hb (Filter.Eventually.of_forall fun z => ?_)
    exact hS (xW z.2 z.1.1) (xW z.2 z.1.2) (normSq_xW hn _ _) (normSq_xW hn _ _)
  have hmap : (μ1.prod P).map MeasurableEquiv.prodAssoc = (lawU2 N).prod (lawR N mW n mA mF) := by
    rw [hμ1, hP, Measure.prodAssoc_prod]
    rfl
  have hf : AEStronglyMeasurable
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        X ω.2.2 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2))
      ((μ1.prod P).map MeasurableEquiv.prodAssoc) := mf.aestronglyMeasurable
  have key : L2le (μ1.prod P)
      (fun z : (((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) ×
          (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) =>
        (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
          X ω.2.2 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2)) (MeasurableEquiv.prodAssoc z)) B :=
    B1.congr_fun fun z => rfl
  have h := L2le.of_comp_map (MeasurableEquiv.measurable _) hf key
  rwa [hmap] at h

/-! ## The five parts -/

/-- `y = A(x(u))`. -/
noncomputable def yA (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : Fin n → ℝ :=
  mlpEval ω.2.2.1 (xW ω.2.1 ω.1.1)

/-- `y′ = A(x(u′))`. -/
noncomputable def yA' (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : Fin n → ℝ :=
  mlpEval ω.2.2.1 (xW ω.2.1 ω.1.2)

/-- `t = ⟨x(u), x(u′)⟩` on `Ω`. -/
noncomputable def tO (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  dotp (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2)

/-- `X1`: the centred part of the link of `F`. -/
noncomputable def kX1 (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  cF ω.2.2.2.2 (yA ω) (yA' ω)

/-- `X2`: the remainder of the link of `F`. -/
noncomputable def kX2 (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  rF ω.2.2.2.2 (yA ω) (yA' ω)

/-- `X3`: the centred part of the link of the last matrix of the Agent network. -/
noncomputable def kX3 (cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  2 / (n : ℝ) * cA ω.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2)

/-- `X4`: the remainder of the link of the Agent network. -/
noncomputable def kX4 (cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  2 / (n : ℝ) * (phiD (kappa ∘ kappa) (yA ω) (yA' ω) - 2 * (1 - kappa^[4] (tO ω)) -
    cA ω.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2))

/-- `X5`: the link of the World network. -/
noncomputable def kX5 (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  4 / (n : ℝ) * (kappa^[6] 0 - kappa^[4] (tO ω))

/-- **The decomposition.** -/
theorem kD_split (cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) :
    kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0) =
      kX1 ω + (kX2 ω + kX4 cA ω + (kX3 cA ω + kX5 ω)) := by
  have h := cF_add_rF ω.2.2.2.2 (yA ω) (yA' ω)
  rw [kD_eq_kernD]
  unfold kernD
  rw [kernD_eq]
  unfold kX1 kX2 kX3 kX4 kX5
  unfold yA yA' at h ⊢
  linear_combination -h

/-! ## The constants -/

/-- The bound of `X1/S`. -/
noncomputable def asmE1 (mF : ℕ) (d0 d1 d2 τ : ℝ) : ℝ :=
  2 * f1a mF * (d0 + d1 * (1 - kappa^[4] 0 + τ) + d2 * (1 - kappa (kappa 0) + τ))

/-- The bound of `X2/S`. -/
noncomputable def asmE2 (n mA mF : ℕ) (d0 d1 d2 δ2 τ : ℝ) : ℝ :=
  2 * f1b mF * (d0 + d1 * (1 - kappa^[4] 0 + τ) + d2 * (1 - kappa (kappa 0) + τ)) +
    2 * f2 mF * ((1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ))) + 2 * f3 mF * √(eps4 n mA) +
    f4 * δ2

/-- The bound of `X3/S`. -/
noncomputable def asmE3 (c0 c1 c2 τ : ℝ) : ℝ :=
  c0 + c1 * (1 - kappa^[6] 0 + sig4 * τ) + c2 * (1 - kappa (kappa 0) + τ)

/-- The bound of `X4/S`. -/
noncomputable def asmE4 (r0 r1 r1' r2 τ : ℝ) : ℝ :=
  r0 + r1 * (1 - kappa^[6] 0) - r1' * (1 - kappa^[4] 0) + r2 * (1 - kappa (kappa 0)) +
    (r1 * sig4 + r1' + r2) * τ

lemma asmD_nonneg {d0 d1 d2 τ : ℝ} (h0 : 0 ≤ d0) (h1 : 0 ≤ d1) (h2 : 0 ≤ d2) (hτ : 0 ≤ τ) :
    0 ≤ d0 + d1 * (1 - kappa^[4] 0 + τ) + d2 * (1 - kappa (kappa 0) + τ) := by
  have a4 := one_sub_k4_nonneg
  have a2 := a2_nonneg
  have := mul_nonneg h1 (add_nonneg a4 hτ)
  have := mul_nonneg h2 (add_nonneg a2 hτ)
  linarith

lemma asmE1_nonneg (mF : ℕ) {d0 d1 d2 τ : ℝ} (h0 : 0 ≤ d0) (h1 : 0 ≤ d1) (h2 : 0 ≤ d2)
    (hτ : 0 ≤ τ) : 0 ≤ asmE1 mF d0 d1 d2 τ := by
  have := asmD_nonneg h0 h1 h2 hτ
  have := f1a_nonneg mF
  unfold asmE1; positivity

lemma asmE2_nonneg (n mA mF : ℕ) {d0 d1 d2 δ2 τ : ℝ} (h0 : 0 ≤ d0) (h1 : 0 ≤ d1) (h2 : 0 ≤ d2)
    (hδ : 0 ≤ δ2) (hτ : 0 ≤ τ) : 0 ≤ asmE2 n mA mF d0 d1 d2 δ2 τ := by
  have := asmD_nonneg h0 h1 h2 hτ
  have := f1b_nonneg mF
  have := f2_nonneg mF
  have := f3_nonneg mF
  have := f4_nonneg
  unfold asmE2; positivity

lemma asmE3_nonneg {c0 c1 c2 τ : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (hτ : 0 ≤ τ) :
    0 ≤ asmE3 c0 c1 c2 τ := by
  have a2 := a2_nonneg
  have aQ := aQ_nonneg
  have := mul_nonneg h1 (add_nonneg aQ (mul_nonneg sig4_nonneg hτ))
  have := mul_nonneg h2 (add_nonneg a2 hτ)
  unfold asmE3; linarith

/-! ## The `L²` bounds of the five parts on `Ω` -/

section parts

variable (hn : 1 ≤ n) (hN : 1 ≤ N)

lemma measurable_ev1 : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n ×
    MlpParam n mF 1) × (Fin n → ℝ) × (Fin n → ℝ) => mlpEval z.1.1 z.2.1) :=
  continuous_mlpEval_joint.measurable.comp
    (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (z.1.1, z.2.1))
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))

lemma measurable_ev2 : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n ×
    MlpParam n mF 1) × (Fin n → ℝ) × (Fin n → ℝ) => mlpEval z.1.1 z.2.2) :=
  continuous_mlpEval_joint.measurable.comp
    (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (z.1.1, z.2.2))
    ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))

include hn hN

/-- `‖X1‖₂ ≤ S·E1`. -/
theorem kX1_L2 (hmF : 1 ≤ mF) {d0 d1 d2 τ : ℝ} (h0 : 0 ≤ d0) (h1 : 0 ≤ d1) (h2 : 0 ≤ d2)
    (hτ : 0 ≤ τ)
    (hDiff : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => normSq (mlpEval A x - mlpEval A x'))
      (4 * (d0 + d1 * (1 - kappa (kappa (dotp x x'))) + d2 * (1 - dotp x x'))))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (kX1 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))
      (4 / (n : ℝ) * asmE1 mF d0 d1 d2 τ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hf := f1a_nonneg mF
  have a4 := one_sub_k4_nonneg
  have a2 := a2_nonneg
  have hb := tX_lin_L2 (mW := mW) hn hN (g0 := 2 * f1a mF * d0) (g1 := 2 * f1a mF * d1)
    (g2 := 2 * f1a mF * d2) (g3 := 0) (by positivity) le_rfl hτ
    (lin_nonneg (by positivity) (by positivity) (by positivity) le_rfl) hT
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * f1a mF * d1)] at hb
  have hXm : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) (x x' : Fin n → ℝ) =>
        cF p.2.2 (mlpEval p.1 x) (mlpEval p.1 x')) z.1 z.2.1 z.2.2) :=
    measurable_cF.comp (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (z.1.2.2, (mlpEval z.1.1 z.2.1, mlpEval z.1.1 z.2.2)))
      (((measurable_snd.comp measurable_snd).comp measurable_fst).prodMk
        (measurable_ev1.prodMk measurable_ev2))
  have key := lift_L2 (mW := mW) hn hN hXm hb (fun x x' hx hx' => by
    have hg := ((hDiff x x' hx hx').const_mul_nonneg hf).const_mul_nonneg
      (c := 2 / (n : ℝ)) (by positivity)
    have m1 : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        cF p.2.2 (mlpEval p.1 x) (mlpEval p.1 x')) :=
      hXm.comp (f := fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        (p, (x, x'))) (by fun_prop)
    refine (L2le.prod' m1.aestronglyMeasurable hg (Filter.Eventually.of_forall fun A =>
      (cF_L2 hn hmF (mlpEval A x) (mlpEval A x')).comp_snd)).congr_bound ?_
    unfold linB
    ring)
  refine (key.congr_fun fun ω => rfl).congr_bound ?_
  unfold asmE1
  ring

/-- `‖X2‖₂ ≤ S·E2`. -/
theorem kX2_L2 (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) {d0 d1 d2 δ2 τ : ℝ} (h0 : 0 ≤ d0) (h1 : 0 ≤ d1)
    (h2 : 0 ≤ d2) (hδ2 : 0 ≤ δ2) (hτ : 0 ≤ τ)
    (hDiff : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => normSq (mlpEval A x - mlpEval A x'))
      (4 * (d0 + d1 * (1 - kappa (kappa (dotp x x'))) + d2 * (1 - dotp x x'))))
    (hDlt : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => dlt (mlpEval A x) (mlpEval A x')) (2 * δ2))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (kX2 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))
      (4 / (n : ℝ) * asmE2 n mA mF d0 d1 d2 δ2 τ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA' : (0 : ℝ) < mA := by exact_mod_cast hmA
  have hf1 := f1b_nonneg mF
  have hf2 := f2_nonneg mF
  have hf3 := f3_nonneg mF
  have hf4 := f4_nonneg
  have a4 := one_sub_k4_nonneg
  have a2 := a2_nonneg
  have he4 := Real.sqrt_nonneg (eps4 n mA)
  set N0 : ℝ := (1 + 5 / (mA : ℝ)) * √(1 + 2 / (n : ℝ)) with hN0
  have hN00 : 0 ≤ N0 := by rw [hN0]; positivity
  have hb := tX_lin_L2 (mW := mW) hn hN
    (g0 := 2 * f1b mF * d0 + 2 * f2 mF * N0 + 2 * f3 mF * √(eps4 n mA) + f4 * δ2)
    (g1 := 2 * f1b mF * d1) (g2 := 2 * f1b mF * d2) (g3 := 0) (by positivity) le_rfl hτ
    (lin_nonneg (by positivity) (by positivity) (by positivity) le_rfl) hT
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * f1b mF * d1)] at hb
  have hXm : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) (x x' : Fin n → ℝ) =>
        rF p.2.2 (mlpEval p.1 x) (mlpEval p.1 x')) z.1 z.2.1 z.2.2) :=
    measurable_rF.comp (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (z.1.2.2, (mlpEval z.1.1 z.2.1, mlpEval z.1.1 z.2.2)))
      (((measurable_snd.comp measurable_snd).comp measurable_fst).prodMk
        (measurable_ev1.prodMk measurable_ev2))
  have key := lift_L2 (mW := mW) hn hN hXm hb (fun x x' hx hx' => by
    have ht := dotp_unit_mem hx hx'
    have hkt := kk_memIcc ht
    have u1 : 0 ≤ 1 - kappa (kappa (dotp x x')) := by linarith [hkt.2]
    have u2 : 0 ≤ 1 - dotp x x' := by linarith [ht.2]
    set δ1 : ℝ := d0 + d1 * (1 - kappa (kappa (dotp x x'))) + d2 * (1 - dotp x x') with hδ1d
    have hδ1 : 0 ≤ δ1 := by rw [hδ1d]; positivity
    have nS := agent_normSq_L2 hn hmA hx
    have nS' := agent_normSq_L2 hn hmA hx'
    have dS := agent_normSq_dev_L2 hn hmA hx
    have dS' := agent_normSq_dev_L2 hn hmA hx'
    have sSum := nS.add0 nS' (by positivity) (by positivity)
    have sDif : L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => |normSq (mlpEval A x) - normSq (mlpEval A x')|)
        (2 * √(eps4 n mA) + 2 * √(eps4 n mA)) := by
      have h0 := dS.add0 dS'.neg (by positivity) (by positivity)
      exact L2le.abs' (h0.congr_fun fun A => by ring)
    have hg : L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => 2 / (n : ℝ) *
          (f1b mF * normSq (mlpEval A x - mlpEval A x') +
          f2 mF * (normSq (mlpEval A x) + normSq (mlpEval A x')) +
          f3 mF * |normSq (mlpEval A x) - normSq (mlpEval A x')| +
          f4 * dlt (mlpEval A x) (mlpEval A x')))
        (2 / (n : ℝ) * (f1b mF * (4 * δ1) + f2 mF * (2 * N0 + 2 * N0) +
          f3 mF * (2 * √(eps4 n mA) + 2 * √(eps4 n mA)) + f4 * (2 * δ2))) := by
      have a1 := (hDiff x x' hx hx').const_mul_nonneg hf1
      have a2 := sSum.const_mul_nonneg hf2
      have a3 := sDif.const_mul_nonneg hf3
      have a4 := (hDlt x x' hx hx').const_mul_nonneg hf4
      have s12 := a1.add0 a2 (by positivity) (by positivity)
      have s123 := s12.add0 a3 (by positivity) (by positivity)
      have s1234 := s123.add0 a4 (by positivity) (by positivity)
      exact s1234.const_mul_nonneg (by positivity)
    have m1 : Measurable (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        rF p.2.2 (mlpEval p.1 x) (mlpEval p.1 x')) :=
      hXm.comp (f := fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
        (p, (x, x'))) (by fun_prop)
    refine (L2le.prod' m1.aestronglyMeasurable hg (Filter.Eventually.of_forall fun A =>
      (rF_L2 hn hmF (mlpEval A x) (mlpEval A x')).comp_snd)).congr_bound ?_
    rw [hδ1d]
    unfold linB
    ring)
  refine (key.congr_fun fun ω => rfl).congr_bound ?_
  unfold asmE2
  rw [← hN0]
  ring

/-- `‖X3‖₂ ≤ S·E3`. -/
theorem kX3_L2 {cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hcAm : Measurable (fun p : MlpParam n mA n × (Fin n → ℝ) × (Fin n → ℝ) =>
      cA p.1 p.2.1 p.2.2))
    {c0 c1 c2 τ : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (hτ : 0 ≤ τ)
    (hcL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n) (fun A : MlpParam n mA n => cA A x x')
        (2 * (c0 + c1 * (1 - kappa^[4] (dotp x x')) + c2 * (1 - dotp x x'))))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (kX3 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) cA)
      (4 / (n : ℝ) * asmE3 c0 c1 c2 τ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have a2 := a2_nonneg
  have aQ := aQ_nonneg
  have hb := tX_lin_L2 (mW := mW) hn hN (g0 := c0) (g1 := 0) (g2 := c2) (g3 := c1) h2 h1 hτ
    (lin_nonneg h0 le_rfl h2 h1) hT
  rw [abs_zero] at hb
  have hXm : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) (x x' : Fin n → ℝ) =>
        2 / (n : ℝ) * cA p.1 x x') z.1 z.2.1 z.2.2) :=
    (hcAm.comp (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) => (z.1.1, z.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).const_mul _
  have key := lift_L2 (mW := mW) hn hN hXm hb (fun x x' hx hx' => by
    have hg := ((hcL x x' hx hx').const_mul_nonneg (c := 2 / (n : ℝ)) (by positivity)).comp_fst
      (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1))
    refine hg.congr_bound ?_
    unfold linB
    ring)
  refine (key.congr_fun fun ω => rfl).congr_bound ?_
  unfold asmE3
  ring

/-- `‖X4‖₂ ≤ S·E4`. -/
theorem kX4_L2 {cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hcAm : Measurable (fun p : MlpParam n mA n × (Fin n → ℝ) × (Fin n → ℝ) =>
      cA p.1 p.2.1 p.2.2))
    {r0 r1 r1' r2 τ : ℝ} (h1 : 0 ≤ r1) (h1' : 0 ≤ r1') (h2 : 0 ≤ r2) (hτ : 0 ≤ τ)
    (hC : 0 ≤ r0 + r1 * (1 - kappa^[6] 0) - r1' * (1 - kappa^[4] 0) +
      r2 * (1 - kappa (kappa 0)))
    (hrL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
          2 * (1 - kappa^[4] (dotp x x')) - cA A x x')
        (2 * (r0 + r1 * (1 - kappa^[4] (dotp x x')) - r1' * (1 - kappa (kappa (dotp x x'))) +
          r2 * (1 - dotp x x'))))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (kX4 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) cA)
      (4 / (n : ℝ) * asmE4 r0 r1 r1' r2 τ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := tX_lin_L2 (mW := mW) hn hN (g0 := r0) (g1 := -r1') (g2 := r2) (g3 := r1) h2 h1 hτ
    (by linarith) hT
  rw [abs_neg, abs_of_nonneg h1'] at hb
  have hk4 : Measurable (kappa^[4]) := (continuous_kappa.iterate 4).measurable
  have hXm : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
      (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) (x x' : Fin n → ℝ) =>
        2 / (n : ℝ) * (phiD (kappa ∘ kappa) (mlpEval p.1 x) (mlpEval p.1 x') -
          2 * (1 - kappa^[4] (dotp x x')) - cA p.1 x x')) z.1 z.2.1 z.2.2) := by
    have m1 : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
        (Fin n → ℝ) × (Fin n → ℝ) =>
        phiD (kappa ∘ kappa) (mlpEval z.1.1 z.2.1) (mlpEval z.1.1 z.2.2)) :=
      Measurable.comp (g := fun q : (Fin n → ℝ) × (Fin n → ℝ) => phiD (kappa ∘ kappa) q.1 q.2)
        (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
          (Fin n → ℝ) × (Fin n → ℝ) => (mlpEval z.1.1 z.2.1, mlpEval z.1.1 z.2.2))
        (measurable_phiD_pair (continuous_kappa.comp continuous_kappa))
        (measurable_ev1.prodMk measurable_ev2)
    have m2 : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
        (Fin n → ℝ) × (Fin n → ℝ) => kappa^[4] (dotp z.2.1 z.2.2)) :=
      hk4.comp (continuous_dotp.measurable.comp measurable_snd)
    have m3 : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
        (Fin n → ℝ) × (Fin n → ℝ) => cA z.1.1 z.2.1 z.2.2) :=
      hcAm.comp (f := fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
        (Fin n → ℝ) × (Fin n → ℝ) => (z.1.1, z.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have m4 : Measurable (fun z : (MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) ×
        (Fin n → ℝ) × (Fin n → ℝ) =>
        2 / (n : ℝ) * (phiD (kappa ∘ kappa) (mlpEval z.1.1 z.2.1) (mlpEval z.1.1 z.2.2) -
          2 * (1 - kappa^[4] (dotp z.2.1 z.2.2)) - cA z.1.1 z.2.1 z.2.2)) :=
      ((m1.sub ((measurable_const.sub m2).const_mul 2)).sub m3).const_mul (2 / (n : ℝ))
    exact m4
  have key := lift_L2 (mW := mW) hn hN hXm hb (fun x x' hx hx' => by
    have hg := ((hrL x x' hx hx').const_mul_nonneg (c := 2 / (n : ℝ)) (by positivity)).comp_fst
      (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1))
    refine hg.congr_bound ?_
    unfold linB
    ring)
  refine (key.congr_fun fun ω => rfl).congr_bound ?_
  unfold asmE4
  ring

omit hn in
/-- `‖X5‖₂ ≤ S·pW`. -/
theorem kX5_L2 (hn0 : 1 ≤ n) {pW : ℝ}
    (hW5 : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        kappa^[4] (tX z) - kappa^[6] 0) pW) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (kX5 (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))
      (4 / (n : ℝ) * pW) := by
  have := lawU2_prob hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hφ : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      (ω.1, ω.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hmap : ((lawU2 N).prod (lawR N mW n mA mF)).map
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => (ω.1, ω.2.1)) =
      (lawU2 N).prod (mlpGauss N mW n) := by
    have h1 : (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => (ω.1, ω.2.1)) =
        Prod.map id Prod.fst := by
      funext ω; rfl
    rw [h1, ← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id]
    unfold lawR
    rw [Measure.map_fst_prod]
    simp
  have h := (hW5.neg.const_mul_nonneg (c := 4 / (n : ℝ)) (by positivity)).comp_map hφ hmap
  refine h.congr_fun fun ω => ?_
  unfold kX5 tO
  change 4 / (n : ℝ) * -(kappa^[4] (dotp (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2)) - kappa^[6] 0) = _
  ring

end parts

/-! ## The two orthogonality steps -/

/-- **Orthogonality (ii)**: `∫ X3·X5 = 0`. -/
theorem cross35 (hN : 1 ≤ N) {cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hcI : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      Integrable (fun A : MlpParam n mA n => cA A x x') (mlpGauss n mA n) ∧
        ∫ A, cA A x x' ∂mlpGauss n mA n = 0) (hn : 1 ≤ n)
    (hI : Integrable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      kX3 cA ω * kX5 ω) ((lawU2 N).prod (lawR N mW n mA mF))) :
    ∫ ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF, kX3 cA ω * kX5 ω
      ∂((lawU2 N).prod (lawR N mW n mA mF)) = 0 := by
  have := lawU2_prob hN
  refine integral_prod_zero hI fun uu h1 => ?_
  refine integral_prod_zero (μ := mlpGauss N mW n)
    (ν := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) h1 fun W _ => ?_
  have h0 : ∫ A : MlpParam n mA n, 2 / (n : ℝ) * cA A (xW W uu.1) (xW W uu.2)
      ∂mlpGauss n mA n = 0 := by
    rw [integral_const_mul, (hcI _ _ (normSq_xW hn _ _) (normSq_xW hn _ _)).2, mul_zero]
  exact integral_fst_mul_zero (μ := mlpGauss n mA n)
    (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1))
    (g := fun A : MlpParam n mA n => 2 / (n : ℝ) * cA A (xW W uu.1) (xW W uu.2)) h0
    (4 / (n : ℝ) * (kappa^[6] 0 - kappa^[4] (dotp (xW W uu.1) (xW W uu.2))))

/-- **Orthogonality (i)**: `∫ X1·(X2 + X4 + (X3 + X5)) = 0`. -/
theorem cross1 (hN : 1 ≤ N) (hmF : 1 ≤ mF)
    (cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hI : Integrable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      kX1 ω * (kX2 ω + kX4 cA ω + (kX3 cA ω + kX5 ω))) ((lawU2 N).prod (lawR N mW n mA mF))) :
    ∫ ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF,
      kX1 ω * (kX2 ω + kX4 cA ω + (kX3 cA ω + kX5 ω))
      ∂((lawU2 N).prod (lawR N mW n mA mF)) = 0 := by
  have := lawU2_prob hN
  refine integral_prod_zero hI fun uu h1 => ?_
  refine integral_prod_zero (μ := mlpGauss N mW n)
    (ν := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) h1 fun W h2 => ?_
  refine integral_prod_zero (μ := mlpGauss n mA n)
    (ν := (mlpGauss n mA n).prod (mlpGauss n mF 1)) h2 fun A h3 => ?_
  refine integral_prod_zero (μ := mlpGauss n mA n) (ν := mlpGauss n mF 1) h3 fun A' h4 => ?_
  refine integral_prod_zero (μ := gaussMat mF n (2 / (n : ℝ)))
    (ν := (gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) h4
    fun F₁ _ => ?_
  exact integral_mul_const_zero
    (g := fun θ : Matrix (Fin mF) (Fin mF) ℝ × Matrix (Fin 1) (Fin mF) ℝ =>
      cF (F₁, θ) (mlpEval A (xW W uu.1)) (mlpEval A (xW W uu.2)))
    (cF_integral_tail hmF F₁ _ _)
    (rF0 F₁ (mlpEval A (xW W uu.1)) (mlpEval A (xW W uu.2)) +
      2 / (n : ℝ) * (phiD (kappa ∘ kappa) (mlpEval A (xW W uu.1)) (mlpEval A (xW W uu.2)) -
        2 * (1 - kappa^[4] (dotp (xW W uu.1) (xW W uu.2))) -
        cA A (xW W uu.1) (xW W uu.2)) +
      (2 / (n : ℝ) * cA A (xW W uu.1) (xW W uu.2) +
        4 / (n : ℝ) * (kappa^[6] 0 - kappa^[4] (dotp (xW W uu.1) (xW W uu.2)))))

/-! ## The assembly -/

/-- **The distance kernel under `(u, u′) ⊗ (W, A, A′, F)`, with the two orthogonality steps.** -/
theorem kernDist143_of (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    {cA : MlpParam n mA n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hcAm : Measurable (fun p : MlpParam n mA n × (Fin n → ℝ) × (Fin n → ℝ) =>
      cA p.1 p.2.1 p.2.2))
    {c0 c1 c2 r0 r1 r1' r2 τ pW : ℝ}
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hr1 : 0 ≤ r1) (hr1' : 0 ≤ r1')
    (hr2 : 0 ≤ r2) (hτ : 0 ≤ τ)
    (hrC : 0 ≤ r0 + r1 * (1 - kappa^[6] 0) - r1' * (1 - kappa^[4] 0) +
      r2 * (1 - kappa (kappa 0)))
    (hcI : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      Integrable (fun A : MlpParam n mA n => cA A x x') (mlpGauss n mA n) ∧
        ∫ A, cA A x x' ∂mlpGauss n mA n = 0)
    (hcL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n) (fun A : MlpParam n mA n => cA A x x')
        (2 * (c0 + c1 * (1 - kappa^[4] (dotp x x')) + c2 * (1 - dotp x x'))))
    (hrL : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le (mlpGauss n mA n)
        (fun A : MlpParam n mA n => phiD (kappa ∘ kappa) (mlpEval A x) (mlpEval A x') -
          2 * (1 - kappa^[4] (dotp x x')) - cA A x x')
        (2 * (r0 + r1 * (1 - kappa^[4] (dotp x x')) - r1' * (1 - kappa (kappa (dotp x x'))) +
          r2 * (1 - dotp x x'))))
    {d0 d1 d2 δ2 : ℝ} (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hδ2 : 0 ≤ δ2)
    (hDiff : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => normSq (mlpEval A x - mlpEval A x'))
      (4 * (d0 + d1 * (1 - kappa (kappa (dotp x x'))) + d2 * (1 - dotp x x'))))
    (hDlt : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 → L2le (mlpGauss n mA n)
      (fun A : MlpParam n mA n => dlt (mlpEval A x) (mlpEval A x')) (2 * δ2))
    (hT : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n => tX z - kappa (kappa 0)) τ)
    (hW5 : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        kappa^[4] (tX z) - kappa^[6] 0) pW) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * √(asmE1 mF d0 d1 d2 τ ^ 2 +
        (asmE2 n mA mF d0 d1 d2 δ2 τ + asmE4 r0 r1 r1' r2 τ +
          √(asmE3 c0 c1 c2 τ ^ 2 + pW ^ 2)) ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS0 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
  have g1 := kX1_L2 (mW := mW) (mA := mA) hn hN hmF hd0 hd1 hd2 hτ hDiff hT
  have g2 := kX2_L2 (mW := mW) hn hN hmA hmF hd0 hd1 hd2 hδ2 hτ hDiff hDlt hT
  have g3 := kX3_L2 (mW := mW) (mF := mF) hn hN hcAm hc0 hc1 hc2 hτ hcL hT
  have g4 := kX4_L2 (mW := mW) (mF := mF) hn hN hcAm hr1 hr1' hr2 hτ hrC hrL hT
  have g5 := kX5_L2 (mA := mA) (mF := mF) hN hn hW5
  have e2 := asmE2_nonneg n mA mF hd0 hd1 hd2 hδ2 hτ
  have e4 : 0 ≤ asmE4 r0 r1 r1' r2 τ := by
    have := sig4_nonneg
    have : 0 ≤ (r1 * sig4 + r1' + r2) * τ := by positivity
    unfold asmE4; linarith
  have g35 := L2le.add_orth g3 g5 (cross35 hN hcI hn)
  have gY := (g2.add0 g4 (by positivity) (by positivity)).add0 g35 (by positivity)
    (Real.sqrt_nonneg _)
  have gAll := L2le.add_orth g1 gY (cross1 hN hmF cA)
  refine (gAll.congr_fun fun ω => (kD_split cA ω).symm).congr_bound ?_
  have q1 : √((4 / (n : ℝ) * asmE3 c0 c1 c2 τ) ^ 2 + (4 / (n : ℝ) * pW) ^ 2) =
      4 / (n : ℝ) * √(asmE3 c0 c1 c2 τ ^ 2 + pW ^ 2) := by
    have e : (4 / (n : ℝ) * asmE3 c0 c1 c2 τ) ^ 2 + (4 / (n : ℝ) * pW) ^ 2 =
        (4 / (n : ℝ)) ^ 2 * (asmE3 c0 c1 c2 τ ^ 2 + pW ^ 2) := by ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS0]
  rw [q1]
  set R : ℝ := √(asmE3 c0 c1 c2 τ ^ 2 + pW ^ 2) with hR
  have e : (4 / (n : ℝ) * asmE1 mF d0 d1 d2 τ) ^ 2 +
      (4 / (n : ℝ) * asmE2 n mA mF d0 d1 d2 δ2 τ + 4 / (n : ℝ) * asmE4 r0 r1 r1' r2 τ +
        4 / (n : ℝ) * R) ^ 2 =
      (4 / (n : ℝ)) ^ 2 * (asmE1 mF d0 d1 d2 τ ^ 2 +
        (asmE2 n mA mF d0 d1 d2 δ2 τ + asmE4 r0 r1 r1' r2 τ + R) ^ 2) := by ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS0]

end General

/-! ## The Focus widths -/

/-- `0 ≤ rR0 + rR1·(1 − κ^{∘6}(0)) − rR1'·(1 − κ^{∘4}(0)) + rR2·(1 − κ(κ(0)))`. -/
lemma rR_ref_nonneg (n m : ℕ) :
    0 ≤ rR0 n m + rR1 n * (1 - kappa^[6] 0) - rR1' n * (1 - kappa^[4] 0) +
      rR2 n m * (1 - kappa (kappa 0)) := by
  have h0 := rR0_nonneg n m
  have h2 := mul_nonneg (rR2_nonneg n m) a2_nonneg
  have h6 : 222757 / 1000000 ≤ 1 - kappa^[6] 0 := by have := kappa6_zero_le''; linarith
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 := one_sub_k4_nonneg
  have hc := AgS.cg2_le
  have hc0 := AgS.cgS_nonneg (kGood_kappa.comp_kappa)
  have hs : (0 : ℝ) ≤ 1 / √(n : ℝ) := by positivity
  have e : rR1 n * (1 - kappa^[6] 0) - rR1' n * (1 - kappa^[4] 0) =
      1 / √(n : ℝ) * ((1 - kappa^[6] 0) - AgS.cgS (kappa ∘ kappa) * (1 - kappa^[4] 0)) := by
    unfold rR1 rR1' sA1'; ring
  have h1 : 0 ≤ (1 - kappa^[6] 0) - AgS.cgS (kappa ∘ kappa) * (1 - kappa^[4] 0) := by
    have : AgS.cgS (kappa ∘ kappa) * (1 - kappa^[4] 0) ≤ 1 / 2 * (319057 / 1000000) :=
      mul_le_mul hc h4 h40 (by norm_num)
    linarith
  have := mul_nonneg hs h1
  linarith

/-- **`kernDist143_of` at the widths of the Focus**, `n ≥ 4096`, with `cA = cAg`; the two facts
of the World network stay hypotheses. -/
theorem kernDist143_focus {n : ℕ} (hn : 4096 ≤ n) {τ pW : ℝ} (hτ : 0 ≤ τ)
    (hT : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) τ)
    (hW5 : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        kappa^[4] (tX z) - kappa^[6] 0) pW) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * √(asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) τ ^ 2 +
        (asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (cAdlt n (mA n)) τ +
          asmE4 (rR0 n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) τ +
          √(asmE3 (cC0 n (mA n)) (cC1 n) (cC2 n (mA n)) τ ^ 2 + pW ^ 2)) ^ 2)) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  exact kernDist143_of (cA := cAg) hn1 hN hmA hmF measurable_cAg
    (cC0_nonneg n (mA n)) (cC1_nonneg n) (cC2_nonneg n (mA n)) (rR1_nonneg n) (rR1'_nonneg n)
    (rR2_nonneg n (mA n)) hτ (rR_ref_nonneg n (mA n))
    (fun x x' hx hx' => cAg_integral hn1 hmA hx hx')
    (fun x x' hx hx' => cAg_L2 hn1 hmA hx hx')
    (fun x x' hx hx' => agent_rem_L2 hn1 hmA hx hx')
    (dA0_nonneg n (mA n)) (dA1_nonneg n (mA n)) (dA2_nonneg n (mA n)) (cAdlt_nonneg n (mA n))
    (fun x x' hx hx' => agent_diff_L2_of reluEDStmt reluPhiStmt hn1 hmA hx hx')
    (fun x x' hx hx' => agent_dlt_L2_of reluSqStmt reluDltStmt linDltStmt hn1 hmA hx hx')
    hT hW5

end BstLean.Part143

open BstLean.Part143 in
#print axioms L2le.add_orth
open BstLean.Part143 in
#print axioms chord_pW
open BstLean.Part143 in
#print axioms kD_split
open BstLean.Part143 in
#print axioms kernDist143_of
open BstLean.Part143 in
#print axioms kernDist143_focus
