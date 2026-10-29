import BstLean.Part139Spread

/-!
# Part 142, item 3: the realized spread through the DISTANCE kernel

Role: `delegations/statements/p142-spec.md`, item 3 (`spread142`). New in this part (not in the
paper sources): the second moment of the realized spread is bounded by the `L²` error of ONE
kernel, the distance kernel `kD(u, u′) = (k(u, u) + k(u′, u′))/2 − k(u, u′)
  = (2/m_F)·|z(u) − z(u′)|²/2`, `z = zU` the last hidden vector of `F` at `A(x(u))`.

* `kD`, `measurable_kD`, `kD_eq` (in terms of `kern`), `kD_zU` (in terms of `zU`).
* `covV_frob_gen`: `Σ_{ij} Cov_{ij}² ≤ E(⟨z, z′⟩ − f(u) − g(u′))²` for bounded measurable `f, g`.
* `covV_frob_dist`: `Σ_{ij} Cov_{ij}² ≤ E(|z − z′|²/2 − c)²`; `covV_trace_dist`:
  `tr Cov = E|z − z′|²/2`.
* `cond_sq_dist`: for fixed `(W, A, F₁, F₂)`: `E_{F₃}(sd² − c)² ≤ 3·E_{u,u′}(kD − c)²`.
* **`spread_L2_dist`**: from `‖kD − c‖₂ ≤ e`: `E_{W,A,F}(sd² − c)² ≤ 3e²`.
* **`spreadLow_dist`**: Chebyshev: `Pr(sd² < θ·c) ≤ 3e²/((1 − θ)c)²`, `c > 0`, `θ < 1`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139

/-! ## The covariance of a bounded vector function and the distance -/

section cov

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ι : Type} [Fintype ι] (z : Ω → ι → ℝ)

/-- `Σ_{ij} Cov_{ij}² ≤ E(⟨z(u), z(u′)⟩ − f(u) − g(u′))²` for bounded measurable `f`, `g`. -/
theorem covV_frob_gen (hz : ∀ i, Measurable fun ω => z ω i) (hb : ∃ B : ℝ, ∀ ω i, |z ω i| ≤ B)
    {f g : Ω → ℝ} (hf : BM f) (hg : BM g) :
    ∑ i, ∑ j, covV μ z i j ^ 2 ≤
      ∫ p : Ω × Ω, (∑ i, z p.1 i * z p.2 i - f p.1 - g p.2) ^ 2 ∂(μ.prod μ) := by
  have hzB : ∀ i, BM (fun ω => z ω i) := fun i =>
    ⟨hz i, hb.imp fun _ hB ω => hB ω i⟩
  let a : ι → ℝ := meanV μ z
  let ζ : Ω → ι → ℝ := fun ω i => z ω i - a i
  have hζB : ∀ i, BM (fun ω => ζ ω i) := fun i => (hzB i).sub (BM.const _)
  have hζ0 : ∀ i, ∫ ω, ζ ω i ∂μ = 0 := by
    intro i
    simp only [ζ]
    rw [integral_sub ((hzB i).integrable μ) (integrable_const _), integral_const]
    simp [a, meanV]
  let r : Ω → ℝ := fun ω => ∑ i, ζ ω i * a i
  have hrB : BM r := BM.sum _ fun i _ => (hζB i).mul (BM.const _)
  let c0 : ℝ := ∑ i, a i * a i
  let F1 : Ω → ℝ := fun ω => r ω - f ω + c0
  let G1 : Ω → ℝ := fun ω => r ω - g ω
  have hF1 : BM F1 := (hrB.sub hf).add (BM.const _)
  have hG1 : BM G1 := hrB.sub hg
  let P : Ω × Ω → ℝ := fun p => ∑ i, ζ p.1 i * ζ p.2 i
  let R : Ω × Ω → ℝ := fun p => F1 p.1 + G1 p.2
  have hK : ∀ p : Ω × Ω, ∑ i, z p.1 i * z p.2 i - f p.1 - g p.2 = P p + R p := by
    intro p
    have e : ∑ i, z p.1 i * z p.2 i =
        ∑ i, ζ p.1 i * ζ p.2 i + ∑ i, ζ p.1 i * a i + ∑ i, ζ p.2 i * a i + ∑ i, a i * a i := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [ζ]; ring
    simp only [P, R, F1, G1, r, c0]
    linarith
  have hPB : BM P := BM.sum _ fun i _ => (hζB i).fst.mul (hζB i).snd
  have hRB : BM R := hF1.fst.add hG1.snd
  have hPR : ∫ p, P p * R p ∂(μ.prod μ) = 0 := by
    have e : (fun p => P p * R p) = fun p : Ω × Ω =>
        ∑ i, ((ζ p.1 i * F1 p.1) * ζ p.2 i + ζ p.1 i * (ζ p.2 i * G1 p.2)) := by
      funext p
      simp only [P, R]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hi1 : ∀ i, Integrable (fun p : Ω × Ω => (ζ p.1 i * F1 p.1) * ζ p.2 i)
        (μ.prod μ) := fun i =>
      (((hζB i).mul hF1).fst.mul (hζB i).snd).integrable _
    have hi2 : ∀ i, Integrable (fun p : Ω × Ω => ζ p.1 i * (ζ p.2 i * G1 p.2))
        (μ.prod μ) := fun i =>
      ((hζB i).fst.mul ((hζB i).mul hG1).snd).integrable _
    have hi12 : ∀ i, Integrable (fun p : Ω × Ω =>
        (ζ p.1 i * F1 p.1) * ζ p.2 i + ζ p.1 i * (ζ p.2 i * G1 p.2)) (μ.prod μ) :=
      fun i => (hi1 i).add (hi2 i)
    rw [e, integral_finsetSum _ fun i _ => hi12 i]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_add (hi1 i) (hi2 i),
      integral_prod_mul (fun ω => ζ ω i * F1 ω) (fun ω => ζ ω i),
      integral_prod_mul (fun ω => ζ ω i) (fun ω => ζ ω i * G1 ω), hζ0 i]
    simp
  have hPP : ∫ p, P p ^ 2 ∂(μ.prod μ) = ∑ i, ∑ j, covV μ z i j ^ 2 := by
    have e : (fun p => P p ^ 2) = fun p : Ω × Ω =>
        ∑ i, ∑ j, (ζ p.1 i * ζ p.1 j) * (ζ p.2 i * ζ p.2 j) := by
      funext p
      simp only [P]
      rw [pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hi : ∀ i j, Integrable (fun p : Ω × Ω => (ζ p.1 i * ζ p.1 j) * (ζ p.2 i * ζ p.2 j))
        (μ.prod μ) := fun i j =>
      (((hζB i).mul (hζB j)).fst.mul ((hζB i).mul (hζB j)).snd).integrable _
    rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_prod_mul (fun ω => ζ ω i * ζ ω j) (fun ω => ζ ω i * ζ ω j), pow_two]
    rfl
  rw [← hPP]
  have e2 : ∫ p, P p ^ 2 ∂(μ.prod μ) = ∫ p, (P p ^ 2 + 2 * (P p * R p)) ∂(μ.prod μ) := by
    rw [integral_add (hPB.sq.integrable _) (((hPB.mul hRB).integrable _).const_mul 2),
      integral_const_mul, hPR]
    simp
  rw [e2]
  refine integral_mono ((hPB.sq.integrable _).add (((hPB.mul hRB).integrable _).const_mul 2))
    ?_ fun p => ?_
  · have hKB : BM (fun p : Ω × Ω => (P p + R p) ^ 2) := (hPB.add hRB).sq
    have e3 : (fun p : Ω × Ω => (∑ i, z p.1 i * z p.2 i - f p.1 - g p.2) ^ 2) =
        fun p => (P p + R p) ^ 2 := by
      funext p; rw [hK p]
    rw [e3]
    exact hKB.integrable _
  · simp only
    rw [hK p]
    nlinarith [sq_nonneg (R p)]

/-- **The Frobenius norm of the covariance and the distance**:
`Σ_{ij} Cov_{ij}² ≤ E(|z(u) − z(u′)|²/2 − c)²` for every constant `c`. -/
theorem covV_frob_dist (hz : ∀ i, Measurable fun ω => z ω i)
    (hb : ∃ B : ℝ, ∀ ω i, |z ω i| ≤ B) (c : ℝ) :
    ∑ i, ∑ j, covV μ z i j ^ 2 ≤
      ∫ p : Ω × Ω, ((∑ i, (z p.1 i - z p.2 i) ^ 2) / 2 - c) ^ 2 ∂(μ.prod μ) := by
  have hzB : ∀ i, BM (fun ω => z ω i) := fun i =>
    ⟨hz i, hb.imp fun _ hB ω => hB ω i⟩
  have hs : BM (fun ω => (∑ i, z ω i ^ 2) / 2) := by
    have := (BM.sum Finset.univ fun i _ => (hzB i).sq).mul (BM.const (α := Ω) (1 / 2))
    simpa [div_eq_mul_inv] using this
  have h := covV_frob_gen μ z hz hb hs (hs.sub (BM.const c))
  refine h.trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have e : ∑ i, (z p.1 i - z p.2 i) ^ 2 =
      ∑ i, z p.1 i ^ 2 + ∑ i, z p.2 i ^ 2 - 2 * ∑ i, z p.1 i * z p.2 i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only
  rw [e]
  ring

/-- `tr Cov = E|z(u) − z(u′)|²/2`. -/
theorem covV_trace_dist (hz : ∀ i, Measurable fun ω => z ω i)
    (hb : ∃ B : ℝ, ∀ ω i, |z ω i| ≤ B) :
    ∑ i, covV μ z i i = ∫ p : Ω × Ω, (∑ i, (z p.1 i - z p.2 i) ^ 2) / 2 ∂(μ.prod μ) := by
  have hzB : ∀ i, BM (fun ω => z ω i) := fun i =>
    ⟨hz i, hb.imp fun _ hB ω => hB ω i⟩
  have hsq : BM (fun ω => ∑ i, z ω i ^ 2) := BM.sum _ fun i _ => (hzB i).sq
  have hdot : BM (fun p : Ω × Ω => ∑ i, z p.1 i * z p.2 i) :=
    BM.sum _ fun i _ => (hzB i).fst.mul (hzB i).snd
  rw [covV_trace μ z hz hb]
  have e : (fun p : Ω × Ω => (∑ i, (z p.1 i - z p.2 i) ^ 2) / 2) = fun p =>
      ((∑ i, z p.1 i ^ 2) / 2 + (∑ i, z p.2 i ^ 2) / 2) - ∑ i, z p.1 i * z p.2 i := by
    funext p
    have e : ∑ i, (z p.1 i - z p.2 i) ^ 2 =
        ∑ i, z p.1 i ^ 2 + ∑ i, z p.2 i ^ 2 - 2 * ∑ i, z p.1 i * z p.2 i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]; ring
  have i1 : Integrable (fun p : Ω × Ω => (∑ i, z p.1 i ^ 2) / 2) (μ.prod μ) :=
    (hsq.fst.integrable _).div_const 2
  have i2 : Integrable (fun p : Ω × Ω => (∑ i, z p.2 i ^ 2) / 2) (μ.prod μ) :=
    (hsq.snd.integrable _).div_const 2
  have a1 : ∫ p : Ω × Ω, ((∑ i, z p.1 i ^ 2) / 2 + (∑ i, z p.2 i ^ 2) / 2) -
      ∑ i, z p.1 i * z p.2 i ∂(μ.prod μ) =
      ∫ p : Ω × Ω, ((∑ i, z p.1 i ^ 2) / 2 + (∑ i, z p.2 i ^ 2) / 2) ∂(μ.prod μ) -
        ∫ p : Ω × Ω, ∑ i, z p.1 i * z p.2 i ∂(μ.prod μ) :=
    integral_sub (i1.add i2) (hdot.integrable _)
  have a2 : ∫ p : Ω × Ω, ((∑ i, z p.1 i ^ 2) / 2 + (∑ i, z p.2 i ^ 2) / 2) ∂(μ.prod μ) =
      ∫ p : Ω × Ω, (∑ i, z p.1 i ^ 2) / 2 ∂(μ.prod μ) +
        ∫ p : Ω × Ω, (∑ i, z p.2 i ^ 2) / 2 ∂(μ.prod μ) := integral_add i1 i2
  have a3 : ∫ p : Ω × Ω, (∑ i, z p.1 i ^ 2) / 2 ∂(μ.prod μ) =
      (∫ ω, ∑ i, z ω i ^ 2 ∂μ) / 2 := by
    rw [integral_div, integral_fun_fst (μ := μ) (ν := μ) (f := fun ω => ∑ i, z ω i ^ 2)]
    simp
  have a4 : ∫ p : Ω × Ω, (∑ i, z p.2 i ^ 2) / 2 ∂(μ.prod μ) =
      (∫ ω, ∑ i, z ω i ^ 2 ∂μ) / 2 := by
    rw [integral_div, integral_fun_snd (μ := μ) (ν := μ) (f := fun ω => ∑ i, z ω i ^ 2)]
    simp
  rw [e, a1, a2, a3, a4]
  ring

end cov

/-! ## The distance kernel -/

section general

variable {N mW n mA mF : ℕ}

/-- **The distance kernel** `kD = (k(u, u) + k(u′, u′))/2 − k(u, u′)` (the same Agent network at
both inputs). -/
noncomputable def kD (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) : ℝ :=
  (kgen false false true ω + kgen false false true ((ω.1.2, ω.1.1), ω.2)) / 2 -
    kgen false false false ω

lemma measurable_kD :
    Measurable (kD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF)) := by
  have hsw : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      (((ω.1.2, ω.1.1), ω.2) : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF)) := by
    fun_prop
  unfold kD
  exact (((measurable_kgen false false true).add
    ((measurable_kgen false false true).comp hsw)).div_const 2).sub
    (measurable_kgen false false false)

/-- The distance kernel in terms of `kern`: with `x = x(u)`, `x′ = x(u′)`:
`kD = (k(x, x) + k(x′, x′))/2 − k(x, x′)`. -/
lemma kD_eq (ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) :
    kD ω = (kern ω.2.2.2.2 ω.2.2.1 ω.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.1) +
        kern ω.2.2.2.2 ω.2.2.1 ω.2.2.1 (xW ω.2.1 ω.1.2) (xW ω.2.1 ω.1.2)) / 2 -
      kern ω.2.2.2.2 ω.2.2.1 ω.2.2.1 (xW ω.2.1 ω.1.1) (xW ω.2.1 ω.1.2) := rfl

/-- The distance kernel in terms of the last hidden vector `z = zU` of `F`:
`kD = (2/m_F)·|z(u) − z(u′)|²/2`. -/
lemma kD_zU (uu : (Fin N → ℝ) × (Fin N → ℝ)) (r : Rest N mW n mA mF) :
    kD (uu, r) = 2 / (mF : ℝ) *
      ((∑ i, (zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.1 i -
        zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.2 i) ^ 2) / 2) := by
  have e1 : kgen false false true (uu, r) =
      2 / (mF : ℝ) * ∑ i, zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.1 i *
        zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.1 i := rfl
  have e2 : kgen false false true (((uu.2, uu.1), r) :
      ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF) =
      2 / (mF : ℝ) * ∑ i, zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.2 i *
        zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.2 i := rfl
  have e3 : kgen false false false (uu, r) =
      2 / (mF : ℝ) * ∑ i, zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.1 i *
        zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 uu.2 i := rfl
  unfold kD
  simp only
  rw [e1, e2, e3]
  set z := zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 with hz
  have e : ∑ i, (z uu.1 i - z uu.2 i) ^ 2 =
      ∑ i, z uu.1 i * z uu.1 i + ∑ i, z uu.2 i * z uu.2 i - 2 * ∑ i, z uu.1 i * z uu.2 i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

/-- The mean over `(u, u′)` of `(kD − c)²`. -/
noncomputable def QD (c : ℝ) (r : Rest N mW n mA mF) : ℝ :=
  ∫ uu, (kD (uu, r) - c) ^ 2 ∂lawU2 N

lemma QD_nonneg (c : ℝ) (r : Rest N mW n mA mF) : 0 ≤ QD c r :=
  integral_nonneg fun _ => sq_nonneg _

/-- **The second moment of the realized spread over the last matrix of `F`, distance form.** For
fixed `(W, A, F₁, F₂)` and a constant `c`: `E_{F₃}(sd² − c)² ≤ 3·E_{u,u′}(kD − c)²`. -/
lemma cond_sq_dist (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) (r : Rest N mW n mA mF) (c : ℝ) :
    Integrable (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
      (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2) (gaussMat 1 mF (2 / (mF : ℝ))) ∧
    ∫ F₃, (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2 ∂gaussMat 1 mF (2 / (mF : ℝ)) ≤
      3 * QD c r := by
  have := uniformSphere_isProbability N hN
  have hm : (0 : ℝ) < mF := by exact_mod_cast hmF
  set α : ℝ := 2 / (mF : ℝ) with hα
  have hα0 : 0 < α := by positivity
  set z := zU r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 with hz
  have hzm : ∀ i, Measurable fun u => z u i := zU_meas _ _ _ _
  have hzb : ∃ B : ℝ, ∀ u i, |z u i| ≤ B := zU_bdd hn _ _ _ _
  have hzB : ∀ i, BM (fun u => z u i) := fun i => ⟨hzm i, hzb.imp fun _ hB u => hB u i⟩
  -- the distance, bounded and measurable
  have hdB : BM (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (∑ i, (z p.1 i - z p.2 i) ^ 2) / 2) := by
    have h1 : BM (fun p : (Fin N → ℝ) × (Fin N → ℝ) => ∑ i, (z p.1 i - z p.2 i) ^ 2) :=
      BM.sum _ fun i _ => ((hzB i).fst.sub (hzB i).snd).sq
    have := h1.mul (BM.const (α := (Fin N → ℝ) × (Fin N → ℝ)) (1 / 2))
    simpa [div_eq_mul_inv] using this
  have hkD : ∀ uu : (Fin N → ℝ) × (Fin N → ℝ),
      kD (uu, r) = α * ((∑ i, (z uu.1 i - z uu.2 i) ^ 2) / 2) := fun uu => kD_zU uu r
  have hkB : BM (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => kD (uu, r) - c) := by
    have := ((BM.const (α := (Fin N → ℝ) × (Fin N → ℝ)) α).mul hdB).sub (BM.const c)
    simpa [hkD] using this
  -- the trace
  have htr : α * (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1).trace - c =
      ∫ uu, (kD (uu, r) - c) ∂lawU2 N := by
    have e1 : (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1).trace =
        ∑ i, covV (uniformSphere N) z i i := by
      simp only [Matrix.trace, Matrix.diag, covMat_eq, hz]
    rw [e1, covV_trace_dist (uniformSphere N) z hzm hzb]
    have hpr : IsProbabilityMeasure (lawU2 N) := lawU2_prob hN
    have iD : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => kD (uu, r)) (lawU2 N) := by
      have := (hkB.add (BM.const c)).integrable (lawU2 N)
      simpa using this
    rw [integral_sub iD (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    simp_rw [hkD]
    rw [integral_const_mul]
    rfl
  -- the Frobenius norm
  have hfr : α ^ 2 * ∑ i, ∑ j, covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 i j ^ 2 ≤ QD c r := by
    have h := covV_frob_dist (uniformSphere N) z hzm hzb (c / α)
    simp_rw [covMat_eq]
    have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg α)
    refine h2.trans (le_of_eq ?_)
    unfold QD lawU2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun uu => ?_)
    simp only
    rw [hkD]
    field_simp
  -- Jensen
  have hJ : (α * (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1).trace - c) ^ 2 ≤ QD c r := by
    have hpr : IsProbabilityMeasure (lawU2 N) := lawU2_prob hN
    rw [htr]
    exact sq_integral_le (hkB.sq.integrable (lawU2 N))
  have e : (fun F₃ : Matrix (Fin 1) (Fin mF) ℝ =>
      (sdn r.1 r.2.1 (r.2.2.2.1, r.2.2.2.2.1, F₃) ^ 2 - c) ^ 2) =
      fun F₃ => (rowOf 0 F₃ ⬝ᵥ covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1 *ᵥ rowOf 0 F₃ - c) ^ 2 := by
    funext F₃
    rw [sdn_last hn hN, Real.sq_sqrt (covMat_nonneg hn hN _ _ _ _ _)]
  obtain ⟨hi, he⟩ := gaussRow_qform_sq α hα0.le
    (covMat r.1 r.2.1 r.2.2.2.1 r.2.2.2.2.1) (covMat_symm _ _ _ _) c
  rw [e]
  refine ⟨hi, ?_⟩
  rw [he]
  nlinarith

/-! ## The mean over the networks -/

/-- **The second moment of the realized spread around `c`, distance form.** If
`‖kD − c‖₂ ≤ e` under `(u, u′) ⊗ (W, A, A′, F)`, then `E(sd² − c)² ≤ 3e²`. -/
theorem spread_L2_dist (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {c e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e) :
    ∫⁻ r : Rest N mW n mA mF,
        ENNReal.ofReal ((sdn r.1 r.2.1 r.2.2.2 ^ 2 - c) ^ 2) ∂lawR N mW n mA mF ≤
      ENNReal.ofReal (3 * e ^ 2) := by
  have := lawU2_prob hN
  set f : Rest N mW n mA mF → ℝ≥0∞ :=
    fun r => ENNReal.ofReal ((sdn r.1 r.2.1 r.2.2.2 ^ 2 - c) ^ 2) with hf
  set Rr : Rest N mW n mA mF → ℝ := fun r => 3 * QD c r with hRr
  set g : Rest N mW n mA mF → ℝ≥0∞ := fun r => ENNReal.ofReal (Rr r) with hg
  have mf : Measurable f :=
    ENNReal.measurable_ofReal.comp ((((measurable_sdn_R hN).pow_const 2).sub
      measurable_const).pow_const 2)
  have mQ : Measurable (QD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) c) :=
    ((measurable_kD.sub measurable_const).pow_const 2).stronglyMeasurable.integral_prod_left'.measurable
  have mRr : Measurable Rr := mQ.const_mul 3
  have mg : Measurable g := ENNReal.measurable_ofReal.comp mRr
  have h5 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ)
      (F₂ : Matrix (Fin mF) (Fin mF) ℝ),
      ∫⁻ F₃, f (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) ≤
        ∫⁻ F₃, g (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) := by
    intro W A A' F₁ F₂
    have hconst : ∀ F₃ : Matrix (Fin 1) (Fin mF) ℝ,
        g (W, A, A', F₁, F₂, F₃) = g (W, A, A', F₁, F₂, 0) := fun _ => rfl
    simp_rw [hconst]
    rw [lintegral_const, measure_univ, mul_one]
    obtain ⟨hi, hle⟩ := cond_sq_dist hn hN hmF
      ((W, A, A', F₁, F₂, 0) : Rest N mW n mA mF) c
    have e : ∫⁻ F₃, f (W, A, A', F₁, F₂, F₃) ∂gaussMat 1 mF (2 / (mF : ℝ)) =
        ENNReal.ofReal (∫ F₃, (sdn W A (F₁, F₂, F₃) ^ 2 - c) ^ 2
          ∂gaussMat 1 mF (2 / (mF : ℝ))) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    rw [e]
    exact ENNReal.ofReal_le_ofReal hle
  have h4 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n) (F₁ : Matrix (Fin mF) (Fin n) ℝ),
      ∫⁻ y, f (W, A, A', F₁, y)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) ≤
        ∫⁻ y, g (W, A, A', F₁, y)
          ∂((gaussMat mF mF (2 / (mF : ℝ))).prod (gaussMat 1 mF (2 / (mF : ℝ)))) :=
    fun W A A' F₁ => lintegral_prod_mono'
      (f := fun y => f (W, A, A', F₁, y)) (g := fun y => g (W, A, A', F₁, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun F₂ => h5 W A A' F₁ F₂)
  have h3 : ∀ (W : MlpParam N mW n) (A A' : MlpParam n mA n),
      ∫⁻ y, f (W, A, A', y) ∂mlpGauss n mF 1 ≤ ∫⁻ y, g (W, A, A', y) ∂mlpGauss n mF 1 :=
    fun W A A' => lintegral_prod_mono'
      (f := fun y => f (W, A, A', y)) (g := fun y => g (W, A, A', y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun F₁ => h4 W A A' F₁)
  have h2 : ∀ (W : MlpParam N mW n) (A : MlpParam n mA n),
      ∫⁻ y, f (W, A, y) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) ≤
        ∫⁻ y, g (W, A, y) ∂((mlpGauss n mA n).prod (mlpGauss n mF 1)) :=
    fun W A => lintegral_prod_mono'
      (f := fun y => f (W, A, y)) (g := fun y => g (W, A, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun A' => h3 W A A')
  have h1 : ∀ W : MlpParam N mW n,
      ∫⁻ y, f (W, y) ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) ≤
        ∫⁻ y, g (W, y) ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) :=
    fun W => lintegral_prod_mono'
      (f := fun y => f (W, y)) (g := fun y => g (W, y))
      (mf.comp (by fun_prop)) (mg.comp (by fun_prop)) (fun A => h2 W A)
  have h0 : ∫⁻ r, f r ∂lawR N mW n mA mF ≤ ∫⁻ r, g r ∂lawR N mW n mA mF :=
    lintegral_prod_mono' mf mg h1
  refine h0.trans ?_
  have iQ : Integrable (QD (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) c)
      (lawR N mW n mA mF) := hD.int_sq.integral_prod_right
  have eQ : ∫ r, QD c r ∂lawR N mW n mA mF ≤ e ^ 2 := by
    have := integral_prod_symm (μ := lawU2 N) (ν := lawR N mW n mA mF) _ hD.int_sq
    unfold QD
    rw [← this]
    exact hD.le
  have iR : Integrable Rr (lawR N mW n mA mF) := iQ.const_mul 3
  have hR0 : ∀ r, 0 ≤ Rr r := fun r => by
    have := QD_nonneg c r
    rw [hRr]
    positivity
  rw [hg, ← ofReal_integral_eq_lintegral_ofReal iR (Filter.Eventually.of_forall hR0)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hRr, integral_const_mul]
  linarith

/-- **Chebyshev's inequality for the realized spread, distance form, all widths.** With
`‖kD − c‖₂ ≤ e`, `c > 0` and `θ < 1`: `Pr_{W,A,F}(sd² < θ·c) ≤ 3e²/((1 − θ)·c)²`. -/
theorem spreadLow_dist (hn : 1 ≤ n) (hN : 1 ≤ N) (hmF : 1 ≤ mF) {c e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kD ω - c) e)
    (hc : 0 < c) {θ : ℝ} (hθ : θ < 1) :
    ((mlpGauss N mW n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c} ≤
      3 * e ^ 2 / ((1 - θ) * c) ^ 2 := by
  set T := (mlpGauss N mW n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)) with hT
  have hgap : 0 < (1 - θ) * c := mul_pos (by linarith) hc
  have hgap2 : 0 < ((1 - θ) * c) ^ 2 := by positivity
  set F : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) with hF
  have mF' : Measurable F :=
    ENNReal.measurable_ofReal.comp ((((measurable_sdn (mA := mA) (mF := mF) hN).pow_const 2).sub
      measurable_const).pow_const 2)
  have mπ : Measurable (fun r : Rest N mW n mA mF => (r.1, r.2.1, r.2.2.2)) := by fun_prop
  have hL : ∫⁻ t, F t ∂T ≤ ENNReal.ofReal (3 * e ^ 2) := by
    rw [hT, ← lawR_drop, lintegral_map mF' mπ]
    exact spread_L2_dist hn hN hmF he hD
  have hsub : {t : MlpParam N mW n × MlpParam n mA n × MlpParam n mF 1 |
      sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c} ⊆ {t | ENNReal.ofReal (((1 - θ) * c) ^ 2) ≤ F t} := by
    intro t ht
    have ht' : sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c := ht
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  have hmark := mul_meas_ge_le_lintegral (μ := T) mF' (ENNReal.ofReal (((1 - θ) * c) ^ 2))
  have h1 : ENNReal.ofReal (((1 - θ) * c) ^ 2) * T {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * c} ≤
      ENNReal.ofReal (3 * e ^ 2) :=
    (mul_le_mul' le_rfl (measure_mono hsub)).trans (hmark.trans hL)
  have hv : (0 : ℝ) ≤ 3 * e ^ 2 := by positivity
  rw [le_div_iff₀ hgap2, mul_comm]
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hgap2.le, ENNReal.toReal_ofReal hv] at h2
  exact h2

end general

end BstLean.Part142

open BstLean.Part142 in
#print axioms covV_frob_dist
open BstLean.Part142 in
#print axioms cond_sq_dist
open BstLean.Part142 in
#print axioms spread_L2_dist
open BstLean.Part142 in
#print axioms spreadLow_dist
