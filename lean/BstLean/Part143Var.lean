import BstLean.Part143Lam
import BstLean.Part142Var2

/-!
# Part 143 (helper `lam16`), step 2a: the chain of Part 142 with a general frame constant

The lemmas of Parts 140 and 142 that contain the literal stand-in factor `183/100`, with a
constant `Lc ≥ 0` and the hypothesis `FrameL Lc n` (the frame bound `Lc/n` of the unit residual
directions of the computed centre on `goodHat n`) in the place of `frameHat140`. The proofs are
those of `standInHat140`, `cheapStandInHat` (Part 140), `var_bound_fixed`, `fixed_real`,
`errFixedHat142` (Part 142) with the constant replaced.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-- The frame bound `Lc/n` of the unit residual directions of the computed centre, on the good
hidden event `goodHat n`. `frameHat140` is `FrameL (183/100) n` for `n ≥ 4096`. -/
def FrameL (Lc : ℝ) (n : ℕ) : Prop :=
  ∀ θ ∈ goodHat n, ∀ w : Fin (mW n) → ℝ,
    ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      Lc / (n : ℝ) * ∑ j, w j ^ 2

lemma frameL_140 {n : ℕ} (hn : 4096 ≤ n) : FrameL (183 / 100) n :=
  fun _ hθ w => frameHat140 hn hθ w

lemma frameL_143 {n : ℕ} (hn : 16384 ≤ n) : FrameL L143 n :=
  fun _ hθ w => frameHat143 hn hθ w

section goodL

variable {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : FrameL Lc n)
  {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n)

include hn hLc0 hLc hθ

/-- `standInHat140` with the frame constant `Lc`. -/
theorem standInHatL {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (bhat θ) (M₃.mulVec (bhat θ))) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      Lc / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact s1_mse_mlp (by omega) θ.1 θ.2 (bhat_ne hn hθ) hφ (div_nonneg hLc0 hnpos.le)
    (hLc θ hθ)

/-- **The cheap stand-in theorem with the computed centre, for fixed `(M₁, M₂)`.** For
`n ≥ 4096`, `θ = (M₁, M₂) ∈ goodHat n`, `0 ≤ ζ < 1`, `η > 0`, bounded measurable `φ` and every real `a`,
with the expectation over `M₃`:
`E(E_{μ_W} φ − E_{ν̂′} φ)² ≤ (1 + η)·(1.83/n)·E_c Var_{ν̂_c} φ
   + 2(1 + 1/η)·HbarH n ζ θ·E_c(E_{ν̂_c}(φ − a)² + E_{ν̂′_c}(φ − a)²)`.
`ν̂′ = cheapIn (M₃ b̂) τ̂₀` is the distribution of `sphPt(M₃ b̂ + τ̂₀γ)`. -/
theorem cheapStandInHatL {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (a : ℝ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec (bhat θ)) (tauHat (2 * n) (mW n) θ)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      (1 + η) * (Lc / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        ∫ c, (∫ x, (φ x - a) ^ 2
              ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c +
            ∫ x, (φ x - a) ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ))
          ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  set P := gaussMat n (mW n) (2 / (mW n : ℝ)) with hP
  set b := bhat θ with hb
  set τ₀ := tauHat (2 * n) (mW n) θ with hτ₀
  have hψ : BM (fun x => (φ x - a) ^ 2) := (hφ.sub (BstLean.Part105.BM.const a)).sq
  -- the three means as functions of `M₃`
  have bX : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      ∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) :=
    (bm_muW hN hφ).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have bYc : BM (fun c : Fin n → ℝ =>
      ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c) :=
    bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) b hh hφ
  have bZc : BM (fun c : Fin n → ℝ => ∫ x, φ x ∂cheapIn c τ₀) :=
    bm_cheapIn measurable_id measurable_const hφ
  have bSc : BM (fun c : Fin n → ℝ =>
      ∫ x, (φ x - a) ^ 2
          ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c +
        ∫ x, (φ x - a) ^ 2 ∂cheapIn c τ₀) :=
    (bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) b hh hψ).add
      (bm_cheapIn measurable_id measurable_const hψ)
  have mb : Measurable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ => M₃.mulVec b) :=
    measurable_mulVec_right b
  have bY := bYc.comp mb
  have bZ := bZc.comp mb
  have bS := bSc.comp mb
  -- pointwise in `M₃`
  have hpt : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec b) τ₀) ^ 2 ≤
      (1 + η) * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀) := by
    intro M₃
    have h1 := cheapMeanHat hn hθ hζ0 hζ1 (M₃.mulVec b) hφ a
    exact (sq_split hη _ _ _).trans (add_le_add le_rfl
      (by
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + 1 / η)
        have e : (1 + 1 / η) * (2 * HbarH n ζ θ *
            (∫ x, (φ x - a) ^ 2
                ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
                  (M₃.mulVec b) +
              ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀)) =
            2 * (1 + 1 / η) * HbarH n ζ θ *
            (∫ x, (φ x - a) ^ 2
                ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
                  (M₃.mulVec b) +
              ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀) := by ring
        rw [e] at h2
        exact h2))
  have i1 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      (1 + η) * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2) P := ((BstLean.Part105.BM.const (1 + η)).mul (bX.sub bY).sq).integrable P
  have i2 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      2 * (1 + 1 / η) * HbarH n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀)) P :=
    ((BstLean.Part105.BM.const (2 * (1 + 1 / η) * HbarH n ζ θ)).mul bS).integrable P
  have i12 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      (1 + η) * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀)) P := i1.add i2
  have hmono := integral_mono ((bX.sub bZ).sq.integrable P) i12 hpt
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hmono
  have h136 := standInHatL hn hLc0 hLc hθ hφ
  have ecd : ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀) ∂P =
      ∫ c, (∫ x, (φ x - a) ^ 2
              ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c +
            ∫ x, (φ x - a) ^ 2 ∂cheapIn c τ₀) ∂cDist n (2 / (mW n : ℝ)) b := by
    rw [← cDist_eq, integral_map mb.aemeasurable bSc.meas.aestronglyMeasurable]
  rw [ecd] at hmono
  have h136' : ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 ∂P ≤
      (l ^ 2) / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c]
          ∂cDist n (2 / (mW n : ℝ)) b := h136
  have h137 := mul_le_mul_of_nonneg_left h136' (by positivity : (0 : ℝ) ≤ 1 + η)
  linarith

end goodL

section fixedL

variable {n : ℕ}

/-- **The mean variance under the stand-in**, for `θ ∈ goodHat n` and a bounded measurable
`φ`: `E_c Var_{ν̂_c} φ ≤ (1 + 1.83/n)·E_c E_{ν̂_c} φ² − E_{M₃}(E_{μ_W} φ)²`. -/
lemma var_bound_fixedL (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : FrameL Lc n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c]
        ∂cDist n (2 / (mW n : ℝ)) (bhat θ) ≤
      (1 + Lc / (n : ℝ)) *
        (∫ c, (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) -
      ∫ M₃, (∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  have b1 := bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (bhat θ) hh hφ.sq
  have bY := bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (bhat θ) hh hφ
  have hvar : ∀ c : Fin n → ℝ,
      Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c] =
      (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) -
        (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) ^ 2 := by
    intro c
    have := standIn_prob (n := n) (uniformSphere (2 * n)) hh (2 / (mW n : ℝ)) (bhat θ) c
    exact var_bm _ hφ
  have hVeq : ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
        (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ) =
      (∫ c, (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) -
        ∫ c, (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
          (2 / (mW n : ℝ)) (bhat θ) c) ^ 2 ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by
    simp_rw [hvar]
    exact integral_sub (b1.integrable _) (bY.sq.integrable _)
  have hcross := s1_cross_mlp (n := n) hN θ.1 θ.2 (bhat_ne hn hθ) hφ
  have hmse := standInHatL hn hLc0 hLc hθ hφ
  have hY0 : 0 ≤ ∫ c, (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
      (2 / (mW n : ℝ)) (bhat θ) c) ^ 2 ∂cDist n (2 / (mW n : ℝ)) (bhat θ) :=
    integral_nonneg fun _ => sq_nonneg _
  rw [hcross] at hmse
  rw [hVeq] at hmse ⊢
  have hδ : (0 : ℝ) ≤ (l ^ 2) / (n : ℝ) := by positivity
  set J := ∫ c, (∫ x, φ x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
    (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ)
  set Y2 := ∫ c, (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
    (2 / (mW n : ℝ)) (bhat θ) c) ^ 2 ∂cDist n (2 / (mW n : ℝ)) (bhat θ)
  have h3 : (l ^ 2) / (n : ℝ) * (J - Y2) ≤ (l ^ 2) / (n : ℝ) * J :=
    mul_le_mul_of_nonneg_left (by linarith) hδ
  linarith

/-- **The real inequality for fixed `θ ∈ goodHat n` and fixed `(A, F)`.** -/
lemma fixed_realL (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : FrameL Lc n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n) {ζ : ℝ}
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) (A : MlpParam n (mA n) n)
    (F : MlpParam n (mF n) 1) :
    (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ))) +
      (1 + η) * (Lc / (n : ℝ)) * (∫ ω, phiS A F (oA θ ω) ^ 2
        ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (uniformSphere (2 * n)))) ≤
    (1 + η) * (Lc / (n : ℝ)) * (1 + Lc / (n : ℝ)) *
        (∫ ω, phiS A F (o1 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod
          ((uniformSphere (2 * n)).prod (stdGauss (Fin n))))) +
      (1 + η) * (Lc / (n : ℝ)) * (∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2
        ∂((gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n)))) +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        ((∫ ω, phiS A F (o1 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod
          ((uniformSphere (2 * n)).prod (stdGauss (Fin n))))) +
        ∫ ω, phiS A F (o2 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod (stdGauss (Fin n)))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have := uniformSphere_isProbability (2 * n) hN
  have hH := HbarH_nonneg n ζ θ
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  have hφ : BM (phiS A F) := bm_phiS hn1 A F
  have h0 := cheapStandInHatL hn hLc0 hLc hθ hζ0 hζ1 hη hφ 0
  simp only [sub_zero] at h0
  have eL : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, phiS A F x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, phiS A F x ∂cheapIn (M₃.mulVec (bhat θ)) (tauHat (2 * n) (mW n) θ)) ^ 2 =
      (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
        gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2 := by
    intro M₃
    rw [integral_phiS_muWn hn1, integral_phiS_cheapIn hn1]
    rfl
  simp_rw [eL] at h0
  have b1 := bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (bhat θ) hh hφ.sq
  have b2 : BM (fun c : Fin n → ℝ =>
      ∫ x, phiS A F x ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ)) :=
    bm_cheapIn measurable_id measurable_const hφ.sq
  have hsplit : ∫ c, ((∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
        (2 / (mW n : ℝ)) (bhat θ) c) +
        ∫ x, phiS A F x ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ))
        ∂cDist n (2 / (mW n : ℝ)) (bhat θ) =
      (∫ c, (∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
        (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) +
        ∫ c, (∫ x, phiS A F x ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ))
          ∂cDist n (2 / (mW n : ℝ)) (bhat θ) :=
    integral_add (b1.integrable _) (b2.integrable _)
  have e1 : ∫ c, (∫ x, phiS A F x ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2)
        (2 / (mW n : ℝ)) (bhat θ) c) ∂cDist n (2 / (mW n : ℝ)) (bhat θ) =
      ∫ ω, phiS A F (o1 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod
        ((uniformSphere (2 * n)).prod (stdGauss (Fin n)))) :=
    J1_eq (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (bhat θ) hh hφ.sq
  have e2 : ∫ c, (∫ x, phiS A F x ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ))
        ∂cDist n (2 / (mW n : ℝ)) (bhat θ) =
      ∫ ω, phiS A F (o2 θ ω) ^ 2 ∂((stdGauss (Fin n)).prod (stdGauss (Fin n))) :=
    J2_eq (n := n) (2 / (mW n : ℝ)) (bhat θ) (tauHat (2 * n) (mW n) θ) hφ.sq
  have hV := var_bound_fixedL hn hLc0 hLc hθ hφ
  rw [EX2_eq hn1 θ A F, e1] at hV
  rw [hsplit, e1, e2] at h0
  have hc : (0 : ℝ) ≤ (1 + η) * ((l ^ 2) / (n : ℝ)) := by positivity
  have h5 := mul_le_mul_of_nonneg_left hV hc
  have e5 : (1 + η) * ((l ^ 2) / (n : ℝ) *
      ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
        (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) =
      (1 + η) * ((l ^ 2) / (n : ℝ)) *
      ∫ c, Var[phiS A F; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
        (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by ring
  rw [e5] at h0
  linarith

/-- **The error for fixed `(M₁, M₂)` on the good event, with the variance of the stand-in.**
For `n ≥ 4096`, `θ = (M₁, M₂) ∈ goodHat n` and `0 ≤ ζ < 1`:
`E_{A,F} E_{M₃}(Bn − gHat)² ≤
  ((1 + η)(1.83/n)(D_θ + eAFr + 1.83/n) + 4(1 + 1/η)·HbarH n ζ θ)·(4/n)`. -/
theorem errFixedHatL (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : FrameL Lc n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ goodHat n) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)))
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal (((1 + η) * (Lc / (n : ℝ)) *
        (DTh n θ + eAFr n (mA n) (mF n) + Lc / (n : ℝ)) +
      4 * (1 + 1 / η) * HbarH n ζ θ) * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have := lawU2_prob hN
  have hH := HbarH_nonneg n ζ θ
  have hD0 := DTh_nonneg hn1 θ
  have he0 : 0 ≤ eAFr n (mA n) (mF n) := by
    have hcF := BstLean.Part133.cF2o_pos hmF
    have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn1
    unfold eAFr; positivity
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set Pa := gM.prod (uniformSphere (2 * n)) with hPa
  set Pd := gM.prod (lawU2 (2 * n)) with hPd
  set P₁ := (stdGauss (Fin n)).prod ((uniformSphere (2 * n)).prod (stdGauss (Fin n))) with hP₁
  set P₂ := (stdGauss (Fin n)).prod (stdGauss (Fin n)) with hP₂
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set c : ℝ := (1 + η) * ((l ^ 2) / (n : ℝ)) with hc
  set δ : ℝ := (l ^ 2) / (n : ℝ) with hδ
  set a₂ : ℝ := 2 * (1 + 1 / η) * HbarH n ζ θ with ha₂
  set S : ℝ := 4 / (n : ℝ) with hS
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have ha₂0 : 0 ≤ a₂ := by rw [ha₂]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  set Lf : MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ := fun p =>
    ∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
      gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2 ∂gM with hLf
  have m1 := measurable_Lout (mA := mA n) (mF := mF n) P₁ (measurable_o1 θ)
  have m2 := measurable_Lout (mA := mA n) (mF := mF n) P₂ (measurable_o2 θ)
  have ma := measurable_Lout (mA := mA n) (mF := mF n) Pa (measurable_oA θ)
  have md := measurable_LoutD (mA := mA n) (mF := mF n) Pd (measurable_oD1 θ) (measurable_oD2 θ)
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (Lf p) + ENNReal.ofReal c * Lout Pa (oA θ) p ≤
        ENNReal.ofReal (c * (1 + δ)) * Lout P₁ (o1 θ) p +
          ENNReal.ofReal c * LoutD Pd (oD1 θ) (oD2 θ) p +
          ENNReal.ofReal a₂ * (Lout P₁ (o1 θ) p + Lout P₂ (o2 θ) p) := by
    rintro ⟨A, F⟩
    have hr := fixed_realL hn hLc0 hLc hθ hζ0 hζ1 hη A F
    have iL : 0 ≤ Lf (A, F) := integral_nonneg fun _ => sq_nonneg _
    have ia : 0 ≤ ∫ ω, phiS A F (oA θ ω) ^ 2 ∂Pa := integral_nonneg fun _ => sq_nonneg _
    have i1 : 0 ≤ ∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁ := integral_nonneg fun _ => sq_nonneg _
    have i2 : 0 ≤ ∫ ω, phiS A F (o2 θ ω) ^ 2 ∂P₂ := integral_nonneg fun _ => sq_nonneg _
    have id' : 0 ≤ ∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2 ∂Pd :=
      integral_nonneg fun _ => by positivity
    rw [← ofReal_integral_out Pa hn1 A F (measurable_oA θ),
      ← ofReal_integral_out P₁ hn1 A F (measurable_o1 θ),
      ← ofReal_integral_out P₂ hn1 A F (measurable_o2 θ),
      ← ofReal_integral_outD Pd hn1 A F (measurable_oD1 θ) (measurable_oD2 θ)]
    have eLHS : ENNReal.ofReal (Lf (A, F)) +
        ENNReal.ofReal c * ENNReal.ofReal (∫ ω, phiS A F (oA θ ω) ^ 2 ∂Pa) =
        ENNReal.ofReal (Lf (A, F) + c * ∫ ω, phiS A F (oA θ ω) ^ 2 ∂Pa) := by
      rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add iL (mul_nonneg hc0 ia)]
    have eRHS : ENNReal.ofReal (c * (1 + δ)) * ENNReal.ofReal (∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁) +
        ENNReal.ofReal c *
          ENNReal.ofReal (∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2 ∂Pd) +
        ENNReal.ofReal a₂ * (ENNReal.ofReal (∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁) +
          ENNReal.ofReal (∫ ω, phiS A F (o2 θ ω) ^ 2 ∂P₂)) =
        ENNReal.ofReal (c * (1 + δ) * (∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁) +
          c * (∫ ω, (phiS A F (oD1 θ ω) - phiS A F (oD2 θ ω)) ^ 2 / 2 ∂Pd) +
          a₂ * ((∫ ω, phiS A F (o1 θ ω) ^ 2 ∂P₁) + ∫ ω, phiS A F (o2 θ ω) ^ 2 ∂P₂)) := by
      have hcd : 0 ≤ c * (1 + δ) := by positivity
      rw [← ENNReal.ofReal_add i1 i2, ← ENNReal.ofReal_mul hcd, ← ENNReal.ofReal_mul hc0,
        ← ENNReal.ofReal_mul ha₂0, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [eLHS, eRHS]
    exact ENNReal.ofReal_le_ofReal hr
  have hSa := lintegral_Lout (mA := mA n) (mF := mF n) Pa hn1 hmA hmF (measurable_oA θ)
  have hS1 := lintegral_Lout (mA := mA n) (mF := mF n) P₁ hn1 hmA hmF (measurable_o1 θ)
  have hS2 := lintegral_Lout (mA := mA n) (mF := mF n) P₂ hn1 hmA hmF (measurable_o2 θ)
  have hSd := lint_LoutD_theta (mA := mA n) (mF := mF n) hn1 hmA hmF θ
  have hint := lintegral_mono (μ := PAF) key
  have mX2 : Measurable (fun a : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      ENNReal.ofReal c * LoutD Pd (oD1 θ) (oD2 θ) a) := md.const_mul _
  have mS : Measurable (fun a : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      Lout P₁ (o1 θ) a + Lout P₂ (o2 θ) a) := m1.add m2
  have mX3 : Measurable (fun a : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      ENNReal.ofReal a₂ * (Lout P₁ (o1 θ) a + Lout P₂ (o2 θ) a)) := mS.const_mul _
  have mXa : Measurable (fun a : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      ENNReal.ofReal c * Lout Pa (oA θ) a) := ma.const_mul _
  rw [lintegral_add_right _ mXa, lintegral_const_mul _ ma, hSa,
    lintegral_add_right _ mX3, lintegral_add_right _ mX2, lintegral_const_mul _ m1,
    lintegral_const_mul _ md, lintegral_const_mul _ mS, lintegral_add_right _ m2, hS1, hS2]
    at hint
  have hfin : ∫⁻ p, ENNReal.ofReal (Lf p) ∂PAF + ENNReal.ofReal (c * S) ≤
      ENNReal.ofReal (c * (1 + δ) * S + c * (S * (DTh n θ + eAFr n (mA n) (mF n))) +
        a₂ * (S + S)) := by
    rw [ENNReal.ofReal_mul (q := S) hc0]
    refine hint.trans ?_
    have hD0' : 0 ≤ S * (DTh n θ + eAFr n (mA n) (mF n)) := by positivity
    have hcd : 0 ≤ c * (1 + δ) := by positivity
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (q := S) hcd,
      ENNReal.ofReal_mul (q := S * (DTh n θ + eAFr n (mA n) (mF n))) hc0,
      ENNReal.ofReal_mul (q := S + S) ha₂0, ENNReal.ofReal_add hS0 hS0]
    exact add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hSd)) le_rfl
  have h2 := ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hfin
  rw [← ENNReal.ofReal_sub _ (mul_nonneg hc0 hS0)] at h2
  refine h2.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [ha₂]
  ring

end fixedL

end BstLean.Part143

open BstLean.Part143 in
#print axioms standInHatL
open BstLean.Part143 in
#print axioms cheapStandInHatL
open BstLean.Part143 in
#print axioms errFixedHatL
