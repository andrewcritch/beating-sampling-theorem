import BstLean.Part145G2

/-!
# Part 145 (abstract good hidden event), file 3: the error bound

**`errSampleAG_lint`**: `errSampleAL_lint` of Part 143 for an abstract good hidden event `G`
with `GoodEv n Lc G`. This file makes again the lemmas of `Part143Var` and `Part143Var2` that
read the event. The number `XAL Lc n ζ η η′` is that of Part 143. The proofs are those of the
sources.
Do not use `sorry`, `native_decide` or `axiom`.
-/

-- ===== from Part143Var =====

namespace BstLean.Part145

open BstLean.Part143
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

section goodL

variable {n : ℕ}
  {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
  (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc)
  {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ G)

include hG hn hLc0 hθ

/-- `standInHat140` with the frame constant `Lc`. -/
theorem standInHatLG {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (bhat θ) (M₃.mulVec (bhat θ))) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      Lc / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact s1_mse_mlp (by omega) θ.1 θ.2 (bhatG_ne hG hn hθ) hφ (div_nonneg hLc0 hnpos.le)
    (hG.frame θ hθ)

/-- **The cheap stand-in theorem with the computed centre, for fixed `(M₁, M₂)`.** For
`n ≥ 4096`, `θ = (M₁, M₂) ∈ G`, `0 ≤ ζ < 1`, `η > 0`, bounded measurable `φ` and every real `a`,
with the expectation over `M₃`:
`E(E_{μ_W} φ − E_{ν̂′} φ)² ≤ (1 + η)·(1.83/n)·E_c Var_{ν̂_c} φ
   + 2(1 + 1/η)·HbarH n ζ θ·E_c(E_{ν̂_c}(φ − a)² + E_{ν̂′_c}(φ − a)²)`.
`ν̂′ = cheapIn (M₃ b̂) τ̂₀` is the distribution of `sphPt(M₃ b̂ + τ̂₀γ)`. -/
theorem cheapStandInHatLG {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η)
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
    have h1 := cheapMeanHatG hG hn hθ hζ0 hζ1 (M₃.mulVec b) hφ a
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
          (M₃.mulVec b)) ^ 2) P := ((BstLean.Part105.BM.const (1 + η)).mul (bX.sub
              bY).sq).integrable P
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
  have h136 := standInHatLG hG hn hLc0 hθ hφ
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

variable {n : ℕ} {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)

include hG

/-- **The mean variance under the stand-in**, for `θ ∈ G` and a bounded measurable
`φ`: `E_c Var_{ν̂_c} φ ≤ (1 + 1.83/n)·E_c E_{ν̂_c} φ² − E_{M₃}(E_{μ_W} φ)²`. -/
lemma varG_bound_fixedL (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ G)
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
  have hcross := s1_cross_mlp (n := n) hN θ.1 θ.2 (bhatG_ne hG hn hθ) hφ
  have hmse := standInHatLG hG hn hLc0 hθ hφ
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

/-- **The real inequality for fixed `θ ∈ G` and fixed `(A, F)`.** -/
lemma fixedG_realL (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ G) {ζ :
    ℝ}
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
  have h0 := cheapStandInHatLG hG hn hLc0 hθ hζ0 hζ1 hη hφ 0
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
  have hV := varG_bound_fixedL hG hn hLc0 hθ hφ
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
For `n ≥ 4096`, `θ = (M₁, M₂) ∈ G` and `0 ≤ ζ < 1`:
`E_{A,F} E_{M₃}(Bn − gHat)² ≤
  ((1 + η)(1.83/n)(D_θ + eAFr + 1.83/n) + 4(1 + 1/η)·HbarH n ζ θ)·(4/n)`. -/
theorem errFixedHatLG (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ G) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) :
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
    have hr := fixedG_realL hG hn hLc0 hθ hζ0 hζ1 hη A F
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

end BstLean.Part145

-- ===== from Part143Var2 =====

namespace BstLean.Part145

open BstLean.Part143
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-- **`errVecHat_lint` of Part 140 with the variance of the stand-in.** -/
theorem errVecHatG_lint {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ}
    (hη : 0 < η) :
    ∫⁻ t, ENNReal.ofReal (errGHG G t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (((1 + η) * (Lc / (n : ℝ)) * VbL Lc n +
        4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have mE := hG.meas
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (errGHG G t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_errGHG hG hn1)
  set Gf : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hGf
  have mGf : Measurable Gf := mf.lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, Gf W ∂mlpGauss (2 * n) (mW n) n = _
    rw [e, lintegral_map mGf MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => Gf (MeasurableEquiv.prodAssoc a))
      (mGf.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  -- the bound for fixed θ
  set a : ℝ := (1 + η) * ((l ^ 2) / (n : ℝ)) with ha
  set S : ℝ := 4 / (n : ℝ) with hS
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have he0 : 0 ≤ eAFr n (mA n) (mF n) := by
    have hcF := BstLean.Part133.cF2o_pos hmF
    have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn1
    unfold eAFr; positivity
  set δ : ℝ := (l ^ 2) / (n : ℝ) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  set dd : HidParam (2 * n) (mW n) → ℝ := fun θ => DTh n θ + eAFr n (mA n) (mF n) + δ with hdd
  have hdd0 : ∀ θ, 0 ≤ dd θ := fun θ => by
    have := DTh_nonneg hn1 θ
    rw [hdd]; positivity
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    a * S * G.indicator dd θ +
      4 * (1 + 1 / η) * S * G.indicator (HbarH n ζ) θ with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have h1 : 0 ≤ G.indicator dd θ :=
      Set.indicator_nonneg (fun θ _ => hdd0 θ) _
    have h2 : 0 ≤ G.indicator (HbarH n ζ) θ :=
      Set.indicator_nonneg (fun θ _ => HbarH_nonneg n ζ θ) _
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    have msec : Measurable (fun q : Matrix (Fin n) (Fin (mW n)) ℝ ×
        (MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
        (((θ.1, θ.2, q.1) : MlpParam (2 * n) (mW n) n), q.2)) :=
      ((measurable_const.prodMk (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
    have hswap : ∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM =
        ∫⁻ p, (∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM) ∂PAF :=
      lintegral_lintegral_swap
        (f := fun (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) (mf.comp msec).aemeasurable
    rw [hswap]
    by_cases hθ : θ ∈ G
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWHG G := fun M₃ => hθ
      have hin : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM =
          ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)
            p.1 p.2 - gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2 ∂gM) := by
        rintro ⟨A, F⟩
        have hφ : BM (phiS A F) := bm_phiS hn1 A F
        have hb : BM (fun W : MlpParam (2 * n) (mW n) n =>
            ((∫ x, phiS A F x ∂muWn W) - ∫ x, phiS A F x ∂cheapHat W) ^ 2) :=
          ((bm_muW hN hφ).sub (bm_cheapHat hN hφ)).sq
        have hb' : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
              gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2) := by
          have h1 := hb.comp (g := fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n))
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))
          refine ⟨?_, h1.bdd.imp fun M hM M₃ => ?_⟩
          · convert h1.meas using 2 with M₃
            rw [integral_phiS_muWn hn1]
            unfold cheapHat gHat
            rw [integral_phiS_cheapIn hn1]
            rfl
          · have := hM M₃
            rw [integral_phiS_muWn hn1] at this
            unfold cheapHat at this
            rw [integral_phiS_cheapIn hn1] at this
            exact this
        rw [ofReal_integral_eq_lintegral_ofReal (hb'.integrable gM)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        refine lintegral_congr fun M₃ => ?_
        simp only [hf, errGHG, Set.indicator_of_mem (hW M₃)]
        congr 1
        ring
      simp_rw [hin]
      refine (errFixedHatLG hG hn hLc0 hθ hζ0.le hζ1 hη).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hk]
      simp only [Set.indicator_of_mem hθ]
      rw [ha, hS, hdd, hδ]
      apply le_of_eq
      ring
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWHG G := fun M₃ => hθ
      have hz : ∀ (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
          (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ),
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) = 0 := by
        intro p M₃
        simp only [hf, errGHG, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero]
      simp_rw [hz]
      simp
  obtain ⟨iH, hH⟩ := HbarHG_mean hG hn hζ0 hζ1
  obtain ⟨iD, hDb⟩ := DTh_mean hn
  have idd : Integrable dd (hidGauss (2 * n) (mW n)) :=
    (iD.add (integrable_const _)).add (integrable_const _)
  have i1 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      a * S * G.indicator dd θ) (hidGauss (2 * n) (mW n)) :=
    (idd.indicator mE).const_mul _
  have i2 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      4 * (1 + 1 / η) * S * G.indicator (HbarH n ζ) θ) (hidGauss (2 * n) (mW n)) := iH.const_mul _
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := i1.add i2
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_add i1 i2, integral_const_mul, integral_const_mul]
        have e1 : ∫ θ, G.indicator dd θ ∂hidGauss (2 * n) (mW n) ≤ VbL (l ^ 2) n := by
          have h0 : ∫ θ, G.indicator dd θ ∂hidGauss (2 * n) (mW n) ≤
              ∫ θ, dd θ ∂hidGauss (2 * n) (mW n) :=
            integral_mono (idd.indicator mE) idd
              (fun θ => Set.indicator_le_self' (fun θ _ => hdd0 θ) θ)
          have h1 : ∫ θ, dd θ ∂hidGauss (2 * n) (mW n) =
              (∫ θ, DTh n θ ∂hidGauss (2 * n) (mW n)) + eAFr n (mA n) (mF n) + δ := by
            have e' : dd = fun θ => (DTh n θ + (fun _ => eAFr n (mA n) (mF n)) θ) +
                (fun _ => δ) θ := by rw [hdd]
            rw [e', integral_add (f := fun θ => DTh n θ + (fun _ => eAFr n (mA n) (mF n)) θ)
                (iD.add (integrable_const _)) (integrable_const _),
              integral_add (f := fun θ => DTh n θ) iD (integrable_const _)]
            simp
          unfold VbL
          rw [h1] at h0
          linarith
        have h1 := mul_le_mul_of_nonneg_left e1 (mul_nonneg ha0 hS0)
        have h2 := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 4 * (1 + 1 / η) * S)
        rw [ha, hS] at h1
        rw [hS] at h2
        rw [ha, hS]
        linarith

/-- **`errVecA_lint` of Part 141 with the variance of the stand-in.** -/
theorem errVecAG_lint {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 4096 ≤ n) (hLc0 : 0 ≤ Lc) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ}
    (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (XAL Lc n ζ η η' * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hVb := VbL_nonneg hn hLc0
  unfold XAL
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (errGHG G t)) :=
    ENNReal.measurable_ofReal.comp (measurable_errGHG hG hn1)
  have m2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dGAG G t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dGAG hG hn1)
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (errGAG G t) ≤
        ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGHG G t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGAG G t) := by
    intro t
    have h0 := errGHG_nonneg G t
    have h0' := dGAG_nonneg G t
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases ht : t.1 ∈ goodWAG G
    · have ht' : t.1 ∈ goodWHG G := goodWAG_sub G ht
      simp only [errGAG, errGHG, dGAG, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      have hs := sq_split (η := 1 / η') (by positivity) (gA t.1 t.2.1 t.2.2)
        (gHat t.1 t.2.1 t.2.2) (Part130.Bn t.1 t.2.1 t.2.2)
      rw [one_div_one_div] at hs
      linarith
    · simp only [errGAG, Set.indicator_of_notMem ht]
      positivity
  calc ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGHG G t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGAG G t)) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ENNReal.ofReal (1 + η') * ∫⁻ t, ENNReal.ofReal (errGHG G t) ∂mlpTriple 2 n +
          ENNReal.ofReal (1 + 1 / η') * ∫⁻ t, ENNReal.ofReal (dGAG G t) ∂mlpTriple 2 n := by
        rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
          lintegral_const_mul _ m2]
    _ ≤ ENNReal.ofReal (1 + η') * ENNReal.ofReal (((1 + η) * ((l ^ 2) / (n : ℝ)) * VbL (l ^ 2) n +
            4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (pertA n * (4 / (n : ℝ))) :=
        add_le_add (mul_le_mul' le_rfl (errVecHatG_lint hG hn hLc0 hζ0 hζ1 hη))
          (mul_le_mul' le_rfl (diffVecAG_lint hG hn))
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **`errSampleA_lint` of Part 141 with the variance of the stand-in.** For `n ≥ 4096`,
`0 < ζ < 1`, `k ≥ 1`: `E[1_good(W)·(g̃_k − B)²] ≤ (XAL (l ^ 2) n ζ η η′ + 1/k)·(4/n)`. -/
theorem errSampleAG_lint {n : ℕ} (hn : 4096 ≤ n) {Lc : ℝ} (hLc0 : 0 ≤ Lc)
    {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (errSAG G k p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((XAL Lc n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ))) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℝ, Lc = l ^ 2 := ⟨√Lc, (Real.sq_sqrt hLc0).symm⟩
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hX := XAL_nonneg hn hLc0 ζ hη hη'
  set PW := mlpGauss (2 * n) (mW n) n with hPW
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  have e0 : mlpTriple 2 n = PW.prod PAF := rfl
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errSAG G k p)) :=
    ENNReal.measurable_ofReal.comp (measurable_errSAG hG hn1 k)
  rw [lintegral_prod _ mf.aemeasurable]
  -- the second moment term, as a function of `(W, (A, F))`
  set Lo : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => Lout (stdGauss (Fin n)) (preA t.1) t.2 with hLo
  have mL : Measurable Lo := by
    have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) =>
        ENNReal.ofReal (phiS q.1.2.1 q.1.2.2 (preA q.1.1 q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp
          (measurable_preA.comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))).pow_const 2)
    exact hj.lintegral_prod_right'
  have hLint : ∫⁻ t, Lo t ∂mlpTriple 2 n = ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [e0, lintegral_prod _ mL.aemeasurable]
    have h : ∀ W : MlpParam (2 * n) (mW n) n,
        ∫⁻ q, Lo (W, q) ∂PAF = ENNReal.ofReal (4 / (n : ℝ)) := by
      intro W
      have := lintegral_Lout (mA := mA n) (mF := mF n) (stdGauss (Fin n)) hn1 hmA hmF
        (measurable_preA_W W)
      exact this
    simp_rw [h]
    simp
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (errSAG G k (t, γ)) ∂gamK k n ≤
        ENNReal.ofReal (errGAG G t) + ENNReal.ofReal ((k : ℝ)⁻¹) * Lo t := by
    rintro ⟨W, A, F⟩
    have ho : Measurable (preA W) := measurable_preA_W W
    have hφ : BstLean.Part105.BM (fun γ : Fin n → ℝ => phiS A F (preA W γ)) :=
      (bm_phiS hn1 A F).comp ho
    obtain ⟨hi, he⟩ := iid_mean_sq (stdGauss (Fin n)) hφ hk (Part130.Bn W A F)
    by_cases hW : W ∈ goodWAG G
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSAG G k ((W, A, F), γ) =
          ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (γ i)) - Part130.Bn W A F) ^ 2 := by
        intro γ
        simp only [errSAG, Set.indicator_of_mem hW, gSampleA]
      simp_rw [e1]
      rw [show gamK k n = Measure.pi (fun _ : Fin k => stdGauss (Fin n)) from rfl,
        ← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      have he' : ∫ x : Fin k → Fin n → ℝ, ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (x i)) -
          Part130.Bn W A F) ^ 2 ∂Measure.pi (fun _ : Fin k => stdGauss (Fin n)) =
          (∫ x, phiS A F (preA W x) ∂stdGauss (Fin n) - Part130.Bn W A F) ^ 2 +
            (k : ℝ)⁻¹ * Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] := he
      rw [he', ← gA_eq hn1]
      have hv : Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] ≤
          ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) := by
        rw [BstLean.Part134.var_bm (stdGauss (Fin n)) hφ]
        nlinarith [sq_nonneg (∫ γ, phiS A F (preA W γ) ∂stdGauss (Fin n))]
      have hGf : errGAG G (W, A, F) = (gA W A F - Part130.Bn W A F) ^ 2 := by
        simp only [errGAG, Set.indicator_of_mem hW]
      have i0 : 0 ≤ ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) :=
        integral_nonneg fun _ => sq_nonneg _
      rw [hLo]
      simp only
      rw [← ofReal_integral_out (stdGauss (Fin n)) hn1 A F ho, hGf,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg (by positivity) i0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
      linarith
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSAG G k ((W, A, F), γ) = 0 := by
        intro γ
        simp only [errSAG, Set.indicator_of_notMem hW]
      simp_rw [e1]
      simp
  calc ∫⁻ t, (∫⁻ γ, ENNReal.ofReal (errSAG G k (t, γ)) ∂gamK k n) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (errGAG G t) + ENNReal.ofReal ((k : ℝ)⁻¹) * Lo t) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) := by
        have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1 => ENNReal.ofReal (errGAG G t)) :=
          ENNReal.measurable_ofReal.comp (measurable_errGAG hG hn1)
        rw [lintegral_add_left m1, lintegral_const_mul _ mL, hLint]
    _ ≤ ENNReal.ofReal (XAL (l ^ 2) n ζ η η' * (4 / (n : ℝ))) +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) :=
        add_le_add (errVecAG_lint hG hn hLc0 hζ0 hζ1 hη hη') le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

end BstLean.Part145


open BstLean.Part145 in
#print axioms errSampleAG_lint
open BstLean.Part145 in
#print axioms badAG_prob_gen
open BstLean.Part145 in
#print axioms zeroPtAG_null
open BstLean.Part145 in
#print axioms measurable_errSAG
