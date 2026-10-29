import BstLean.Part236Integration
import BstLean.Part232Master

/-! RF combines full END certificates on each radius/frame cell. -/
namespace BstLean.Part236
open MeasureTheory Real Set BstLean.Part156 BstLean.Part203 BstLean.Part232

section
variable {C Ω S : Type*} [MeasurableSpace C] [MeasurableSpace Ω] [MeasurableSpace S]

theorem rf_end_master (μ : Measure C) (ν : Measure Ω) (σ : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    {E : Set C} (hE : MeasurableSet E) (Rcov : RadiusCover) (Scov : FrameCover)
    {ρ x y Q qt : C → ℝ}
    (hρ : ∀ c, 0 ≤ ρ c) (hx : ∀ c, 0 ≤ x c) (hy : ∀ c, 0 ≤ y c)
    (hmax : ∀ c ∈ E, x c + y c ≤ Scov.maximum) (hqt : Measurable qt)
    {p : C × Ω → ℝ} (hp : Measurable p) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    {R : C × S → ℝ} (hR : Measurable R) (hR0 : ∀ c, 0 ≤ R c)
    {n cbase f a hA ds c₀ c₁ q r v A B δs δret : ℝ}
    (hn : 0 < n) (hc : 0 < cbase) (hf : 0 < f) (ha : 0 < a)
    (hhA : 0 ≤ hA) (hds : 0 ≤ ds) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hq : 0 < q) (hr : 0 ≤ r) (hδs : 0 ≤ δs)
    (cert : ∀ i j, Option (EndCertificate n (cbase + Scov.h (j + 1)) f a
      (hA + ds) (Rcov.h (i + 1))))
    (iρ : IntegrableOn (fun c => ρ c ^ 2) E μ)
    (ix : IntegrableOn (fun c => x c ^ 2) E μ) (iy : IntegrableOn y E μ)
    (hv : ∫ c in E, ρ c ^ 2 ∂μ ≤ v) (hAmom : ∫ c in E, x c ^ 2 ∂μ ≤ A)
    (hB : ∫ c in E, y c ∂μ ≤ B)
    (hline : ∀ i < Rcov.K, ∀ j < Scov.K,
      cellPayment (cert i j) ≤ c₀ + c₁ * Rcov.h i ^ 2 + framePrice q r (Scov.h j))
    (hterminal : 1 ≤ c₀ + c₁ * Rcov.h Rcov.K ^ 2)
    (hQ : ∀ c ∈ E, 0 ≤ Q c ∧ Q c ≤ 1)
    (hQq : ∀ c ∈ E, |√(Q c) - √(qt c)| ≤ hA)
    (hCP : ∀ c ∈ E, ∀ i < Rcov.K, ∀ j < Scov.K,
      radiusCell Rcov.h i (ρ c) → radiusCell Scov.h j (x c + y c) →
      (cert i j).isSome → FreeCPR ν (fun ω => p (c, ω)) n
        (cbase + Scov.h (j + 1)) f (Rcov.h (i + 1)) (Q c))
    (hsamp : ∀ c ∈ E, σ.real {s | ds < |√(R (c, s)) - √(qt c)|} ≤ δs)
    (hcomp : μ.real Eᶜ ≤ δret) :
    (μ.prod (ν.prod σ)).real (programFailure a p R) ≤
      δret + (c₀ + c₁ * v + q * A + r * B) + δs := by
  have mF := measurableSet_programFailure (a := a) hp hR
  have mT := measurableSet_samplingSuccess (Ω := Ω) (ds := ds) hR hqt
  apply rf_retained_ledger μ (ν.prod σ) hE mF mT _
    (retained_sampling μ (ν.prod σ) hE mT hδs ?_) hcomp
  · have hmaxAE : ∀ᵐ c ∂μ.restrict E, x c + y c ≤ Scov.maximum := by
      filter_upwards [ae_restrict_mem hE] with c hcE
      exact hmax c hcE
    apply rf_product_integrated (μ.restrict E) (ν.prod σ) (retained_mass μ hE)
      Rcov Scov (mF.inter mT) hc₀ hc₁ hq hr hρ hx hy hmaxAE iρ ix iy hv hAmom hB hline hterminal
    filter_upwards [ae_restrict_mem hE] with c hcE
    intro i hi j hj hρcell hScell
    cases he : cert i j with
    | none => exact measureReal_le_one
    | some e =>
      have hsome : (cert i j).isSome := by simp [he]
      have hcc : 0 < cbase + Scov.h (j + 1) :=
        add_pos_of_pos_of_nonneg hc (Scov.toRadiusCover.nonneg (by omega))
      exact endpoint_sampling_success ν σ (R := fun s => R (c, s))
        (hp.comp measurable_prodMk_left) (fun _ => hp0 _) (fun _ => hp1 _)
        (fun _ => hR0 _) hn hcc hf (Rcov.nonneg (by omega))
        (hQ c hcE).1 (hQ c hcE).2 ha hhA hds e
        (hCP c hcE i hi j hj hρcell hScell hsome) (hQq c hcE)
  · intro c hcE
    have heq : Prod.mk c ⁻¹' (samplingSuccess (Ω := Ω) R qt ds)ᶜ =
        (univ : Set Ω) ×ˢ {s | ds < |√(R (c, s)) - √(qt c)|} := by
      ext s
      simp [samplingSuccess, not_le]
    rw [heq, real_prod_right]
    exact hsamp c hcE
end
end BstLean.Part236
