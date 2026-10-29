import BstLean.Part232Endpoint
import BstLean.Part232Retained

/-! Part 232: LM composes complete cell certificates with one sampling payment. -/
namespace BstLean.Part232
open MeasureTheory Real Set BstLean.Part156 BstLean.Part203

section Master
variable {C Ω S : Type*} [MeasurableSpace C] [MeasurableSpace Ω] [MeasurableSpace S]

def programFailure (a : ℝ) (p : C × Ω → ℝ) (R : C × S → ℝ) :
    Set (C × (Ω × S)) :=
  {x | ¬ success (p (x.1, x.2.1)) (outRule a (R (x.1, x.2.2)))}

def samplingSuccess (R : C × S → ℝ) (qt : C → ℝ) (ds : ℝ) :
    Set (C × (Ω × S)) :=
  {x | |√(R (x.1, x.2.2)) - √(qt x.1)| ≤ ds}

lemma measurableSet_programFailure {a : ℝ} {p : C × Ω → ℝ} {R : C × S → ℝ}
    (hp : Measurable p) (hR : Measurable R) : MeasurableSet (programFailure a p R) := by
  have hp' : Measurable (fun x : C × (Ω × S) => p (x.1, x.2.1)) :=
    hp.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hR' : Measurable (fun x : C × (Ω × S) => R (x.1, x.2.2)) :=
    hR.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (BstLean.Part157.measurableSet_success hp'
    (BstLean.Part157.measurable_outRule a hR')).compl

lemma measurableSet_samplingSuccess {R : C × S → ℝ} {qt : C → ℝ} {ds : ℝ}
    (hR : Measurable R) (hq : Measurable qt) :
    MeasurableSet (samplingSuccess (Ω := Ω) R qt ds) := by
  exact measurableSet_le
    (((hR.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).sqrt.sub
      (hq.comp measurable_fst).sqrt).abs) measurable_const

/-- LM uses selected END certificates; cells with no certificate use failure bound one. -/
theorem lm_end_master (μ : Measure C) (ν : Measure Ω) (σ : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    {E : Set C} (hE : MeasurableSet E) (cover : RadiusCover)
    {r Q qt : C → ℝ} (hr : ∀ c, 0 ≤ r c) (hqt : Measurable qt)
    {p : C × Ω → ℝ} (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {R : C × S → ℝ} (hR : Measurable R) (hR0 : ∀ x, 0 ≤ R x)
    {n c f a hA ds c₀ c₁ v δs δret : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hf : 0 < f) (ha : 0 < a)
    (hhA : 0 ≤ hA) (hds : 0 ≤ ds) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hδs : 0 ≤ δs)
    (cert : ∀ i, Option (EndCertificate n c f a (hA + ds) (cover.h (i + 1))))
    (hi : IntegrableOn (fun x => r x ^ 2) E μ) (hv : ∫ x in E, r x ^ 2 ∂μ ≤ v)
    (hline : ∀ i < cover.K, cellPayment (cert i) ≤ c₀ + c₁ * cover.h i ^ 2)
    (hterminal : 1 ≤ c₀ + c₁ * cover.h cover.K ^ 2)
    (hQ : ∀ x ∈ E, 0 ≤ Q x ∧ Q x ≤ 1)
    (hQq : ∀ x ∈ E, |√(Q x) - √(qt x)| ≤ hA)
    (hCP : ∀ x ∈ E, ∀ i, i < cover.K → radiusCell cover.h i (r x) →
      (cert i).isSome → FreeCPR ν (fun ω => p (x, ω)) n c f (cover.h (i + 1)) (Q x))
    (hsamp : ∀ x ∈ E, σ.real {s | ds < |√(R (x, s)) - √(qt x)|} ≤ δs)
    (hcomp : μ.real Eᶜ ≤ δret) :
    (μ.prod (ν.prod σ)).real (programFailure a p R) ≤ δret + (c₀ + c₁ * v) + δs := by
  apply lm_retained_master μ (ν.prod σ) hE cover hr
    (measurableSet_programFailure hp hR)
    (measurableSet_samplingSuccess (ds := ds) hR hqt)
    hc₀ hc₁ hδs hi hv hline hterminal _ _ hcomp
  · intro x hx i hi hcell
    cases he : cert i with
    | none => exact measureReal_le_one
    | some e =>
      have hsome : (cert i).isSome := by simp [he]
      exact endpoint_sampling_success ν σ (R := fun s => R (x, s))
        (hp.comp measurable_prodMk_left)
        (fun _ => hp0 _) (fun _ => hp1 _) (fun s => hR0 (x, s))
        hn hc hf (cover.nonneg (by omega)) (hQ x hx).1 (hQ x hx).2
        ha hhA hds e (hCP x hx i hi hcell hsome) (hQq x hx)
  · intro x hx
    have heq : Prod.mk x ⁻¹' (samplingSuccess (Ω := Ω) R qt ds)ᶜ =
        (univ : Set Ω) ×ˢ {s | ds < |√(R (x, s)) - √(qt x)|} := by
      ext y
      simp [samplingSuccess, not_le]
    rw [heq, real_prod_right]
    exact hsamp x hx

end Master
end BstLean.Part232
