import BstLean.Part203Tail
import BstLean.Part156Master

/-! Part 203: a radius-cell failure bound pays the sampling complement once. -/
namespace BstLean.Part203
open MeasureTheory Real Set BstLean.Part156

section Fibre
variable {Ω ΩS : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩS]

/-- Radius integration can retain sampling success and pay its complement after integration. -/
theorem failure_on_sampling_success (μ : Measure Ω) (μS : Measure ΩS)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μS]
    {p : Ω → ℝ} (hp1 : ∀ ω, p ω ≤ 1) {R : ΩS → ℝ} (hR0 : ∀ σ, 0 ≤ R σ)
    {Q a hA ds qt Bp Bm : ℝ} (ha : 0 < a) (hQq : |√Q - √qt| ≤ hA)
    (hplus : μ.real {ω | zplus a (hA + ds) Q < p ω} ≤ Bp)
    (hminus : μ.real {ω | p ω < zminus a (hA + ds) Q ∧
      1 / 1000 < zminus a (hA + ds) Q} ≤ Bm) :
    (μ.prod μS).real {x | ¬ success (p x.1) (outRule a (R x.2)) ∧
      |√(R x.2) - √qt| ≤ ds} ≤ Bp + Bm := by
  have hincl : {x : Ω × ΩS | ¬ success (p x.1) (outRule a (R x.2)) ∧
      |√(R x.2) - √qt| ≤ ds} ⊆
      ({ω | zplus a (hA + ds) Q < p ω} ×ˢ (univ : Set ΩS)) ∪
      ({ω | p ω < zminus a (hA + ds) Q ∧
        1 / 1000 < zminus a (hA + ds) Q} ×ˢ (univ : Set ΩS)) := by
    rintro ⟨ω, σ⟩ ⟨hfail, hs⟩
    have hRQ : |√(R σ) - √Q| ≤ hA + ds := by
      have h1 := abs_sub_le (√(R σ)) (√qt) (√Q)
      have h2 : |√qt - √Q| ≤ hA := by simpa [abs_sub_comm] using hQq
      linarith
    rcases not_success (hp1 ω) (hR0 σ) ha hRQ hfail with h1 | h1
    · exact Or.inl ⟨h1.2, mem_univ _⟩
    · exact Or.inr ⟨⟨h1.2.1, h1.2.2⟩, mem_univ _⟩
  have hbound := (measureReal_mono (μ := μ.prod μS) hincl).trans
    (measureReal_union_le _ _)
  rw [real_prod_left, real_prod_left] at hbound
  exact hbound.trans (add_le_add hplus hminus)

/-- END covers failure intersected with sampling success; the sampling payment occurs once. -/
theorem fibre_fail (μ : Measure Ω) (μS : Measure ΩS)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μS]
    {p : Ω → ℝ} (hp : Measurable p) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1)
    {R : ΩS → ℝ} (hR0 : ∀ σ, 0 ≤ R σ)
    (mp mm : LogChoice) (hmp : mp.Valid) (hmm : mm.Valid)
    {n c f H Q a hA ds qt τp τm vp vm bp bm δs : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hf : 0 < f) (hH : 0 ≤ H)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (ha : 0 < a) (hhA : 0 ≤ hA) (hds : 0 ≤ ds)
    (hτp : 0 < τp) (hτm : τm < 0)
    (hvp0 : 0 ≤ vp) (hvp1 : vp ≤ 1) (hvm0 : 0 ≤ vm) (hvm1 : vm ≤ 1)
    (hbp : 0 < bp) (hbm : 0 < bm)
    (hside : 2 * (hA + ds) + 2 * H / bm < √(1 / 100 / a))
    (hEp : endpointPlus mp a (hA + ds) H c f τp vp bp ≤ 0)
    (hEm : endpointMinus mm a (hA + ds) H c f τm vm bm ≤ 0)
    (hCP : FreeCPR μ p n c f H Q) (hQq : |√Q - √qt| ≤ hA)
    (hsamp : μS.real {σ | ds < |√(R σ) - √qt|} ≤ δs) :
    (μ.prod μS).real {x | ¬ success (p x.1) (outRule a (R x.2))} ≤
      exp (n * endpointPlus mp a (hA + ds) H c f τp vp bp) +
      exp (n * endpointMinus mm a (hA + ds) H c f τm vm bm) + δs := by
  set h := hA + ds
  set Bp := exp (n * endpointPlus mp a h H c f τp vp bp)
  set Bm := exp (n * endpointMinus mm a h H c f τm vm bm)
  have hh : 0 ≤ h := add_nonneg hhA hds
  have hplus : μ.real {ω | zplus a h Q < p ω} ≤ Bp :=
    Part203.tail_plus μ hp hp0 hp1 mp hmp hn hc hf hH hQ0 hQ1 ha hh
      hτp hvp0 hvp1 hbp hEp hCP
  have hminus : μ.real {ω | p ω < zminus a h Q ∧ 1 / 1000 < zminus a h Q} ≤ Bm := by
    by_cases hz : 1 / 1000 < zminus a h Q
    · exact (measureReal_mono (fun _ hω => hω.1)).trans
        (Part203.tail_minus μ hp hp0 hp1 mm hmm hn hc hf hH hQ0 hQ1 ha hh
          hτm hvm0 hvm1 hbm hside hEm hCP hz)
    · have he : {ω | p ω < zminus a h Q ∧ 1 / 1000 < zminus a h Q} = (∅ : Set Ω) := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun _ => hz
      rw [he, measureReal_empty]
      exact (exp_pos _).le
  have hincl : {x : Ω × ΩS | ¬ success (p x.1) (outRule a (R x.2))} ⊆
      ({ω | zplus a h Q < p ω} ×ˢ (univ : Set ΩS)) ∪
        ({ω | p ω < zminus a h Q ∧ 1 / 1000 < zminus a h Q} ×ˢ (univ : Set ΩS)) ∪
        ((univ : Set Ω) ×ˢ {σ | ds < |√(R σ) - √qt|}) := by
    rintro ⟨ω, σ⟩ hfail
    by_cases hs : ds < |√(R σ) - √qt|
    · exact Or.inr ⟨mem_univ _, hs⟩
    · apply Or.inl
      have hRQ : |√(R σ) - √Q| ≤ h := by
        have h1 := abs_sub_le (√(R σ)) (√qt) (√Q)
        have h2 : |√qt - √Q| ≤ hA := by simpa [abs_sub_comm] using hQq
        have h3 := not_lt.mp hs
        linarith
      rcases not_success (hp1 ω) (hR0 σ) ha hRQ hfail with h1 | h1
      · exact Or.inl ⟨h1.2, mem_univ _⟩
      · exact Or.inr ⟨⟨h1.2.1, h1.2.2⟩, mem_univ _⟩
  have hbound := (measureReal_mono (μ := μ.prod μS) hincl).trans
    ((measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _))
  rw [real_prod_left, real_prod_left, real_prod_right] at hbound
  exact hbound.trans (add_le_add (add_le_add hplus hminus) hsamp)

end Fibre
end BstLean.Part203
