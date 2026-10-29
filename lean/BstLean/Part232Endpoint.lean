import BstLean.Part232Integration

/-! Part 232: complete END certificates supply finite-cell payments. -/
namespace BstLean.Part232
open MeasureTheory Real Set BstLean.Part156 BstLean.Part203

/-- Every root, sign and exponent guard belongs to the selected certificate. -/
structure EndCertificate (n c f a h H : ℝ) where
  plus : LogChoice
  minus : LogChoice
  plus_valid : plus.Valid
  minus_valid : minus.Valid
  τp : ℝ
  τm : ℝ
  vp : ℝ
  vm : ℝ
  bp : ℝ
  bm : ℝ
  τp_pos : 0 < τp
  τm_neg : τm < 0
  vp_nonneg : 0 ≤ vp
  vp_le_one : vp ≤ 1
  vm_nonneg : 0 ≤ vm
  vm_le_one : vm ≤ 1
  bp_pos : 0 < bp
  bm_pos : 0 < bm
  root_guard : 2 * h + 2 * H / bm < √(1 / 100 / a)
  plus_nonpos : endpointPlus plus a h H c f τp vp bp ≤ 0
  minus_nonpos : endpointMinus minus a h H c f τm vm bm ≤ 0

noncomputable def EndCertificate.payment {n c f a h H : ℝ}
    (e : EndCertificate n c f a h H) : ℝ :=
  min 1 (exp (n * endpointPlus e.plus a h H c f e.τp e.vp e.bp) +
    exp (n * endpointMinus e.minus a h H c f e.τm e.vm e.bm))

lemma EndCertificate.payment_nonneg {n c f a h H : ℝ}
    (e : EndCertificate n c f a h H) : 0 ≤ e.payment :=
  le_min (by norm_num) (add_nonneg (exp_pos _).le (exp_pos _).le)

section Endpoint
variable {Ω ΩS : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩS]

/-- Certified END bounds failure intersected with sampling success, without a draw payment. -/
theorem endpoint_sampling_success (μ : Measure Ω) (μS : Measure ΩS)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μS]
    {p : Ω → ℝ} (hp : Measurable p) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1)
    {R : ΩS → ℝ} (hR0 : ∀ σ, 0 ≤ R σ)
    {n c f H Q a hA ds qt : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hf : 0 < f) (hH : 0 ≤ H)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (ha : 0 < a) (hhA : 0 ≤ hA) (hds : 0 ≤ ds)
    (e : EndCertificate n c f a (hA + ds) H)
    (hCP : FreeCPR μ p n c f H Q) (hQq : |√Q - √qt| ≤ hA) :
    (μ.prod μS).real {x | ¬ success (p x.1) (outRule a (R x.2)) ∧
      |√(R x.2) - √qt| ≤ ds} ≤ e.payment := by
  have hplus := tail_plus μ hp hp0 hp1 e.plus e.plus_valid hn hc hf hH hQ0 hQ1
    ha (add_nonneg hhA hds) e.τp_pos e.vp_nonneg e.vp_le_one e.bp_pos e.plus_nonpos hCP
  have hminus : μ.real {ω | p ω < zminus a (hA + ds) Q ∧
      1 / 1000 < zminus a (hA + ds) Q} ≤
      exp (n * endpointMinus e.minus a (hA + ds) H c f e.τm e.vm e.bm) := by
    by_cases hz : 1 / 1000 < zminus a (hA + ds) Q
    · exact (measureReal_mono (fun _ hω => hω.1)).trans
        (tail_minus μ hp hp0 hp1 e.minus e.minus_valid hn hc hf hH hQ0 hQ1 ha
          (add_nonneg hhA hds) e.τm_neg e.vm_nonneg e.vm_le_one e.bm_pos
          e.root_guard e.minus_nonpos hCP hz)
    · have he : {ω | p ω < zminus a (hA + ds) Q ∧
          1 / 1000 < zminus a (hA + ds) Q} = (∅ : Set Ω) := by
        ext ω
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun _ => hz
      rw [he, measureReal_empty]
      exact (exp_pos _).le
  exact le_min measureReal_le_one
    (failure_on_sampling_success μ μS hp1 hR0 ha hQq hplus hminus)

/-- Absence of a complete certificate gives the fallback payment one. -/
noncomputable def cellPayment {n c f a h H : ℝ}
    (e : Option (EndCertificate n c f a h H)) : ℝ :=
  match e with
  | none => 1
  | some e => e.payment

lemma cellPayment_nonneg {n c f a h H : ℝ}
    (e : Option (EndCertificate n c f a h H)) : 0 ≤ cellPayment e := by
  cases e with
  | none => norm_num [cellPayment]
  | some e => exact e.payment_nonneg

end Endpoint
end BstLean.Part232
