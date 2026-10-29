import BstLean.Part151Inputs

/-!
# Part 151, glue: from a family of `A`-stage events indexed by the stand-in input `(c, τ)` to an
event `X12` of `(W, (A₁, A₂))`

Role: `delegations/statements/p151-spec.md` (the frame). The `A`-stage events of the other Parts
are events of `(A₁, A₂)` for a fixed stand-in input `(c, τ)`, with a probability bound for every
`(c, τ)` with `τ > 0`. In the program `c = cenA W`, `τ = tauWA W`, and `W` is independent of
`(A₁, A₂)`. Here:

* `prod_fst_real`, `triple_W_real`, `triple_WA12_real`: the marginal facts.
* `wBadW151`, `wBadWA151`: `Pr(W not in the good hidden event of Part 145) ≤ 1/n` for the
  distribution of `W` alone and of `(W, (A₁, A₂))`.
* `tauWA_pos_of_good`: `0 < tauWA W` on the good hidden event.
* `X12fam`, `X12famW`: the events; **`X12_of_family`**, **`X12_of_family_window`**: they are
  measurable, `Pr(X12ᶜ) ≤ 1/n + p` (resp. `1/n + p_W + p`), and `0 < tauWA` on them.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143 BstLean.Part145
open BstLean.Part149 BstLean.Part150

variable {n : ℕ}

/-- The probability of an event of the first coordinate, for a product with a probability
measure. No measurability is needed. -/
lemma prod_fst_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite ν] [IsProbabilityMeasure ν] (E : Set α) :
    (μ.prod ν).real {x | x.1 ∈ E} = μ.real E := by
  have e : {x : α × β | x.1 ∈ E} = E ×ˢ (univ : Set β) := by
    ext x; simp
  rw [e, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ, mul_one]

/-- The `mlpTriple`-probability of an event of `W` is its `mlpGauss`-probability. -/
lemma triple_W_real (E : Set (MlpParam (2 * n) (mW n) n)) :
    (mlpTriple 2 n).real {t | t.1 ∈ E} = (mlpGauss (2 * n) (mW n) n).real E := by
  unfold mlpTriple
  exact prod_fst_real _ _ E

/-- `Pr(W not in the good hidden event of Part 145) ≤ 1/n`, for the distribution of `W` alone. -/
theorem wBadW151 (hn : 4096 ≤ n) :
    (mlpGauss (2 * n) (mW n) n).real (goodWAG (Gwin n))ᶜ ≤ 1 / (n : ℝ) := by
  have h := wBad151 hn
  have e := triple_W_real (n := n) (goodWAG (Gwin n))ᶜ
  have e2 : {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∈ (goodWAG (Gwin n))ᶜ} = {t | t.1 ∉ goodWAG (Gwin n)} := rfl
  rw [e2] at e
  rw [← e]
  exact h

/-- The same for the distribution of `(W, (A₁, A₂))`. -/
theorem wBadWA151 (hn : 4096 ≤ n) :
    ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real
      {x | x.1 ∉ goodWAG (Gwin n)} ≤ 1 / (n : ℝ) := by
  have e := prod_fst_real (mlpGauss (2 * n) (mW n) n) (hidGauss n (mA n)) (goodWAG (Gwin n))ᶜ
  have e2 : {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) |
      x.1 ∈ (goodWAG (Gwin n))ᶜ} = {x | x.1 ∉ goodWAG (Gwin n)} := rfl
  rw [e2] at e
  rw [e]
  exact wBadW151 hn

/-- On the good hidden event of `W` the stand-in noise scale is positive. -/
lemma tauWA_pos_of_good (hn : 4096 ≤ n) {W : MlpParam (2 * n) (mW n) n}
    (hW : W ∈ goodWAG (Gwin n)) : 0 < tauWA W :=
  (winOK2_149 hn (W.1, W.2.1) hW).2.1

/-- The event of `(W, (A₁, A₂))` made from a family `S` of events of `(A₁, A₂)` indexed by the
stand-in input `(c, τ)`: `W` is in the good hidden event and `(A₁, A₂)` is in the event of the
family at `(c, τ) = (cenA W, tauWA W)`. -/
def X12fam (n : ℕ) (S : Set (((Fin n → ℝ) × ℝ) × HidParam n (mA n))) :
    Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
  {x | x.1 ∈ goodWAG (Gwin n) ∧ ((cenA x.1, tauWA x.1), x.2) ∈ S}

/-- The same, intersected with the event that `(cenA W, tauWA W)` is in a set `Wd` of good
windows. -/
def X12famW (n : ℕ) (Wd : Set ((Fin n → ℝ) × ℝ))
    (S : Set (((Fin n → ℝ) × ℝ) × HidParam n (mA n))) :
    Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
  X12fam n S ∩ {x | (cenA x.1, tauWA x.1) ∈ Wd}

lemma measurable_cenTau :
    Measurable (fun W : MlpParam (2 * n) (mW n) n => (cenA W, tauWA W)) :=
  measurable_cenA.prodMk measurable_tauWA

lemma X12fam_meas (hn : 4096 ≤ n) {S : Set (((Fin n → ℝ) × ℝ) × HidParam n (mA n))}
    (hS : MeasurableSet S) : MeasurableSet (X12fam n S) := by
  have hG := goodWAG0_meas (goodEvFR hn).to0 (show 1 ≤ n by omega)
  have hf : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      ((cenA x.1, tauWA x.1), x.2)) :=
    (measurable_cenTau.comp measurable_fst).prodMk measurable_snd
  exact (measurable_fst hG).inter (hf hS)

lemma X12famW_meas (hn : 4096 ≤ n) {Wd : Set ((Fin n → ℝ) × ℝ)} (hWd : MeasurableSet Wd)
    {S : Set (((Fin n → ℝ) × ℝ) × HidParam n (mA n))}
    (hS : MeasurableSet S) : MeasurableSet (X12famW n Wd S) :=
  (X12fam_meas hn hS).inter ((measurable_cenTau.comp measurable_fst) hWd)

/-- **The glue lemma with a set of good windows.** If, for every stand-in input `(c, τ)` with
`τ > 0` in the measurable set `Wd`, the event of the family fails with probability at most `p`
over `(A₁, A₂)`, and `(cenA W, tauWA W) ∉ Wd` has probability at most `p_W` over `W`, then the
event `X12famW n Wd S` of `(W, (A₁, A₂))` is measurable, fails with probability at most
`1/n + p_W + p`, and `0 < tauWA W` and `(cenA W, tauWA W) ∈ Wd` on it. -/
theorem X12_of_family_window (hn : 4096 ≤ n) {Wd : Set ((Fin n → ℝ) × ℝ)}
    (hWd : MeasurableSet Wd) {S : Set (((Fin n → ℝ) × ℝ) × HidParam n (mA n))}
    (hS : MeasurableSet S) {p pW : ℝ} (hp : 0 ≤ p)
    (hfam : ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ → (c, τ) ∈ Wd →
      (hidGauss n (mA n)).real {θ | ((c, τ), θ) ∉ S} ≤ p)
    (hW : (mlpGauss (2 * n) (mW n) n).real {W | (cenA W, tauWA W) ∉ Wd} ≤ pW) :
    MeasurableSet (X12famW n Wd S) ∧
    ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real (X12famW n Wd S)ᶜ ≤
      1 / (n : ℝ) + pW + p ∧
    (∀ x ∈ X12famW n Wd S, 0 < tauWA x.1) ∧
    (∀ x ∈ X12famW n Wd S, (cenA x.1, tauWA x.1) ∈ Wd) := by
  refine ⟨X12famW_meas hn hWd hS, ?_, fun x hx => tauWA_pos_of_good hn hx.1.1, fun x hx => hx.2⟩
  set μ := mlpGauss (2 * n) (mW n) n with hμ
  set ν := hidGauss n (mA n) with hν
  have hG := goodWAG0_meas (goodEvFR hn).to0 (show 1 ≤ n by omega)
  have hf : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      ((cenA x.1, tauWA x.1), x.2)) :=
    (measurable_cenTau.comp measurable_fst).prodMk measurable_snd
  -- the third bad event
  set T : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) :=
    {x | (x.1 ∈ goodWAG (Gwin n) ∧ (cenA x.1, tauWA x.1) ∈ Wd) ∧
      ((cenA x.1, tauWA x.1), x.2) ∉ S} with hT
  have hTm : MeasurableSet T :=
    ((measurable_fst hG).inter ((measurable_cenTau.comp measurable_fst) hWd)).inter
      (hf hS).compl
  have hTp : (μ.prod ν).real T ≤ p := by
    have h1 : (μ.prod ν) T ≤ ENNReal.ofReal p := by
      rw [Measure.prod_apply hTm]
      calc ∫⁻ W, ν (Prod.mk W ⁻¹' T) ∂μ ≤ ∫⁻ _, ENNReal.ofReal p ∂μ := by
            refine lintegral_mono fun W => ?_
            by_cases hg : W ∈ goodWAG (Gwin n) ∧ (cenA W, tauWA W) ∈ Wd
            · have hsub : Prod.mk W ⁻¹' T ⊆ {θ | ((cenA W, tauWA W), θ) ∉ S} :=
                fun θ hθ => hθ.2
              refine (measure_mono hsub).trans ?_
              have h := hfam (cenA W) (tauWA W) (tauWA_pos_of_good hn hg.1) hg.2
              rw [measureReal_def] at h
              exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hp).mpr h
            · have he : Prod.mk W ⁻¹' T = ∅ := by
                ext θ
                simp only [mem_preimage, mem_empty_iff_false, iff_false]
                exact fun hθ => hg hθ.1
              rw [he, measure_empty]
              exact zero_le
        _ = ENNReal.ofReal p := by rw [lintegral_const, measure_univ, mul_one]
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hp h1
  have hsub : (X12famW n Wd S)ᶜ ⊆
      ({x | x.1 ∉ goodWAG (Gwin n)} ∪ {x | x.1 ∈ {W | (cenA W, tauWA W) ∉ Wd}}) ∪ T := by
    intro x hx
    by_cases h1 : x.1 ∈ goodWAG (Gwin n)
    swap
    · exact Or.inl (Or.inl h1)
    by_cases h2 : (cenA x.1, tauWA x.1) ∈ Wd
    swap
    · exact Or.inl (Or.inr h2)
    refine Or.inr ⟨⟨h1, h2⟩, fun h3 => hx ⟨⟨h1, h3⟩, h2⟩⟩
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  have hu := measureReal_union_le (μ := μ.prod ν)
    {x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) | x.1 ∉ goodWAG (Gwin n)}
    {x | x.1 ∈ {W | (cenA W, tauWA W) ∉ Wd}}
  have h1 := wBadWA151 hn
  have h2 := prod_fst_real μ ν {W | (cenA W, tauWA W) ∉ Wd}
  linarith

/-- **The glue lemma.** If, for every stand-in input `(c, τ)` with `τ > 0`, the event of the
family fails with probability at most `p` over `(A₁, A₂)`, then the event `X12fam n S` of
`(W, (A₁, A₂))` is measurable, fails with probability at most `1/n + p`, and `0 < tauWA W` on
it. -/
theorem X12_of_family (hn : 4096 ≤ n) {S : Set (((Fin n → ℝ) × ℝ) × HidParam n (mA n))}
    (hS : MeasurableSet S) {p : ℝ} (hp : 0 ≤ p)
    (hfam : ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ →
      (hidGauss n (mA n)).real {θ | ((c, τ), θ) ∉ S} ≤ p) :
    MeasurableSet (X12fam n S) ∧
    ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real (X12fam n S)ᶜ ≤
      1 / (n : ℝ) + p ∧
    (∀ x ∈ X12fam n S, 0 < tauWA x.1) := by
  have h := X12_of_family_window hn (Wd := univ) MeasurableSet.univ hS (pW := 0) hp
    (fun c τ hτ _ => hfam c τ hτ) (by simp)
  have e : X12famW n univ S = X12fam n S := by
    unfold X12famW; simp
  rw [e] at h
  refine ⟨h.1, ?_, h.2.2.1⟩
  have := h.2.1
  linarith

/-- The `mlpTriple`-probability of an event of `(W, (A₁, A₂))` is its probability for the
product of the distribution of `W` and the distribution of the hidden layers of `A`. -/
lemma triple_WA12_real {E : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (hE : MeasurableSet E) :
    (mlpTriple 2 n).real {t | (t.1, (t.2.1.1, t.2.1.2.1)) ∈ E} =
      ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real E := by
  set g : MlpParam n (mA n) n × MlpParam n (mF n) 1 → HidParam n (mA n) :=
    fun q => (q.1.1, q.1.2.1) with hg
  have hgm : Measurable g :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).comp measurable_fst)
  have hmap : ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)).map g = hidGauss n (mA n) := by
    ext B hB
    rw [Measure.map_apply hgm hB]
    have e : g ⁻¹' B = {q : MlpParam n (mA n) n × MlpParam n (mF n) 1 |
        q.1 ∈ {a : MlpParam n (mA n) n | (a.1, a.2.1) ∈ B}} := rfl
    have h1 := prod_fst_real (mlpGauss n (mA n) n) (mlpGauss n (mF n) 1)
      {a : MlpParam n (mA n) n | (a.1, a.2.1) ∈ B}
    have h2 : (mlpGauss n (mA n) n) {a : MlpParam n (mA n) n | (a.1, a.2.1) ∈ B} =
        hidGauss n (mA n) B := by
      unfold mlpGauss hidGauss
      have e3 : {a : MlpParam n (mA n) n | (a.1, a.2.1) ∈ B} =
          (MeasurableEquiv.prodAssoc (α := Matrix (Fin (mA n)) (Fin n) ℝ)
            (β := Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
            (γ := Matrix (Fin n) (Fin (mA n)) ℝ)) '' (B ×ˢ univ) := by
        ext a
        constructor
        · intro ha
          exact ⟨((a.1, a.2.1), a.2.2), ⟨ha, mem_univ _⟩, rfl⟩
        · rintro ⟨b, hb, rfl⟩
          exact hb.1
      rw [e3, ← Measure.prodAssoc_prod, MeasurableEquiv.map_apply,
        MeasurableEquiv.preimage_image, Measure.prod_prod, measure_univ, mul_one]
    rw [e]
    rw [measureReal_def, measureReal_def, h2] at h1
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h1
  unfold mlpTriple
  rw [← hmap, ← Measure.map_id (μ := mlpGauss (2 * n) (mW n) n)]
  rw [Measure.map_prod_map _ _ measurable_id hgm, Measure.map_id]
  rw [measureReal_def, measureReal_def, Measure.map_apply (measurable_id.prodMap hgm) hE]
  rfl

end BstLean.Part151
