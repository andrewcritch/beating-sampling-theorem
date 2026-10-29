import BstLean.Part238Final
import BstLean.Part193Cover

/-! Part 238: overlap-cell selection for the three-mode TI hypothesis.
A deterministic cover selects one fixed-pair statement before the weights are drawn;
there is no union charge over the cells. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part182
open BstLean.Part153 (nrm nuA)
open BstLean.Part151 (jac)

/-- Larger constants and a larger cap weaken the mode bounds. -/
theorem modeBounds_mono {m n : ℕ} {J J' : Matrix (Fin m) (Fin n) ℝ} {x x' : Fin n → ℝ}
    {kE ko ks cp kE' ko' ks' cp' : ℝ} (hE : kE ≤ kE') (ho : ko ≤ ko') (hs : ks ≤ ks')
    (hcp0 : 0 ≤ cp) (hcp : cp ≤ cp')
    (h : ModeBounds J J' kE ko ks cp x x') : ModeBounds J J' kE' ko' ks' cp' x x' := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.trans (pow_le_pow_left₀ hcp0 hcp 2), h2.trans (mul_le_mul_of_nonneg_left hE hn),
    h3.trans (mul_le_mul_of_nonneg_left ho hn), h4.trans (mul_le_mul_of_nonneg_left ho hn),
    h5.trans (mul_le_mul_of_nonneg_left hs hn)⟩

/-- **Cell selection for `TI3_hyp`.** Local three-mode statements on the cells of a finite cover
of `[lo, cp]` give one global statement with the largest constants and the largest charge. -/
theorem TI3_of_cover {n : ℕ} {lo cp kE ko ks δ : ℝ} {ι : Type*}
    (cover : BstLean.Part193.FiniteCover ℝ ι (Set.Icc lo cp))
    (loC hiC kEC koC ksC δC : ι → ℝ)
    (local_hyp : ∀ i ∈ cover.indices, TI3_hyp n (loC i) (hiC i) (kEC i) (koC i) (ksC i) (δC i))
    (contains : ∀ i ∈ cover.indices, ∀ c ∈ Set.Icc lo cp, c ∈ cover.cell i →
      loC i ≤ c ∧ c ≤ hiC i)
    (hhi : ∀ i ∈ cover.indices, 0 ≤ hiC i ∧ hiC i ≤ cp)
    (hk : ∀ i ∈ cover.indices, kEC i ≤ kE ∧ koC i ≤ ko ∧ ksC i ≤ ks)
    (hδ : ∀ i ∈ cover.indices, δC i ≤ δ) :
    TI3_hyp n lo cp kE ko ks δ := by
  intro x x' hx hx' hlo hhi'
  obtain ⟨i, hi, hcell⟩ := cover.covers (x ⬝ᵥ x') ⟨hlo, hhi'⟩
  obtain ⟨hl, hu⟩ := contains i hi _ ⟨hlo, hhi'⟩ hcell
  obtain ⟨h0, hcp⟩ := hhi i hi
  obtain ⟨hE, ho, hs⟩ := hk i hi
  haveI : IsProbabilityMeasure (nuA n) := by
    unfold nuA BstLean.Part130.gaussMat; infer_instance
  refine (measureReal_mono (fun θ hθ => ?_) (measure_ne_top _ _)).trans
    ((local_hyp i hi x x' hx hx' hl hu).trans (hδ i hi))
  exact fun hloc => hθ (modeBounds_mono hE ho hs h0 hcp hloc)

end BstLean.Part238
