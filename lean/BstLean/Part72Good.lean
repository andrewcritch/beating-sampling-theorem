import BstLean.Part72Iface
import BstLean.Part71Error

/-!
# Part 72: the moment conditions of the Theorem 4 chain

Source: `delegations/answers/omOV-cx-disprover.md` §5–§6 and `omOV-opus-prover.md` §2, §5.
Specification: `delegations/statements/p72-spec.md`.

* `featDev μ c = frob(E_μ φ^{⊗c} − e₀^{⊗c})`: the main-term tensor of Prop E.
* `Good72 n d k μ w F Em`: the four inputs of the chain. Sphere support; the trace moments
  `E_μ δ°^{2i} ≤ w(i)·d^{2i}/n^{2i}` only for `1 ≤ i`, `2i ≤ k`; the main-term tensors
  `featDev μ c ≤ F(c)/n` for `1 ≤ c ≤ k`; the coordinate mean `Σ_i (E_μ x_i)² ≤ Em/n`.
* `MomCtl n μ d k w A E`: the specification's form, with the feature-operator inequality
  `FeatOp n d μ A` (`E_μ (a·φ)² ≤ A·((d+1)/n)‖a‖²` for `a₀ = 0`) in place of the tensor bounds.
  `momCtl_good` turns it into `Good72` with `F(c) = (4(d+1))^c·A·(d+1)`.
* `wExt`: an extension of a weight given for `2i ≤ k` to a weight for every `i`, so that the
  Part 71 lemmas that take the full `DevW` apply unchanged (the extension only changes indices
  that the correction sums never use).

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory
open BstLean.Part71
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM phiSq frob)
open BstLean.Part53 (c0 error53_e0)

variable {n d : ℕ}

/-- The main-term tensor `frob(E_μ φ^{⊗c} − e₀^{⊗c})`. -/
noncomputable def featDev (d : ℕ) (μ : Measure (Fin n → ℝ)) (c : ℕ) : ℝ :=
  frob (fun p : Fin c → Mono n d => (∫ x, ∏ t, phiM x (p t) ∂μ) - ∏ t, error53_e0 (p t))

/-- **The moment conditions of the chain.** -/
structure Good72 (n d k : ℕ) (μ : Measure (Fin n → ℝ)) (w F : ℕ → ℝ) (Em : ℝ) : Prop where
  sph : SphLaw n μ
  dev : ∀ i : ℕ, 1 ≤ i → 2 * i ≤ k →
    (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤ w i * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i)
  feat : ∀ c : ℕ, 1 ≤ c → c ≤ k → featDev d μ c ≤ F c / n
  mean : ∑ i : Fin n, (∫ x, x i ∂μ) ^ 2 ≤ Em / n

/-- **The specification's moment conditions** (P1 restricted to `2i ≤ k`, P2 as an operator
inequality, the coordinate mean). -/
def MomCtl (n : ℕ) (μ : Measure (Fin n → ℝ)) (d k : ℕ) (w : ℕ → ℝ) (A E : ℝ) : Prop :=
  SphLaw n μ ∧
  (∀ i : ℕ, 1 ≤ i → 2 * i ≤ k →
    (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤ w i * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i)) ∧
  FeatOp n d μ A ∧
  ∑ i : Fin n, (∫ x, x i ∂μ) ^ 2 ≤ E / n

/-- The tensor constant that `FeatOp` with weight `A` gives. -/
noncomputable def Fop (d : ℕ) (A : ℝ) (c : ℕ) : ℝ := (4 * ((d : ℝ) + 1)) ^ c * (A * ((d : ℝ) + 1))

lemma momCtl_good (hn : 1 ≤ n) (hd : 1 ≤ d) {k : ℕ} {μ : Measure (Fin n → ℝ)} {w : ℕ → ℝ}
    {A E : ℝ} (hA : 0 < A) (h : MomCtl n μ d k w A E) : Good72 n d k μ w (Fop d A) E := by
  obtain ⟨hs, hdev, hop, hm⟩ := h
  refine ⟨hs, hdev, ?_, hm⟩
  intro c _ _
  have := feature_tensor71 hn hd hs hA hop c
  unfold featDev Fop
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by ring)))
  rfl

/-! ## Extending a weight given for `2i ≤ k` -/

/-- The extended weight: `w i` for `2i ≤ k`, and the exact normalized moment otherwise. -/
noncomputable def wExt (n d k : ℕ) (μ : Measure (Fin n → ℝ)) (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  if 2 * i ≤ k then w i else
    (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) * (n : ℝ) ^ (2 * i) / (d : ℝ) ^ (2 * i)

lemma wExt_nonneg {k : ℕ} {μ : Measure (Fin n → ℝ)} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (i : ℕ) :
    0 ≤ wExt n d k μ w i := by
  unfold wExt
  split_ifs
  · exact hw i
  · have : 0 ≤ ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ := by
      apply integral_nonneg
      intro x
      simp only [Pi.zero_apply]
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    positivity

lemma devW_ext (hn : 1 ≤ n) (hd : 1 ≤ d) {k : ℕ} {μ : Measure (Fin n → ℝ)} {w F : ℕ → ℝ}
    {Em : ℝ} (h : Good72 n d k μ w F Em) : DevW n d μ (wExt n d k μ w) := by
  intro i hi
  unfold wExt
  split_ifs with hk
  · exact h.dev i hi hk
  · have hn0 : (0 : ℝ) < (n : ℝ) ^ (2 * i) := by
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    have hd0 : (0 : ℝ) < (d : ℝ) ^ (2 * i) := by
      have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      positivity
    rw [le_div_iff₀ hn0]
    field_simp
    exact le_refl _

lemma corrW_ext {k c i : ℕ} (μ : Measure (Fin n → ℝ)) (w : ℕ → ℝ) (h : c + 2 * i ≤ k) :
    corrW d c i (wExt n d k μ w) = corrW d c i w := by
  unfold corrW wExt
  rw [if_pos (by omega)]

lemma corrSum_ext (k c : ℕ) (μ : Measure (Fin n → ℝ)) (w : ℕ → ℝ) :
    (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k), corrW d c i (wExt n d k μ w)) =
      ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k), corrW d c i w :=
  Finset.sum_congr rfl (fun i hi => corrW_ext μ w (Finset.mem_filter.mp hi).2)

lemma totW_ext (k : ℕ) (s : Finset ℕ) (μ : Measure (Fin n → ℝ)) (w : ℕ → ℝ) :
    totW d k s (wExt n d k μ w) = totW d k s w := by
  unfold totW
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i hi
  exact corrW_ext μ w (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2

/-- The class of distributions with the moment conditions `Good72 · d k · w F Em`. -/
def GoodClass (d k : ℕ) (w F : ℕ → ℝ) (Em : ℝ) : DistClass :=
  fun n μ => Good72 n d k μ w F Em

lemma goodClass_sph (d k : ℕ) (w F : ℕ → ℝ) (Em : ℝ) : SphClass (GoodClass d k w F Em) :=
  fun _ _ h => h.sph

end BstLean.Part72
