import BstLean.Part78Defs
import BstLean.Part36Index
import BstLean.Part49Main

/-!
# Part 78, wave 1: the split of the coefficient vector (`SplitIface`) and the values of `𝒟`, `a`
(`DDval`)
-/

namespace BstLean.Part78

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD monoVal)
open BstLean.Part41 (Mono phiM colM)
open BstLean.Part53 (aH c0)

variable {n : ℕ}

/-- The constant column and the rest, as an equivalence of index types. -/
def splitEquiv (n : ℕ) : Fin n ⊕ WIdx n ≃ CoefIdxD n 2 where
  toFun := Sum.elim (fun i => ⟨0, (Sym.nil, i)⟩) (fun p => ⟨p.1.1.1, (p.1.1.2, p.2)⟩)
  invFun α := if h : (⟨α.1, α.2.1⟩ : Mono n 2) = default then Sum.inl α.2.2
    else Sum.inr (⟨⟨α.1, α.2.1⟩, h⟩, α.2.2)
  left_inv a := by
    rcases a with i | ⟨⟨q, hq⟩, i⟩
    · have h : (⟨0, Sym.nil⟩ : Mono n 2) = default := rfl
      simp [h]
    · simp [hq]
  right_inv α := by
    obtain ⟨i, β, p⟩ := α
    by_cases h : (⟨i, β⟩ : Mono n 2) = default
    · simp only [h, dite_true, Sum.elim_inl]
      have h' : (⟨i, β⟩ : Mono n 2) = ⟨0, Sym.nil⟩ := h
      cases h'
      rfl
    · simp [h]

/-- The split as a measurable equivalence. -/
noncomputable def combEquiv (n : ℕ) :
    ((Fin n → ℝ) × (WIdx n → ℝ)) ≃ᵐ (CoefIdxD n 2 → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ WIdx n => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : CoefIdxD n 2 => ℝ) (splitEquiv n))

lemma combEquiv_apply (p : (Fin n → ℝ) × (WIdx n → ℝ)) (α : CoefIdxD n 2) :
    combEquiv n p α = Sum.elim p.1 p.2 ((splitEquiv n).symm α) := by
  simp [combEquiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  cases (splitEquiv n).symm α <;> rfl

lemma combEquiv_inl (u : Fin n → ℝ) (W : WIdx n → ℝ) (i : Fin n) :
    combEquiv n (u, W) ⟨0, (Sym.nil, i)⟩ = u i := by
  have h : (⟨0, (Sym.nil, i)⟩ : CoefIdxD n 2) = splitEquiv n (Sum.inl i) := rfl
  rw [combEquiv_apply, h, Equiv.symm_apply_apply]
  rfl

lemma combEquiv_inr (u : Fin n → ℝ) (W : WIdx n → ℝ) (q : JJ n) (i : Fin n) :
    combEquiv n (u, W) ⟨q.1.1, (q.1.2, i)⟩ = W (q, i) := by
  have h : (⟨q.1.1, (q.1.2, i)⟩ : CoefIdxD n 2) = splitEquiv n (Sum.inr (q, i)) := rfl
  rw [combEquiv_apply, h, Equiv.symm_apply_apply]
  rfl

lemma combEquiv_preserving : MeasurePreserving (combEquiv n)
    ((stdGauss (Fin n)).prod (stdGauss (WIdx n))) (stdGauss (CoefIdxD n 2)) := by
  exact (measurePreserving_piCongrLeft
    (fun _ : CoefIdxD n 2 => gaussianReal 0 1) (splitEquiv n)).comp
    (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin n ⊕ WIdx n => gaussianReal 0 1))

/-- **The split** of the Gaussian coefficient vector. -/
theorem splitIface (n : ℕ) : SplitIface n := by
  classical
  refine ⟨combEquiv n, (combEquiv n).measurable, combEquiv_preserving.map_eq, ?_⟩
  intro u W
  refine ⟨?_, ?_, ?_⟩
  · funext i
    exact combEquiv_inl u W i
  · intro x i
    rw [BstLean.Part49.mapMD_eq]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (default : Mono n 2))]
    congr 1
    · have h1 : phiM x (default : Mono n 2) = 1 := by
        show monoVal x (Sym.nil : Sym (Fin n) 0).1 = 1
        simp [monoVal]
      rw [h1, mul_one]
      exact combEquiv_inl u W i
    · unfold zv pf
      have hs : (Finset.univ.erase (default : Mono n 2)) =
          Finset.univ.filter (fun q : Mono n 2 => q ≠ default) := by
        ext q; simp
      rw [hs, ← Finset.sum_subtype_eq_sum_filter (p := fun q : Mono n 2 => q ≠ default)]
      apply Finset.sum_congr
      · ext q; simp
      · intro q _
        rw [combEquiv_inr u W q i]
  · rw [← (splitEquiv n).sum_comp, Fintype.sum_sum_type]
    have h1 : ∀ i : Fin n, combEquiv n (u, W) (splitEquiv n (Sum.inl i)) = u i :=
      fun i => combEquiv_inl u W i
    have h2 : ∀ β : WIdx n, combEquiv n (u, W) (splitEquiv n (Sum.inr β)) = W β :=
      fun β => combEquiv_inr u W β.1 β.2
    simp only [h1, h2]

/-- The values of `𝒟` and `a` at `d = 2`. -/
theorem ddval (n : ℕ) : DDval n := by
  have hD : DD n 2 = (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
    rw [BstLean.Part36.DD_eq, Nat.cast_choose_two]
    push_cast
    ring
  refine ⟨hD, ?_⟩
  unfold aH c0
  simp [Finset.sum_range_succ, Nat.factorial]
  norm_num

end BstLean.Part78

#print axioms BstLean.Part78.splitIface
#print axioms BstLean.Part78.ddval
