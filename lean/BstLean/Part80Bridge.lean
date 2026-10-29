import BstLean.Part80Defs
import BstLean.Part78BridgeB
import BstLean.Part78Wick

/-!
# Part 80, wave 1: bridges (`TensBridge`, `RixIface`, `AnchorMom`)
-/

namespace BstLean.Part80

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU frob Tens TSymm fval contr trL glue)
open BstLean.Part53 (linZ TF fvA heatA sg)
open BstLean.Part78 (nsq frobH trH qfun aU zv sum_word0 sum_word1 sum_word2 contr1 contr2
  heat_pos heat_zero)

variable {n : ℕ}

/-- **Tensor form = `(f₀, ℓ, H)` form** at `d_f = 2`, and the heat form. -/
theorem tensBridge (n : ℕ) : TensBridge n := by
  classical
  intro f0 T hsym
  refine ⟨fun i => T 1 (fun _ => i), Matrix.of (fun i j => T 2 ![i, j]), ?_, ?_, ?_, ?_⟩
  · ext i j
    have h := hsym 2 (by norm_num) le_rfl (Equiv.swap 0 1) ![j, i]
    have e : (![j, i] ∘ (Equiv.swap (0 : Fin 2) 1)) = ![i, j] := by
      funext t; fin_cases t <;> simp
    rw [e] at h
    simpa using h.symm
  · intro y
    unfold fval qfun
    have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    rw [hI, Finset.sum_pair (by norm_num), contr1, contr2]
    simp [add_assoc]
  · unfold frob frobH
    rw [sum_word2]
    simp
  · intro a y
    unfold fvA qfun trH
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, contr1, contr2]
    unfold contr
    rw [sum_word0]
    simp only [heat_zero, heat_pos _ _ 1 (by norm_num) le_rfl, heat_pos _ _ 2 le_rfl (by norm_num)]
    simp [TF]
    ring

/-- The reindexing of the coefficient index as `Mono n 2 × Fin n`. -/
def rixEquiv (n : ℕ) : Mono n 2 × Fin n ≃ CoefIdxD n 2 where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun α := (⟨α.1, α.2.1⟩, α.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Reindexing** the coefficient array as `Mono n 2 × Fin n`. -/
theorem rixIface (n : ℕ) : RixIface n := by
  classical
  have hp := (measurePreserving_piCongrLeft
    (fun _ : CoefIdxD n 2 => gaussianReal 0 1) (rixEquiv n)).symm
  refine ⟨(MeasurableEquiv.piCongrLeft (fun _ : CoefIdxD n 2 => ℝ) (rixEquiv n)).symm,
    MeasurableEquiv.measurable _, hp.map_eq, ?_⟩
  intro W ψ i
  unfold linZ zv colM
  rfl

/-- **Second moment of `H u`**, `u = Z c` an anchor. -/
theorem anchorMom (n : ℕ) : AnchorMom n := by
  classical
  intro H c
  set b : Fin n → CoefIdxD n 2 → ℝ := fun i α => H i α.2.2 * c ⟨α.1, α.2.1⟩ with hb
  have hlin : ∀ (Z : CoefIdxD n 2 → ℝ) (i : Fin n),
      ∑ j, H i j * linZ Z c j = ∑ α, b i α * Z α := by
    intro Z i
    rw [← (rixEquiv n).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold linZ colM
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hb, rixEquiv, Equiv.coe_fn_mk]
    ring
  have hfun : (fun Z : CoefIdxD n 2 → ℝ => nsq (fun i => ∑ j, H i j * linZ Z c j)) =
      fun Z => ∑ i, (∑ α, b i α * Z α) * (∑ α, b i α * Z α) := by
    funext Z
    unfold nsq
    refine Finset.sum_congr rfl fun i _ => ?_
    show (∑ j, H i j * linZ Z c j) ^ 2 = _
    rw [hlin Z i, sq]
  have hint : ∀ i : Fin n, Integrable
      (fun Z : CoefIdxD n 2 → ℝ => (∑ α, b i α * Z α) * (∑ α, b i α * Z α))
      (stdGauss (CoefIdxD n 2)) := fun i => (BstLean.Part78.gaussLin _ (b i) (b i)).1
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i _ => hint i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hint i]
  unfold frobH
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(BstLean.Part78.gaussLin _ (b i) (b i)).2, ← (rixEquiv n).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [hb, rixEquiv, Equiv.coe_fn_mk]
  ring

end BstLean.Part80

#print axioms BstLean.Part80.tensBridge
#print axioms BstLean.Part80.rixIface
#print axioms BstLean.Part80.anchorMom
