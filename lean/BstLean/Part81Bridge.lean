import BstLean.Part81Defs
import BstLean.Part78Final

/-!
# Part 81, bridge: the split of the coefficient vector, the coefficient bridge, the radius tail,
the values of `𝒟`, and the program, at `d_f = 2` and every map degree `d`
-/

namespace BstLean.Part81.Br

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD monoVal)
open BstLean.Part41 (Mono phiM colM)
open BstLean.Part53 (aH c0)
open BstLean.Part78 (zv)
open BstLean.Part81

variable {n d : ℕ}

/-- The constant column and the rest, as an equivalence of index types. -/
def splitEquiv (n d : ℕ) : Fin n ⊕ WIdx n d ≃ CoefIdxD n d where
  toFun := Sum.elim (fun i => ⟨0, (Sym.nil, i)⟩) (fun p => ⟨p.1.1.1, (p.1.1.2, p.2)⟩)
  invFun α := if h : (⟨α.1, α.2.1⟩ : Mono n d) = default then Sum.inl α.2.2
    else Sum.inr (⟨⟨α.1, α.2.1⟩, h⟩, α.2.2)
  left_inv a := by
    rcases a with i | ⟨⟨q, hq⟩, i⟩
    · have h : (⟨0, Sym.nil⟩ : Mono n d) = default := rfl
      simp [h]
    · simp [hq]
  right_inv α := by
    obtain ⟨i, β, p⟩ := α
    by_cases h : (⟨i, β⟩ : Mono n d) = default
    · simp only [h, dite_true, Sum.elim_inl]
      have h' : (⟨i, β⟩ : Mono n d) = ⟨0, Sym.nil⟩ := h
      cases h'
      rfl
    · simp [h]

/-- The split as a measurable equivalence. -/
noncomputable def combEquiv (n d : ℕ) :
    ((Fin n → ℝ) × (WIdx n d → ℝ)) ≃ᵐ (CoefIdxD n d → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ WIdx n d => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : CoefIdxD n d => ℝ) (splitEquiv n d))

lemma combEquiv_apply (p : (Fin n → ℝ) × (WIdx n d → ℝ)) (α : CoefIdxD n d) :
    combEquiv n d p α = Sum.elim p.1 p.2 ((splitEquiv n d).symm α) := by
  simp [combEquiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  cases (splitEquiv n d).symm α <;> rfl

lemma combEquiv_inl (u : Fin n → ℝ) (W : WIdx n d → ℝ) (i : Fin n) :
    combEquiv n d (u, W) ⟨0, (Sym.nil, i)⟩ = u i := by
  have h : (⟨0, (Sym.nil, i)⟩ : CoefIdxD n d) = splitEquiv n d (Sum.inl i) := rfl
  rw [combEquiv_apply, h, Equiv.symm_apply_apply]
  rfl

lemma combEquiv_inr (u : Fin n → ℝ) (W : WIdx n d → ℝ) (q : JJ n d) (i : Fin n) :
    combEquiv n d (u, W) ⟨q.1.1, (q.1.2, i)⟩ = W (q, i) := by
  have h : (⟨q.1.1, (q.1.2, i)⟩ : CoefIdxD n d) = splitEquiv n d (Sum.inr (q, i)) := rfl
  rw [combEquiv_apply, h, Equiv.symm_apply_apply]
  rfl

lemma combEquiv_preserving : MeasurePreserving (combEquiv n d)
    ((stdGauss (Fin n)).prod (stdGauss (WIdx n d))) (stdGauss (CoefIdxD n d)) := by
  exact (measurePreserving_piCongrLeft
    (fun _ : CoefIdxD n d => gaussianReal 0 1) (splitEquiv n d)).comp
    (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin n ⊕ WIdx n d => gaussianReal 0 1))

lemma comb_facts (u : Fin n → ℝ) (W : WIdx n d → ℝ) :
    colM (combEquiv n d (u, W)) default = u ∧
    (∀ (x : Fin n → ℝ) (i : Fin n),
      mapMD (combEquiv n d (u, W)) x i = u i + zv W (pf x) i) ∧
    ∑ α, combEquiv n d (u, W) α ^ 2 = ∑ i, u i ^ 2 + ∑ β, W β ^ 2 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · funext i
    exact combEquiv_inl u W i
  · intro x i
    rw [BstLean.Part49.mapMD_eq]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (default : Mono n d))]
    congr 1
    · have h1 : phiM x (default : Mono n d) = 1 := by
        show BstLean.Part36.monoVal x (Sym.nil : Sym (Fin n) 0).1 = 1
        simp [BstLean.Part36.monoVal]
      rw [h1, mul_one]
      exact combEquiv_inl u W i
    · unfold zv pf
      have hs : (Finset.univ.erase (default : Mono n d)) =
          Finset.univ.filter (fun q : Mono n d => q ≠ default) := by
        ext q; simp
      rw [hs, ← Finset.sum_subtype_eq_sum_filter (p := fun q : Mono n d => q ≠ default)]
      apply Finset.sum_congr
      · ext q; simp
      · intro q _
        rw [combEquiv_inr u W q i]
  · rw [← (splitEquiv n d).sum_comp, Fintype.sum_sum_type]
    have h1 : ∀ i : Fin n, combEquiv n d (u, W) (splitEquiv n d (Sum.inl i)) = u i :=
      fun i => combEquiv_inl u W i
    have h2 : ∀ β : WIdx n d, combEquiv n d (u, W) (splitEquiv n d (Sum.inr β)) = W β :=
      fun β => combEquiv_inr u W β.1 β.2
    simp only [h1, h2]

end BstLean.Part81.Br

namespace BstLean.Part81

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount contr trL frob IsSymmT Tens TSymm fval glue)
open BstLean.Part53 (aH c0 g0 heatA fvA TF)
open BstLean.Part59
open BstLean.Part78 (nsq frobH trH qfun zv sum_word0 sum_word1 sum_word2 contr1 contr2
  heat_zero heat_pos Good good_coord markov_gt)

/-- **The split** of the Gaussian coefficient vector, every map degree. -/
theorem splitIface (n d : ℕ) : SplitIface n d :=
  ⟨Br.combEquiv n d, Br.combEquiv_preserving, fun u W => Br.comb_facts u W⟩

/-- **Coefficient form = `(f₀, ℓ, H)` form**, and the value of `g₀` at `d_f = 2`, map degree `d`. -/
theorem coefBridge (n d : ℕ) : CoefBridge n d := by
  classical
  intro c
  obtain ⟨hsym, hval, htop⟩ := coefTens59 n 2 c
  set T := tensOf 2 c with hT
  refine ⟨fun i => T 1 (fun _ => i), Matrix.of (fun i j => T 2 ![i, j]), ?_, ?_, ?_, ?_⟩
  · ext i j
    have h := hsym 2 (by norm_num) le_rfl (Equiv.swap 0 1) ![j, i]
    have e : (![j, i] ∘ (Equiv.swap (0 : Fin 2) 1)) = ![i, j] := by
      funext t; fin_cases t <;> simp
    rw [e] at h
    simpa using h.symm
  · intro y
    rw [← hval y]
    unfold fval qfun
    have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    rw [hI, Finset.sum_pair (by norm_num), contr1, contr2]
    simp [add_assoc]
  · intro h
    have := htop h
    unfold frob at this
    rw [sum_word2] at this
    simpa [frobH] using this
  · intro M
    have ha : eD d / DD n d = aH n d := by unfold aH eD; rfl
    rw [lemmaQ59 n d 2 c M, ha]
    unfold g0 fvA qfun trH
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, contr1, contr2]
    unfold contr
    rw [sum_word0]
    simp only [heat_zero, heat_pos _ _ 1 (by norm_num) le_rfl, heat_pos _ _ 2 le_rfl (by norm_num)]
    simp [TF, hT]
    ring

/-- **Radius tail**, every map degree. -/
theorem radTail (n d : ℕ) (hn : 1 ≤ n) : RadTail n d := by
  intro δ hδ
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn
  have hev : ∀ Z : CoefIdxD n d → ℝ,
      MvPolynomial.eval Z (BstLean.Part53.T2Aux.radialPoly n d (BstLean.Part53.sg n d)) =
        (∑ α, Z α ^ 2) / DD n d := by
    intro Z
    have hs : (BstLean.Part53.sg n d) ^ 2 = 1 / DD n d := by
      rw [BstLean.Part53.sg, div_pow, one_pow, Real.sq_sqrt hD.le]
    simp only [BstLean.Part53.T2Aux.radialPoly, map_sum, map_pow, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, mul_pow, hs]
    rw [← Finset.mul_sum]; ring
  have hB := BstLean.Part63.centered_exact63 n d hn 1 le_rfl (by norm_num)
  simp only [hev, mul_one, pow_one] at hB
  have hB' : ∫ Z, ((∑ α, Z α ^ 2) / DD n d - 1) ^ 2 ∂stdGauss (CoefIdxD n d) ≤ 2 / DD n d := by
    simpa [BstLean.Part63.mR63] using hB
  have hgood : Good (stdGauss (CoefIdxD n d))
      (fun Z : CoefIdxD n d → ℝ => ((∑ α, Z α ^ 2) / DD n d - 1) ^ 2) := by
    have h1 : Good (stdGauss (CoefIdxD n d)) (fun Z : CoefIdxD n d → ℝ => ∑ α, Z α ^ 2) :=
      Good.sum _ fun α _ => (good_coord α).pow 2
    have h2 := ((h1.mul_const (1 / DD n d)).sub (Good.const 1)).pow 2
    have h3 : (fun Z : CoefIdxD n d → ℝ => ((∑ α, Z α ^ 2) / DD n d - 1) ^ 2) =
        fun Z => ((∑ α, Z α ^ 2) * (1 / DD n d) - 1) ^ 2 := by
      funext Z; ring
    rw [h3]; exact h2
  exact markov_gt (fun Z => sq_nonneg _) hgood.integrable (by positivity) hB'

/-- `𝒟(n,d) ≥ n(n+1)(n+2)/2` for `d ≥ 2`. -/
theorem DD_ge_of_two_le (n d : ℕ) (hd : 2 ≤ d) :
    (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 ≤ BstLean.Part36.DD n d := by
  rw [BstLean.Part36.DD_eq]
  have h1 : (n + 2).choose 2 ≤ (n + d).choose d := by
    rw [← Nat.choose_symm_add, ← Nat.choose_symm_add (a := n) (b := d)]
    exact Nat.choose_le_choose n (by omega)
  have h2 : ((n + 2).choose 2 : ℝ) ≤ ((n + d).choose d : ℝ) := by exact_mod_cast h1
  have h3 : ((n + 2).choose 2 : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
    rw [Nat.cast_choose_two]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2
      = (n : ℝ) * ((n + 2).choose 2 : ℝ) := by rw [h3]; ring
    _ ≤ (n : ℝ) * ((n + d).choose d : ℝ) := mul_le_mul_of_nonneg_left h2 hn0

/-- `𝒟(n,1) = n(n+1)`. -/
theorem DD_one (n : ℕ) : BstLean.Part36.DD n 1 = (n : ℝ) * ((n : ℝ) + 1) := by
  rw [BstLean.Part36.DD_eq, Nat.choose_one_right]
  push_cast; ring

/-- **The program**: computes `g₀`, reads only the constant column, costs less than the charged
baseline; `d_f = 2`, every map degree `d ≥ 1`, every `n ≥ 6d + 26`. -/
theorem prog81 (n d : ℕ) (hd : 1 ≤ d) (hn : 6 * d + 26 ≤ n) (ε : ℝ) :
    ∃ pg : Prog (In59 n d 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d 2 → ℝ, pg.eval v () = g0Q n d 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d 2 ε ∧
      ∀ (c : Mono n 2 → ℝ) (M : CoefIdxD n d → ℝ),
        pg.eval (inp59 c M) () = g0Q n d 2 c M := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n d 2 hn1 hd (by norm_num)
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 2 ε pg.cost hcost
    ((costG59_lt_twoPp n d 2 hd (by omega)).trans_le (twoPp_le_baselineF n d 2 ε)), ?_⟩
  intro c M
  rw [hspec, (cv59_inp 2 c M).1, (cv59_inp 2 c M).2]

end BstLean.Part81

#print axioms BstLean.Part81.splitIface
#print axioms BstLean.Part81.coefBridge
#print axioms BstLean.Part81.radTail
#print axioms BstLean.Part81.DD_ge_of_two_le
#print axioms BstLean.Part81.DD_one
#print axioms BstLean.Part81.prog81
