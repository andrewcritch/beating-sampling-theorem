import BstLean.Part163All

/-!
# Part 164 (file `Ev`): two new Agent events and their charges

No proof is left open; no `native_decide` or `axiom` is used.

* `noiseC_agent`: under the noise of the retained data, an event that reads only the Agent noise
  `x.2.1 = ((A₁, A₂), ξ_A)` has the probability of that event under `cAm n`.
* `charge_of_noise`: a charge under `retDist` from a bad set of the Agent noise.
* `EcA D`: the norm event of `c_A` (paper `t7:p07:c-norm`):
  `t_A|b|²·(n − 2√(12n)) ≤ |c_A|² ≤ t_A|b|²·(n + 2√(12n) + 24)`, `t_A = 2/m_A`;
  `EcA_charge`: `Pr((EcA D)ᶜ) ≤ 2e^{−12}` (Laurent–Massart, both tails).
* `Eop2`: the operator-norm event of the second Agent matrix,
  `‖A₂‖_op ≤ √t_A·(2n + 5)`; `Eop2_charge`: `Pr(Eop2ᶜ) ≤ e^{−25/2}`.
-/

namespace BstLean.Part164

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160

variable {n : ℕ}

/-- The noise of the retained data: the probability of an event that reads only the Agent noise. -/
lemma noiseC_agent (T : Set (ARet n)) :
    (noiseC n).real {x | x.2.1 ∈ T} = (cAm n).real T := by
  have e : {x : Ret n | x.2.1 ∈ T} = Set.univ ×ˢ (T ×ˢ Set.univ) := by
    ext x; simp
  rw [e, noiseC, measureReal_def, Measure.prod_prod, Measure.prod_prod]
  simp [measureReal_def]

/-- **A charge under `retDist` from a bad set of the Agent noise.** If every noise value whose Agent
part is outside `T` is mapped by `retVal D` into `E`, then `Pr(Eᶜ) ≤ Pr_{cAm}(T)`. -/
lemma charge_of_noise (D : Centres n) {E : Set (Ret n)} (hE : MeasurableSet E)
    {T : Set (ARet n)} (hT : MeasurableSet T)
    (hsub : ∀ x : Ret n, x.2.1 ∉ T → retVal D x ∈ E) :
    (retDist D).real Eᶜ ≤ (cAm n).real T := by
  rw [← noise_retVal D, map_measureReal_apply (measurable_retVal D) hE.compl, ← noiseC_agent T]
  refine measureReal_mono (fun x hx => ?_)
  by_contra h
  exact hx (hsub x h)

/-! ## The norm event of `c_A` -/

/-- The upper Laurent–Massart level `n + 2√(12n) + 24`. -/
noncomputable def chiUp (n : ℕ) : ℝ := (n : ℝ) + 2 * √((n : ℝ) * 12) + 2 * 12

/-- The lower Laurent–Massart level `n − 2√(12n)`. -/
noncomputable def chiLo (n : ℕ) : ℝ := (n : ℝ) - 2 * √((n : ℝ) * 12)

/-- **The norm event of `c_A`** (paper `t7:p07:c-norm`, both sides):
`t_A|b|²·(n − 2√(12n)) ≤ |c_A|² ≤ t_A|b|²·(n + 2√(12n) + 24)`, with `b = b_A` the computed centre. -/
def EcA (D : Centres n) : Set (Ret n) :=
  {c | normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiUp n ∧
    2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) * chiLo n ≤ normSq c.2.1.2}

lemma measurable_normSq' {ι : Type*} [Fintype ι] : Measurable (fun y : ι → ℝ => normSq y) := by
  unfold normSq; fun_prop

theorem measurableSet_EcA (D : Centres n) : MeasurableSet (EcA D) := by
  have hb : Measurable (fun c : Ret n => normSq (D.bA c.1 c.2.1.1)) :=
    measurable_normSq'.comp (D.mbA.comp (measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  have hc : Measurable (fun c : Ret n => normSq c.2.1.2) :=
    measurable_normSq'.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact (measurableSet_le hc ((hb.const_mul _).mul_const _)).inter
    (measurableSet_le ((hb.const_mul _).mul_const _) hc)

/-- The bad set of the Agent noise for `EcA`: `|ξ_A|²` outside `(n − 2√(12n), n + 2√(12n) + 24)`. -/
def badCA (n : ℕ) : Set (ARet n) :=
  {x | chiUp n ≤ normSq x.2} ∪ {x | normSq x.2 ≤ chiLo n}

lemma measurableSet_badCA (n : ℕ) : MeasurableSet (badCA n) :=
  (measurableSet_le measurable_const (measurable_normSq'.comp measurable_snd)).union
    (measurableSet_le (measurable_normSq'.comp measurable_snd) measurable_const)

lemma cAm_badCA (hn : 1 ≤ n) : (cAm n).real (badCA n) ≤ 2 * rexp (-12) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hU := BstLean.Part152.chiSq_upper_LM (ι := Fin n) (x := 12) (by norm_num)
  have hL := BstLean.Part152.chiSq_lower_LM (ι := Fin n) (x := 12) (by norm_num)
  simp only [Fintype.card_fin] at hU hL
  have e : badCA n = Set.univ ×ˢ ({ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} ∪
      {ξ : Fin n → ℝ | normSq ξ ≤ chiLo n}) := by
    ext x; simp [badCA]
  rw [e, cAm, measureReal_def, Measure.prod_prod]
  simp only [measure_univ, one_mul]
  rw [← measureReal_def]
  refine (measureReal_union_le _ _).trans ?_
  have e1 : {ξ : Fin n → ℝ | chiUp n ≤ normSq ξ} =
      {ξ | (n : ℝ) + 2 * √((n : ℝ) * 12) + 2 * 12 ≤ ∑ i, ξ i ^ 2} := rfl
  have e2 : {ξ : Fin n → ℝ | normSq ξ ≤ chiLo n} =
      {ξ | ∑ i, ξ i ^ 2 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)} := rfl
  rw [e1, e2]
  linarith

/-- **The charge of the norm event of `c_A`**: `Pr((EcA D)ᶜ) ≤ 2e^{−12}` (`n ≥ 1`). Given the
World data and `(A₁, A₂)`, `c_A = √t_A·|b|·ξ_A` with `ξ_A` standard Gaussian (`retVal`); the two
tails are Laurent–Massart with `x = 12`. -/
theorem EcA_charge (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (EcA D)ᶜ ≤ 2 * rexp (-12) := by
  refine (charge_of_noise D (measurableSet_EcA D) (measurableSet_badCA n) fun x hx => ?_).trans
    (cAm_badCA hn)
  simp only [badCA, Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hx
  obtain ⟨h1, h2⟩ := hx
  set v : ℝ := 2 / (mA n : ℝ)
  set B : ℝ := normSq (D.bA (retValW D x.1) x.2.1.1)
  have hv : 0 ≤ v := by positivity
  have hB : 0 ≤ B := normSq_nonneg _
  have hc : normSq (retVal D x).2.1.2 = v * B * normSq x.2.1.2 := by
    show normSq (cOf v (D.bA (retValW D x.1) x.2.1.1) x.2.1.2) = _
    unfold cOf
    rw [normSq_smul, mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hB]
  have hvB : 0 ≤ v * B := mul_nonneg hv hB
  refine ⟨?_, ?_⟩
  · show normSq (retVal D x).2.1.2 ≤ v * B * chiUp n
    rw [hc]; exact mul_le_mul_of_nonneg_left h1.le hvB
  · show v * B * chiLo n ≤ normSq (retVal D x).2.1.2
    rw [hc]; exact mul_le_mul_of_nonneg_left h2.le hvB

/-! ## The operator-norm event of `A₂` -/

/-- **The operator-norm event of the second Agent matrix**: `‖A₂‖_op ≤ √t_A·(2n + 5)`. -/
def Eop2 (n : ℕ) : Set (Ret n) :=
  {c | BstLean.Part152.opN c.2.1.1.2 ≤ √(2 / (mA n : ℝ)) * (2 * (n : ℝ) + 5)}

theorem measurableSet_Eop2 (n : ℕ) : MeasurableSet (Eop2 n) :=
  measurableSet_le (BstLean.Part152.opN_continuous.measurable.comp
    (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))))
    measurable_const

/-- **The charge of `Eop2`**: `Pr(Eop2ᶜ) ≤ e^{−25/2}` (Gaussian operator-norm tail, `u = 5`). -/
theorem Eop2_charge (hn : 1 ≤ n) (D : Centres n) : (retDist D).real (Eop2 n)ᶜ ≤ rexp (-(25 / 2)) := by
  set T : Set (ARet n) := {x | √(2 / (mA n : ℝ)) * (2 * (n : ℝ) + 5) < BstLean.Part152.opN x.1.2}
  have hT : MeasurableSet T :=
    measurableSet_lt measurable_const (BstLean.Part152.opN_continuous.measurable.comp
      (measurable_snd.comp measurable_fst))
  refine (charge_of_noise D (measurableSet_Eop2 n) hT fun x hx => ?_).trans ?_
  · simp only [T, Set.mem_ofPred_eq, not_lt] at hx
    exact hx
  · have hm : (0 : ℝ) < (mA n : ℝ) := by
      have : 0 < mA n := by unfold mA; exact pow_pos hn 2
      exact_mod_cast this
    have h := BstLean.Part152.opN_tail' (p := mA n) (q := mA n) (v := 2 / (mA n : ℝ))
      (div_pos two_pos hm) (u := 5) (by norm_num)
    have hs : √((mA n : ℕ) : ℝ) = (n : ℝ) := BstLean.Part153.sqrt_mA n
    rw [hs] at h
    have e : T = ((Set.univ : Set (Matrix (Fin (mA n)) (Fin n) ℝ)) ×ˢ
        {M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
          √(2 / (mA n : ℝ)) * (2 * (n : ℝ) + 5) < BstLean.Part152.opN M}) ×ˢ Set.univ := by
      ext x; simp [T]
    rw [e, cAm, BstLean.Part136.hidGauss, measureReal_def, Measure.prod_prod, Measure.prod_prod]
    simp only [measure_univ, one_mul, mul_one]
    rw [← measureReal_def]
    refine le_trans (measureReal_mono (fun M hM => ?_)) (h.trans (le_of_eq ?_))
    · simp only [Set.mem_ofPred_eq] at hM ⊢
      have e2 : (n : ℝ) + n + 5 = 2 * n + 5 := by ring
      rw [e2]; exact hM.le
    · norm_num

end BstLean.Part164
