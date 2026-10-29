import BstLean.Part41Defs
import BstLean.Part40Imported
import BstLean.Part35Wick

/-!
# Part 41, wave 1: the upper tails (Lemma `upper`)

Paper: Lemma `upper` of `proofs/option-m/41-arbitrary-degree.tex`. Specification:
`delegations/answers/p41-spec-opus.md`. Do not use `native_decide`.

Route (heavy). For fixed `x`, `Zφ(x) = ‖φ(x)‖ g` with `g ∼ N(0, I_n)`, and
`T_j[g^{⊗j}] = Σ_l c_{j,l} ⟨tr^l T_j, :g^{⊗s}:⟩` (Hermite). Subtract the constant
`c_{j,j/2} tr^{j/2} T_j E‖φ‖^j` (even `j`). Then `E_Z Var_x u_j ≤ (d+1)^j Σ_{s≥1} c² s! ‖tr^l T_j‖² +
(c tr^{j/2}T_j)² Var_x ‖φ‖^j`; `‖φ‖² ∈ [2, d+1]` on the sphere, Part 40's `popoviciu`, `frob_trL_le`.
So `D^{−j} E Var u_j ≤ G'_j t_j`, `E (Σ_j D^{−j/2} sd u_j)² ≤ Γ' Σ_j t_j ≤ Γ' 𝒩(f)`; Markov on the square.
-/

namespace BstLean.Part41

open MeasureTheory
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)

variable {n d : ℕ}

set_option backward.isDefEq.respectTransparency false

private def AllLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Prop := ∀ p : ℝ≥0, MemLp f p μ

private lemma allLp_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AllLp μ f) (hg : AllLp μ g) :
    AllLp μ (fun x => f x * g x) := by
  intro p
  letI : ENNReal.HolderTriple ((2 * p : ℝ≥0) : ℝ≥0∞)
      ((2 * p : ℝ≥0) : ℝ≥0∞) (p : ℝ≥0∞) := by
    constructor
    simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
    rw [ENNReal.mul_inv (by left; norm_num) (by left; norm_num)]
    rw [← add_mul]
    rw [ENNReal.inv_two_add_inv_two, one_mul]
  exact (hf (2 * p)).fun_mul (hg (2 * p))

private lemma allLp_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, AllLp μ (f i)) :
    AllLp μ (fun x => ∑ i ∈ s, f i x) := by
  intro p
  exact memLp_finsetSum _ (fun i hi => hf i hi p)

private lemma allLp_prod {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, AllLp μ (f i)) :
    AllLp μ (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro p; simpa using (memLp_const (1 : ℝ) (p := (p : ℝ≥0∞)))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact allLp_mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private lemma sphere_cont_allLp (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : AllLp (BstLean.Part29.uniformSphere n) f := by
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => (1 : ℝ)))).bddAbove_image
      hf.norm.continuousOn
  intro p
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma monoVal_cont (s : Multiset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x s) := by
  exact continuous_multiset_prod s (fun _ _ => continuous_apply _)

private lemma joint_map_allLp (hn : 1 ≤ n) (a : Fin n) :
    AllLp ((stdGauss (CoefIdxD n d)).prod (BstLean.Part29.uniformSphere n))
      (fun zx => BstLean.Part36.mapMD zx.1 zx.2 a) := by
  classical
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  unfold BstLean.Part36.mapMD
  apply allLp_sum
  intro i hi
  apply allLp_sum
  intro b _
  apply allLp_mul
  · intro p
    simp only [BstLean.Part36.coefD, Finset.mem_range.mp hi, dite_true]
    exact ((ProbabilityTheory.memLp_id_gaussianReal p).comp_measurePreserving
      (measurePreserving_eval (fun _ : CoefIdxD n d =>
        ProbabilityTheory.gaussianReal 0 1) ⟨⟨i, Finset.mem_range.mp hi⟩, b, a⟩)).comp_fst
          (BstLean.Part29.uniformSphere n)
  · intro p
    exact (sphere_cont_allLp hn (monoVal_cont b.1) p).comp_snd (stdGauss (CoefIdxD n d))

private lemma joint_uJ_allLp (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    AllLp ((stdGauss (CoefIdxD n d)).prod (BstLean.Part29.uniformSphere n))
      (fun zx => uJ T j zx.1 zx.2) := by
  classical
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  unfold uJ contr
  apply allLp_sum
  intro w _
  apply allLp_mul
  · intro p; exact memLp_const _
  · exact allLp_prod _ _ (fun t _ => joint_map_allLp hn (w t))

private lemma joint_map_cont (a : Fin n) : Continuous
    (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      BstLean.Part36.mapMD zx.1 zx.2 a) := by
  classical
  unfold BstLean.Part36.mapMD
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro b _
  simp only [BstLean.Part36.coefD, Finset.mem_range.mp hi, dite_true]
  exact (((continuous_apply _).comp continuous_fst).mul
    ((monoVal_cont b.1).comp continuous_snd))

private lemma joint_uJ_cont (T : Tens n) (j : ℕ) : Continuous
    (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => uJ T j zx.1 zx.2) := by
  classical
  unfold uJ contr
  apply continuous_finsetSum
  intro w _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro t _
  exact joint_map_cont (w t)

private lemma uJ_cont (T : Tens n) (j : ℕ) (Z : CoefIdxD n d → ℝ) :
    Continuous (uJ T j Z) := by
  classical
  have hm (a : Fin n) : Continuous (fun x => BstLean.Part36.mapMD Z x a) := by
    unfold BstLean.Part36.mapMD
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro b _
    exact continuous_const.mul (monoVal_cont b.1)
  unfold uJ contr
  apply continuous_finsetSum
  intro w _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro t _
  exact hm (w t)

private lemma varU_uJ_measurable (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    Measurable (fun Z : CoefIdxD n d → ℝ =>
      varU (BstLean.Part29.uniformSphere n) (uJ T j Z)) := by
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  have hh := (joint_uJ_cont (d := d) T j).measurable
  have hm : Measurable (fun Z : CoefIdxD n d → ℝ =>
      ∫ x, uJ T j Z x ∂BstLean.Part29.uniformSphere n) :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  have hc := (hh.sub (hm.comp measurable_fst)).pow_const 2
  exact hc.stronglyMeasurable.integral_prod_right'.measurable

private lemma varU_le_second (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : (Fin n → ℝ) → ℝ) (hh : AEStronglyMeasurable h μ) :
    varU μ h ≤ ∫ x, h x ^ 2 ∂μ := by
  have hv := ProbabilityTheory.variance_eq_integral (μ := μ) (X := h) hh.aemeasurable
  exact hv.symm.le.trans (ProbabilityTheory.variance_le_expectation_sq hh)

private lemma varU_uJ_integrable (hn : 1 ≤ n) (T : Tens n) (j : ℕ) :
    Integrable (fun Z : CoefIdxD n d → ℝ =>
      varU (BstLean.Part29.uniformSphere n) (uJ T j Z)) (stdGauss (CoefIdxD n d)) := by
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  have hi : Integrable (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      uJ T j zx.1 zx.2 ^ 2)
      ((stdGauss (CoefIdxD n d)).prod (BstLean.Part29.uniformSphere n)) :=
    (joint_uJ_allLp hn T j 2).integrable_sq
  apply hi.integral_prod_left.mono' (varU_uJ_measurable hn T j).aestronglyMeasurable
  filter_upwards [] with Z
  have hv0 : 0 ≤ varU (BstLean.Part29.uniformSphere n) (uJ T j Z) :=
    integral_nonneg fun _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hv0]
  have hc := uJ_cont T j Z
  exact varU_le_second (BstLean.Part29.uniformSphere n) (uJ T j Z) hc.aestronglyMeasurable

private lemma varU_le_shifted (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : (Fin n → ℝ) → ℝ) (hh : AEStronglyMeasurable h μ) (c : ℝ) :
    varU μ h ≤ ∫ x, (h x - c) ^ 2 ∂μ := by
  have heq := ProbabilityTheory.variance_eq_integral (μ := μ) (X := h) hh.aemeasurable
  have hv := ProbabilityTheory.variance_add_const hh (-c)
  have hs := ProbabilityTheory.variance_le_expectation_sq (hh.add_const (-c))
  exact heq.symm.le.trans (by
    simpa only [sub_eq_add_neg, hv, Pi.pow_apply] using hs)

/-- Center at any deterministic constant, then exchange the two integrals. -/
private lemma expected_var_le_shifted_moment (hn : 1 ≤ n) (T : Tens n) (j : ℕ) (c : ℝ) :
    (∫ Z : CoefIdxD n d → ℝ,
      varU (BstLean.Part29.uniformSphere n) (uJ T j Z) ∂stdGauss (CoefIdxD n d)) ≤
    ∫ x, ∫ Z : CoefIdxD n d → ℝ, (uJ T j Z x - c) ^ 2
      ∂stdGauss (CoefIdxD n d) ∂BstLean.Part29.uniformSphere n := by
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  have hi : Integrable (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      (uJ T j zx.1 zx.2 - c) ^ 2)
      ((stdGauss (CoefIdxD n d)).prod (BstLean.Part29.uniformSphere n)) :=
    ((joint_uJ_allLp hn T j 2).sub (memLp_const c)).integrable_sq
  have hp (Z : CoefIdxD n d → ℝ) :
      varU (BstLean.Part29.uniformSphere n) (uJ T j Z) ≤
      ∫ x, (uJ T j Z x - c) ^ 2 ∂BstLean.Part29.uniformSphere n := by
    have hc := uJ_cont T j Z
    exact varU_le_shifted (BstLean.Part29.uniformSphere n) (uJ T j Z) hc.aestronglyMeasurable c
  calc
    _ ≤ ∫ Z, ∫ x, (uJ T j Z x - c) ^ 2 ∂BstLean.Part29.uniformSphere n
        ∂stdGauss (CoefIdxD n d) :=
      integral_mono (varU_uJ_integrable hn T j) hi.integral_prod_left hp
    _ = _ := integral_integral_swap hi

private lemma enum_exists {ι : Type*} {i : ℕ} (β : Sym ι i) :
    ∃ w : Fin i → ι, Finset.univ.val.map w = β.val := by
  have enum (b : Multiset ι) : ∃ (r : ℕ) (w : Fin r → ι),
      r = b.card ∧ Finset.univ.val.map w = b := by
    induction b using Quot.inductionOn with
    | h a => exact ⟨a.length, a.get, rfl, by simp [Fin.univ_val_map]⟩
  obtain ⟨r, w, hr, hw⟩ := enum β.val
  have hri : r = i := hr.trans β.property
  clear hr
  subst r
  exact ⟨w, hw⟩

private noncomputable def enumSym {ι : Type*} {i : ℕ} (β : Sym ι i) : Fin i → ι :=
  Classical.choose (enum_exists β)

private lemma enumSym_spec {ι : Type*} {i : ℕ} (β : Sym ι i) :
    Finset.univ.val.map (enumSym β) = β.val := Classical.choose_spec (enum_exists β)

private lemma enumSym_injective {ι : Type*} {i : ℕ} :
    Function.Injective (enumSym : Sym ι i → Fin i → ι) := by
  intro β γ h
  apply Subtype.ext
  rw [← enumSym_spec β, ← enumSym_spec γ, h]

private lemma mono_enum {i : ℕ} (β : Sym (Fin n) i) (x : Fin n → ℝ) :
    BstLean.Part36.monoVal x β.val = ∏ t, x (enumSym β t) := by
  rw [BstLean.Part36.monoVal, ← enumSym_spec β, Multiset.map_map]
  rfl

private lemma phiSq_le (x : Fin n → ℝ) (hx : ∑ a, x a ^ 2 = 1) :
    phiSq d x ≤ (d : ℝ) + 1 := by
  classical
  have hlevel (i : ℕ) : (∑ β : Sym (Fin n) i, BstLean.Part36.monoVal x β.val ^ 2) ≤ 1 := by
    calc
      _ = ∑ β : Sym (Fin n) i, ∏ t, x (enumSym β t) ^ 2 := by
        apply Finset.sum_congr rfl
        intro β hβ
        rw [mono_enum, Finset.prod_pow]
      _ ≤ ∑ w : Fin i → Fin n, ∏ t, x (w t) ^ 2 := by
        calc
          _ = ∑ w ∈ Finset.univ.image (enumSym : Sym (Fin n) i → Fin i → Fin n),
              ∏ t, x (w t) ^ 2 := by
            rw [Finset.sum_image (fun β _ γ _ h => enumSym_injective h)]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => Finset.prod_nonneg (fun t _ => sq_nonneg _))
      _ = ∏ t : Fin i, ∑ a : Fin n, x a ^ 2 :=
        (Fintype.prod_sum (fun (_ : Fin i) (a : Fin n) => x a ^ 2)).symm
      _ = 1 := by simp [hx]
  unfold phiSq phiM
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ i : Fin (d + 1), (1 : ℝ) := Finset.sum_le_sum (fun i _ => hlevel i.val)
    _ = (d : ℝ) + 1 := by simp


private lemma trace_frob_le_local {ι : Type*} [Fintype ι] {j : ℕ} (l : ℕ)
    (hl : 2 * l ≤ j) (A : (Fin j → ι) → ℝ) :
    frob (trL l A) ≤ (Fintype.card ι : ℝ) ^ l * frob A := by
  classical
  let G : (Fin l → ι) × (Fin (j - 2 * l) → ι) → (Fin j → ι) :=
    fun p => glue j l p.1 p.2
  have hinj : Function.Injective G := by
    intro p q h
    apply Prod.ext
    · funext t
      have h' := congrFun h ⟨2 * t.val, by omega⟩
      simpa [G, glue, show 2 * t.val < 2 * l by omega] using h'
    · funext t
      have h' := congrFun h ⟨2 * l + t.val, by omega⟩
      simpa [G, glue, show ¬2 * l + t.val < 2 * l by omega] using h'
  have hsum : (∑ w, ∑ c, A (glue j l c w) ^ 2) ≤ frob A := by
    rw [Finset.sum_comm]
    change (∑ c, ∑ w, A (G (c, w)) ^ 2) ≤ frob A
    rw [← Fintype.sum_prod_type (fun p => A (G p) ^ 2)]
    calc
      _ = ∑ v ∈ Finset.univ.image G, A v ^ 2 := by
        rw [Finset.sum_image (fun p _ q _ h => hinj h)]
      _ ≤ frob A := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  unfold frob trL
  calc
    _ ≤ ∑ w, (Fintype.card ι : ℝ) ^ l * ∑ c, A (glue j l c w) ^ 2 := by
      apply Finset.sum_le_sum
      intro w hw
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : Fin l → ι => (1 : ℝ)) (fun c => A (glue j l c w))
      simpa using h
    _ = (Fintype.card ι : ℝ) ^ l * ∑ w, ∑ c, A (glue j l c w) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)


private lemma Nn_nonneg (k : ℕ) (T : Tens n) : 0 ≤ Nn n d k T := by
  unfold Nn aSq BstLean.Part36.DD
  apply Finset.sum_nonneg
  intro jl _
  have hf : 0 ≤ frob (trL jl.2 (T jl.1)) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

private lemma phiSq_nonneg (x : Fin n → ℝ) : 0 ≤ phiSq d x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma phiSq_ge_two (hd : 1 ≤ d) (x : Fin n → ℝ)
    (hx : ∑ a, x a ^ 2 = 1) : 2 ≤ phiSq d x := by
  classical
  let L : ℕ → ℝ := fun i => ∑ b : Sym (Fin n) i, BstLean.Part36.monoVal x b.val ^ 2
  have h0 : L 0 = 1 := by
    have hm (b : Sym (Fin n) 0) : BstLean.Part36.monoVal x b.val = 1 := by
      have hb : b.val = 0 := Multiset.card_eq_zero.mp b.property
      change (b.val.map x).prod = 1
      rw [hb]
      simp
    change (∑ b : Sym (Fin n) 0, BstLean.Part36.monoVal x b.val ^ 2) = 1
    rw [Finset.univ_unique, Finset.sum_singleton, hm]
    norm_num
  have h1 : L 1 = 1 := by
    have he := (Sym.oneEquiv : Fin n ≃ Sym (Fin n) 1).sum_comp
      (fun b => BstLean.Part36.monoVal x b.val ^ 2)
    calc
      L 1 = ∑ i : Fin n, BstLean.Part36.monoVal x (Sym.oneEquiv i).val ^ 2 := he.symm
      _ = ∑ i : Fin n, x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        change (({i} : Multiset (Fin n)).map x).prod ^ 2 = x i ^ 2
        simp
      _ = 1 := hx
  let a : Fin (d + 1) := ⟨0, by omega⟩
  let b : Fin (d + 1) := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  have hL (i : ℕ) : 0 ≤ L i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold phiSq phiM
  rw [Fintype.sum_sigma]
  change 2 ≤ ∑ i : Fin (d + 1), L i.val
  calc
    2 = L a.val + L b.val := by norm_num [a, b, h0, h1]
    _ = ∑ i ∈ ({a, b} : Finset (Fin (d + 1))), L i.val := by simp [hab]
    _ ≤ ∑ i : Fin (d + 1), L i.val :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hL i.val)

private lemma phiSq_cont : Continuous (phiSq d : (Fin n → ℝ) → ℝ) := by
  classical
  unfold phiSq phiM
  apply continuous_finsetSum
  intro p _
  exact (monoVal_cont p.2.val).pow 2

private lemma radial_variance_bound (hn : 1 ≤ n) (hd : 1 ≤ d) (j : ℕ) :
    varU (BstLean.Part29.uniformSphere n) (fun x => Real.sqrt (phiSq d x ^ j)) ≤
      (Real.sqrt (((d : ℝ) + 1) ^ j) - Real.sqrt (2 ^ j)) ^ 2 / 4 := by
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  apply BstLean.Part40.popoviciu
    (BstLean.Part29.uniformSphere n) (fun x => Real.sqrt (phiSq d x ^ j))
    (phiSq_cont.pow j).sqrt.measurable.aemeasurable
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  constructor
  · apply Real.sqrt_le_sqrt
    exact pow_le_pow_left₀ (by norm_num) (phiSq_ge_two hd x hx) _
  · apply Real.sqrt_le_sqrt
    exact pow_le_pow_left₀ (phiSq_nonneg x) (phiSq_le x hx) _

private lemma trL_zero {j : ℕ} (A : (Fin j → Fin n) → ℝ) : trL 0 A = A := by
  classical
  funext w
  simp only [trL, Finset.univ_unique, Finset.sum_singleton]
  congr 1

private lemma cQ_zero (j : ℕ) : cQ j 0 = 1 := by
  simp [cQ, Nat.factorial_ne_zero]

private lemma DD_pos (hn : 1 ≤ n) : 0 < BstLean.Part36.DD n d := by
  have hne : Nonempty (CoefIdxD n d) :=
    ⟨⟨⟨0, by omega⟩, ⟨⟨0, by simp⟩, ⟨0, by omega⟩⟩⟩⟩
  unfold BstLean.Part36.DD
  exact_mod_cast Fintype.card_pos_iff.mpr hne

private noncomputable def degreeUpperConstant (n d j : ℕ) : ℝ :=
  ((d : ℝ) + 1) ^ j *
      ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 * (n : ℝ) ^ l +
    (if Even j then (cQ j (j / 2) : ℝ) ^ 2 * (n : ℝ) ^ (j / 2) *
      (Real.sqrt (((d : ℝ) + 1) ^ j) - Real.sqrt (2 ^ j)) ^ 2 / 4 else 0)

private noncomputable def chaosEnergy (T : Tens n) (j : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
    ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 * frob (trL l (T j))

private noncomputable def meanCoeff (T : Tens n) (j : ℕ) : ℝ :=
  if Even j then (cQ j (j / 2) : ℝ) * ∑ w, trL (j / 2) (T j) w else 0

private lemma chaosEnergy_nonneg (T : Tens n) (j : ℕ) : 0 ≤ chaosEnergy T j := by
  apply Finset.sum_nonneg
  intro l _
  have hf : 0 ≤ frob (trL l (T j)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

private lemma chaosEnergy_le (T : Tens n) (j : ℕ) :
    chaosEnergy T j ≤
      (∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 * (n : ℝ) ^ l) * frob (T j) := by
  unfold chaosEnergy
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l hl
  have hlt := (Finset.mem_filter.mp hl).2
  have hf := trace_frob_le_local l (by omega : 2 * l ≤ j) (T j)
  have h : frob (trL l (T j)) ≤ (n : ℝ) ^ l * frob (T j) := by simpa using hf
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 by positivity)
  simpa only [mul_assoc] using hm

private lemma meanCoeff_sq_le (T : Tens n) (j : ℕ) :
    meanCoeff T j ^ 2 ≤
      (if Even j then (cQ j (j / 2) : ℝ) ^ 2 * (n : ℝ) ^ (j / 2) else 0) * frob (T j) := by
  classical
  by_cases hj : Even j
  · have hs : j - 2 * (j / 2) = 0 := by
      obtain ⟨l, hl⟩ := hj
      omega
    have hsum : (∑ w, trL (j / 2) (T j) w) ^ 2 ≤ frob (trL (j / 2) (T j)) := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := trL (j / 2) (T j))
      simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hs,
        pow_zero, Nat.cast_one, one_mul, frob] using h
    have ht := trace_frob_le_local (j / 2) (Nat.mul_div_le j 2) (T j)
    have hb : (∑ w, trL (j / 2) (T j) w) ^ 2 ≤ (n : ℝ) ^ (j / 2) * frob (T j) :=
      hsum.trans (by simpa using ht)
    simp only [meanCoeff, if_pos hj, mul_pow]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (sq_nonneg (cQ j (j / 2) : ℝ))
  · simp [meanCoeff, hj]

private lemma degree_variance_from_pointwise (hn : 1 ≤ n) (hd : 1 ≤ d)
    (T : Tens n) (j : ℕ)
    (hp : ∀ x : Fin n → ℝ, (∑ a, x a ^ 2 = 1) →
      (∫ Z : CoefIdxD n d → ℝ,
        (uJ T j Z x - meanCoeff T j *
          ∫ y, Real.sqrt (phiSq d y ^ j) ∂BstLean.Part29.uniformSphere n) ^ 2
        ∂stdGauss (CoefIdxD n d)) ≤
      phiSq d x ^ j * chaosEnergy T j + meanCoeff T j ^ 2 *
        (Real.sqrt (phiSq d x ^ j) -
          ∫ y, Real.sqrt (phiSq d y ^ j) ∂BstLean.Part29.uniformSphere n) ^ 2) :
    (∫ Z : CoefIdxD n d → ℝ,
      varU (BstLean.Part29.uniformSphere n) (uJ T j Z) ∂stdGauss (CoefIdxD n d)) ≤
      degreeUpperConstant n d j * frob (T j) := by
  classical
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  let μ := BstLean.Part29.uniformSphere n
  let H : (Fin n → ℝ) → ℝ := fun x => Real.sqrt (phiSq d x ^ j)
  let m : ℝ := ∫ x, H x ∂μ
  let a := meanCoeff T j
  let C := ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
    ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 * (n : ℝ) ^ l
  let R := (Real.sqrt (((d : ℝ) + 1) ^ j) - Real.sqrt (2 ^ j)) ^ 2 / 4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcont : Continuous H := (phiSq_cont.pow j).sqrt
  have hpow : Integrable (fun x => phiSq d x ^ j) μ :=
    (sphere_cont_allLp hn (phiSq_cont.pow j) 1).integrable (by norm_num)
  have hsquare : Integrable (fun x => (H x - m) ^ 2) μ :=
    (sphere_cont_allLp hn ((hcont.sub continuous_const).pow 2) 1).integrable (by norm_num)
  have hshift : Integrable (fun zx : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      (uJ T j zx.1 zx.2 - a * m) ^ 2) ((stdGauss (CoefIdxD n d)).prod μ) :=
    ((joint_uJ_allLp hn T j 2).sub (memLp_const (a * m))).integrable_sq
  have hphi : (∫ x, phiSq d x ^ j ∂μ) ≤ ((d : ℝ) + 1) ^ j := by
    calc
      _ ≤ ∫ _x : Fin n → ℝ, ((d : ℝ) + 1) ^ j ∂μ := by
        apply integral_mono_ae hpow (integrable_const _)
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
        exact pow_le_pow_left₀ (phiSq_nonneg x) (phiSq_le x hx) _
      _ = _ := by simp [μ]
  have hvar : varU μ H ≤ R := radial_variance_bound hn hd j
  have hfirst : (∫ x, phiSq d x ^ j ∂μ) * chaosEnergy T j ≤
      ((d : ℝ) + 1) ^ j * C * frob (T j) := by
    calc
      _ ≤ ((d : ℝ) + 1) ^ j * chaosEnergy T j :=
        mul_le_mul_of_nonneg_right hphi (chaosEnergy_nonneg T j)
      _ ≤ ((d : ℝ) + 1) ^ j * (C * frob (T j)) :=
        mul_le_mul_of_nonneg_left (chaosEnergy_le T j) (by positivity)
      _ = _ := by ring
  have hsecond : a ^ 2 * varU μ H ≤
      (if Even j then (cQ j (j / 2) : ℝ) ^ 2 * (n : ℝ) ^ (j / 2) else 0) *
        frob (T j) * R := by
    calc
      _ ≤ a ^ 2 * R := mul_le_mul_of_nonneg_left hvar (sq_nonneg a)
      _ ≤ _ := mul_le_mul_of_nonneg_right (meanCoeff_sq_le T j) hR
  calc
    _ ≤ ∫ x, ∫ Z : CoefIdxD n d → ℝ, (uJ T j Z x - a * m) ^ 2
        ∂stdGauss (CoefIdxD n d) ∂μ := expected_var_le_shifted_moment hn T j (a * m)
    _ ≤ ∫ x, phiSq d x ^ j * chaosEnergy T j + a ^ 2 * (H x - m) ^ 2 ∂μ := by
      apply integral_mono_ae hshift.integral_prod_right
        ((hpow.mul_const _).add (hsquare.const_mul _))
      filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
      exact hp x hx
    _ = (∫ x, phiSq d x ^ j ∂μ) * chaosEnergy T j + a ^ 2 * varU μ H := by
      rw [integral_add (hpow.mul_const _) (hsquare.const_mul _),
        integral_mul_const, integral_const_mul]
      rfl
    _ ≤ ((d : ℝ) + 1) ^ j * C * frob (T j) +
        (if Even j then (cQ j (j / 2) : ℝ) ^ 2 * (n : ℝ) ^ (j / 2) else 0) *
          frob (T j) * R := add_le_add hfirst hsecond
    _ = degreeUpperConstant n d j * frob (T j) := by
      unfold degreeUpperConstant
      dsimp [C, R]
      split_ifs <;> ring

private lemma gaussian_linear_second {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    (∫ Z : ι → ℝ, (∑ i, c i * Z i) ^ 2 ∂stdGauss ι) = ∑ i, c i ^ 2 := by
  classical
  have hi (a b : ι) : Integrable (fun Z : ι → ℝ => Z a * Z b) (stdGauss ι) := by
    simpa [Fin.prod_univ_succ] using BstLean.Part35.stdGauss_prod_integrable 2 ![a, b]
  have hm (a b : ι) : (∫ Z : ι → ℝ, Z a * Z b ∂stdGauss ι) = if a = b then 1 else 0 := by
    have h := BstLean.Part35.stdGauss_wick_step a 1 ![b]
    simpa [Fin.prod_univ_succ, Fin.sum_univ_succ, eq_comm] using h
  have he (Z : ι → ℝ) : (∑ i, c i * Z i) ^ 2 =
      ∑ i, ∑ l, (c i * c l) * (Z i * Z l) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun l _ => (hi i l).const_mul (c i * c l)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun l _ => (hi i l).const_mul (c i * c l))]
  simp_rw [integral_const_mul, hm]
  simp [pow_two]

private def coefEquiv : CoefIdxD n d ≃ Mono n d × Fin n where
  toFun a := (⟨a.1, a.2.1⟩, a.2.2)
  invFun a := ⟨a.1.1, a.1.2, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma map_as_columns (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) (a : Fin n) :
    BstLean.Part36.mapMD M x a = ∑ p : Mono n d, colM M p a * phiM x p := by
  classical
  unfold BstLean.Part36.mapMD
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  simp [BstLean.Part36.coefD, colM, phiM, i.isLt]

private lemma contr_one (A : (Fin 1 → Fin n) → ℝ) (v : Fin n → ℝ) :
    contr A (fun _ => v) = ∑ a : Fin n, A (fun _ => a) * v a := by
  classical
  unfold contr
  have he := (Equiv.funUnique (Fin 1) (Fin n)).symm.sum_comp
    (fun w => A w * ∏ t, v (w t))
  apply he.symm.trans
  apply Finset.sum_congr rfl
  intro a _
  have hconst : (Equiv.funUnique (Fin 1) (Fin n)).symm a = fun _ => a := by
    funext t
    have ht : t = default := Subsingleton.elim _ _
    subst t
    rfl
  rw [hconst]
  simp

private lemma frob_one (A : (Fin 1 → Fin n) → ℝ) :
    frob A = ∑ a : Fin n, A (fun _ => a) ^ 2 := by
  have he := (Equiv.funUnique (Fin 1) (Fin n)).symm.sum_comp (fun w => A w ^ 2)
  exact he.symm

private lemma uJ_one_linear (T : Tens n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    uJ T 1 Z x = ∑ i : CoefIdxD n d,
      (T 1 (fun _ => i.2.2) * phiM x ⟨i.1, i.2.1⟩) * Z i := by
  classical
  rw [uJ, contr_one]
  simp_rw [map_as_columns, Finset.mul_sum]
  rw [Finset.sum_comm]
  have he := coefEquiv.symm.sum_comp (fun i : CoefIdxD n d =>
    (T 1 (fun _ => i.2.2) * phiM x ⟨i.1, i.2.1⟩) * Z i)
  rw [← he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro a _
  dsimp [coefEquiv, colM]
  ring

private lemma uJ_one_second (T : Tens n) (x : Fin n → ℝ) :
    (∫ Z : CoefIdxD n d → ℝ, uJ T 1 Z x ^ 2 ∂stdGauss (CoefIdxD n d)) =
      phiSq d x * frob (T 1) := by
  classical
  simp_rw [uJ_one_linear]
  rw [gaussian_linear_second]
  have he := coefEquiv.symm.sum_comp (fun i : CoefIdxD n d =>
    (T 1 (fun _ => i.2.2) * phiM x ⟨i.1, i.2.1⟩) ^ 2)
  rw [← he, Fintype.sum_prod_type, frob_one]
  unfold phiSq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  dsimp [coefEquiv]
  ring

private lemma degree_variance_one (hn : 1 ≤ n) (hd : 1 ≤ d) (T : Tens n) :
    (∫ Z : CoefIdxD n d → ℝ,
      varU (BstLean.Part29.uniformSphere n) (uJ T 1 Z) ∂stdGauss (CoefIdxD n d)) ≤
      degreeUpperConstant n d 1 * frob (T 1) := by
  apply degree_variance_from_pointwise hn hd T 1
  intro x _
  have hm : meanCoeff T 1 = 0 := by norm_num [meanCoeff]
  have he : chaosEnergy T 1 = frob (T 1) := by
    norm_num [chaosEnergy, cQ_zero, trL_zero]
  simp only [hm, zero_mul, sub_zero, pow_two, mul_zero, add_zero, pow_one, he]
  simpa only [pow_two] using (uJ_one_second (d := d) T x).le

set_option linter.unusedSectionVars false

section GaussTensor

open BstLean.Part29 (gaussMom)

private lemma gt_poly_integrable {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z p) (stdGauss ι) := by
  classical
  conv in MvPolynomial.eval _ p => rw [p.as_sum]
  simp only [MvPolynomial.eval_sum]
  apply integrable_finsetSum
  intro d _
  simp only [MvPolynomial.eval_monomial]
  have he (z : ι → ℝ) : d.prod (fun i e => z i ^ e) = ∏ i, z i ^ d i :=
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  simp_rw [he]
  exact (Integrable.fintype_prod (f := fun i x => x ^ d i) (fun i =>
    ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
      (μ := ProbabilityTheory.gaussianReal 0 1) (by simp) _)).const_mul _

private lemma gt_gaussMom_step (a : ℕ) : gaussMom (a + 2) = (a + 1 : ℝ) * gaussMom a := by
  unfold gaussMom
  have h : Even (a + 2) ↔ Even a := by simp [Nat.even_add]
  simp only [h]
  split_ifs with ha
  · rw [show a + 2 - 1 = a + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    rfl
  · ring

private lemma gt_gaussMom_stein (a : ℕ) : gaussMom (a + 1) = (a : ℝ) * gaussMom (a - 1) := by
  cases a with
  | zero => norm_num [gaussMom]
  | succ a => simpa [Nat.succ_eq_add_one] using gt_gaussMom_step a

private lemma gt_power_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (i : ι) :
    (∫ Z, Z i * ∏ j, Z j ^ a j ∂stdGauss ι) =
      (a i : ℝ) * ∫ Z, ∏ j, Z j ^ (a j - if j = i then 1 else 0) ∂stdGauss ι := by
  classical
  have he (Z : ι → ℝ) : Z i * (∏ j, Z j ^ a j) =
      ∏ j, Z j ^ (a j + if j = i then 1 else 0) := by
    simp only [pow_add, Finset.prod_mul_distrib]
    simp [mul_comm, Finset.prod_ite_eq']
  simp_rw [he]
  have hmom (b : ι → ℕ) : (∫ Z, ∏ j, Z j ^ b j ∂stdGauss ι) = ∏ j, gaussMom (b j) := by
    unfold stdGauss
    rw [integral_fintype_prod_eq_prod (f := fun j (x : ℝ) => x ^ b j)]
    simp_rw [BstLean.Part29.gaussMom_eq]
  rw [hmom, hmom, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true, gt_gaussMom_stein]
  have hprod :
      (∏ j ∈ Finset.univ.erase i, gaussMom (a j + if j = i then 1 else 0)) =
        ∏ j ∈ Finset.univ.erase i, gaussMom (a j - if j = i then 1 else 0) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj]
  rw [hprod]
  ring

/-- Gaussian expectation of a polynomial. -/
private noncomputable def Ex {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) : ℝ :=
  ∫ z, MvPolynomial.eval z p ∂stdGauss ι

private lemma Ex_add {ι : Type*} [Fintype ι] (p q : MvPolynomial ι ℝ) :
    Ex (p + q) = Ex p + Ex q := by
  unfold Ex
  simp only [MvPolynomial.eval_add]
  exact integral_add (gt_poly_integrable p) (gt_poly_integrable q)

private lemma Ex_C_mul {ι : Type*} [Fintype ι] (c : ℝ) (p : MvPolynomial ι ℝ) :
    Ex (MvPolynomial.C c * p) = c * Ex p := by
  unfold Ex
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  exact integral_const_mul _ _

private lemma Ex_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (p : κ → MvPolynomial ι ℝ) :
    Ex (∑ a ∈ s, p a) = ∑ a ∈ s, Ex (p a) := by
  unfold Ex
  simp only [MvPolynomial.eval_sum]
  exact integral_finsetSum _ (fun a _ => gt_poly_integrable (p a))

private lemma Ex_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (i : ι) :
    Ex (MvPolynomial.X i * p) = Ex (MvPolynomial.pderiv i p) := by
  classical
  unfold Ex
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
  have hmono (d : ι →₀ ℕ) (c : ℝ) :
      (∫ Z, Z i * MvPolynomial.eval Z (MvPolynomial.monomial d c) ∂stdGauss ι) =
        ∫ Z, MvPolynomial.eval Z (MvPolynomial.pderiv i (MvPolynomial.monomial d c))
          ∂stdGauss ι := by
    have he (d : ι →₀ ℕ) (Z : ι → ℝ) : d.prod (fun j e => Z j ^ e) = ∏ j, Z j ^ d j :=
      Finsupp.prod_fintype _ _ (by simp)
    simp only [MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial, he,
      Finsupp.tsub_apply, Finsupp.single_apply]
    simp_rw [show ∀ Z : ι → ℝ, Z i * (c * ∏ j, Z j ^ d j) =
      c * (Z i * ∏ j, Z j ^ d j) by intro Z; ring]
    rw [integral_const_mul, gt_power_stein, integral_const_mul]
    simp only [eq_comm, mul_assoc]
  have hi (q : MvPolynomial ι ℝ) : Integrable
      (fun Z => Z i * MvPolynomial.eval Z q) (stdGauss ι) := by
    have := gt_poly_integrable (MvPolynomial.X i * q)
    simpa using this
  have hd (q : MvPolynomial ι ℝ) : Integrable
      (fun Z => MvPolynomial.eval Z (MvPolynomial.pderiv i q)) (stdGauss ι) :=
    gt_poly_integrable _
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, MvPolynomial.eval_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun d _ => hi _), integral_finsetSum _ (fun d _ => hd _)]
  exact Finset.sum_congr rfl (fun d _ => hmono d (p.coeff d))

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The linear forms `ℓ_b = Σ_i v b i X_i`. -/
private noncomputable def lf (v : κ → ι → ℝ) (b : κ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (v b i) * MvPolynomial.X i

/-- `P_A = A[ℓ^{⊗p}]`. -/
private noncomputable def PA (v : κ → ι → ℝ) {p : ℕ} (A : (Fin p → κ) → ℝ) : MvPolynomial ι ℝ :=
  ∑ w : Fin p → κ, MvPolynomial.C (A w) * ∏ t, lf v (w t)

/-- The slot-0 slice. -/
private def sl {p : ℕ} (A : (Fin (p + 1) → κ) → ℝ) (a : κ) : (Fin p → κ) → ℝ :=
  fun w => A (Fin.cons a w)

private lemma sum_cons {p : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (p + 1) → κ) → M) :
    ∑ w, f w = ∑ a, ∑ w : Fin p → κ, f (Fin.cons a w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (p + 1) => κ)).sum_comp, Fintype.sum_prod_type]
  rfl

private lemma PA_peel (v : κ → ι → ℝ) {p : ℕ} (A : (Fin (p + 1) → κ) → ℝ) :
    PA v A = ∑ a, lf v a * PA v (sl A a) := by
  unfold PA sl
  rw [sum_cons]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

private lemma PA_zero (v : κ → ι → ℝ) (A : (Fin 0 → κ) → ℝ) :
    PA v A = MvPolynomial.C (A Fin.elim0) := by
  unfold PA
  rw [Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  congr 2

private lemma sl_symm {p : ℕ} {A : (Fin (p + 1) → κ) → ℝ} (hA : IsSymmT A) (a : κ) :
    IsSymmT (sl A a) := by
  intro σ w
  have h := hA (Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.cons a w)
  unfold sl
  rw [← h]
  congr 1
  funext t
  refine Fin.cases ?_ (fun t => ?_) t
  · simp
  · simp [Equiv.Perm.decomposeFin_symm_apply_succ]

private lemma sl_comm {p : ℕ} {A : (Fin (p + 2) → κ) → ℝ} (hA : IsSymmT A) (a b : κ) :
    sl (sl A a) b = sl (sl A b) a := by
  funext w
  unfold sl
  have h := hA (Equiv.swap 0 1) (Fin.cons b (Fin.cons a w))
  rw [← h]
  congr 1
  funext t
  refine Fin.cases ?_ (fun t => ?_) t
  · simp
  · refine Fin.cases ?_ (fun t => ?_) t
    · simp
    · have h0 : (t.succ.succ : Fin (p + 2)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (t.succ.succ : Fin (p + 2)) ≠ 1 := by
        intro h; have := congrArg Fin.val h; simp at this
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1]
      simp

private lemma pderiv_lf (v : κ → ι → ℝ) (b : κ) (i : ι) :
    MvPolynomial.pderiv i (lf v b) = MvPolynomial.C (v b i) := by
  unfold lf
  simp [MvPolynomial.pderiv_X, Pi.single_apply]

private lemma pderiv_PA (v : κ → ι → ℝ) (i : ι) : ∀ (p : ℕ) (A : (Fin (p + 1) → κ) → ℝ),
    IsSymmT A → MvPolynomial.pderiv i (PA v A) =
      MvPolynomial.C ((p + 1 : ℕ) : ℝ) * ∑ b, MvPolynomial.C (v b i) * PA v (sl A b) := by
  intro p
  induction p with
  | zero =>
    intro A _
    rw [PA_peel]
    simp only [map_sum, Derivation.leibniz, pderiv_lf, PA_zero, MvPolynomial.pderiv_C,
      smul_zero, zero_add, smul_eq_mul]
    simp [mul_comm]
  | succ p ih =>
    intro A hA
    rw [PA_peel]
    simp only [map_sum, Derivation.leibniz, pderiv_lf, smul_eq_mul]
    rw [Finset.sum_add_distrib]
    have h2 : ∑ a, lf v a * MvPolynomial.pderiv i (PA v (sl A a)) =
        MvPolynomial.C ((p + 1 : ℕ) : ℝ) * ∑ b, MvPolynomial.C (v b i) * PA v (sl A b) := by
      simp_rw [ih _ (sl_symm hA _)]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [PA_peel v (sl A b), Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [sl_comm hA a b]
      ring
    rw [h2]
    have h1 : ∑ a, PA v (sl A a) * MvPolynomial.C (v a i) =
        ∑ b, MvPolynomial.C (v b i) * PA v (sl A b) :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [h1]
    push_cast
    simp only [map_add, map_one]
    ring


/-- The directional derivative `Σ_i v a i ∂_i P_C`. -/
private noncomputable def Dterm (v : κ → ι → ℝ) {m : ℕ} (C : (Fin m → κ) → ℝ) (a : κ) :
    MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (v a i) * MvPolynomial.pderiv i (PA v C)

private lemma Dterm_zero (v : κ → ι → ℝ) (C : (Fin 0 → κ) → ℝ) (a : κ) : Dterm v C a = 0 := by
  unfold Dterm
  simp [PA_zero]

private lemma Dterm_succ (v : κ → ι → ℝ)
    (hv : ∀ a b, ∑ i, v a i * v b i = if a = b then 1 else 0)
    {m : ℕ} (C : (Fin (m + 1) → κ) → ℝ) (hC : IsSymmT C) (a : κ) :
    Dterm v C a = MvPolynomial.C ((m + 1 : ℕ) : ℝ) * PA v (sl C a) := by
  unfold Dterm
  simp_rw [pderiv_PA v _ m C hC, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (b : κ) : ∑ i, MvPolynomial.C (v a i) * (MvPolynomial.C ((m + 1 : ℕ) : ℝ) *
      (MvPolynomial.C (v b i) * PA v (sl C b))) =
      MvPolynomial.C (if a = b then 1 else 0) *
        (MvPolynomial.C ((m + 1 : ℕ) : ℝ) * PA v (sl C b)) := by
    rw [← hv a b, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_mul]
    ring
  simp_rw [h]
  simp

private noncomputable def Qm (v : κ → ι → ℝ) {p q : ℕ} (A : (Fin p → κ) → ℝ)
    (B : (Fin q → κ) → ℝ) : ℝ := Ex (PA v A * PA v B)

private lemma Qm_comm (v : κ → ι → ℝ) {p q : ℕ} (A : (Fin p → κ) → ℝ)
    (B : (Fin q → κ) → ℝ) : Qm v A B = Qm v B A := by
  unfold Qm; rw [mul_comm]

private lemma Qm_rec (v : κ → ι → ℝ) {p q : ℕ} (A : (Fin (p + 1) → κ) → ℝ)
    (B : (Fin q → κ) → ℝ) :
    Qm v A B = ∑ a, (Ex (Dterm v (sl A a) a * PA v B) + Ex (PA v (sl A a) * Dterm v B a)) := by
  unfold Qm
  rw [PA_peel, Finset.sum_mul, Ex_sum]
  apply Finset.sum_congr rfl
  intro a _
  have e1 : lf v a * PA v (sl A a) * PA v B =
      ∑ i, MvPolynomial.C (v a i) * (MvPolynomial.X i * (PA v (sl A a) * PA v B)) := by
    unfold lf
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e1, Ex_sum]
  simp_rw [Ex_C_mul, Ex_stein, Derivation.leibniz, smul_eq_mul]
  rw [← Ex_add]
  unfold Dterm
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, Ex_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Ex_C_mul]
  congr 1
  ring

/-! ### Coefficients -/

private noncomputable def kap (m s : ℕ) : ℝ :=
  if s ≤ m ∧ Even (m - s) then (cQ m ((m - s) / 2) : ℝ) else 0

private lemma kap_form (s l : ℕ) :
    kap (s + 2 * l) s = ((s + 2 * l).factorial : ℝ) /
      ((l.factorial : ℝ) * 2 ^ l * (s.factorial : ℝ)) := by
  unfold kap
  rw [if_pos ⟨by omega, ⟨l, by omega⟩⟩]
  have h1 : (s + 2 * l - s) / 2 = l := by omega
  have h2 : s + 2 * l - 2 * l = s := by omega
  rw [h1]
  unfold cQ
  rw [h2]
  push_cast
  rfl

private lemma kap_zero (m s : ℕ) (h : ¬ ∃ l, m = s + 2 * l) : kap m s = 0 := by
  unfold kap
  rw [if_neg]
  rintro ⟨h1, l, hl⟩
  exact h ⟨l, by omega⟩

private lemma kap_ne_zero {m s : ℕ} (h : kap m s ≠ 0) : ∃ l, m = s + 2 * l := by
  by_contra hc
  exact h (kap_zero m s hc)

private lemma kap_K1 (m s : ℕ) : ((s + 1 : ℕ) : ℝ) * kap (m + 1) (s + 1) =
    ((m + 1 : ℕ) : ℝ) * kap m s := by
  by_cases h : ∃ l, m = s + 2 * l
  · obtain ⟨l, rfl⟩ := h
    rw [show s + 2 * l + 1 = (s + 1) + 2 * l by ring, kap_form, kap_form]
    rw [show (s + 1) + 2 * l = (s + 2 * l) + 1 by ring]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
  · rw [kap_zero m s h, kap_zero]
    · simp
    · rintro ⟨l, hl⟩; exact h ⟨l, by omega⟩

private lemma kap_K2 (p s : ℕ) : kap (p + 1) (s + 1) =
    (p : ℝ) * kap (p - 1) (s + 1) + kap p s := by
  by_cases h : ∃ l, p = s + 2 * l
  · obtain ⟨l, rfl⟩ := h
    rcases l with _ | l
    · simp only [Nat.mul_zero, Nat.add_zero]
      have e1 := kap_form (s + 1) 0
      have e0 := kap_form s 0
      simp only [Nat.mul_zero, Nat.add_zero] at e1 e0
      rw [e1, e0, kap_zero]
      · have h1 : ((s + 1).factorial : ℝ) ≠ 0 := by positivity
        have h2 : (s.factorial : ℝ) ≠ 0 := by positivity
        simp [h1, h2]
      · rintro ⟨l, hl⟩; omega
    · rw [show s + 2 * (l + 1) + 1 = (s + 1) + 2 * (l + 1) by ring, kap_form,
        show s + 2 * (l + 1) - 1 = (s + 1) + 2 * l by omega, kap_form, kap_form]
      rw [show (s + 1) + 2 * (l + 1) = ((s + 1) + 2 * l + 1) + 1 by ring,
        show s + 2 * (l + 1) = (s + 1) + 2 * l + 1 by ring]
      simp only [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
      ring
  · rw [kap_zero p s h, kap_zero (p + 1) (s + 1)]
    · rcases p with _ | p
      · simp
      · rw [kap_zero]
        · simp
        · rintro ⟨l, hl⟩; exact h ⟨l + 1, by omega⟩
    · rintro ⟨l, hl⟩; exact h ⟨l, by omega⟩

private lemma kap_K0 (p : ℕ) : kap (p + 1) 0 = (p : ℝ) * kap (p - 1) 0 := by
  by_cases h : ∃ l, p + 1 = 0 + 2 * l
  · obtain ⟨l, hl⟩ := h
    rcases l with _ | l
    · omega
    · have hp : p = 2 * l + 1 := by omega
      subst hp
      rw [show 2 * l + 1 + 1 = 0 + 2 * (l + 1) by ring, kap_form,
        show 2 * l + 1 - 1 = 0 + 2 * l by omega, kap_form]
      rw [show 0 + 2 * (l + 1) = (0 + 2 * l + 1) + 1 by ring]
      simp only [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
      ring
  · rw [kap_zero _ _ h]
    rcases p with _ | p
    · simp
    · rw [kap_zero]
      · simp
      · rintro ⟨l, hl⟩; exact h ⟨l + 1, by omega⟩

private lemma kap_zero_zero : kap 0 0 = 1 := by
  have := kap_form 0 0
  simpa using this

private lemma kap_gt {m s : ℕ} (h : m < s) : kap m s = 0 :=
  kap_zero m s (by rintro ⟨l, hl⟩; omega)

/-! ### Traced pairings -/

private def rd (d0 : κ) (p : ℕ) {l s : ℕ} (c : Fin l → κ) (w : Fin s → κ) : Fin p → κ :=
  fun t => if h : t.1 < 2 * l then c ⟨t.1 / 2, by omega⟩ else
    if h2 : t.1 - 2 * l < s then w ⟨t.1 - 2 * l, h2⟩ else d0

private noncomputable def J (d0 : κ) {p q : ℕ} (A : (Fin p → κ) → ℝ) (B : (Fin q → κ) → ℝ)
    (l l' s : ℕ) : ℝ :=
  ∑ w : Fin s → κ, (∑ c : Fin l → κ, A (rd d0 p c w)) * (∑ c : Fin l' → κ, B (rd d0 q c w))

private lemma J_comm (d0 : κ) {p q : ℕ} (A : (Fin p → κ) → ℝ) (B : (Fin q → κ) → ℝ)
    (l l' s : ℕ) : J d0 A B l l' s = J d0 B A l' l s := by
  unfold J
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private lemma cons_at {m : ℕ} (a : κ) (c : Fin m → κ) (i : Fin (m + 1)) :
    (Fin.cons a c : Fin (m + 1) → κ) i = if h : i.1 = 0 then a else c ⟨i.1 - 1, by omega⟩ := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp

private lemma rd_cons2 (d0 : κ) (p : ℕ) {l s : ℕ} (a : κ) (c : Fin l → κ) (w : Fin s → κ) :
    rd d0 (p + 2) (Fin.cons a c : Fin (l + 1) → κ) w =
      Fin.cons a (Fin.cons a (rd d0 p c w)) := by
  funext t
  simp only [rd, cons_at, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; ext; simp only [Fin.val_mk]; omega)

private lemma sum_cons_fun {l : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (l + 1) → κ) → M) :
    ∑ c, f c = ∑ a, ∑ c : Fin l → κ, f (Fin.cons a c) := sum_cons f

private lemma J_T1 (d0 : κ) {p q : ℕ} (A : (Fin (p + 2) → κ) → ℝ) (B : (Fin q → κ) → ℝ)
    (l l' s : ℕ) : ∑ a, J d0 (sl (sl A a) a) B l l' s = J d0 A B (l + 1) l' s := by
  unfold J
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.sum_mul]
  congr 1
  rw [sum_cons_fun]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [rd_cons2]
  rfl

private lemma J_T1' (d0 : κ) {p q : ℕ} (A : (Fin p → κ) → ℝ) (B : (Fin (q + 2) → κ) → ℝ)
    (l l' s : ℕ) : ∑ a, J d0 A (sl (sl B a) a) l l' s = J d0 A B l (l' + 1) s := by
  rw [J_comm, ← J_T1]
  exact Finset.sum_congr rfl (fun a _ => J_comm _ _ _ _ _ _)

private lemma rd_cycle (d0 : κ) {p l s : ℕ} (hp : p = s + 2 * l) (a : κ) (c : Fin l → κ)
    (w : Fin s → κ) :
    rd d0 (p + 1) c (Fin.cons a w : Fin (s + 1) → κ) =
      (Fin.cons a (rd d0 p c w) : Fin (p + 1) → κ) ∘
        (Fin.cycleRange (⟨2 * l, by omega⟩ : Fin (p + 1))) := by
  have hcr (t : Fin (p + 1)) : ((Fin.cycleRange (⟨2 * l, by omega⟩ : Fin (p + 1))) t).1 =
      if t.1 < 2 * l then t.1 + 1 else if t.1 = 2 * l then 0 else t.1 := by
    by_cases h1 : t.1 < 2 * l
    · rw [if_pos h1, Fin.coe_cycleRange_of_lt (by simpa [Fin.lt_def] using h1)]
    · by_cases h2 : t.1 = 2 * l
      · rw [if_neg h1, if_pos h2]
        have : t = ⟨2 * l, by omega⟩ := Fin.ext h2
        rw [this, Fin.cycleRange_self]
        rfl
      · rw [if_neg h1, if_neg h2, Fin.cycleRange_of_gt]
        rw [Fin.lt_def]; simp; omega
  funext t
  rw [Function.comp_apply]
  by_cases h1 : t.1 < 2 * l
  · have e : (Fin.cycleRange (⟨2 * l, by omega⟩ : Fin (p + 1))) t = ⟨t.1 + 1, by omega⟩ :=
      Fin.ext (by rw [hcr, if_pos h1])
    rw [e]
    simp only [rd, cons_at, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; ext; simp only [Fin.val_mk]; omega)
  · by_cases h2 : t.1 = 2 * l
    · have e : (Fin.cycleRange (⟨2 * l, by omega⟩ : Fin (p + 1))) t = ⟨0, by omega⟩ :=
        Fin.ext (by rw [hcr, if_neg h1, if_pos h2])
      rw [e]
      simp only [rd, cons_at, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; ext; simp only [Fin.val_mk]; omega)
    · have e : (Fin.cycleRange (⟨2 * l, by omega⟩ : Fin (p + 1))) t = t :=
        Fin.ext (by rw [hcr, if_neg h1, if_neg h2])
      rw [e]
      simp only [rd, cons_at, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; ext; simp only [Fin.val_mk]; omega)

private lemma J_T2 (d0 : κ) {p q l l' s : ℕ} (hp : p = s + 2 * l) (hq : q = s + 2 * l')
    (A : (Fin (p + 1) → κ) → ℝ) (B : (Fin (q + 1) → κ) → ℝ) (hA : IsSymmT A) (hB : IsSymmT B) :
    ∑ a, J d0 (sl A a) (sl B a) l l' s = J d0 A B l l' (s + 1) := by
  unfold J
  rw [sum_cons]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  · apply Finset.sum_congr rfl
    intro c _
    rw [rd_cycle d0 hp, hA]
    rfl
  · apply Finset.sum_congr rfl
    intro c _
    rw [rd_cycle d0 hq, hB]
    rfl

/-! ### The closed form -/

private lemma Ex_C (c : ℝ) : Ex (MvPolynomial.C c : MvPolynomial ι ℝ) = c := by
  unfold Ex
  simp

private lemma Ex_zero : Ex (0 : MvPolynomial ι ℝ) = 0 := by
  simpa using Ex_C (ι := ι) 0

private lemma fin0_eq (f g : Fin 0 → κ) : f = g := funext fun t => t.elim0

private lemma CFmean (v : κ → ι → ℝ) (hv : ∀ a b, ∑ i, v a i * v b i = if a = b then 1 else 0)
    (d0 : κ) : ∀ (q : ℕ) (B : (Fin q → κ) → ℝ) (A : (Fin 0 → κ) → ℝ), IsSymmT B →
    Qm v B A = kap q 0 * J d0 A B 0 (q / 2) 0 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro B A hB
  match q, ih, B, hB with
  | 0, _, B, _ =>
    unfold Qm
    rw [PA_zero v B, PA_zero v A, ← map_mul, Ex_C, kap_zero_zero]
    unfold J
    simp only [Fintype.sum_unique, one_mul]
    rw [mul_comm]
    congr 1
    · congr 1; funext t; exact t.elim0
    · rw [Fintype.sum_eq_single (fun _ => d0)
        (fun c hc => absurd (funext fun t => absurd t.2 (by simp)) hc)]
      congr 1; funext t; exact t.elim0
  | 1, _, B, _ =>
    rw [Qm_rec]
    simp only [Dterm_zero, zero_mul, mul_zero, Ex_zero, add_zero, Finset.sum_const_zero]
    rw [kap_zero]
    · simp
    · rintro ⟨l, hl⟩; omega
  | q + 2, ih, B, hB =>
    rw [Qm_rec]
    simp only [Dterm_zero, mul_zero, Ex_zero, add_zero]
    have h1 (a : κ) : Ex (Dterm v (sl B a) a * PA v A) =
        ((q + 1 : ℕ) : ℝ) * (kap q 0 * J d0 A (sl (sl B a) a) 0 (q / 2) 0) := by
      rw [Dterm_succ v hv _ (sl_symm hB a), mul_assoc, Ex_C_mul]
      congr 1
      exact ih q (by omega) _ A (sl_symm (sl_symm hB a) a)
    simp_rw [h1]
    rw [← Finset.mul_sum, ← Finset.mul_sum, J_T1', kap_K0 (q + 1)]
    rw [show (q + 2) / 2 = q / 2 + 1 by omega]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

private lemma CF (v : κ → ι → ℝ) (hv : ∀ a b, ∑ i, v a i * v b i = if a = b then 1 else 0)
    (d0 : κ) : ∀ (p q : ℕ) (A : (Fin p → κ) → ℝ) (B : (Fin q → κ) → ℝ), IsSymmT A → IsSymmT B →
    ∀ N, p < N → Qm v A B = ∑ s ∈ Finset.range N, (s.factorial : ℝ) * kap p s * kap q s *
      J d0 A B ((p - s) / 2) ((q - s) / 2) s := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro q A B hA hB N hN
  rcases p with _ | p
  · rw [Qm_comm, CFmean v hv d0 q B A hB]
    rw [Finset.sum_eq_single 0]
    · simp [kap_zero_zero]
    · intro s _ hs
      rw [kap_gt (by omega : 0 < s)]
      ring
    · intro h; exact absurd (Finset.mem_range.mpr hN) h
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  let g : ℕ → ℝ := fun s => (p : ℝ) * ((s.factorial : ℝ) * kap (p - 1) s * kap q s *
    J d0 A B ((p - 1 - s) / 2 + 1) ((q - s) / 2) s)
  let h : ℕ → ℝ := fun s => (q : ℝ) * ((s.factorial : ℝ) * kap p s * kap (q - 1) s *
    J d0 A B ((p - s) / 2) ((q - 1 - s) / 2) (s + 1))
  have hS1 : ∑ a, Ex (Dterm v (sl A a) a * PA v B) = ∑ s ∈ Finset.range (N + 1), g s := by
    rcases p with _ | p
    · simp [Dterm_zero, Ex_zero, g]
    · have h1 (a : κ) : Ex (Dterm v (sl A a) a * PA v B) =
          ((p + 1 : ℕ) : ℝ) * ∑ s ∈ Finset.range (N + 1), (s.factorial : ℝ) * kap p s * kap q s *
            J d0 (sl (sl A a) a) B ((p - s) / 2) ((q - s) / 2) s := by
        rw [Dterm_succ v hv _ (sl_symm hA a), mul_assoc, Ex_C_mul]
        congr 1
        exact ih p (by omega) q _ B (sl_symm (sl_symm hA a) a) hB (N + 1) (by omega)
      simp_rw [h1]
      rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, J_T1]
      simp only [g, Nat.add_sub_cancel]
      push_cast
      ring
  have hS2 : ∑ a, Ex (PA v (sl A a) * Dterm v B a) = ∑ s ∈ Finset.range N, h s := by
    rcases q with _ | q
    · simp [Dterm_zero, Ex_zero, h]
    · have h1 (a : κ) : Ex (PA v (sl A a) * Dterm v B a) =
          ((q + 1 : ℕ) : ℝ) * ∑ s ∈ Finset.range N, (s.factorial : ℝ) * kap p s * kap q s *
            J d0 (sl A a) (sl B a) ((p - s) / 2) ((q - s) / 2) s := by
        rw [Dterm_succ v hv _ hB a, mul_left_comm, Ex_C_mul]
        congr 1
        exact ih p (by omega) q _ _ (sl_symm hA a) (sl_symm hB a) N (by omega)
      simp_rw [h1]
      rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [h, Nat.add_sub_cancel]
      by_cases hk : kap p s * kap q s = 0
      · have : ∀ a : κ, (s.factorial : ℝ) * kap p s * kap q s *
            J d0 (sl A a) (sl B a) ((p - s) / 2) ((q - s) / 2) s = 0 := by
          intro a; rw [mul_assoc (s.factorial : ℝ), hk]; ring
        simp_rw [this]
        rw [mul_assoc (s.factorial : ℝ), hk]
        try simp
      · obtain ⟨l, hl⟩ := kap_ne_zero (left_ne_zero_of_mul hk)
        obtain ⟨l', hl'⟩ := kap_ne_zero (right_ne_zero_of_mul hk)
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          J_T2 d0 (by omega : p = s + 2 * ((p - s) / 2)) (by omega : q = s + 2 * ((q - s) / 2))
            A B hA hB]
        all_goals (push_cast; ring)
  rw [Qm_rec, Finset.sum_add_distrib, hS1, hS2, Finset.sum_range_succ', Finset.sum_range_succ',
    add_comm (∑ s ∈ Finset.range N, g (s + 1)) (g 0), add_assoc, ← Finset.sum_add_distrib,
    add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    simp only [g, h]
    have ej : ∀ (l : ℕ) (hl : kap (p - 1) (s + 1) ≠ 0),
        (p - 1 - (s + 1)) / 2 + 1 = (p + 1 - (s + 1)) / 2 := by
      intro l hl
      obtain ⟨m, hm⟩ := kap_ne_zero hl
      omega
    have eg : (p : ℝ) * (((s + 1).factorial : ℝ) * kap (p - 1) (s + 1) * kap q (s + 1) *
        J d0 A B ((p - 1 - (s + 1)) / 2 + 1) ((q - (s + 1)) / 2) (s + 1)) =
        (p : ℝ) * (((s + 1).factorial : ℝ) * kap (p - 1) (s + 1) * kap q (s + 1)) *
        J d0 A B ((p + 1 - (s + 1)) / 2) ((q - (s + 1)) / 2) (s + 1) := by
      by_cases hk : kap (p - 1) (s + 1) = 0
      · rw [hk]; ring
      · rw [ej 0 hk]; ring
    have eh : (q - 1 - s) / 2 = (q - (s + 1)) / 2 := by omega
    have ep : (p - s) / 2 = (p + 1 - (s + 1)) / 2 := by omega
    rw [eg, eh, ep]
    have hc : ((s + 1).factorial : ℝ) * kap (p + 1) (s + 1) * kap q (s + 1) =
        (p : ℝ) * (((s + 1).factorial : ℝ) * kap (p - 1) (s + 1) * kap q (s + 1)) +
        (q : ℝ) * ((s.factorial : ℝ) * kap p s * kap (q - 1) s) := by
      rw [kap_K2]
      have hq : ((s + 1).factorial : ℝ) * kap q (s + 1) = (q : ℝ) * (s.factorial * kap (q - 1) s) := by
        rcases q with _ | q
        · rw [kap_gt (by omega)]; simp
        · have := kap_K1 q s
          rw [Nat.factorial_succ]
          push_cast at this ⊢
          try simp only [Nat.add_sub_cancel]
          linear_combination (s.factorial : ℝ) * this
      have : ((s + 1).factorial : ℝ) * ((p : ℝ) * kap (p - 1) (s + 1) + kap p s) * kap q (s + 1) =
          (p : ℝ) * (((s + 1).factorial : ℝ) * kap (p - 1) (s + 1) * kap q (s + 1)) +
          kap p s * (((s + 1).factorial : ℝ) * kap q (s + 1)) := by ring
      rw [this, hq]
      ring
    rw [hc]
    ring
  · simp only [g]
    rw [kap_K0]
    by_cases hk : kap (p - 1) 0 = 0
    · rw [hk]; ring
    · rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst hp0; simp
      obtain ⟨m, hm⟩ := kap_ne_zero hk
      rw [show (p - 1 - 0) / 2 + 1 = (p + 1 - 0) / 2 by omega]
      ring

end GaussTensor

/-! ### Bridge from the abstract Gaussian tensor calculus to `uJ` -/

private noncomputable def vX (d : ℕ) (x : Fin n → ℝ) (a : Fin n) (i : CoefIdxD n d) : ℝ :=
  if i.2.2 = a then phiM x (⟨i.1, i.2.1⟩ : Mono n d) / Real.sqrt (phiSq d x) else 0

private lemma vX_orth (x : Fin n → ℝ) (hR : 0 < phiSq d x) (a b : Fin n) :
    ∑ i, vX d x a i * vX d x b i = if a = b then 1 else 0 := by
  classical
  have he := (coefEquiv (n := n) (d := d)).symm.sum_comp (fun i => vX d x a i * vX d x b i)
  rw [← he, Fintype.sum_prod_type]
  have hin (p : Mono n d) : ∑ c : Fin n, vX d x a (coefEquiv.symm (p, c)) *
      vX d x b (coefEquiv.symm (p, c)) =
      if a = b then phiM x p ^ 2 / phiSq d x else 0 := by
    rw [Finset.sum_eq_single a]
    · by_cases hab : a = b
      · subst hab
        simp only [vX, coefEquiv, Equiv.coe_fn_symm_mk, if_true]
        rw [div_mul_div_comm, Real.mul_self_sqrt hR.le, pow_two]
      · simp [vX, coefEquiv, hab]
    · intro c _ hc
      simp [vX, coefEquiv, hc]
    · simp
  simp_rw [hin]
  by_cases hab : a = b
  · simp only [hab, if_true]
    rw [← Finset.sum_div]
    exact div_self hR.ne'
  · simp [hab]

private lemma mapMD_eq (x : Fin n → ℝ) (hR : 0 < phiSq d x) (Z : CoefIdxD n d → ℝ) (a : Fin n) :
    BstLean.Part36.mapMD Z x a =
      Real.sqrt (phiSq d x) * MvPolynomial.eval Z (lf (vX d x) a) := by
  classical
  rw [map_as_columns]
  unfold lf
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  have he := (coefEquiv (n := n) (d := d)).symm.sum_comp (fun i => vX d x a i * Z i)
  rw [← he, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single a]
  · have hs : Real.sqrt (phiSq d x) ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
    simp only [vX, coefEquiv, Equiv.coe_fn_symm_mk, if_true, colM]
    field_simp
  · intro c _ hc
    simp [vX, coefEquiv, hc]
  · simp

private lemma uJ_eq (x : Fin n → ℝ) (hR : 0 < phiSq d x) (T : Tens n) (j : ℕ)
    (Z : CoefIdxD n d → ℝ) :
    uJ T j Z x = Real.sqrt (phiSq d x) ^ j * MvPolynomial.eval Z (PA (vX d x) (T j)) := by
  classical
  unfold uJ contr PA
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, mapMD_eq x hR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private lemma glue_rd {κ : Type*} (d0 : κ) {j l : ℕ} (h : 2 * l ≤ j) (c : Fin l → κ)
    (w : Fin (j - 2 * l) → κ) : glue j l c w = rd d0 j c w := by
  funext t
  simp only [glue, rd]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma sq_sum_fin0 {κ : Type*} [Fintype κ] {r : ℕ} (hr : r = 0)
    (X : (Fin r → κ) → ℝ) : ∑ w, X w ^ 2 = (∑ w, X w) ^ 2 := by
  subst hr
  simp [Fintype.sum_unique]

private lemma J_frob {κ : Type*} [Fintype κ] (d0 : κ) {j l : ℕ} (h : 2 * l ≤ j)
    (A : (Fin j → κ) → ℝ) : J d0 A A l l (j - 2 * l) = frob (trL l A) := by
  unfold J frob trL
  apply Finset.sum_congr rfl
  intro w _
  rw [pow_two]
  simp_rw [glue_rd d0 h]

private lemma kap_diag (j l : ℕ) (h : 2 * l ≤ j) : kap j (j - 2 * l) = (cQ j l : ℝ) := by
  have := kap_form (j - 2 * l) l
  rw [show j - 2 * l + 2 * l = j by omega] at this
  rw [this]
  unfold cQ
  rw [show j - 2 * l = j - 2 * l from rfl]
  push_cast
  ring

private lemma diag_eq {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : κ → ι → ℝ)
    (hv : ∀ a b, ∑ i, v a i * v b i = if a = b then 1 else 0) (d0 : κ)
    {j : ℕ} (A : (Fin j → κ) → ℝ) (hA : IsSymmT A) :
    Qm v A A = (∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 * frob (trL l A)) +
      (if Even j then (cQ j (j / 2) : ℝ) * ∑ w, trL (j / 2) A w else 0) ^ 2 := by
  classical
  rw [CF v hv d0 j j A A hA hA (j + 1) (by omega)]
  let F : ℕ → ℝ := fun s => (s.factorial : ℝ) * kap j s * kap j s *
    J d0 A A ((j - s) / 2) ((j - s) / 2) s
  change ∑ s ∈ Finset.range (j + 1), F s = _
  have hinj : Set.InjOn (fun l => j - 2 * l) (Finset.range (j / 2 + 1) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    omega
  have hsub : (Finset.range (j / 2 + 1)).image (fun l => j - 2 * l) ⊆ Finset.range (j + 1) := by
    intro s hs
    simp only [Finset.mem_image, Finset.mem_range] at hs ⊢
    omega
  rw [← Finset.sum_subset hsub (fun s hs hns => by
    have hk : kap j s = 0 := by
      apply kap_zero
      rintro ⟨l, hl⟩
      apply hns
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨l, by omega, by omega⟩
    simp [F, hk]), Finset.sum_image hinj]
  have hG (l : ℕ) (hl : l ∈ Finset.range (j / 2 + 1)) : F (j - 2 * l) =
      ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 * frob (trL l A) := by
    have h2 : 2 * l ≤ j := by simp at hl; omega
    simp only [F]
    rw [show (j - (j - 2 * l)) / 2 = l by omega, J_frob d0 h2, kap_diag j l h2]
    ring
  rw [Finset.sum_congr rfl hG, ← Finset.sum_filter_add_sum_filter_not _ (fun l => 2 * l < j)]
  congr 1
  by_cases hj : Even j
  · have hf : (Finset.range (j / 2 + 1)).filter (fun l => ¬ 2 * l < j) = {j / 2} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      obtain ⟨r, hr⟩ := hj
      omega
    have h0 : j - 2 * (j / 2) = 0 := by obtain ⟨r, hr⟩ := hj; omega
    rw [hf, Finset.sum_singleton, if_pos hj,
      show ((j - 2 * (j / 2)).factorial : ℝ) = 1 by rw [h0]; simp, one_mul, mul_pow]
    congr 1
    exact sq_sum_fin0 h0 _
  · have hf : (Finset.range (j / 2 + 1)).filter (fun l => ¬ 2 * l < j) = ∅ := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and,
        not_not]
      intro hl
      have : ¬ (j % 2 = 0) := by
        intro h; exact hj (Nat.even_iff.mpr h)
      omega
    rw [hf, if_neg hj]
    simp

private lemma rd_indep {κ : Type*} (d0 : κ) {p l s s' : ℕ} (h : p ≤ 2 * l) (c : Fin l → κ)
    (w : Fin s → κ) (w' : Fin s' → κ) : rd d0 p c w = rd d0 p c w' := by
  funext t
  simp only [rd]
  rw [dif_pos (by omega), dif_pos (by omega)]

private lemma mean_eq {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : κ → ι → ℝ)
    (hv : ∀ a b, ∑ i, v a i * v b i = if a = b then 1 else 0) (d0 : κ)
    {j : ℕ} (A : (Fin j → κ) → ℝ) (hA : IsSymmT A) :
    Ex (PA v A) = if Even j then (cQ j (j / 2) : ℝ) * ∑ w, trL (j / 2) A w else 0 := by
  classical
  let A1 : (Fin 0 → κ) → ℝ := fun _ => 1
  have h1 : Ex (PA v A) = Qm v A A1 := by
    unfold Qm
    rw [PA_zero v A1]
    simp [A1]
  rw [h1, CFmean v hv d0 j A A1 hA]
  by_cases hj : Even j
  · have h0 : j - 2 * (j / 2) = 0 := by obtain ⟨r, hr⟩ := hj; omega
    have hk : kap j 0 = (cQ j (j / 2) : ℝ) := by
      have := kap_diag j (j / 2) (by omega)
      rwa [h0] at this
    rw [if_pos hj, hk]
    congr 1
    unfold J trL
    simp only [Fintype.sum_unique, A1, one_mul]
    have hc : ∀ w : Fin (j - 2 * (j / 2)) → κ, ∑ c : Fin (j / 2) → κ, A (glue j (j / 2) c w) =
        ∑ c : Fin (j / 2) → κ, A (rd d0 j c (default : Fin 0 → κ)) := by
      intro w
      apply Finset.sum_congr rfl
      intro c _
      rw [glue_rd d0 (by omega), rd_indep d0 (by omega) c w (default : Fin 0 → κ)]
    simp_rw [hc]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, h0]
    simp
  · rw [if_neg hj, kap_zero]
    · simp
    · rintro ⟨l, hl⟩; exact hj ⟨l, by omega⟩

private lemma sqrt_pow_eq (R : ℝ) (hR : 0 ≤ R) (j : ℕ) :
    Real.sqrt (R ^ j) = Real.sqrt R ^ j := by
  rw [show R ^ j = (Real.sqrt R ^ j) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hR]]
  exact Real.sqrt_sq (by positivity)

/-- The fixed-input Gaussian computation, as an equality. -/
private lemma pointwise_eq (hn : 1 ≤ n) (hd : 1 ≤ d) (T : Tens n) (j : ℕ)
    (hsym : IsSymmT (T j)) (x : Fin n → ℝ) (hx : ∑ a, x a ^ 2 = 1) (m : ℝ) :
    (∫ Z : CoefIdxD n d → ℝ, (uJ T j Z x - meanCoeff T j * m) ^ 2 ∂stdGauss (CoefIdxD n d)) =
      phiSq d x ^ j * chaosEnergy T j + meanCoeff T j ^ 2 * (Real.sqrt (phiSq d x ^ j) - m) ^ 2 := by
  classical
  have hR : 0 < phiSq d x := lt_of_lt_of_le (by norm_num) (phiSq_ge_two hd x hx)
  let v := vX d x
  have hv := vX_orth x hR
  let d0 : Fin n := ⟨0, hn⟩
  let P := PA v (T j)
  let α := Real.sqrt (phiSq d x) ^ j
  let β := meanCoeff T j * m
  have hint : (fun Z : CoefIdxD n d → ℝ => (uJ T j Z x - meanCoeff T j * m) ^ 2) =
      fun Z => MvPolynomial.eval Z ((MvPolynomial.C α * P - MvPolynomial.C β) ^ 2) := by
    funext Z
    simp only [uJ_eq x hR, MvPolynomial.eval_pow, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
      MvPolynomial.eval_C]
    rfl
  have hpoly : (MvPolynomial.C α * P - MvPolynomial.C β) ^ 2 =
      MvPolynomial.C (α ^ 2) * (P * P) + (MvPolynomial.C (-2 * α * β) * P +
        MvPolynomial.C (β ^ 2)) := by
    simp only [map_pow, map_mul, map_neg, map_ofNat]
    ring
  rw [hint]
  change Ex _ = _
  rw [hpoly, Ex_add, Ex_add, Ex_C_mul, Ex_C_mul, Ex_C]
  have hPP : Ex (P * P) = chaosEnergy T j + meanCoeff T j ^ 2 :=
    diag_eq v hv d0 (T j) hsym
  have hP : Ex P = meanCoeff T j := mean_eq v hv d0 (T j) hsym
  rw [hPP, hP, sqrt_pow_eq _ hR.le]
  have hα : α ^ 2 = phiSq d x ^ j := by
    simp only [α]
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hR.le]
  rw [← hα]
  ring

private lemma Gpj_mul_tj {j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) (k : ℕ) (T : Tens n) :
    Gpj n d k j * tj n d k T j =
      degreeUpperConstant n d j * frob (T j) / BstLean.Part36.DD n d ^ j := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hfact : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hD := ne_of_gt (DD_pos (d := d) hn)
  simp only [Gpj, tj, aSq, cQ_zero, Rat.cast_one, one_pow, trL_zero]
  change ((n : ℝ) ^ (k - j) / ((j.factorial : ℝ) * j) * degreeUpperConstant n d j) *
    ((j.factorial : ℝ) * j * (1 / BstLean.Part36.DD n d ^ j * frob (T j)) /
      (n : ℝ) ^ (k - j)) = _
  field_simp [hn0, hj0, hfact, hD]

private lemma sum_tj_le_Nn (k : ℕ) (T : Tens n) :
    ∑ j ∈ Finset.Icc 1 k, tj n d k T j ≤ Nn n d k T := by
  classical
  let F : ℕ × ℕ → ℝ := fun jl =>
    ((jl.1 - 2 * jl.2).factorial : ℝ) * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 *
      aSq n d T jl.1 jl.2 / (n : ℝ) ^ (k - (jl.1 - 2 * jl.2))
  have hsub : (Finset.Icc 1 k).image (fun j => (j, 0)) ⊆ levels k := by
    intro jl hjl
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjl
    simp only [levels, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hj, by omega⟩, by have := (Finset.mem_Icc.mp hj).1; omega⟩
  have hF (jl : ℕ × ℕ) : 0 ≤ F jl := by
    dsimp [F, aSq]
    unfold BstLean.Part36.DD
    have hf : 0 ≤ frob (trL jl.2 (T jl.1)) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  calc
    ∑ j ∈ Finset.Icc 1 k, tj n d k T j =
        ∑ jl ∈ (Finset.Icc 1 k).image (fun j => (j, 0)), F jl := by
      rw [Finset.sum_image]
      · simp [F, tj]
      · intro a _ b _ hab; exact congrArg Prod.fst hab
    _ ≤ ∑ jl ∈ levels k, F jl :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun jl _ _ => hF jl)
    _ = Nn n d k T := rfl

private lemma maxJ_nonneg (k : ℕ) (g : ℕ → ℝ) : 0 ≤ maxJ k g := by
  unfold maxJ
  generalize ((List.range' 1 k).map g) = xs
  induction xs with
  | nil => simp
  | cons x xs ih => exact le_trans ih (le_max_right _ _)

private lemma GamP_nonneg (n d k : ℕ) : 0 ≤ GamP n d k :=
  mul_nonneg (Nat.cast_nonneg _) (maxJ_nonneg k _)

private lemma le_maxJ (k j : ℕ) (g : ℕ → ℝ) (hj : j ∈ Finset.Icc 1 k) :
    g j ≤ maxJ k g := by
  have hfold : ∀ (xs : List ℝ) (a : ℝ), a ∈ xs → a ≤ xs.foldr max 0 := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_max_left _ _
      · exact (ih a ha).trans (le_max_right _ _)
  apply hfold
  apply List.mem_map.mpr
  refine ⟨j, ?_, rfl⟩
  have := Finset.mem_Icc.mp hj
  simp only [List.mem_range'_1]
  omega

/-- Cauchy--Schwarz separates the degrees before taking Gaussian expectations. -/
private lemma upperSum_sq_le (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) :
    upperSum k T Z ^ 2 ≤ (k : ℝ) *
      ∑ j ∈ Finset.Icc 1 k,
        varU (BstLean.Part29.uniformSphere n) (uJ T j Z) / BstLean.Part36.DD n d ^ j := by
  classical
  have hv (j : ℕ) : 0 ≤ varU (BstLean.Part29.uniformSphere n) (uJ T j Z) :=
    integral_nonneg fun _ => sq_nonneg _
  have hD : 0 ≤ BstLean.Part36.DD n d := by
    unfold BstLean.Part36.DD
    positivity
  have hs (j : ℕ) :
      (sdU (BstLean.Part29.uniformSphere n) (uJ T j Z) /
        Real.sqrt (BstLean.Part36.DD n d) ^ j) ^ 2 =
      varU (BstLean.Part29.uniformSphere n) (uJ T j Z) / BstLean.Part36.DD n d ^ j := by
    rw [div_pow, sdU, Real.sq_sqrt (hv j)]
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, Real.sq_sqrt hD]
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 k)
    (f := fun j => sdU (BstLean.Part29.uniformSphere n) (uJ T j Z) /
      Real.sqrt (BstLean.Part36.DD n d) ^ j)
  simpa only [upperSum, hs, Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_id] using h

private lemma upperSum_sq_integrable (hn : 1 ≤ n) (k : ℕ) (T : Tens n) :
    Integrable (fun Z : CoefIdxD n d → ℝ => upperSum k T Z ^ 2)
      (stdGauss (CoefIdxD n d)) := by
  classical
  have hm : Measurable (upperSum (d := d) k T) := by
    unfold upperSum sdU
    apply Finset.measurable_sum
    intro j _
    exact ((varU_uJ_measurable hn T j).sqrt).div_const _
  have hi : Integrable (fun Z : CoefIdxD n d → ℝ => (k : ℝ) *
      ∑ j ∈ Finset.Icc 1 k,
        varU (BstLean.Part29.uniformSphere n) (uJ T j Z) / BstLean.Part36.DD n d ^ j)
      (stdGauss (CoefIdxD n d)) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    exact (varU_uJ_integrable hn T j).div_const _
  apply hi.mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with Z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact upperSum_sq_le k T Z

private lemma upperSum_second_moment_of_degree_bounds (hn : 1 ≤ n) (k : ℕ) (T : Tens n)
    (hdeg : ∀ j ∈ Finset.Icc 1 k,
      (∫ Z : CoefIdxD n d → ℝ,
        varU (BstLean.Part29.uniformSphere n) (uJ T j Z)
          ∂stdGauss (CoefIdxD n d)) / BstLean.Part36.DD n d ^ j ≤
        Gpj n d k j * tj n d k T j) :
    (∫ Z, upperSum k T Z ^ 2 ∂stdGauss (CoefIdxD n d)) ≤
      GamP n d k * Nn n d k T := by
  classical
  have hi (j : ℕ) := (varU_uJ_integrable (d := d) hn T j).div_const
    (BstLean.Part36.DD n d ^ j)
  have ht (j : ℕ) : 0 ≤ tj n d k T j := by
    unfold tj aSq BstLean.Part36.DD
    have hf : 0 ≤ frob (trL 0 (T j)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  calc
    (∫ Z, upperSum k T Z ^ 2 ∂stdGauss (CoefIdxD n d)) ≤
        ∫ Z, (k : ℝ) * ∑ j ∈ Finset.Icc 1 k,
          varU (BstLean.Part29.uniformSphere n) (uJ T j Z) / BstLean.Part36.DD n d ^ j
          ∂stdGauss (CoefIdxD n d) :=
      integral_mono (upperSum_sq_integrable hn k T)
        ((integrable_finsetSum _ (fun j _ => hi j)).const_mul _) (upperSum_sq_le k T)
    _ = (k : ℝ) * ∑ j ∈ Finset.Icc 1 k,
        (∫ Z : CoefIdxD n d → ℝ,
          varU (BstLean.Part29.uniformSphere n) (uJ T j Z) ∂stdGauss (CoefIdxD n d)) /
          BstLean.Part36.DD n d ^ j := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
      simp only [integral_div]
    _ ≤ (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, Gpj n d k j * tj n d k T j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hdeg) (Nat.cast_nonneg _)
    _ ≤ (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, maxJ k (Gpj n d k) * tj n d k T j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (le_maxJ k j _ hj) (ht j)) (Nat.cast_nonneg _)
    _ = GamP n d k * ∑ j ∈ Finset.Icc 1 k, tj n d k T j := by
      rw [← Finset.mul_sum]
      unfold GamP
      ring
    _ ≤ GamP n d k * Nn n d k T :=
      mul_le_mul_of_nonneg_left (sum_tj_le_Nn k T) (GamP_nonneg n d k)

/-- Markov on the square, including the zero second-moment case. -/
private lemma sqrt_tail_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (A β : ℝ)
    (hA : 0 ≤ A) (hβ : 0 < β)
    (hint : Integrable (fun z => S z ^ 2) μ)
    (hbound : (∫ z, S z ^ 2 ∂μ) ≤ A) :
    μ {z | Real.sqrt (A / β) < S z} ≤ ENNReal.ofReal β := by
  by_cases hzero : A = 0
  · subst A
    have hi : (∫ z, S z ^ 2 ∂μ) = 0 :=
      le_antisymm hbound (integral_nonneg fun _ => sq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun z => sq_nonneg (S z)) hint).mp hi
    have hevent : μ {z | Real.sqrt (0 / β) < S z} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae] with z hz
      have hz' : S z = 0 := sq_eq_zero_iff.mp hz
      simp [hz']
    rw [hevent]
    exact bot_le
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
    have hc : 0 < A / β := div_pos hApos hβ
    have hsub : {z | Real.sqrt (A / β) < S z} ⊆ {z | A / β ≤ S z ^ 2} := by
      intro z hz
      change Real.sqrt (A / β) < S z at hz
      change A / β ≤ S z ^ 2
      have hs := Real.sqrt_nonneg (A / β)
      have hsq := Real.sq_sqrt hc.le
      nlinarith
    have hm := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun z => sq_nonneg (S z)) hint (A / β)
    have hreal : (μ {z | A / β ≤ S z ^ 2}).toReal ≤ β := by
      have hmul : A / β * (μ {z | A / β ≤ S z ^ 2}).toReal ≤ A := hm.trans hbound
      have hdiv : (μ {z | A / β ≤ S z ^ 2}).toReal ≤ A / (A / β) :=
        (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hmul)
      have hid : A / (A / β) = β := by field_simp
      simpa [hid] using hdiv
    calc μ {z | Real.sqrt (A / β) < S z} ≤ μ {z | A / β ≤ S z ^ 2} := measure_mono hsub
      _ = ENNReal.ofReal ((μ {z | A / β ≤ S z ^ 2}).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal β := ENNReal.ofReal_le_ofReal hreal

/-- **Lemma `upper`**: `Pr{Σ_j D^{−j/2} sd_x u_j > √(Γ' 𝒩(f)/β)} ≤ β`. -/
theorem upper_event (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (T : Tens n) (hT : TSymm k T) (β : ℝ) (hβ : 0 < β) :
    stdGauss (CoefIdxD n d) {Z | Real.sqrt (GamP n d k * Nn n d k T / β) < upperSum k T Z} ≤
      ENNReal.ofReal β := by
  classical
  by_cases hk : k = 0
  · subst k
    have he : {Z : CoefIdxD n d → ℝ |
        Real.sqrt (GamP n d 0 * Nn n d 0 T / β) < upperSum 0 T Z} = ∅ := by
      ext Z
      simp [upperSum, GamP]
    rw [he, measure_empty]
    exact bot_le
  by_cases hb : 1 ≤ β
  · exact (prob_le_one).trans (by simpa using ENNReal.ofReal_le_ofReal hb)
  have hA : 0 ≤ GamP n d k * Nn n d k T :=
    mul_nonneg (GamP_nonneg n d k) (Nn_nonneg k T)
  -- The remaining step is the fixed-input Gaussian tensor estimate.
  have hraw : ∀ j ∈ Finset.Icc 1 k,
      (∫ Z : CoefIdxD n d → ℝ,
        varU (BstLean.Part29.uniformSphere n) (uJ T j Z)
          ∂stdGauss (CoefIdxD n d)) ≤
        degreeUpperConstant n d j * frob (T j) := by
    intro j hj
    by_cases hj1 : j = 1
    · subst j
      exact degree_variance_one hn hd T
    have hj2 : 2 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hsym := hT j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    apply degree_variance_from_pointwise hn hd T j
    intro x hx
    exact (pointwise_eq hn hd T j hsym x hx _).le
  have hdeg : ∀ j ∈ Finset.Icc 1 k,
      (∫ Z : CoefIdxD n d → ℝ,
        varU (BstLean.Part29.uniformSphere n) (uJ T j Z)
          ∂stdGauss (CoefIdxD n d)) / BstLean.Part36.DD n d ^ j ≤
        Gpj n d k j * tj n d k T j := by
    intro j hj
    rw [Gpj_mul_tj hn (Finset.mem_Icc.mp hj).1 k T]
    exact div_le_div_of_nonneg_right (hraw j hj) (pow_nonneg (DD_pos hn).le _)
  exact sqrt_tail_of_second_moment _ (upperSum k T)
    (GamP n d k * Nn n d k T) β hA hβ (upperSum_sq_integrable hn k T)
      (upperSum_second_moment_of_degree_bounds hn k T hdeg)


end BstLean.Part41
