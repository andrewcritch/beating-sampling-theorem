import BstLean.Part238Assembly
import BstLean.Part235Charge

/-! Part 238: the actual mode-failure event of the sharp assembly and its single charge.
A fixed-pair three-mode TI hypothesis integrates to a pair-mass event by Fubini and Markov.
No independence between inputs is assumed; the inputs share the Agent matrices. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part160 BstLean.Part182
open BstLean.Part153 (nrm nuA)
open BstLean.Part151 (jac mask measurable_mask)

variable {n : ℕ}

/-- The raw Jacobian is jointly measurable in the weights and the point. -/
lemma measurable_jac_comp {α : Type*} [MeasurableSpace α] {m : ℕ}
    {A : α → Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin m) ℝ} {x : α → Fin n → ℝ}
    (hA : Measurable A) (hx : Measurable x) :
    Measurable (fun q => jac (A q).1 (A q).2 (x q)) := by
  have hA1 : Measurable (fun q => (A q).1) := measurable_fst.comp hA
  have hA2 : Measurable (fun q => (A q).2) := measurable_snd.comp hA
  have hmv : ∀ {p r : ℕ} {f : α → Matrix (Fin p) (Fin r) ℝ} {g : α → Fin r → ℝ},
      Measurable f → Measurable g → Measurable (fun q => f q *ᵥ g q) := by
    intro p r f g hf hg
    have hc : Continuous (fun z : Matrix (Fin p) (Fin r) ℝ × (Fin r → ℝ) => z.1 *ᵥ z.2) :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    exact hc.measurable.comp (hf.prodMk hg)
  have hc1 : Measurable (fun q => (A q).1 *ᵥ x q) := hmv hA1 hx
  have hc2 : Measurable (fun q => (A q).2 *ᵥ reluV ((A q).1 *ᵥ x q)) :=
    hmv hA2 (continuous_reluV.measurable.comp hc1)
  refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
  have h1 : ∀ i : Fin m, Measurable (fun q => ((A q).1 *ᵥ x q) i) := fun i =>
    (measurable_pi_apply i).comp hc1
  have h2 : Measurable (fun q => ((A q).2 *ᵥ reluV ((A q).1 *ᵥ x q)) j) :=
    (measurable_pi_apply j).comp hc2
  have hE1 : ∀ i, Measurable (fun q => (A q).1 i l) := fun i =>
    (measurable_pi_apply l).comp ((measurable_pi_apply i).comp hA1)
  have hE2 : ∀ i, Measurable (fun q => (A q).2 j i) := fun i =>
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hA2)
  change Measurable (fun q => mask (((A q).2 *ᵥ reluV ((A q).1 *ᵥ x q)) j) *
    ∑ i, (A q).2 j i * mask (((A q).1 *ᵥ x q) i) * (A q).1 i l)
  exact (measurable_mask.comp h2).mul (Finset.measurable_sum _ fun i _ =>
    ((hE2 i).mul (measurable_mask.comp (h1 i))).mul (hE1 i))

lemma measurable_eTan_comp {α : Type*} [MeasurableSpace α] {x x' : α → Fin n → ℝ}
    (hx : Measurable x) (hx' : Measurable x') : Measurable (fun q => eTan (x q) (x' q)) := by
  have hxi : ∀ k, Measurable (fun q => x q k) := fun k => (measurable_pi_apply k).comp hx
  have hxi' : ∀ k, Measurable (fun q => x' q k) := fun k => (measurable_pi_apply k).comp hx'
  have hd : Measurable (fun q => x q ⬝ᵥ x' q) :=
    Finset.measurable_sum _ fun k _ => (hxi k).mul (hxi' k)
  refine measurable_pi_iff.mpr fun i => ?_
  change Measurable (fun q => (√(1 - (x q ⬝ᵥ x' q) ^ 2))⁻¹ * (x' q i - (x q ⬝ᵥ x' q) * x q i))
  exact ((measurable_const.sub (hd.pow_const 2)).sqrt.inv).mul
    ((hxi' i).sub (hd.mul (hxi i)))

lemma measurable_PEm_comp {α : Type*} [MeasurableSpace α] {x x' : α → Fin n → ℝ}
    (hx : Measurable x) (hx' : Measurable x') : Measurable (fun q => PEm (x q) (x' q)) := by
  have he := measurable_eTan_comp hx hx'
  have hei : ∀ k, Measurable (fun q => eTan (x q) (x' q) k) :=
    fun k => (measurable_pi_apply k).comp he
  have hxi : ∀ k, Measurable (fun q => x q k) := fun k => (measurable_pi_apply k).comp hx
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  change Measurable (fun q =>
    (1 : Matrix (Fin n) (Fin n) ℝ) i j - x q i * x q j - eTan (x q) (x' q) i * eTan (x q) (x' q) j)
  exact (measurable_const.sub ((hxi i).mul (hxi j))).sub ((hei i).mul (hei j))

/-- Measurability of the mode-bound predicate as a function of the two Jacobians and points. -/
lemma measurableSet_modeBounds {α : Type*} [MeasurableSpace α] {m : ℕ}
    {J J' : α → Matrix (Fin m) (Fin n) ℝ} {x x' : α → Fin n → ℝ}
    (hJ : Measurable J) (hJ' : Measurable J') (hx : Measurable x) (hx' : Measurable x')
    (kE ko ks cp : ℝ) :
    MeasurableSet {q | ModeBounds (J q) (J' q) kE ko ks cp (x q) (x' q)} := by
  have hxx : Measurable (fun q => (x q, x' q)) := hx.prodMk hx'
  have hx'x : Measurable (fun q => (x' q, x q)) := hx'.prodMk hx
  have hP : Measurable (fun q => PEm (x q) (x' q)) := measurable_PEm_comp hx hx'
  have he : Measurable (fun q => eTan (x q) (x' q)) := measurable_eTan_comp hx hx'
  have he' : Measurable (fun q => eTan (x' q) (x q)) := measurable_eTan_comp hx' hx
  have hM : Measurable (fun q => (J q)ᵀ * J' q) := BstLean.Part182.measurable_tmul hJ hJ'
  have hM' : Measurable (fun q => (J' q)ᵀ * J q) := BstLean.Part182.measurable_tmul hJ' hJ
  have hmul : ∀ {p r s : ℕ} {f : α → Matrix (Fin p) (Fin r) ℝ} {g : α → Matrix (Fin r) (Fin s) ℝ},
      Measurable f → Measurable g → Measurable (fun q => f q * g q) := by
    intro p r s f g hf hg
    have hc : Continuous (fun z : Matrix (Fin p) (Fin r) ℝ × Matrix (Fin r) (Fin s) ℝ =>
        z.1 * z.2) := continuous_fst.matrix_mul continuous_snd
    exact hc.measurable.comp (hf.prodMk hg)
  have hmv : ∀ {p r : ℕ} {f : α → Matrix (Fin p) (Fin r) ℝ} {g : α → Fin r → ℝ},
      Measurable f → Measurable g → Measurable (fun q => f q *ᵥ g q) := by
    intro p r f g hf hg
    have hc : Continuous (fun z : Matrix (Fin p) (Fin r) ℝ × (Fin r → ℝ) => z.1 *ᵥ z.2) :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    exact hc.measurable.comp (hf.prodMk hg)
  have hdot : ∀ {f g : α → Fin n → ℝ}, Measurable f → Measurable g →
      Measurable (fun q => f q ⬝ᵥ g q) := by
    intro f g hf hg
    have hc : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) => z.1 ⬝ᵥ z.2) :=
      continuous_fst.dotProduct continuous_snd
    exact hc.measurable.comp (hf.prodMk hg)
  have hdotm : ∀ {f g : α → Fin m → ℝ}, Measurable f → Measurable g →
      Measurable (fun q => f q ⬝ᵥ g q) := by
    intro f g hf hg
    have hc : Continuous (fun z : (Fin m → ℝ) × (Fin m → ℝ) => z.1 ⬝ᵥ z.2) :=
      continuous_fst.dotProduct continuous_snd
    exact hc.measurable.comp (hf.prodMk hg)
  have hnrm : ∀ {f : α → Fin n → ℝ}, Measurable f → Measurable (fun q => nrm (f q)) := by
    intro f hf
    unfold nrm normSq
    exact (Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hf).pow_const 2).sqrt
  have S1 : MeasurableSet {q | (x q ⬝ᵥ x' q) ^ 2 ≤ cp ^ 2} :=
    measurableSet_le ((hdot hx hx').pow_const 2) measurable_const
  have hE : Measurable (fun q => PEm (x q) (x' q) * ((J q)ᵀ * J' q) * PEm (x q) (x' q)) :=
    hmul (hmul hP hM) hP
  have S2 : MeasurableSet {q | opN (PEm (x q) (x' q) * ((J q)ᵀ * J' q) * PEm (x q) (x' q)) ≤
      (n : ℝ) * kE} :=
    measurableSet_le (opN_continuous.measurable.comp hE) measurable_const
  have S3 : MeasurableSet {q | nrm (PEm (x q) (x' q) *ᵥ (((J q)ᵀ * J' q) *ᵥ eTan (x' q) (x q))) ≤
      (n : ℝ) * ko} :=
    measurableSet_le (hnrm (hmv hP (hmv hM he'))) measurable_const
  have S4 : MeasurableSet {q | nrm (PEm (x q) (x' q) *ᵥ (((J' q)ᵀ * J q) *ᵥ eTan (x q) (x' q))) ≤
      (n : ℝ) * ko} :=
    measurableSet_le (hnrm (hmv hP (hmv hM' he))) measurable_const
  have S5 : MeasurableSet {q | |(J q *ᵥ eTan (x q) (x' q)) ⬝ᵥ (J' q *ᵥ eTan (x' q) (x q))| ≤
      (n : ℝ) * ks} :=
    measurableSet_le (hdotm (hmv hJ he) (hmv hJ' he')).abs measurable_const
  have e : {q | ModeBounds (J q) (J' q) kE ko ks cp (x q) (x' q)} =
      {q | (x q ⬝ᵥ x' q) ^ 2 ≤ cp ^ 2} ∩
      ({q | opN (PEm (x q) (x' q) * ((J q)ᵀ * J' q) * PEm (x q) (x' q)) ≤ (n : ℝ) * kE} ∩
      ({q | nrm (PEm (x q) (x' q) *ᵥ (((J q)ᵀ * J' q) *ᵥ eTan (x' q) (x q))) ≤ (n : ℝ) * ko} ∩
      ({q | nrm (PEm (x q) (x' q) *ᵥ (((J' q)ᵀ * J q) *ᵥ eTan (x q) (x' q))) ≤ (n : ℝ) * ko} ∩
      {q | |(J q *ᵥ eTan (x q) (x' q)) ⬝ᵥ (J' q *ᵥ eTan (x' q) (x q))| ≤ (n : ℝ) * ks}))) := by
    ext q
    simp only [ModeBounds, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [e]
  exact S1.inter (S2.inter (S3.inter (S4.inter S5)))

/-- The joint mode-failure set: a core pair whose three TI mode bounds (or overlap cap) fail. -/
def modeBadSet (n : ℕ) (w : BstLean.Part199.Window) (kE ko ks cp : ℝ) :
    Set (AgFam n × ((Fin n → ℝ) × (Fin n → ℝ))) :=
  {q | q.2 ∈ GammaS q.1.1.1 w.t w.z w.pair ∧
    ¬ ModeBounds (jac q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2.1)))
      (jac q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2.2))) kE ko ks cp
      (sphPt (q.1.1.1 + q.1.1.2 • q.2.1)) (sphPt (q.1.1.1 + q.1.1.2 • q.2.2))}

theorem measurableSet_modeBadSet (w : BstLean.Part199.Window) (kE ko ks cp : ℝ) :
    MeasurableSet (modeBadSet n w kE ko ks cp) := by
  have hc : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.1.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hτ : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hA : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.1.2) :=
    measurable_snd.comp measurable_fst
  have h1 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.2.1) :=
    measurable_fst.comp measurable_snd
  have h2 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hx1 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      sphPt (q.1.1.1 + q.1.1.2 • q.2.1)) := measurable_sphPt.comp (hc.add (hτ.smul h1))
  have hx2 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      sphPt (q.1.1.1 + q.1.1.2 • q.2.2)) := measurable_sphPt.comp (hc.add (hτ.smul h2))
  have hJ1 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      jac q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2.1))) :=
    measurable_jac_comp hA hx1
  have hJ2 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      jac q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2.2))) :=
    measurable_jac_comp hA hx2
  have hO := measurableSet_OmegaS_joint (n := n) w.t w.z
  have hO1 : MeasurableSet {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
      q.2.1 ∈ OmegaS q.1.1.1 w.t w.z} := (hc.prodMk h1) hO
  have hO2 : MeasurableSet {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
      q.2.2 ∈ OmegaS q.1.1.1 w.t w.z} := (hc.prodMk h2) hO
  have hp1 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => perpC q.1.1.1 q.2.1) :=
    measurable_perpC_joint.comp (hc.prodMk h1)
  have hp2 : Measurable (fun q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) => perpC q.1.1.1 q.2.2) :=
    measurable_perpC_joint.comp (hc.prodMk h2)
  have hG3 : MeasurableSet {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
      |perpC q.1.1.1 q.2.1 ⬝ᵥ perpC q.1.1.1 q.2.2| ≤ w.pair * gPlus n w.z} :=
    measurableSet_le (measurable_dot hp1 hp2).abs measurable_const
  have hΓ : MeasurableSet {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
      q.2 ∈ GammaS q.1.1.1 w.t w.z w.pair} := by
    have e : {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) |
        q.2 ∈ GammaS q.1.1.1 w.t w.z w.pair} =
        {q : AgFam n × ((Fin n → ℝ) × (Fin n → ℝ)) | q.2.1 ∈ OmegaS q.1.1.1 w.t w.z} ∩
        ({q | q.2.2 ∈ OmegaS q.1.1.1 w.t w.z} ∩
          {q | |perpC q.1.1.1 q.2.1 ⬝ᵥ perpC q.1.1.1 q.2.2| ≤ w.pair * gPlus n w.z}) := by
      ext q
      simp only [GammaS, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [e]
    exact hO1.inter (hO2.inter hG3)
  exact hΓ.inter (measurableSet_modeBounds hJ1 hJ2 hx1 hx2 kE ko ks cp).compl

end BstLean.Part238
