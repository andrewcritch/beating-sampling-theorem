import BstLean.Part235Routes
import BstLean.Part222Allowance
import BstLean.Part241Frontier

/-! Part 243: one retained Agent event for the fixed-radius bridge.
The sharp TI inputs remain explicit. All input averages use the original stand-in distribution. -/
namespace BstLean.Part243
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part188
open BstLean.Part199 BstLean.Part235 BstLean.Part161 BstLean.Part182
open BstLean.Part169 (paperDesignP)

noncomputable def covarianceEvent (n : ℕ) (thetaLo thetaHi lam₀ lam₁ : ℝ) : Set (Ret n) :=
  agentEv (paperDesignP n) (JointCovEvent n exampleWide exampleCore
    thetaLo thetaHi lam₀ lam₁ ((50 * exp (-46)) / (1 / 4000)))

lemma covarianceEvent_measurable (n : ℕ) (thetaLo thetaHi lam₀ lam₁ : ℝ) :
    MeasurableSet (covarianceEvent n thetaLo thetaHi lam₀ lam₁) :=
  measurableSet_agentEv _ (measurableSet_JointCovEvent _ _ _ _ _ _ _ _)

/-- One local frame certificate keeps its full and parallel centre errors distinct. -/
structure FrameInputs (n : ℕ) (c : Ret n) (thetaLo thetaHi lam₀ lam₁ cf : ℝ) where
  M : ℝ
  H : ℝ
  xiP : ℝ
  E : ℝ
  u : ℝ
  d : ℝ
  N : ℝ
  xiF : ℝ
  beta : ℝ
  fourth : ℝ
  scale_pos : 0 < (paperDesignP n).tau0 c
  window : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
    Icc thetaLo thetaHi
  thetaHi_lt : thetaHi < 1
  wide_radius : radiusMinus n
    (BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c)) exampleWide < 1
  core_radius : radiusMinus n
    (BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c)) exampleCore < 1
  centre_pos : 0 < normSq ((paperDesignP n).bA c.1 c.2.1.1)
  centre_nonneg : ∀ j, 0 ≤ (paperDesignP n).bA c.1 c.2.1.1 j
  interfaces : WFInterfaces (paperDesignP n) c M H xiP
  centre_energy : centreEnergy (paperDesignP n) c ≤ E
  u_pos : 0 < u
  u_lt : u < 1
  cutoff_pos : 0 < d
  cutoff_lt : d < (1-u)^2
  gap_pos : 0 < √((1-u)^2-d) - (√E + √(xiP/n))
  covariance_nonneg : 0 ≤ N
  fourth_nonneg : 0 ≤ fourth
  fourth_bound : BstLean.Part153.Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2
    ((paperDesignP n).tau0 c) ≤ fourth * (2 / (n : ℝ)) / n
  covariance_scalar : jointCovScalar n
    (BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c)) exampleWide exampleCore
    lam₀ lam₁ (1 - 4 * BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) / n)⁻¹
    fourth ((50 * exp (-46)) / (1 / 4000)) ≤ N
  full_centre : CENTRE_at (paperDesignP n) c xiF
  mass_scalar : BstLean.Part222.massBound n M H xiP E u d ≤ beta
  frame_scalar : (N + xiF) / d + beta ≤ cf

theorem frame_from_inputs {n : ℕ} (hn : 50 ≤ n) {c : Ret n}
    {thetaLo thetaHi lam₀ lam₁ cf : ℝ} (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁)
    (F : FrameInputs n c thetaLo thetaHi lam₀ lam₁ cf)
    (hc : c ∈ covarianceEvent n thetaLo thetaHi lam₀ lam₁) :
    ∀ v : Fin (mA n) → ℝ,
      ∫ ξ, (∑ j, BstLean.Part134.eDir ((paperDesignP n).bA c.1 c.2.1.1)
        (hStand (paperDesignP n) c ξ) j * v j)^2 ∂BstLean.Part29.stdGauss (Fin n) ≤
      cf / n * ∑ j, v j^2 := by
  have hcov := cov_at_joint (by omega) (paperDesignP n) c F.scale_pos
    exampleWide exampleCore example_nested hl₀ hl₁ F.fourth_nonneg F.window
    F.thetaHi_lt F.wide_radius F.core_radius
    F.fourth_bound (hc F.scale_pos) F.covariance_scalar
  exact BstLean.Part222.freeAllowance_frame (by omega) (paperDesignP n) c
    F.scale_pos F.centre_pos F.centre_nonneg F.interfaces F.centre_energy
    F.u_pos F.u_lt F.cutoff_pos F.cutoff_lt F.gap_pos F.covariance_nonneg hcov
    F.full_centre F.mass_scalar F.frame_scalar

/-- The root package retains the stored-pass moments and the selected split. -/
structure RootInputs (n : ℕ) (t : ℝ) (c : Ret n) (root : ℝ) where
  split : SplitData n
  chi : ℝ
  biasFloor : ℝ
  epsilon : ℝ
  vmax : ℝ
  aw : ℝ
  af : ℝ
  Hf : ℝ
  Cv : ℝ
  B : ℝ
  mix : ℝ
  displacement : ℝ
  window : WINDOW (paperDesignP n) c
  passes : BstLean.Part241.PassInputs c split chi biasFloor epsilon vmax aw af Hf Cv
  fluctuation : FLUCT_hyp (paperDesignP n) t c split
    (√(2 * (1 + split.eta⁻¹) * B) + mix + √displacement)
  scalar : √(2 * (1 + split.eta⁻¹) * B) + mix + √displacement +
    BstLean.Part241.biasRoot n chi biasFloor epsilon vmax aw af Hf Cv +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ root

/-- The bridge consumes only the charged event, frame and replacement root. -/
structure AgentPackage (n : ℕ) (H : Set (Ret n)) (radius frame root charge t : ℝ) where
  event : Set (Ret n)
  measurable : MeasurableSet event
  retained_charge : (retDist (paperCentres n)).real (H ∩ eventᶜ) ≤ charge
  frame_bound : FRAME_A_hyp (paperDesignP n) (frame / n)
    (goodSet H event (HbarW (paperDesignP n)) radius)
  root_bound : REPLA_mix_hyp (paperDesignP n) t root
    (goodSet H event (HbarW (paperDesignP n)) radius)

/-- Sharp TI pays once. The other retained-event inputs keep their separate charge.
No union payment is added for local frame or root certificates. -/
noncomputable def agentPackage {n : ℕ} (hn : 8000 ≤ n)
    {H E : Set (Ret n)} (hE : MeasurableSet E)
    {radius frame root charge t thetaLo thetaHi lam₀ lam₁ : ℝ}
    {wideLo wideHi coreLo coreHi : ℝ}
    (hcharge : (retDist (paperCentres n)).real (H ∩ Eᶜ) ≤ charge)
    (hτ : TauWorld (paperDesignP n))
    (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁) (hlam : lam₁ ≤ lam₀)
    (hwide_order : wideLo ≤ wideHi) (hcore_order : coreLo ≤ coreHi)
    (hwide_guard : ∀ θ ∈ Icc thetaLo thetaHi,
      OverlapGuard n θ exampleWide wideLo wideHi)
    (hcore_guard : ∀ θ ∈ Icc thetaLo thetaHi,
      OverlapGuard n θ exampleCore coreLo coreHi)
    (hwide : ∀ j < 12, TI_hyp n (overlapLo wideLo wideHi j)
      (overlapHi wideLo wideHi j) lam₀ (50 * exp (-46)))
    (hcore : ∀ j < 12, TI_hyp n (overlapLo coreLo coreHi j)
      (overlapHi coreLo coreHi j) lam₁ (50 * exp (-46)))
    (hframe : ∀ c ∈ goodSet H (E ∩ covarianceEvent n thetaLo thetaHi lam₀ lam₁)
      (HbarW (paperDesignP n)) radius,
      Nonempty (FrameInputs n c thetaLo thetaHi lam₀ lam₁ frame))
    (hroot : ∀ c ∈ goodSet H (E ∩ covarianceEvent n thetaLo thetaHi lam₀ lam₁)
      (HbarW (paperDesignP n)) radius, Nonempty (RootInputs n t c root)) :
    AgentPackage n H radius frame root (charge + 1 / 4000) t := by
  have hTI := JointCovEvent_ret_charge (by omega) (paperDesignP n) hτ
    exampleWide exampleCore example_nested hlam (by positivity) (by norm_num : (0 : ℝ) < 1 / 4000)
    hwide_guard hcore_guard (TI_of_twelve_cells hwide_order hwide)
    (TI_of_twelve_cells hcore_order hcore)
  refine { event := E ∩ covarianceEvent n thetaLo thetaHi lam₀ lam₁
           measurable := hE.inter (covarianceEvent_measurable _ _ _ _ _)
           retained_charge := ?_
           frame_bound := ?_
           root_bound := ?_ }
  · have hs : H ∩ (E ∩ covarianceEvent n thetaLo thetaHi lam₀ lam₁)ᶜ ⊆
        (H ∩ Eᶜ) ∪ (covarianceEvent n thetaLo thetaHi lam₀ lam₁)ᶜ := by
      intro c hc
      by_cases he : c ∈ E
      · exact Or.inr (fun ht => hc.2 ⟨he, ht⟩)
      · exact Or.inl ⟨hc.1, he⟩
    exact (measureReal_mono hs (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add hcharge hTI))
  · intro c hc v
    obtain ⟨F⟩ := hframe c hc
    exact frame_from_inputs (by omega) hl₀ hl₁ F hc.2.2 v
  · intro c hc
    obtain ⟨R⟩ := hroot c hc
    exact (BstLean.Part241.root_new_8000 (by omega) t c R.split R.window R.passes
      R.fluctuation).trans R.scalar

end BstLean.Part243
#print axioms BstLean.Part243.covarianceEvent_measurable
#print axioms BstLean.Part243.frame_from_inputs
#print axioms BstLean.Part243.agentPackage
