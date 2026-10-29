import BstLean.Part192Bridge
import Lean

/-! Part 192: retained-event witnesses from the existing lower baseline chain.
The extraction tactic unfolds only the concluding theorem applications and keeps
their local proof bindings. Lean checks the resulting witness proof in its kernel.
The tactic changes no existing declaration and assumes no certificate premise. -/

namespace BstLean.Part192
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part156 (aL hAL hWL cWL)

/-- This is the legacy Agent junction, with its actual shared event and payment.
The sharp AgentCell remains a separate interface for the later analytic rows. -/
structure BaselineJunction (n : ℕ) (t : ℝ) where
  design : Design n
  program_identity : design = paperDesignP n
  hidden : Set (Ret n)
  event : Set (Ret n)
  hiddenCharge : ℝ
  worldMoment : ℝ
  retainedCharge : ℝ
  hidden_identity : hidden = BstLean.Part159.Hof (BstLean.Part159.GPap n)
  hiddenCharge_identity : hiddenCharge = BstLean.Part188.Base159_R.δPap
  worldMoment_identity : worldMoment = BstLean.Part188.Base159_R.vPap
  events : EVENTS_hyp design.toCentres hidden event (HbarW design)
    hiddenCharge worldMoment retainedCharge
  retained_budget : hiddenCharge + worldMoment / hWL ^ 2 + retainedCharge ≤
    5111 / 1000000
  world_frame : FRAME_W_hyp design.toCentres (cWL / n)
    (goodSet hidden event (HbarW design) hWL)
  agent_inputs : FrameInputs design (goodSet hidden event (HbarW design) hWL)
  agent_frame : FRAME_A_hyp design (193 / 100 / n)
    (goodSet hidden event (HbarW design) hWL)
  agent_root : REPLA_mix_hyp design t hAL
    (goodSet hidden event (HbarW design) hWL)

theorem baseline_witness_of {n : ℕ} (D : Design n) (t : ℝ)
    {H E : Set (Ret n)} {δhid vW δret : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E (HbarW D) δhid vW δret)
    (hledger : δhid + vW / hWL ^ 2 + δret ≤ 5111 / 1000000)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (193 / 100 / n) (goodSet H E (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E (HbarW D) hWL))
    (hD : D = paperDesignP n) (hInputs : FrameInputs D (goodSet H E (HbarW D) hWL))
    (hH : H = BstLean.Part159.Hof (BstLean.Part159.GPap n))
    (hδ : δhid = BstLean.Part188.Base159_R.δPap)
    (hv : vW = BstLean.Part188.Base159_R.vPap) :
    Nonempty (BaselineJunction n t) :=
  ⟨⟨D, hD, H, E, δhid, vW, δret, hH, hδ, hv,
    hEv, hledger, hFW, hInputs, hFA, hRA⟩⟩

open Lean Meta Elab Tactic in
private partial def revealProof (e : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "The baseline proof projection did not expose a constructor."
  let e ← whnf e
  match e.getAppFn with
  | .proj name index major =>
    let major ← revealProof major (fuel - 1)
    revealProof (mkAppN (.proj name index major) e.getAppArgs) (fuel - 1)
  | .const name levels =>
    let ci ← getConstInfo name
    if let some val := ci.value? (allowOpaque := true) then
      revealProof (mkAppN (val.instantiateLevelParams ci.levelParams levels)
        e.getAppArgs).headBeta (fuel - 1)
    else return e
  | _ => return e

open Lean Meta Elab Tactic in
private partial def extractWitness (e : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "Baseline extraction exhausted its theorem depth."
  let e ← instantiateMVars e
  match e with
  | .letE n ty val body _ =>
    withLetDecl n ty val fun v => do
      let result ← extractWitness (body.instantiate1 v) (fuel - 1)
      mkLetFVars #[v] result
  | .lam n ty body bi =>
    withLocalDecl n bi ty fun v => do
      let result ← extractWitness (body.instantiate1 v) (fuel - 1)
      mkLambdaFVars #[v] result
  | _ =>
    let e ← whnf e
    if e.isLet then return ← extractWitness e (fuel - 1)
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``And.rec then
      if args.size != 5 then throwError "Unexpected And elimination signature: {args.size}."
      let left ← mkAppM ``And.left #[args[4]!]
      let right ← mkAppM ``And.right #[args[4]!]
      return ← extractWitness (mkAppN args[3]! #[left, right]).headBeta (fuel - 1)
    if fn.isConstOf ``Exists.rec then
      if args.size != 5 then throwError "Unexpected Exists elimination signature: {args.size}."
      let major ← revealProof args[4]! 200
      unless major.getAppFn.isConstOf ``Exists.intro do
        throwError "The baseline existential witness did not expose its constructor."
      let witnesses := major.getAppArgs
      return ← extractWitness
        (mkAppN args[3]! (witnesses.extract 2 4)).headBeta (fuel - 1)
    if fn.isConstOf ``BstLean.Part190.Frame16200.classifier_frame_16200K16 then
      if args.size != 14 then throwError "The baseline junction signature changed: {args.size}."
      let fa ← whnf args[12]!
      unless fa.getAppFn.isConstOf ``BstLean.Part190.Frame16200.frameA_K_16200 do
        throwError "The baseline frame is not the checked frame input application: {fa.getAppFn}."
      let fs := fa.getAppArgs
      if fs.size != 19 then throwError "The frame signature changed: {fs.size}."
      let inputs ← mkAppM ``FrameInputs.mk (#[fs[3]!] ++ fs.extract 5 19)
      let hD ← mkEqRefl args[2]!
      let hH ← mkEqRefl args[4]!
      let hδ ← mkEqRefl args[6]!
      let hv ← mkEqRefl args[7]!
      return ← mkAppM ``baseline_witness_of
        (#[args[2]!, args[3]!] ++ args.extract 9 14 ++ #[hD, inputs, hH, hδ, hv])
    match fn with
    | .const name _ =>
      let ci ← getConstInfo name
      if let some val := ci.value? (allowOpaque := true) then
        let val := val.instantiateLevelParams ci.levelParams fn.constLevels!
        return ← extractWitness (mkAppN val args).headBeta (fuel - 1)
      throwError "Baseline extraction reached a declaration without a proof body: {name}."
    | .proj .. =>
      let exposed ← revealProof e 200
      extractWitness exposed (fuel - 1)
    | _ => throwError "Baseline extraction reached an unsupported proof head: {fn}."

open Lean Meta Elab Tactic in
elab "extract_baseline " term:term : tactic => do
  let proof ← elabTerm term none
  let witness ← extractWitness proof 1000
  closeMainGoal `extract_baseline witness

/-- The lower baseline chain supplies an actual charged Agent frame/root event. -/
theorem baseline16200 {n : ℕ} (hn : 16200 ≤ n) (hN : n ≤ 16384) (t : ℝ) :
    Nonempty (BaselineJunction n t) := by
  extract_baseline (BstLean.Part190.classifier_paper_uncond_16200HB
    ⟨BstLean.Part180.hq_proved, BstLean.Part190.FREE16200K_proved⟩
    BstLean.Part184.EnB_proved BstLean.Part184.EnFB_proved
    BstLean.Part190.M.BiasRA82_proved hn hN t)

end BstLean.Part192
#print axioms BstLean.Part192.baseline_witness_of
#print axioms BstLean.Part192.baseline16200
