import BstLean.Part287Interval
import BstLean.Part285Downstream

/-! A band constructor from World packages, sharp roots and block frame supplies.
The functions below accept interval proofs; no enumeration of dimensions is needed. -/
namespace BstLean.Part287

open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169
open BstLean.Part188 BstLean.Part192 BstLean.Part196
open BstLean.Part280 BstLean.Part285.Interval BstLean.Part285.Downstream

/-- Frame and source data for one World package. A block certificate supplies this
record uniformly on its block; the root band can have different endpoints. -/
structure BlockFrameInputs (n : ℕ) {w : WorldParameters}
    (W : WorldPackage (paperProgram n) w) (a : AgentParameters) where
  event : Set (BstLean.Part160.AgFam n)
  cell : Fin 60 → Set ℝ
  caps : Fin 60 → ℝ
  measurable : MeasurableSet event
  payment : (retDist (paperCentres n)).real
    (BstLean.Part160.agentEv (paperDesignP n) event)ᶜ ≤ (1 / 4000 : ℝ)
  frame : ∀ {hW : ℝ} c, c ∈ goodSet (Hof W.hidden)
    (BstLean.Part262.sourceBase n ∩ BstLean.Part259.covarianceGood event)
    (HbarW (paperDesignP n)) hW →
    Nonempty (BstLean.Part259.LocalFrameInputs n event cell caps c a.frame)
  localRoot : BstLean.Part262.LocalRootSupply n (Hof W.hidden)
  paidWindow : PaidWindow n (Hof W.hidden)

/-- Analytic inputs on one band. Root and table allowances can be constant on a
root band or use Part285's dimension-dependent selectors. -/
structure BandInputs (lo hi : ℕ) where
  dimension : 13225 ≤ lo
  worldParameters : ℕ → WorldParameters
  agentParameters : ℕ → AgentParameters
  world : ∀ n ∈ Icc lo hi, WorldPackage (paperProgram n) (worldParameters n)
  master : ∀ n ∈ Icc lo hi, MasterCertificate n (worldParameters n) (agentParameters n)
  rootAllowance : ℕ → ℝ
  tableAllowance : ℕ → ℝ
  root : ∀ n ∈ Icc lo hi, SharpRootCertificate n (rootAllowance n)
    (intervalCaps (tableAllowance n)) (sharpTableN n) (m2Guard n)
  root_le : ∀ n ∈ Icc lo hi, rootAllowance n ≤ (agentParameters n).root
  block : ∀ n (hn : n ∈ Icc lo hi), BlockFrameInputs n (world n hn) (agentParameters n)
  payment : ∀ n ∈ Icc lo hi,
    (601 / 10 ^ 6 : ℝ) + tableAllowance n + 3 / 10000 ≤ (agentParameters n).charge
  compatible : ∀ n (hn : n ∈ Icc lo hi),
    (agentParameters n).charge ≤ (master n hn).retainedCharge

/-- The only per-dimension wrapper: instantiate the supplied band and block records. -/
noncomputable def BandInputs.row {lo hi : ℕ} (B : BandInputs lo hi)
    (n : ℕ) (hn : n ∈ Icc lo hi) : BstLean.Part259.RowInputs n :=
  row_from_sharp_supplies (B.dimension.trans hn.1)
    (B.world n hn) (B.agentParameters n) (B.master n hn) (B.root n hn) (B.root_le n hn)
    (B.block n hn).event (B.block n hn).cell (B.block n hn).caps
    (B.block n hn).measurable (B.block n hn).payment (B.block n hn).frame
    (B.block n hn).localRoot (B.block n hn).paidWindow
    (B.payment n hn) (B.compatible n hn)

noncomputable def BandInputs.interval {lo hi : ℕ} (B : BandInputs lo hi) :
    IntervalInputs lo hi where
  dimension := by have := B.dimension; omega
  row := B.row
  source := fun n _ => BstLean.Part270.fallbackBase_subset n

theorem BandInputs.classifier {lo hi : ℕ} (B : BandInputs lo hi) :
    ∀ n ∈ Icc lo hi, ∀ t : ℝ,
      99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
        {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
          BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := B.interval.classifier

end BstLean.Part287
