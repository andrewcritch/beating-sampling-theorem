import BstLean.Part285IntervalRoot12000
import BstLean.Part285IntervalRoot12225
import BstLean.Part285IntervalRoot12525
import BstLean.Part285IntervalRoot12825
import BstLean.Part285IntervalRoot13125
import BstLean.Part285IntervalRoot13225
import BstLean.Part285IntervalRoot13525
import BstLean.Part285IntervalRoot13825
import BstLean.Part285IntervalRoot14125
import BstLean.Part285IntervalRoot14425
import BstLean.Part285IntervalRoot14725
import BstLean.Part285IntervalRoot15025
import BstLean.Part285IntervalRoot15325
import BstLean.Part285IntervalRoot15625
import BstLean.Part285IntervalRoot15925
 
/-! Sharp roots and table prices on 12000–16199, with no per-row proof data. -/
namespace BstLean.Part285.Interval
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part280

noncomputable def rootOnBand (n : ℕ) : ℝ :=
  if n ≤ 12224 then Band12000.root else
  if n ≤ 12524 then Band12225.root else
  if n ≤ 12824 then Band12525.root else
  if n ≤ 13124 then Band12825.root else
  if n ≤ 13224 then Band13125.root else
  if n ≤ 13524 then Band13225.root else
  if n ≤ 13824 then Band13525.root else
  if n ≤ 14124 then Band13825.root else
  if n ≤ 14424 then Band14125.root else
  if n ≤ 14724 then Band14425.root else
  if n ≤ 15024 then Band14725.root else
  if n ≤ 15324 then Band15025.root else
  if n ≤ 15624 then Band15325.root else
  if n ≤ 15924 then Band15625.root else
  Band15925.root

noncomputable def requirementOnBand (n : ℕ) : ℝ :=
  if n ≤ 12224 then Band12000.requirement else
  if n ≤ 12524 then Band12225.requirement else
  if n ≤ 12824 then Band12525.requirement else
  if n ≤ 13124 then Band12825.requirement else
  if n ≤ 13224 then Band13125.requirement else
  if n ≤ 13524 then Band13225.requirement else
  if n ≤ 13824 then Band13525.requirement else
  if n ≤ 14124 then Band13825.requirement else
  if n ≤ 14424 then Band14125.requirement else
  if n ≤ 14724 then Band14425.requirement else
  if n ≤ 15024 then Band14725.requirement else
  if n ≤ 15324 then Band15025.requirement else
  if n ≤ 15624 then Band15325.requirement else
  if n ≤ 15924 then Band15625.requirement else
  Band15925.requirement

noncomputable def capOnBand (n : ℕ) : ℝ :=
  if n ≤ 12224 then Band12000.tableCap else
  if n ≤ 12524 then Band12225.tableCap else
  if n ≤ 12824 then Band12525.tableCap else
  if n ≤ 13124 then Band12825.tableCap else
  if n ≤ 13224 then Band13125.tableCap else
  if n ≤ 13524 then Band13225.tableCap else
  if n ≤ 13824 then Band13525.tableCap else
  if n ≤ 14124 then Band13825.tableCap else
  if n ≤ 14424 then Band14125.tableCap else
  if n ≤ 14724 then Band14425.tableCap else
  if n ≤ 15024 then Band14725.tableCap else
  if n ≤ 15324 then Band15025.tableCap else
  if n ≤ 15624 then Band15325.tableCap else
  if n ≤ 15924 then Band15625.tableCap else
  Band15925.tableCap

theorem select12000 {n : ℕ} (hn : 12000 ≤ n) (hn2 : n ≤ 12224) :
    rootOnBand n = Band12000.root ∧ requirementOnBand n = Band12000.requirement ∧
      capOnBand n = Band12000.tableCap := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_pos hn2]

theorem select12225 {n : ℕ} (hn : 12225 ≤ n) (hn2 : n ≤ 12524) :
    rootOnBand n = Band12225.root ∧ requirementOnBand n = Band12225.requirement ∧
      capOnBand n = Band12225.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_pos hn2]

theorem select12525 {n : ℕ} (hn : 12525 ≤ n) (hn2 : n ≤ 12824) :
    rootOnBand n = Band12525.root ∧ requirementOnBand n = Band12525.requirement ∧
      capOnBand n = Band12525.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_pos hn2]

theorem select12825 {n : ℕ} (hn : 12825 ≤ n) (hn2 : n ≤ 13124) :
    rootOnBand n = Band12825.root ∧ requirementOnBand n = Band12825.requirement ∧
      capOnBand n = Band12825.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_pos hn2]

theorem select13125 {n : ℕ} (hn : 13125 ≤ n) (hn2 : n ≤ 13224) :
    rootOnBand n = Band13125.root ∧ requirementOnBand n = Band13125.requirement ∧
      capOnBand n = Band13125.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos hn2]

theorem select13225 {n : ℕ} (hn : 13225 ≤ n) (hn2 : n ≤ 13524) :
    rootOnBand n = Band13225.root ∧ requirementOnBand n = Band13225.requirement ∧
      capOnBand n = Band13225.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos hn2]

theorem select13525 {n : ℕ} (hn : 13525 ≤ n) (hn2 : n ≤ 13824) :
    rootOnBand n = Band13525.root ∧ requirementOnBand n = Band13525.requirement ∧
      capOnBand n = Band13525.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos hn2]

theorem select13825 {n : ℕ} (hn : 13825 ≤ n) (hn2 : n ≤ 14124) :
    rootOnBand n = Band13825.root ∧ requirementOnBand n = Band13825.requirement ∧
      capOnBand n = Band13825.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  have h6 : ¬ n ≤ 13824 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos hn2]

theorem select14125 {n : ℕ} (hn : 14125 ≤ n) (hn2 : n ≤ 14424) :
    rootOnBand n = Band14125.root ∧ requirementOnBand n = Band14125.requirement ∧
      capOnBand n = Band14125.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  have h6 : ¬ n ≤ 13824 := by omega
  have h7 : ¬ n ≤ 14124 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos hn2]

theorem select14425 {n : ℕ} (hn : 14425 ≤ n) (hn2 : n ≤ 14724) :
    rootOnBand n = Band14425.root ∧ requirementOnBand n = Band14425.requirement ∧
      capOnBand n = Band14425.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  have h6 : ¬ n ≤ 13824 := by omega
  have h7 : ¬ n ≤ 14124 := by omega
  have h8 : ¬ n ≤ 14424 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos hn2]

theorem select14725 {n : ℕ} (hn : 14725 ≤ n) (hn2 : n ≤ 15024) :
    rootOnBand n = Band14725.root ∧ requirementOnBand n = Band14725.requirement ∧
      capOnBand n = Band14725.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  have h6 : ¬ n ≤ 13824 := by omega
  have h7 : ¬ n ≤ 14124 := by omega
  have h8 : ¬ n ≤ 14424 := by omega
  have h9 : ¬ n ≤ 14724 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos hn2]

theorem select15025 {n : ℕ} (hn : 15025 ≤ n) (hn2 : n ≤ 15324) :
    rootOnBand n = Band15025.root ∧ requirementOnBand n = Band15025.requirement ∧
      capOnBand n = Band15025.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  have h6 : ¬ n ≤ 13824 := by omega
  have h7 : ¬ n ≤ 14124 := by omega
  have h8 : ¬ n ≤ 14424 := by omega
  have h9 : ¬ n ≤ 14724 := by omega
  have h10 : ¬ n ≤ 15024 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_pos hn2]

theorem select15325 {n : ℕ} (hn : 15325 ≤ n) (hn2 : n ≤ 15624) :
    rootOnBand n = Band15325.root ∧ requirementOnBand n = Band15325.requirement ∧
      capOnBand n = Band15325.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  have h6 : ¬ n ≤ 13824 := by omega
  have h7 : ¬ n ≤ 14124 := by omega
  have h8 : ¬ n ≤ 14424 := by omega
  have h9 : ¬ n ≤ 14724 := by omega
  have h10 : ¬ n ≤ 15024 := by omega
  have h11 : ¬ n ≤ 15324 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_pos hn2]

theorem select15625 {n : ℕ} (hn : 15625 ≤ n) (hn2 : n ≤ 15924) :
    rootOnBand n = Band15625.root ∧ requirementOnBand n = Band15625.requirement ∧
      capOnBand n = Band15625.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  have h6 : ¬ n ≤ 13824 := by omega
  have h7 : ¬ n ≤ 14124 := by omega
  have h8 : ¬ n ≤ 14424 := by omega
  have h9 : ¬ n ≤ 14724 := by omega
  have h10 : ¬ n ≤ 15024 := by omega
  have h11 : ¬ n ≤ 15324 := by omega
  have h12 : ¬ n ≤ 15624 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_pos hn2]

theorem select15925 {n : ℕ} (hn : 15925 ≤ n) (hn2 : n ≤ 16199) :
    rootOnBand n = Band15925.root ∧ requirementOnBand n = Band15925.requirement ∧
      capOnBand n = Band15925.tableCap := by
  have h0 : ¬ n ≤ 12224 := by omega
  have h1 : ¬ n ≤ 12524 := by omega
  have h2 : ¬ n ≤ 12824 := by omega
  have h3 : ¬ n ≤ 13124 := by omega
  have h4 : ¬ n ≤ 13224 := by omega
  have h5 : ¬ n ≤ 13524 := by omega
  have h6 : ¬ n ≤ 13824 := by omega
  have h7 : ¬ n ≤ 14124 := by omega
  have h8 : ¬ n ≤ 14424 := by omega
  have h9 : ¬ n ≤ 14724 := by omega
  have h10 : ¬ n ≤ 15024 := by omega
  have h11 : ¬ n ≤ 15324 := by omega
  have h12 : ¬ n ≤ 15624 := by omega
  have h13 : ¬ n ≤ 15924 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rootOnBand, requirementOnBand, capOnBand, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12, if_neg h13]

theorem rootOnBand_le_requirement (n : ℕ) (hn : 12000 ≤ n) (hn2 : n ≤ 16199) :
    rootOnBand n ≤ requirementOnBand n := by
  by_cases h0 : n ≤ 12224
  · obtain ⟨hr, hq, _⟩ := select12000 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band12000.root_le_requirement
  by_cases h1 : n ≤ 12524
  · obtain ⟨hr, hq, _⟩ := select12225 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band12225.root_le_requirement
  by_cases h2 : n ≤ 12824
  · obtain ⟨hr, hq, _⟩ := select12525 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band12525.root_le_requirement
  by_cases h3 : n ≤ 13124
  · obtain ⟨hr, hq, _⟩ := select12825 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band12825.root_le_requirement
  by_cases h4 : n ≤ 13224
  · obtain ⟨hr, hq, _⟩ := select13125 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band13125.root_le_requirement
  by_cases h5 : n ≤ 13524
  · obtain ⟨hr, hq, _⟩ := select13225 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band13225.root_le_requirement
  by_cases h6 : n ≤ 13824
  · obtain ⟨hr, hq, _⟩ := select13525 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band13525.root_le_requirement
  by_cases h7 : n ≤ 14124
  · obtain ⟨hr, hq, _⟩ := select13825 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band13825.root_le_requirement
  by_cases h8 : n ≤ 14424
  · obtain ⟨hr, hq, _⟩ := select14125 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band14125.root_le_requirement
  by_cases h9 : n ≤ 14724
  · obtain ⟨hr, hq, _⟩ := select14425 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band14425.root_le_requirement
  by_cases h10 : n ≤ 15024
  · obtain ⟨hr, hq, _⟩ := select14725 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band14725.root_le_requirement
  by_cases h11 : n ≤ 15324
  · obtain ⟨hr, hq, _⟩ := select15025 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band15025.root_le_requirement
  by_cases h12 : n ≤ 15624
  · obtain ⟨hr, hq, _⟩ := select15325 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band15325.root_le_requirement
  by_cases h13 : n ≤ 15924
  · obtain ⟨hr, hq, _⟩ := select15625 (n := n) (by omega) (by omega)
    rw [hr, hq]
    exact Band15625.root_le_requirement
  obtain ⟨hr, hq, _⟩ := select15925 (n := n) (by omega) (by omega)
  rw [hr, hq]
  exact Band15925.root_le_requirement

noncomputable def sharpCertificate {n : ℕ} (hn : 12000 ≤ n) (hn2 : n ≤ 16199) :
    SharpRootCertificate n (rootOnBand n) (intervalCaps (capOnBand n))
      (sharpTableN n) (m2Guard n) := by
  by_cases h0 : n ≤ 12224
  · letI : Fact (12000 ≤ n ∧ n ≤ 12224) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select12000 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band12000.certificate
  by_cases h1 : n ≤ 12524
  · letI : Fact (12225 ≤ n ∧ n ≤ 12524) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select12225 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band12225.certificate
  by_cases h2 : n ≤ 12824
  · letI : Fact (12525 ≤ n ∧ n ≤ 12824) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select12525 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band12525.certificate
  by_cases h3 : n ≤ 13124
  · letI : Fact (12825 ≤ n ∧ n ≤ 13124) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select12825 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band12825.certificate
  by_cases h4 : n ≤ 13224
  · letI : Fact (13125 ≤ n ∧ n ≤ 13224) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select13125 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band13125.certificate
  by_cases h5 : n ≤ 13524
  · letI : Fact (13225 ≤ n ∧ n ≤ 13524) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select13225 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band13225.certificate
  by_cases h6 : n ≤ 13824
  · letI : Fact (13525 ≤ n ∧ n ≤ 13824) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select13525 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band13525.certificate
  by_cases h7 : n ≤ 14124
  · letI : Fact (13825 ≤ n ∧ n ≤ 14124) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select13825 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band13825.certificate
  by_cases h8 : n ≤ 14424
  · letI : Fact (14125 ≤ n ∧ n ≤ 14424) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select14125 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band14125.certificate
  by_cases h9 : n ≤ 14724
  · letI : Fact (14425 ≤ n ∧ n ≤ 14724) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select14425 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band14425.certificate
  by_cases h10 : n ≤ 15024
  · letI : Fact (14725 ≤ n ∧ n ≤ 15024) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select14725 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band14725.certificate
  by_cases h11 : n ≤ 15324
  · letI : Fact (15025 ≤ n ∧ n ≤ 15324) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select15025 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band15025.certificate
  by_cases h12 : n ≤ 15624
  · letI : Fact (15325 ≤ n ∧ n ≤ 15624) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select15325 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band15325.certificate
  by_cases h13 : n ≤ 15924
  · letI : Fact (15625 ≤ n ∧ n ≤ 15924) := ⟨by omega⟩
    obtain ⟨hr, _, hc⟩ := select15625 (n := n) (by omega) (by omega)
    rw [hr, hc]
    exact Band15625.certificate
  letI : Fact (15925 ≤ n ∧ n ≤ 16199) := ⟨by omega⟩
  obtain ⟨hr, _, hc⟩ := select15925 (n := n) (by omega) (by omega)
  rw [hr, hc]
  exact Band15925.certificate

/-- The same root with the smaller price at the actual dimension. -/
noncomputable def sharpCertificate_per_n {n : ℕ} (hn : 12000 ≤ n) (hn2 : n ≤ 16199) :
    SharpRootCertificate n (rootOnBand n) (intervalCaps (smallerTablePrice n))
      (sharpTableN n) (m2Guard n) where
  dimension := by omega
  table_measurable := sharpTableN_measurable
  source_charge := sourceChargeFn_le_m2 (by omega)
  table_payment := sharpTable_smaller_charge hn hn2
  inputs := (sharpCertificate hn hn2).inputs

theorem certified_root_on_interval {n : ℕ} (hn : 12000 ≤ n) (hn2 : n ≤ 16199) :
    ∃ r : ℝ, r ≤ requirementOnBand n ∧
      Nonempty (SharpRootCertificate n r (intervalCaps (smallerTablePrice n))
        (sharpTableN n) (m2Guard n)) :=
  ⟨rootOnBand n, rootOnBand_le_requirement n hn hn2, ⟨sharpCertificate_per_n hn hn2⟩⟩

end BstLean.Part285.Interval
