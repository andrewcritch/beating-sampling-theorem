import BstLean.Part203Stages
import BstLean.Part157Hell

/-! Part 203: exact composition for the actual World and Agent residuals. -/
namespace BstLean.Part203
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part196

theorem network_free_cpr {n : ℕ} (hn : 1 ≤ n) (D : Design n) (t : ℝ)
    {E : Set (Ret n)} {c f H : ℝ} (hc : 0 < c) (hf : 0 < f) (hH : 0 ≤ H)
    (hFW : FRAME_W_hyp D.toCentres (c / n) E)
    (hFA : FRAME_A_hyp D (f / n) E) (hRW : REPLW_test_hyp D H E) :
    ∀ x ∈ E, FreeCPR ((resW n).prod (resA n)) (pRes D.toCentres t x)
      n c f H (QStand D t x) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw := world_primitive hn D.toCentres t (div_pos hc hnR) hFW
  have ha := agent_primitive hn D t (div_pos hf hnR) hFA
  have hr := replw_of_test hn D t hRW
  intro x hx
  rw [← mean_PStand D t x]
  exact free_cpr_of_stages (resW n) (resA n)
    ((measurable_pRes D.toCentres t).comp measurable_prodMk_left)
    (fun ω => pRes_nonneg D.toCentres t x ω)
    (fun ω => pRes_le_one hn D.toCentres t x ω)
    (measurable_PStand D t x) (fun ω => PStand_nonneg D t x ω)
    (fun ω => PStand_le_one D t x ω) hnR hc hf hH
    (hw x hx) (ha x hx) (hr x hx)

/-- A radius cell can use the existing uniform World replacement construction. -/
theorem network_free_cpr_radius {n : ℕ} (hn : 1 ≤ n) (D : Design n) (t : ℝ)
    {H₀ E : Set (Ret n)} {c f H : ℝ} (hc : 0 < c) (hf : 0 < f) (hH : 0 ≤ H)
    (hFW : FRAME_W_hyp D.toCentres (c / n) (goodSet H₀ E (HbarW D) H))
    (hFA : FRAME_A_hyp D (f / n) (goodSet H₀ E (HbarW D) H)) :
    ∀ x ∈ goodSet H₀ E (HbarW D) H,
      FreeCPR ((resW n).prod (resA n)) (pRes D.toCentres t x)
        n c f H (QStand D t x) :=
  network_free_cpr hn D t hc hf hH hFW hFA (replw_test_of_Hbar hn D H H₀ E)

/-- The actual Agent mean lies in the probability interval used by negative END. -/
lemma QStand_mem_01 {n : ℕ} (D : Design n) (t : ℝ) (x : Ret n) :
    0 ≤ QStand D t x ∧ QStand D t x ≤ 1 := by
  rw [← mean_PStand D t x]
  exact integral_mem_01 (resA n) (measurable_PStand D t x)
    (fun ω => PStand_nonneg D t x ω) (fun ω => PStand_le_one D t x ω)

end BstLean.Part203
