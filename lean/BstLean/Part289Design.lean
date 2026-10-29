import BstLean.Part272Stated

/-! Part 289: the adopted dimension-dependent residual scale floor.
All centres, tables, nodes, and latitude calculations are shared with Part 272. -/
namespace BstLean.Part289

open Real MeasureTheory
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part157
open BstLean.Part272

variable {n : ℕ}

/-- The adopted residual scale floor. -/
noncomputable def scaleFloor (n : ℕ) : ℝ := if n < 11883 then 17 / 100 else 1 / 5

theorem scaleFloor_low (hn : n < 11883) : scaleFloor n = 17 / 100 := by
  simp only [scaleFloor, if_pos hn]

theorem scaleFloor_high (hn : 11883 ≤ n) : scaleFloor n = 1 / 5 := by
  simp only [scaleFloor, if_neg (not_lt_of_ge hn)]

theorem scaleFloor_bounds (n : ℕ) : (17 / 100 : ℝ) ≤ scaleFloor n ∧ scaleFloor n ≤ 1 / 5 := by
  unfold scaleFloor
  split_ifs <;> norm_num

theorem scaleFloor_pos (n : ℕ) : 0 < scaleFloor n :=
  lt_of_lt_of_le (by norm_num) (scaleFloor_bounds n).1

/-- The existing grid index, named once for floor-parametric mixtures. -/
noncomputable def gridNode (τ : Ret n → ℝ) (c : Ret n) (s : ℝ) : ℕ :=
  nodeIdx (Js n)
    (√(normSq c.1.2) / rhoC c.1.2 (τ c) - 6 * τ c / rhoC c.1.2 (τ c))
    (√(normSq c.1.2) / rhoC c.1.2 (τ c) + 6 * τ c / rhoC c.1.2 (τ c)) s

/-- Only the lower endpoint in the scale maximum changes. -/
noncomputable def gridMixFloor (s₀ : ℝ) (D : Centres n) (τ : Ret n → ℝ)
    (fT wT : Ret n → ℕ → ℝ) (c : Ret n) (s : ℝ) : ℝ × ℝ :=
  ((gridMix D τ fT wT c s).1,
    2 / (n : ℝ) * max s₀ (wT c (gridNode τ c s) - fT c (gridNode τ c s) ^ 2))

theorem gridMixFloor_one_fifth (D : Centres n) (τ : Ret n → ℝ)
    (fT wT : Ret n → ℕ → ℝ) : gridMixFloor (1 / 5) D τ fT wT = gridMix D τ fT wT := rfl

theorem measurable_gridNode {τ : Ret n → ℝ} (hτ : Measurable τ) :
    Measurable (fun p : Ret n × ℝ => gridNode τ p.1 p.2) := by
  have hc : Measurable (fun p : Ret n × ℝ => p.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have ht : Measurable (fun p : Ret n × ℝ => τ p.1) := hτ.comp measurable_fst
  have hr : Measurable (fun p : Ret n × ℝ => rhoC p.1.1.2 (τ p.1)) :=
    (measurable_rhoC (n := n)).comp (hc.prodMk ht)
  have hs := ((measurable_normSq.comp hc).sqrt).div hr
  have hd := (ht.const_mul 6).div hr
  exact measurable_nodeIdx_comp (Js n) (hs.sub hd) (hs.add hd) measurable_snd

theorem measurable_gridMixFloor (s₀ : ℝ) (D : Centres n)
    {τ : Ret n → ℝ} (hτ : Measurable τ) {fT wT : Ret n → ℕ → ℝ}
    (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) :
    Measurable (fun p : Ret n × ℝ => gridMixFloor s₀ D τ fT wT p.1 p.2) := by
  have hg := measurable_gridNode hτ
  have hF := measurable_table_comp hf
    (measurable_fst : Measurable (fun p : Ret n × ℝ => p.1)) hg
  have hW := measurable_table_comp hw
    (measurable_fst : Measurable (fun p : Ret n × ℝ => p.1)) hg
  exact (measurable_gridMix D hτ hf hw).fst.prodMk
    ((measurable_const.max (hW.sub (hF.pow_const 2))).const_mul _)

/-- The paper design with an arbitrary residual scale floor and the same stored tables. -/
noncomputable def paperDesignFloor (n : ℕ) (s₀ : ℝ) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) : Design n :=
  { paperDesign n fT wT hf hw with
    mix := gridMixFloor s₀ (paperCentres n) (fun c => tau0p c.1.1) fT wT
    mmix := measurable_gridMixFloor s₀ (paperCentres n)
      (measurable_tau0p.comp (measurable_fst.comp measurable_fst)) hf hw }

theorem paperDesignFloor_one_fifth (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) :
    paperDesignFloor n (1 / 5) fT wT hf hw = paperDesign n fT wT hf hw := rfl

/-- The revised stated design. The dimension branch changes only the scale floor. -/
noncomputable def statedDesign2 (n : ℕ) : Design n :=
  paperDesignFloor n (scaleFloor n) passFSt passWSt measurable_passFSt measurable_passWSt

theorem statedDesign2_eq (hn : 11883 ≤ n) : statedDesign2 n = statedDesign n := by
  unfold statedDesign2
  rw [scaleFloor_high hn]
  rfl

theorem statedDesign2_toCentres (n : ℕ) :
    (statedDesign2 n).toCentres = (statedDesign n).toCentres := rfl

theorem statedDesign2_tau0 (n : ℕ) : (statedDesign2 n).tau0 = (statedDesign n).tau0 := rfl

theorem statedDesign2_location (c : Ret n) (s : ℝ) :
    ((statedDesign2 n).mix c s).1 = ((statedDesign n).mix c s).1 := rfl

theorem statedDesign2_scale (c : Ret n) (s : ℝ) :
    ((statedDesign2 n).mix c s).2 = 2 / (n : ℝ) * max (scaleFloor n)
      (passWSt c (gridNode (fun c => tau0p c.1.1) c s) -
        passFSt c (gridNode (fun c => tau0p c.1.1) c s) ^ 2) := rfl

/-- Any theorem about the old design transfers on the unchanged upper branch. -/
theorem statedDesign2_transfer (hn : 11883 ≤ n) (P : Design n → Prop)
    (h : P (statedDesign n)) : P (statedDesign2 n) := by
  rw [statedDesign2_eq hn]
  exact h

end BstLean.Part289

/-- info: 'BstLean.Part289.statedDesign2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.statedDesign2_eq

/-- info: 'BstLean.Part289.statedDesign2_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.statedDesign2_transfer
