import BstLean.Part293SYScale
import BstLean.Part293SYMass
import BstLean.Part242Pass
import BstLean.Part289Pass

/-! The SY/R reciprocal price for the actual conditional passes with a positive floor. -/
namespace BstLean.Part293
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part241 (fullF varianceTerm measurable_fullF measurable_varianceTerm)
open BstLean.Part228 BstLean.Part242 BstLean.Part289

structure SYPassInputsFloor {n : ℕ} (s₀ : ℝ) (c : Ret n) (split : SplitData n)
    (χ d ε vmax aw af F8 F24 Γ Cv : ℝ) : Prop where
  floor_pos : 0 < s₀
  he : 0 < eR c
  hd : s₀ ≤ d
  hε : ε < 1
  hT : 0 < ε - vmax / d
  haw : 0 < aw
  haf : 0 < af
  hF24 : 0 < F24
  hCv : 0 < Cv
  hχ : 0 ≤ χ
  hSbd : ∀ a ∈ keptIx (paperDesignP n) c split, 2 / (n : ℝ) * d ≤ split.Sb a
  hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ
  hVm : ∀ a ∈ keptIx (paperDesignP n) c split, |varianceTerm c split a| ≤ vmax
  hW : LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 8
    (fun a => (n : ℝ) * (wbR c a - wtR c a)) aw
  hF : LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 8
    (fun a => (n : ℝ) * (fullF c split a - ftR c a)) af
  hf8 : LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 8 (fullF c split) F8
  hf24 : LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 24 (fullF c split) F24
  hR : LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 4
    (fun a => 1 / (split.Sb a / (2 / (n : ℝ)))) Γ
  hV : LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 2
    (fun a => (n : ℝ) * varianceTerm c split a) Cv

theorem conditional_pass_bias_SY_floor {n : ℕ} (hn : 0 < n) (s₀ : ℝ)
    (c : Ret n) (split : SplitData n) {χ d ε vmax aw af F8 F24 Γ Cv : ℝ}
    (P : SYPassInputsFloor s₀ c split χ d ε vmax aw af F8 F24 Γ Cv) :
    BIAS_hyp (idealDesignFloor n s₀) c split (syBiasRoot n χ d ε vmax aw af F8 F24 Γ Cv) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hse : 0 < sqrt (eR c) := sqrt_pos.mpr P.he
  let K := keptIx (paperDesignP n) c split
  have mK : MeasurableSet K :=
    measurableSet_keptSet _ split.mgood (measurableSet_bulkIx _ c) _
  have hKm : ((muI n).restrict K) Set.univ ≤ 1 :=
    (Measure.restrict_le_self Set.univ).trans (by simp)
  have idS : ∀ a, split.Sb a = 2 / (n : ℝ) *
      (wbR c a - fullF c split a ^ 2 - varianceTerm c split a) := by
    intro a
    unfold varianceTerm
    field_simp <;> ring
  have idY : ∀ a, split.Sb a / (2 / (n : ℝ)) =
      wbR c a - fullF c split a ^ 2 - varianceTerm c split a := by
    intro a
    rw [idS]
    field_simp
  have hfloor : ∀ a ∈ K, d ≤ wbR c a - fullF c split a ^ 2 - varianceTerm c split a := by
    intro a ha
    have h := P.hSbd a ha
    rw [idS] at h
    exact (mul_le_mul_iff_right₀ hγ).mp (by simpa only [mul_comm] using h)
  have hR : LBound ((muI n).restrict K) 4
      (fun a => 1 / (wbR c a - fullF c split a ^ 2 - varianceTerm c split a)) Γ := by
    simpa only [idY] using P.hR
  have hscale := SY_scale_floor n hn hKm P.floor_pos hγ P.hd
    (measurable_fullF c split) (measurable_ftR c) (measurable_wbR c) (measurable_wtR c)
    (measurable_varianceTerm c split)
    ((ae_restrict_iff' mK).mpr (Filter.Eventually.of_forall hfloor))
    P.hW P.hF P.hf8 hR P.hV
  have idMixS : ∀ a, ((idealDesignFloor n s₀).mix c
      (latC (idealDesignFloor n s₀) c a)).2 =
        2 / (n : ℝ) * max s₀ (wtR c a - ftR c a ^ 2) := fun _ => rfl
  have idMixF : ∀ a, sqrt (eR c) * (split.lamb a -
      ((idealDesignFloor n s₀).mix c (latC (idealDesignFloor n s₀) c a)).1) =
      fullF c split a - ftR c a := fun a => by
    change sqrt (eR c) * (split.lamb a - ftR c a / sqrt (eR c)) = _
    unfold fullF
    field_simp
  have hS : LBound ((muI n).restrict K) 2
      (fun a => (n : ℝ) * (((idealDesignFloor n s₀).mix c
        (latC (idealDesignFloor n s₀) c a)).2 / split.Sb a - 1))
      (syScale n aw af F8 Γ Cv d) := by
    simpa only [idMixS, idS] using hscale
  have hF : LBound ((muI n).restrict K) 8
      (fun a => (n : ℝ) * (sqrt (eR c) * (split.lamb a -
        ((idealDesignFloor n s₀).mix c (latC (idealDesignFloor n s₀) c a)).1))) af := by
    simpa only [idMixF] using P.hF
  have hmass := SY_exceptional_mass_floor (muI n) mK (measureReal_le_one) hKm n hn
    P.floor_pos hγ P.hd P.haw P.haf P.hF24 P.hCv P.hT
    (measurable_fullF c split) (measurable_ftR c) (measurable_wbR c)
    (measurable_wtR c) (measurable_varianceTerm c split)
    (fun a ha => (idS a) ▸ P.hSbd a ha) P.hVm P.hW P.hF P.hf24 P.hV
  have hmass' : (muI n).real (K ∩ {a | ε <
      |((idealDesignFloor n s₀).mix c (latC (idealDesignFloor n s₀) c a)).2 / split.Sb a - 1|}) ≤
      BstLean.Part241.exceptionalMass n d ε vmax aw af F24 := by
    simpa only [idMixS, idS] using hmass
  have hd0 : 0 < d := P.floor_pos.trans_le P.hd
  have hSb : ∀ a ∈ K, 0 < split.Sb a := fun a ha =>
    (mul_pos hγ hd0).trans_le (P.hSbd a ha)
  have hSt : ∀ a ∈ K, 0 < ((idealDesignFloor n s₀).mix c
      (latC (idealDesignFloor n s₀) c a)).2 := by
    intro a _
    rw [idMixS]
    exact mul_pos hγ (P.floor_pos.trans_le (le_max_left _ _))
  have mSt : Measurable (fun a => ((idealDesignFloor n s₀).mix c
      (latC (idealDesignFloor n s₀) c a)).2) :=
    measurable_snd.comp ((measurable_mix_c _ c).comp (measurable_latC _ c))
  have hp := SY_price (muI n) mK (by simp) n hn split.mSb mSt hγ P.he P.hχ
    (normSq_nonneg _) P.hc P.hε hSb hSt hF P.hR hS hmass'
  exact sqrt_le_sqrt hp

end BstLean.Part293

/-- info: 'BstLean.Part293.conditional_pass_bias_SY_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.conditional_pass_bias_SY_floor
