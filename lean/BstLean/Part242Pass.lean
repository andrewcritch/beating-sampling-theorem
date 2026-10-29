import BstLean.Part242Price
import BstLean.Part242Mass
import BstLean.Part241Frontier

/-! The SY price uses the same stored conditional passes as Part241. -/
namespace BstLean.Part242
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part241 (fullF varianceTerm measurable_fullF measurable_varianceTerm)
open BstLean.Part228

variable {n : ℕ}

structure SYPassInputs (c : Ret n) (split : SplitData n)
    (χ d ε vmax aw af F8 F24 Γ Cv : ℝ) : Prop where
  he : 0 < eR c
  hd : 1 / 5 ≤ d
  hε : ε < 1
  hT : 0 < ε - vmax / d
  haw : 0 < aw
  haf : 0 < af
  hF24 : 0 < F24
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

noncomputable def syBiasPrice (n : ℕ) (χ d ε vmax aw af F8 F24 Γ Cv : ℝ) : ℝ :=
  syPrice n χ ε af Γ (syScale n aw af F8 Γ Cv d)
    (BstLean.Part241.exceptionalMass n d ε vmax aw af F24)

noncomputable def syBiasRoot (n : ℕ) (χ d ε vmax aw af F8 F24 Γ Cv : ℝ) : ℝ :=
  sqrt (syBiasPrice n χ d ε vmax aw af F8 F24 Γ Cv)

theorem conditional_pass_bias_SY (hn : 0 < n) (c : Ret n) (split : SplitData n)
    {χ d ε vmax aw af F8 F24 Γ Cv : ℝ}
    (P : SYPassInputs c split χ d ε vmax aw af F8 F24 Γ Cv) :
    BIAS_hyp (paperDesignP n) c split (syBiasRoot n χ d ε vmax aw af F8 F24 Γ Cv) := by
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
  have hscale := SY_scale n hn hKm hγ P.hd (measurable_fullF c split)
    (measurable_ftR c) (measurable_wbR c) (measurable_wtR c)
    (measurable_varianceTerm c split)
    ((ae_restrict_iff' mK).mpr (Filter.Eventually.of_forall hfloor))
    P.hW P.hF P.hf8 hR P.hV
  have idMixS : ∀ a, ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2 =
      2 / (n : ℝ) * max (1 / 5) (wtR c a - ftR c a ^ 2) := fun a => by
    rw [mixP_eq]
    rfl
  have idMixF : ∀ a, sqrt (eR c) * (split.lamb a -
      ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1) =
      fullF c split a - ftR c a := fun a => by
    rw [mixP_eq]
    change sqrt (eR c) * (split.lamb a - ftR c a / sqrt (eR c)) = _
    unfold fullF
    field_simp
  have hS : LBound ((muI n).restrict K) 2
      (fun a => (n : ℝ) * (((paperDesignP n).mix c (latC (paperDesignP n) c a)).2 /
        split.Sb a - 1)) (syScale n aw af F8 Γ Cv d) := by
    simpa only [idMixS, idS] using hscale
  have hF : LBound ((muI n).restrict K) 8
      (fun a => (n : ℝ) * (sqrt (eR c) * (split.lamb a -
        ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1))) af := by
    simpa only [idMixF] using P.hF
  have hmass := SY_exceptional_mass (muI n) mK (measureReal_le_one) hKm n hn hγ P.hd
    P.haw P.haf P.hF24 P.hT (measurable_fullF c split) (measurable_ftR c)
    (measurable_wbR c) (measurable_wtR c)
    (fun a ha => (idS a) ▸ P.hSbd a ha) P.hVm P.hW P.hF P.hf24
  have hmass' : (muI n).real (K ∩ {a | ε <
      |((paperDesignP n).mix c (latC (paperDesignP n) c a)).2 / split.Sb a - 1|}) ≤
      BstLean.Part241.exceptionalMass n d ε vmax aw af F24 := by
    simpa only [idMixS, idS] using hmass
  have hd0 : 0 < d := by linarith [P.hd]
  have hSb : ∀ a ∈ K, 0 < split.Sb a := fun a ha =>
    (mul_pos hγ hd0).trans_le (P.hSbd a ha)
  have hSt : ∀ a ∈ K, 0 < ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2 := by
    intro a ha
    rw [idMixS]
    exact mul_pos hγ ((by norm_num : (0 : ℝ) < 1 / 5).trans_le (le_max_left _ _))
  have mSt : Measurable (fun a => ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2) :=
    measurable_snd.comp ((measurable_mix_c _ c).comp (measurable_latC _ c))
  have hp := SY_price (muI n) mK (by simp) n hn split.mSb mSt hγ P.he P.hχ
    (normSq_nonneg _) P.hc P.hε hSb hSt hF P.hR hS hmass'
  exact sqrt_le_sqrt hp

theorem conditional_pass_root_SY (hn : 2 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hc : c.1.2 ≠ 0)
    {χ d ε vmax aw af F8 F24 Γ Cv hfl tl tu : ℝ}
    (P : SYPassInputs c split χ d ε vmax aw af F8 F24 Γ Cv)
    (hF : FLUCT_hyp (paperDesignP n) t c split hfl)
    (hT : BulkChernoffDomain (paperDesignP n) c tl tu) :
    |sqrt (QStand (paperDesignP n) t c) - sqrt (qTilde (paperDesignP n) t c)| ≤
      hfl + syBiasRoot n χ d ε vmax aw af F8 F24 Γ Cv +
        bulkTailRoot (paperDesignP n) c tl tu := by
  exact repla_root_of_split hn (paperDesignP n) t c hc hT.tau_pos split hF
    (conditional_pass_bias_SY (by omega) c split P)
    (tail_hyp_chernoff (paperDesignP n) c hT)

theorem conditional_pass_root_SY_8000 (hn : 8000 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hW : WINDOW (paperDesignP n) c)
    {χ d ε vmax aw af F8 F24 Γ Cv hfl : ℝ}
    (P : SYPassInputs c split χ d ε vmax aw af F8 F24 Γ Cv)
    (hF : FLUCT_hyp (paperDesignP n) t c split hfl) :
    |sqrt (QStand (paperDesignP n) t c) - sqrt (qTilde (paperDesignP n) t c)| ≤
      hfl + syBiasRoot n χ d ε vmax aw af F8 F24 Γ Cv + 1 / 10 ^ 8 + 1 / 10 ^ 20 := by
  have h := conditional_pass_root_SY (by omega) t c split hW.1 P hF
    (bulk_domain_explicit (by omega) (paperDesignP n) c hW)
  have ht := frontierTailRoot_lt hn (paperDesignP n) c hW
  change _ ≤ hfl + syBiasRoot n χ d ε vmax aw af F8 F24 Γ Cv +
    frontierTailRoot (paperDesignP n) c at h
  have hr : (0 : ℝ) ≤ 1 / 10 ^ 20 := by positivity
  linarith

end BstLean.Part242
