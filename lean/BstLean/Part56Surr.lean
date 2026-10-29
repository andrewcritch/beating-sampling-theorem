import BstLean.Part56Defs
import BstLean.Part50Surr
import BstLean.Part50Laws

/-!
# Part 56, wave 1: the surrogate (density ratio and contraction of conditional expectation)

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56Surr`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Status: proved (no `sorry`). Route: Part 50's `surrA_bias` at `A = B = t·vvᵀ`, range bound `C n`
(`0 ≤ t (v·x)² ≤ t ≤ C n` on the sphere) gives `(B_{Q̃} − B_D)² ≤ etaQ(e)² Var_D` pointwise in `M`;
orthogonality for both laws with `h = g_{Q̃} − g_D` (a continuous function of the anchors, through
the weight form) gives `E (g_{Q̃} − g_D)² = E (g_{Q̃} − g_D)(B_{Q̃} − B_D)`, hence `≤ E (B_{Q̃} − B_D)²`.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob Tens TSymm Pn NN baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (LemmaR53 GaussPolar53)
open BstLean.Part48 (SBLevel)

open BstLean.Part41 (contr trL varU)
open BstLean.Part43 (etaQ)
open BstLean.Part50 (qA PSDq)
open BstLean.Part53 (TF sg)

section
variable {n d : ℕ}
theorem qA_rk1 (t : ℝ) (v x : Fin n → ℝ) : qA (rk1 t v) x = t * (∑ i, v i * x i) ^ 2 := by
  unfold qA rk1
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qA_rk1_range (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) : 0 ≤ qA (rk1 t v) x ∧ qA (rk1 t v) x ≤ t := by
  rw [qA_rk1]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
  rw [hv, hx, one_mul] at hcs
  exact ⟨by positivity, by nlinarith [sq_nonneg (∑ i, v i * x i)]⟩

theorem psd_rk1 (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) : PSDq (rk1 t v) := by
  intro x; rw [qA_rk1]; positivity

/-- `∫ X² ≤ ∫ Y²` when `∫ X² = ∫ X Y`. -/
theorem sq_le_of_inner {α : Type*} [MeasurableSpace α] {μ : Measure α} {X Y : α → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (h : ∫ a, X a ^ 2 ∂μ = ∫ a, X a * Y a ∂μ) :
    ∫ a, X a ^ 2 ∂μ ≤ ∫ a, Y a ^ 2 ∂μ := by
  have hXY : Integrable (fun a => X a * Y a) μ := hX.integrable_mul hY
  have hle : ∫ a, X a * Y a ∂μ ≤ ∫ a, (X a ^ 2 + Y a ^ 2) / 2 ∂μ :=
    integral_mono hXY ((hX.integrable_sq.add hY.integrable_sq).div_const 2)
      (fun a => by nlinarith [sq_nonneg (X a - Y a)])
  rw [integral_div, integral_add hX.integrable_sq hY.integrable_sq] at hle
  linarith

/-- The anchors, extended by `0` to all of `ℕ`. -/
noncomputable def extU (u : Fin (d + 1) → Fin n → ℝ) : ℕ → Fin n → ℝ := fun j =>
  if hj : j < d + 1 then u ⟨j, hj⟩ else 0

theorem continuous_gW (k : ℕ) (A : Tens n) (c : KeyRK k d → ℝ) :
    Continuous fun u : Fin (d + 1) → Fin n → ℝ => gW k A c (extU u) := by
  unfold gW
  refine continuous_finsetSum _ fun κ _ => ?_
  split_ifs
  · refine continuous_const.mul ?_
    unfold contr
    refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
    refine continuous_finsetProd _ fun r _ => ?_
    have : (fun u : Fin (d + 1) → Fin n → ℝ => extU u (κ.2 r) (w r)) =
        fun u => u (κ.2 r) (w r) := by
      funext u; unfold extU; rw [dif_pos (κ.2 r).2]
    rw [this]
    exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const

theorem gW_extU (k : ℕ) (A : Tens n) (c : KeyRK k d → ℝ) (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) :
    gW k A c (extU (fun j : Fin (d + 1) => ancRK M v j)) = gW k A c (fun j => ancRK M v j) := by
  unfold gW
  refine Finset.sum_congr rfl fun κ _ => ?_
  congr 3
  funext r
  unfold extU
  rw [dif_pos (κ.2 r).2]

/-- **Surrogate**, from orthogonality and weights, for `e > 0`. -/
theorem propSurr56_of (d k : ℕ) (C e : ℝ) (he : 0 < e) (hO : PropOrth56 d k)
    (hW : PropWeights56 d k) : PropSurr56 d k C e := by
  intro n hn v hv t ht0 ht f0 T hT
  have hn1 : 1 ≤ n := by omega
  set K := KRK C n e
  set D := lawRK n t v
  set Q := surrRK n K t v
  have hD : SphLaw n D := (BstLean.Part50.binghamA_antipodal hn1 _).sph
  have hQ : SphLaw n Q := (BstLean.Part50.binghamKA_antipodal hn1 K _ (psd_rk1 t ht0 v)).sph
  obtain ⟨hbD, hgD, hvD, horD⟩ := hO n D hD v hv f0 T hT
  obtain ⟨hbQ, hgQ, -, horQ⟩ := hO n Q hQ v hv f0 T hT
  set γ := stdGauss (CoefIdxD n d)
  set H : (CoefIdxD n d → ℝ) → ℝ := fun Z =>
    gLineH Q k f0 T v (sg n d • Z) - gLineH D k f0 T v (sg n d • Z) with hHdef
  set h : (Fin (d + 1) → Fin n → ℝ) → ℝ := fun u =>
    gW k (TF k f0 T) (wRK Q d v) (extU u) - gW k (TF k f0 T) (wRK D d v) (extU u) with hhdef
  have hh : Measurable h :=
    ((continuous_gW k _ _).sub (continuous_gW k _ _)).measurable
  have hHh : (fun Z : CoefIdxD n d → ℝ => h (fun j => ancRK (sg n d • Z) v j)) = H := by
    funext Z
    simp only [hhdef, hHdef, gW_extU]
    rw [← hW n Q hQ v hv f0 T hT, ← hW n D hD v hv f0 T hT]
    rfl
  have hHL : MemLp H 2 γ := hgQ.sub hgD
  have hHL' : MemLp (fun Z : CoefIdxD n d → ℝ => h (fun j => ancRK (sg n d • Z) v j)) 2 γ := by
    rw [hHh]; exact hHL
  have h1 := horQ h hh hHL'
  have h2 := horD h hh hHL'
  have hHhZ : ∀ Z : CoefIdxD n d → ℝ, h (fun j => ancRK (sg n d • Z) v j) = H Z := congrFun hHh
  simp only [hHhZ] at h1 h2
  set bQ : (CoefIdxD n d → ℝ) → ℝ := fun Z => BofQ Q k f0 T (sg n d • Z)
  set bD : (CoefIdxD n d → ℝ) → ℝ := fun Z => BofQ D k f0 T (sg n d • Z)
  set gQ : (CoefIdxD n d → ℝ) → ℝ := fun Z => gLineH Q k f0 T v (sg n d • Z)
  set gD : (CoefIdxD n d → ℝ) → ℝ := fun Z => gLineH D k f0 T v (sg n d • Z)
  have iQ : Integrable (fun Z => (bQ Z - gQ Z) * H Z) γ := (hbQ.sub hgQ).integrable_mul hHL
  have iD : Integrable (fun Z => (bD Z - gD Z) * H Z) γ := (hbD.sub hgD).integrable_mul hHL
  have iB : Integrable (fun Z => (bQ Z - bD Z) * H Z) γ := (hbQ.sub hbD).integrable_mul hHL
  have hinner : ∫ Z, H Z ^ 2 ∂γ = ∫ Z, H Z * (bQ Z - bD Z) ∂γ := by
    have e1 : (fun Z => H Z ^ 2) = fun Z => (bQ Z - bD Z) * H Z - (bQ Z - gQ Z) * H Z +
        (bD Z - gD Z) * H Z := by
      funext Z; simp only [hHdef]; ring
    rw [e1, integral_add (f := fun Z => (bQ Z - bD Z) * H Z - (bQ Z - gQ Z) * H Z)
      (g := fun Z => (bD Z - gD Z) * H Z) (iB.sub iQ) iD, integral_sub iB iQ]
    change ∫ Z, (bQ Z - bD Z) * H Z ∂γ - ∫ Z, (bQ Z - gQ Z) * H Z ∂γ +
      ∫ Z, (bD Z - gD Z) * H Z ∂γ = _
    rw [h1, h2]
    simp only [sub_zero, add_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun Z => by ring)
  have hX := sq_le_of_inner hHL (hbQ.sub hbD) hinner
  have hpt : ∀ Z, (bQ Z - bD Z) ^ 2 ≤ etaQ e ^ 2 * varFQ D k f0 T (sg n d • Z) := by
    intro Z
    have hb := BstLean.Part50.surrA_bias (d := d) hn1 (rk1 t v) (rk1 t v) 0 (C * n)
      (fun x _ => by ring) (fun x hx => ⟨(qA_rk1_range t ht0 v hv x hx).1,
        (qA_rk1_range t ht0 v hv x hx).2.trans ht⟩) e he k f0 T (sg n d • Z)
    have hv0 : 0 ≤ varFQ D k f0 T (sg n d • Z) := by
      unfold varFQ varU; exact integral_nonneg fun _ => sq_nonneg _
    have : (bQ Z - bD Z) ^ 2 = |BofQ D k f0 T (sg n d • Z) - BofQ Q k f0 T (sg n d • Z)| ^ 2 := by
      rw [sq_abs]; ring
    rw [this]
    have hq0 : 0 ≤ etaQ e := by unfold etaQ BstLean.Part43.xi43; positivity
    calc _ ≤ (etaQ e * Real.sqrt (varFQ D k f0 T (sg n d • Z))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hv0]
  refine ⟨hHL.integrable_sq, hX.trans ?_⟩
  unfold EV56
  rw [← integral_const_mul]
  exact integral_mono (hbQ.sub hbD).integrable_sq (hvD.const_mul _) hpt

end

end BstLean.Part56
