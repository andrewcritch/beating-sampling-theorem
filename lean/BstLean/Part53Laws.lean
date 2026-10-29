import BstLean.Part53Defs
import BstLean.Part51Laws
import BstLean.Part36Index

/-!
# Part 53, wave 1: the laws and the small algebraic facts

Specification: `delegations/answers/p53-spec-opus.md` §3.11. Proved here, with no `sorry`.
Do not use `native_decide` or `axiom` anywhere.

* `densLaw_sph`: a `DensLaw` is a probability law on the sphere.
* `lawE_dens`: `lawE n U ∝ e^U σ` with `U` continuous and oscillation `≤ Λ` on the sphere is a
  `DensLaw` with ratio in `[e^{−Λ}, e^{Λ}]`.
* `fvA_TF`, `TF_symm`, `heatA_top`, `Ncirc_pos`, `mapMD_linZ`, `gh_unit`: the algebra used by the
  wave-1 provers and by the assembly.
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount glue)

variable {n d : ℕ}


theorem fvA_TF (k : ℕ) (f0 : ℝ) (T : Tens n) (y : Fin n → ℝ) : fvA k (TF k f0 T) y = fval k f0 T y := by
  unfold fvA fval
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [contr, TF]
  · rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by rfl, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [add_comm 1 i]
    unfold contr TF
    apply Finset.sum_congr rfl
    intro w _
    simp only [show i + 1 ≠ 0 by omega, show i + 1 ≤ k by omega, ↓reduceIte]

theorem TF_symm (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (j : ℕ) : IsSymmT (TF k f0 T j) := by
  intro σ w
  unfold TF
  split_ifs with h0 h1
  · rfl
  · exact hT j (by omega) h1 σ w
  · rfl

theorem heatA_top (k : ℕ) (v : ℝ) (A : Tens n) : heatA k v A k = A k := by
  funext w
  unfold heatA
  have : (Finset.range (k + 1)).filter (fun i => k + 2 * i ≤ k) = {0} := by
    ext i; simp
  rw [this, Finset.sum_singleton]
  have hf : ((k.factorial : ℝ) / (k.factorial : ℝ)) = 1 := div_self (by positivity)
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero, hf, one_mul]
  unfold trL
  simp only [Finset.univ_unique, Finset.sum_singleton]
  show A k (glue k 0 default fun t => w ⟨t.1, by have := t.2; omega⟩) = A k w
  congr 1

theorem mapMD_linZ (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    mapMD M x = linZ M (fun p => phiM x p) := by
  classical
  funext a
  unfold mapMD linZ BstLean.Part36.coefD
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun i => ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then M ⟨⟨i, h⟩, (β, a)⟩ else 0) * BstLean.Part36.monoVal x β.1)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  simp [colM, phiM, i.2]

open BstLean.Part40 (SphLaw)
open BstLean.Part51 (lawE OscLE ZE)

theorem densLaw_sph {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (h : DensLaw n μ Λ) :
    SphLaw n μ := by
  obtain ⟨hp, ρ, -, -, hμ, -⟩ := h
  refine ⟨hp, ?_⟩
  rw [hμ]
  exact (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)

private lemma sph_cont_int (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

theorem lawE_dens (hn : 1 ≤ n) (U : (Fin n → ℝ) → ℝ) (hU : Continuous U) (Λ : ℝ) (hosc : OscLE U Λ) :
    DensLaw n (lawE n U) Λ := by
  have hP := BstLean.Part29.uniformSphere_isProbability n hn
  have hc : Continuous (fun x => Real.exp (U x)) := Real.continuous_exp.comp hU
  have hint := sph_cont_int hn hc
  have hz : 0 < ZE n U := integral_exp_pos hint
  refine ⟨(BstLean.Part51.lawE_sph hn U hU).prob, fun x => Real.exp (U x) / ZE n U,
    (hc.div_const _).measurable, fun x => div_nonneg (Real.exp_pos _).le hz.le, rfl, ?_⟩
  intro x hx
  have hup : ZE n U ≤ Real.exp (U x + Λ) := by
    have h := integral_mono_ae hint (integrable_const (Real.exp (U x + Λ)))
      (show (fun y => Real.exp (U y)) ≤ᵐ[uniformSphere n] fun _ => Real.exp (U x + Λ) by
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
        exact Real.exp_le_exp.mpr (by have := hosc y x hy hx; linarith))
    simpa [ZE] using h
  have hlo : Real.exp (U x - Λ) ≤ ZE n U := by
    have h := integral_mono_ae (integrable_const (Real.exp (U x - Λ))) hint
      (show (fun _ => Real.exp (U x - Λ)) ≤ᵐ[uniformSphere n] fun y => Real.exp (U y) by
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
        exact Real.exp_le_exp.mpr (by have := hosc x y hx hy; linarith))
    simpa [ZE] using h
  constructor
  · rw [le_div_iff₀ hz]
    calc Real.exp (-Λ) * ZE n U ≤ Real.exp (-Λ) * Real.exp (U x + Λ) :=
          mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le
      _ = Real.exp (U x) := by rw [← Real.exp_add]; ring_nf
  · rw [div_le_iff₀ hz]
    calc Real.exp (U x) = Real.exp Λ * Real.exp (U x - Λ) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp Λ * ZE n U := mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le

theorem Ncirc_pos (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (f0 : ℝ) (T : Tens n) (hTk : 0 < frob (T k)) :
    0 < Ncirc n d k f0 T := by
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn
  have htop : frob (Tcirc n d k f0 T k) = frob (T k) := by
    unfold Tcirc
    rw [heatA_top]
    congr 1
    funext w
    simp [TF, show k ≠ 0 by omega]
  unfold Ncirc
  apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun c => frob (Tcirc n d k f0 T c) / DD n d ^ c)
    (fun c _ => div_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _) (pow_pos hD c).le)
    (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩))
  rw [htop]
  exact div_pos hTk (pow_pos hD k)


/-- `g^h = g₀` on the sphere. -/
theorem gh_unit (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) (hM : ∑ α, M α ^ 2 = 1) :
    gh n d k f0 T M = g0 n d k f0 T M := by
  unfold gh g0
  rw [hM, one_mul]

end BstLean.Part53
