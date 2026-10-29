import BstLean.Part158Final

/-! Part 196: exact Gaussian primitives before exponential linearization. -/
namespace BstLean.Part196
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part156
open BstLean.Part29 (stdGauss uniformSphere)

/-- The exact primitive uses the actual residual mean and every real tilt. -/
def ExactPrimitive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : Ω → ℝ) (L : ℝ) : Prop :=
  ∀ s : ℝ, ∫ ω, exp (s * p ω / L) ∂μ ≤
    (1 - (∫ ω, p ω ∂μ) + (∫ ω, p ω ∂μ) * exp s) ^ (1 / L)

theorem primitive_log {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → ℝ} {L : ℝ}
    (hL : 0 < L) (hm : Measurable p) (h0 : ∀ ω, 0 ≤ p ω)
    (h1 : ∀ ω, p ω ≤ 1) (h : ExactPrimitive μ p L) (s : ℝ) :
    log (∫ ω, exp (s * p ω) ∂μ) ≤
      log (1 + (∫ ω, p ω ∂μ) * (exp (s * L) - 1)) / L := by
  obtain ⟨hq0, hq1⟩ := integral_mem_01 μ hm h0 h1
  have hb : 0 < 1 - (∫ ω, p ω ∂μ) + (∫ ω, p ω ∂μ) * exp (s * L) := by
    by_cases hq : (∫ ω, p ω ∂μ) = 0
    · rw [hq]; norm_num
    · have hqpos : 0 < ∫ ω, p ω ∂μ := lt_of_le_of_ne hq0 (Ne.symm hq)
      have := mul_pos hqpos (exp_pos (s * L))
      linarith
  have he : (fun ω => exp (s * L * p ω / L)) = fun ω => exp (s * p ω) := by
    funext ω
    congr 1
    field_simp
  have hi := h (s * L)
  rw [he] at hi
  have hl := Real.log_le_log (integral_exp_pos (integrable_exp_mul μ hm h0 h1 s)) hi
  rw [Real.log_rpow hb] at hl
  have heq : 1 - (∫ ω, p ω ∂μ) + (∫ ω, p ω ∂μ) * exp (s * L) =
      1 + (∫ ω, p ω ∂μ) * (exp (s * L) - 1) := by ring
  rw [heq] at hl
  simpa [div_eq_mul_inv, mul_comm] using hl

theorem primitive_linear {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → ℝ} {L : ℝ}
    (hL : 0 < L) (hm : Measurable p) (h0 : ∀ ω, 0 ≤ p ω)
    (h1 : ∀ ω, p ω ≤ 1) (h : ExactPrimitive μ p L) (s : ℝ) :
    ∫ ω, exp (s * p ω) ∂μ ≤ exp (Tfun L s * ∫ ω, p ω ∂μ) := by
  obtain ⟨hq0, hq1⟩ := integral_mem_01 μ hm h0 h1
  exact gp_of_primitive μ hL hq0 hq1 h s

variable {n : ℕ}

theorem world_primitive (hn : 1 ≤ n) (D : Centres n) (t : ℝ) {LW : ℝ}
    (hLW : 0 < LW) {E : Set (Ret n)} (hF : FRAME_W_hyp D LW E) :
    ∀ c ∈ E, ∀ ωA : ResA n,
      ExactPrimitive (resW n) (fun ωW => pRes D t c (ωW, ωA)) LW := by
  intro c hc ωA s
  have hprob := BstLean.Part29.uniformSphere_isProbability (2 * n) (by omega)
  have hv : (0 : ℝ) < 2 / (mW n : ℝ) := by
    have : (0 : ℝ) < (mW n : ℝ) := by exact_mod_cast mW_pos hn
    positivity
  have e : ∀ ωW : ResW n, (uniformSphere (2 * n)).real
        {u | (u, ωW.mulVec (res (D.bW c.1.1) (hid2 c.1.1.1 c.1.1.2 u))) ∈
          setW D t c (agentOf D c ωA)} = pRes D t c (ωW, ωA) :=
    fun ωW => (pRes_eq_frame D t c (ωW, ωA)).symm
  have key := BstLean.Part158.gaussFrameMGF (2 * n) n (mW n)
    (uniformSphere (2 * n)) hprob (D.bW c.1.1)
    (hid2 c.1.1.1 c.1.1.2) (continuous_hid2 c.1.1.1 c.1.1.2).measurable
    (setW D t c (agentOf D c ωA)) (measurableSet_setW D t c _) (2 / (mW n : ℝ)) LW hv hLW
    (hF c hc)
  simpa only [e, resW] using key s

theorem agent_primitive (hn : 1 ≤ n) (D : Design n) (t : ℝ) {LA : ℝ}
    (hLA : 0 < LA) {E : Set (Ret n)} (hF : FRAME_A_hyp D LA E) :
    ∀ c ∈ E, ExactPrimitive (resA n) (PStand D t c) LA := by
  intro c hc u
  have hv : (0 : ℝ) < 2 / (mA n : ℝ) := by
    have : (0 : ℝ) < (mA n : ℝ) := by exact_mod_cast mA_pos hn
    positivity
  have e : ∀ ωA : ResA n, (stdGauss (Fin n)).real
        {ξ | (ξ, ωA.mulVec (res (D.bA c.1 c.2.1.1) (hStand D c ξ))) ∈ setA D t c} =
      PStand D t c ωA := fun ωA => (PStand_eq_frame D t c ωA).symm
  have key := BstLean.Part158.gaussFrameMGF n n (mA n) (stdGauss (Fin n))
    inferInstance (D.bA c.1 c.2.1.1)
    (hStand D c) (measurable_hStand D c) (setA D t c) (measurableSet_setA D t c)
    (2 / (mA n : ℝ)) LA hv hLA (hF c hc)
  simpa only [e, resA] using key u

end BstLean.Part196
